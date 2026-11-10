/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
import LibsignalBinary.Heap.Fine.ClientBounds
import LibsignalBinary.Heap.RustStdAllocBudgetBridge
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegDhErr
import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps
import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWrappers
import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit
import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightSpec
import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvCreditHelpers
import LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux
import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
import LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
import LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak
import LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak
import LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
import LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738
import LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
import LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
import LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetSym
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12Budget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux
import LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# Guarded-Tight `W2` (`decryptSignal` `@109`) Exact Slot Credit and Group Specs

**Checked by Lean.**

Proves `ckx2_w2DecSigExact_phaseCredit`, `ckx2_w2DecSigExact_groupSpec`, and
`ckx2_w2DecSigExact_singleSlotFineSpec` for `ckx2_cliDecryptSignalBinaryKitSlotEnvExact`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.CliKitW2RecvExactAuxR2Race

open Arm64.Process (bytesOfString)
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession
  (ChainKey Crypto IdentityKey MessageKeyGenerator MessageKeys Mut PublicKey RatchetState
   ReceiverChain SessionState ShaCompress SignalMessage TripleRatchet maxForwardJumps
   maxMessageKeys maxReceiverChains rootCreateChain)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams pqxdhSpqrModel)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (recGhostOf)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes CIPHERTEXT1_SIZE Chunk DECAPSULATION_KEY_SIZE Epoch Message MlKem
   PqRatchetState SortedSetPt States V1Recv V1State VersionNegotiationPB protoPolyDecoderToPb
   spqrAuthApi spqrPolyApi spqrV1)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendCt
  (Ct1Acknowledged Ct1Sampled Ct2Sampled EkReceivedCt1Sampled HeaderReceived NoHeaderReceived)
open CryptoVerification.LibsignalSpqrV1.Chunked.SendEk
  (Ct1Received EkSentCt1Received HeaderSent KeysSampled KeysUnsampled)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel TrGhost TryDecryptGhost)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup (fromSessionState_exec)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegB
  (dhRatchetStep_none dhRatchetStep_some_eq)
open CryptoVerification.LibsignalTripleRatchetRepr
  (SessionGhost UuidParser coinsOf serviceIdParse uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs Inputs)
open CryptoVerification.SignalSession.Cli (DirGhost StoresGhost pathOf)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (DecSigGhost RunSem runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.DecryptLemmas (toDecryptGhost)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.Poly.AddChunk (addChunkTotal)
open CryptoVerification.SpqrV1.Poly.DecodedMessage (decodedMessageTotal)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.StateSize
  (except_bind_eq_ok optRaw rawAuth rawChCt1Acknowledged rawChCt1Sampled rawChEkSentCt1Received
   rawChHeaderSent rawChNoHeaderReceived rawInnerState rawPolyDec rawUcCt1Sent
   rawUcEkSentCt1Received rawV1State)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs RustCliAllocBudget SeqEnv rustAllocEvents
   rustDeallocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_smallMaxReq_eq smallAllocCost_le_738_of_le_44)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv libcruxHmacSha256Events)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (BoundedFreshEvs aesDecCtShape_groupSpec dhCommitStep12Evs_fine_groupSpec
   fine_rustAlloc_le_28 fine_rustAlloc_le_44 growOne104Env_groupSpec w2AesDecErrEnv_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact
  (w2DecSigExactCum w2DecSigExactGrpS w2DecSigExactLive w2DecSigExactMaxReq w2DecSigExactPeak)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
  (ckx2_DecodeStateTightEnvOf ckx2_EkSentCt1ReceivedRecvCt2ChunkEnv'
   ckx2_RecvCt2ChunkTailEnv' ckx2_RecvEkChunkSendCt2TailEnv'
   ckx2_SpqrRecvC07C09aBytesEnvOf ckx2_SpqrRecvC07C09aTightLinkedEnvOf
   ckx2_SpqrRecvC07C09aTightLinkedEnvRecvOf ckx2_StatesRecvEnv' ckx2_StatesRecvProtoEnv'
   ckx2_TryDecryptCliLinkedEnvOf ckx2_TryDecryptCliLinkedLoopEnvOf
   ckx2_cliDecryptSignalBinaryKitSlotEnvExact ckx2_tryDecryptCmkSeg4EnvOf
   ckx2_tryDecryptCmkSeg4EnvOf_cmk_eq ckx2_w2DecSigExact_groupSpec_Stmt
   ckx2_w2DecSigExact_phaseCredit_Stmt ckx2_w2DecSigExact_singleSlotFineSpec_of_stmts)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W2BinaryWhisperDom W2BinaryWhisperParams decBinaryIdKitPlacedBudget decBinarySessKitPlacedBudget)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.CmkLoopAdvanceCredit
  (cmkLoop25000Live cmkLoop25000MaxReq cmkLoop25000Peak cmkLoop25000TightCum cmkLoop25000TightGrpS
   tryDecryptCmkSeg4Env_fine_groupSpec_tight tryDecryptCmkSeg4Env_fine_phaseCreditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked (tryDecryptEnvArgsToGhost)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (HasFineGroupCredit NonFreeBound PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (decBinaryIdKitPlacedBudgetFixed decBinarySessKitPlacedBudgetFixed
   dirGetEnv_fixed_eq_of_not_overCap not_overCapFile_runFiles_identities
   not_overCapFile_runFiles_sessions)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv DeallocCreditSpec ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
  (StatesIntoPbTightEnv spqrTightEvs_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
  (StatesFromPbTightEnv statesFromPb_fine_phaseCreditSpec_tight
   statesIntoPb_fine_phaseCreditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps (StatesDecPtsNeededBound)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvGroupSpec
  (C07TightGroupSpec StatesRecvTightGroupSpec spqrRecvParts_phaseGroupSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
  (SpqrRecvGhostLink SpqrRecvTightLinkedEnv spqrRecvTightDomain_of_topStateTight_and_link)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (C07TightCreditSpec StatesRecvTightCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit
  (decodedMessage_fine_phaseGroupSpec_split rustAlloc_align16_fine_groupSpec
   rustRealloc_align16_fine_groupSpec spqrTightEvs_fine_phaseGroupSpec_align16
   statesFromPbTightGroupS_split statesFromPbTight_fine_phaseGroupSpec_split
   statesIntoPbTightGroupS_split statesIntoPbTight_fine_phaseGroupSpec_split
   statesRecvTightGroupS_split)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightSpec
  (spqrRecvParts_phaseCreditSpec_tight_uncondHist)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvCreditHelpers
  (NonFreeBound.append_eq PhaseCreditSpec.append_eq addChunkSlots_fine_replicate16_phaseCreditSpec
   addChunkSlots_fine_two_mul_phaseCreditSpec addChunkSlots_nonFreeBound
   decodedMessage_fine_tight_phaseCreditSpec decodedMessage_ptsNeeded_le_576_nonFreeBound
   encodeBytes_fine_1152_phaseCreditSpec encodeBytes_nonFreeBound
   fineSmallAllocCost_le_9789_of_le_1280 libcruxHmacSha256_fine_phaseCreditSpec
   libcruxHmacSha256_phaseCreditSpec ptsLenSum sendCt2ConcatHmac_nonFreeBound
   sendCt2Reserve128_fine_le_1088_phaseCreditSpec sendCt2Reserve128_nonFreeBound
   sendCt2Reserve128_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec
  (AuthUpdateEnv NoHeaderReceivedRecvHdrChunkBodyEnv SendCt2EncoderEnv SendCt2EncoderGrowEnv
   StatesProtocolSizes UnchunkedSendCt2BySizesEnv addChunkTotal_ptsNeeded_uncond
   authUpdate_fine_two_mul_phaseCreditSpec authUpdate_nonFreeBound authUpdate_phaseCreditSpec
   isEkReceivedCt1AckMsg isStatesProtoSized isStatesProtoSized_eq_true_iff optBytesLen
   optBytesLen_decodedMessageTotal_le rawPolyDec_intoPb_eq recvCt2AllocMacCt2Events
   recvHdrChunkTail_fine_le_96_phaseCreditSpec recvHdrChunkTail_nonFreeBound
   sendCt2Encoder_128_32_phaseCreditSpec sendCt2Encoder_fine_128_32_phaseCreditSpec
   sendCt2Encoder_nonFreeBound sliceConcat2Events_phaseCreditSpec statesRecvTightDeltaCum
   statesRecvTightDeltaLive statesRecvTightDeltaPeak statesRecvTightGroupS
   statesRecvTightRawMaxReq unchunkedSendCt2BySizes_fine_le_1088_phaseCreditSpec
   unchunkedSendCt2BySizes_nonFreeBound unchunkedSendCt2BySizes_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCapsAux (StatesPtsBoundedAt)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
  (PeerSpqrStateTight640 peerSpqrStateTight640_of_cliPqInputs_recv)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (TopStateTight)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (ghostCloneValid_of_sessionGhostValid)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec (w2CmkChainTightLive)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak
  (AesDecCtShape dhCommitStep12Evs phaseCreditSpec_aesDecCt phaseCreditSpec_dhCommitStep12)
open LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738 (phaseCreditSpec_boundedFresh_fine_44)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak (phaseCredit_seq_freeOnly)
open LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak
  (W4AesDecErrEnv phaseCredit_dhCommitStep3_small phaseCredit_exists phaseCredit_fromS2GenEnv
   phaseCredit_w4AesDecErr_cancel)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (FromKeyReadyEnv FromLoadPolledEnv FromPostSomeEnv FromRegionSomeEnv FromTrustedTrueEnv
   LoadPollStepEnv SessionGhostValid WithStoresDecEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (GrowOne104Env growOne104Events)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSavePollEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (cliSessionKitLoadPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.SpecPlacedBudget
  (decIdKitPlaced decSessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.DecryptLemmas.TopPlacedBudget
  (CliDecryptSignalSlotEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (sliceConcat2Events)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
  (AddChunkSlotEnv AddChunkSlotsEnv growOnePtEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget (DecodedMessageEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (EncodeBytesEnv encodeBytesAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsBudget (OptSecret32AllocEnv)
open LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
  (SendCt2Reserve128Env sendCt2ConcatHmacEvents sendCt2FlipAllocEvents sendCt2FlipDeallocEvents
   sendCt2Reserve128Events sendCt2Seg23Events)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudgetAux (AesDecCtEnv s8Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudgetAux (s9Env s9From6d0Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitMainBudgetCore
  (DhCommitEnv dhCommitAllocEvents s3CommitDefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep12Budget (dhCommitStep12Events)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhCommitStep3Budget
  (DhCommitStep3Env dhCommitStep3Events dhCommitStep3aEvents)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore
  (dhStepPairEvents s3DefaultEnv s3EnvOf)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
  (FromS2GenEnv FromS3GenEnv FromS4GenEnv FromS5GenEnv FromS6GenEnv FromS7GenEnv FromS8GenEnv
   s1InitTrGhost s3AfterTrGhost seqEnv_mono stdAesOpt)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux (s7Env vmacEvents)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
  (computeMacEvents verifyMacWithAddressesEvents)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.DefsBudget
  (TrApplyEnv TrApplySenderAllocEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## `ckx2_StatesRecvProtoEnv'` Protocol-Size Reduction -/

private theorem ckx2_statesRecvProtoEnv'_eq_of_protocolSizes {F : ShaCompress} (K : MlKem)
    {st : States spqrPolyApi (spqrAuthApi F)} (hproto : StatesProtocolSizes st)
    (msg : Message spqrPolyApi) :
    ckx2_StatesRecvProtoEnv' K st msg = ckx2_StatesRecvEnv' K st msg := by
  unfold ckx2_StatesRecvProtoEnv'
  rw [(isStatesProtoSized_eq_true_iff st).mpr hproto]
  simp only [↓reduceIte]

private theorem ckx2_statesRecvProtoEnv'_eq_of_from_pb {F : ShaCompress} (K : MlKem)
    {pb : V1State} {st : States spqrPolyApi (spqrAuthApi F)}
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st)
    (msg : Message spqrPolyApi) :
    ckx2_StatesRecvProtoEnv' K st msg = ckx2_StatesRecvEnv' K st msg :=
  ckx2_statesRecvProtoEnv'_eq_of_protocolSizes K (StatesProtocolSizes.of_from_pb hfrom) msg

/-! ## Leaf and Aggregate `StatesRecvProtoEnv'` Credit and Group Specs -/

private theorem seq_freeOnly {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E : List AllocEvent → Prop} {cum req : Nat}
    (h : PhaseCreditSpec M E cum 0 0 req) :
    PhaseCreditSpec M (SeqEnv E FreeOnlyEvs) cum 0 0 req :=
  (h.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
    (by omega) (by decide) (by decide) (by omega)

private theorem uc_recv_ek_ct1_eq {F : ShaCompress} (K : MlKem)
    {uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F)}
    {epoch : Epoch} {ekBytes : Bytes}
    {uc1 : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)}
    (h : uc.recv_ek K epoch ekBytes = .ok uc1) :
    uc1.ct1 = uc.ct1 := by
  unfold CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.recv_ek at h
  split at h
  · contradiction
  · split at h
    · cases Except.ok.inj h
      rfl
    · contradiction

private theorem optSecret32Alloc_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M OptSecret32AllocEnv 9603 8227 8227 32 := by
  unfold OptSecret32AllocEnv
  exact ((PhaseCreditSpec.nil M).or
    (PhaseCreditSpec.rustAlloc_aff hM (req := 32) (al := 1) (by decide))).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem optSecret32Alloc_fine_phaseCreditSpec :
    PhaseCreditSpec fineCostModel OptSecret32AllocEnv 738 0 0 32 := by
  unfold OptSecret32AllocEnv
  have h32 := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
    (req := 32) (al := 1) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
    (smallAllocCost_le_738_of_le_44 (by decide))
    (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 32)
  exact ((PhaseCreditSpec.nil fineCostModel).or h32).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem sliceConcat2Events_fine_le_44 {n : Nat} (hn : n ≤ 44) :
    PhaseCreditSpec fineCostModel (· = sliceConcat2Events n) 738 0 0 n := by
  unfold sliceConcat2Events
  split
  · exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  · have hsm : n ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; omega
    exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
      (req := n) (al := 1) (by decide) hsm).mono
      (smallAllocCost_le_738_of_le_44 hn) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl n)

/-- Leaf `PhaseCreditSpec` for `ckx2_RecvCt2ChunkTailEnv'` under `ModelHyps M`
(including the `32`-B `OptSecret32AllocEnv` allocation). -/
private theorem recvCt2ChunkTail'_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (rootKeyLen ct1Len dkLen : Nat) (optCt2 : Option Bytes) :
    let n := optBytesLen optCt2
    PhaseCreditSpec M (ckx2_RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen optCt2)
      (2 * n + 2 * rootKeyLen + 6 * ct1Len + 164417)
      (n + rootKeyLen + 3 * ct1Len + 140430)
      (n + rootKeyLen + 3 * ct1Len + 140430)
      (max n (max (rootKeyLen + 64) (2 * ct1Len + 254))) := by
  cases optCt2 with
  | none =>
    change PhaseCreditSpec M (ckx2_RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen none)
      (2 * 0 + 2 * rootKeyLen + 6 * ct1Len + 164417)
      (0 + rootKeyLen + 3 * ct1Len + 140430)
      (0 + rootKeyLen + 3 * ct1Len + 140430)
      (max 0 (max (rootKeyLen + 64) (2 * ct1Len + 254)))
    exact (PhaseCreditSpec.freeOnly_of_hyps hM).mono (by omega) (by omega) (by omega) (by omega)
  | some ct2Full =>
    change PhaseCreditSpec M (ckx2_RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen (some ct2Full))
      (2 * ct2Full.length + 2 * rootKeyLen + 6 * ct1Len + 164417)
      (ct2Full.length + rootKeyLen + 3 * ct1Len + 140430)
      (ct2Full.length + rootKeyLen + 3 * ct1Len + 140430)
      (max ct2Full.length (max (rootKeyLen + 64) (2 * ct1Len + 254)))
    have h1 :
        PhaseCreditSpec M (· = recvCt2AllocMacCt2Events ct2Full.length)
          (2 * ct2Full.length + 19334) (ct2Full.length + 16518) (ct2Full.length + 16518)
          (max ct2Full.length 128) := by
      unfold recvCt2AllocMacCt2Events
      have ha :
          PhaseCreditSpec M
            (· = if ct2Full.length = 128 then [] else rustAllocEvents (ct2Full.length - 128) 1)
            (2 * (ct2Full.length - 128) + 9539) (ct2Full.length - 128 + 8195)
            (ct2Full.length - 128 + 8195) (ct2Full.length - 128) := by
        split
        · exact (PhaseCreditSpec.nil M).mono (by omega) (by omega) (by omega) (by omega)
        · exact PhaseCreditSpec.rustAlloc_aff hM (req := ct2Full.length - 128) (al := 1)
            (by decide)
      have hb := PhaseCreditSpec.rustAlloc_aff hM (req := 128) (al := 1) (by decide)
      exact (PhaseCreditSpec.append_eq ha hb).mono (by omega) (by omega) (by omega) (by omega)
    have hFree := PhaseCreditSpec.freeOnly_of_hyps hM
    by_cases hlt : ct2Full.length < 128
    · have heq : ckx2_RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen (some ct2Full) = FreeOnlyEvs := by
        funext evs; simp [ckx2_RecvCt2ChunkTailEnv', hlt]
      rw [heq]
      exact hFree.mono (by omega) (by omega) (by omega) (by omega)
    · by_cases hpan : (ct1Len != 960 || dkLen != 2400) = true
      · have heq :
            ckx2_RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen (some ct2Full) =
              SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length) FreeOnlyEvs := by
          funext evs; simp [ckx2_RecvCt2ChunkTailEnv', hlt, hpan]
        rw [heq]
        exact (h1.seq hFree).mono (by omega) (by omega) (by omega) (by omega)
      · have heq :
            ckx2_RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen (some ct2Full) =
              SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length)
                (SeqEnv (· = rustAllocEvents 32 1)
                  (SeqEnv (· = sliceConcat2Events 41)
                    (SeqEnv (· = rustAllocEvents 32 1)
                      (SeqEnv (AuthUpdateEnv rootKeyLen 32)
                        (SeqEnv (SendCt2Reserve128Env ct1Len)
                          (SeqEnv (· = sendCt2ConcatHmacEvents ct1Len)
                            (SeqEnv FreeOnlyEvs
                              (SeqEnv OptSecret32AllocEnv FreeOnlyEvs)))))))) := by
          funext evs
          simp [ckx2_RecvCt2ChunkTailEnv', hlt, hpan,
            LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlacedBudget.OptSecret32AllocEnv]
        rw [heq]
        have h2 := PhaseCreditSpec.rustAlloc_aff hM (req := 32) (al := 1) (by decide)
        have h3 := sliceConcat2Events_phaseCreditSpec hM 41
        have h4 := PhaseCreditSpec.rustAlloc_aff hM (req := 32) (al := 1) (by decide)
        have h5 := authUpdate_phaseCreditSpec hM rootKeyLen 32
        have h6 := sendCt2Reserve128_phaseCreditSpec hM ct1Len
        have h7 :
            PhaseCreditSpec M (· = sendCt2ConcatHmacEvents ct1Len)
              (2 * ct1Len + 48485) (ct1Len + 41358) (ct1Len + 41358) (max (ct1Len + 171) 64) := by
          unfold sendCt2ConcatHmacEvents
          have hc := PhaseCreditSpec.rustAlloc_aff hM (req := 35 + 8 + (ct1Len + 128)) (al := 1)
            (by decide)
          exact (PhaseCreditSpec.append_eq hc (libcruxHmacSha256_phaseCreditSpec hM)).mono
            (by omega) (by omega) (by omega) (by omega)
        have hOpt := optSecret32Alloc_phaseCreditSpec hM
        exact (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq
          (h7.seq (hFree.seq (hOpt.seq hFree))))))))).mono
          (by omega) (by omega) (by omega) (by omega)

/-- Fine-model leaf `PhaseCreditSpec` for `ckx2_RecvCt2ChunkTailEnv'` (`Δlive = 0`, `Δpeak = 0`,
including `738` B from `OptSecret32AllocEnv`). -/
private theorem recvCt2ChunkTail'_fine_two_mul_phaseCreditSpec {rootKeyLen ct1Len : Nat} (dkLen : Nat)
    (hrk : rootKeyLen + 32 ≤ 135167) (hct1 : ct1Len ≤ 1088)
    {optCt2 : Option Bytes} (hn : optBytesLen optCt2 ≤ 160) :
    PhaseCreditSpec fineCostModel (ckx2_RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen optCt2)
      (2 * rootKeyLen + 53867) 0 0 (max (rootKeyLen + 64) 2430) := by
  have hFree := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  cases optCt2 with
  | none =>
    exact hFree.mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  | some ct2Full =>
    dsimp only [optBytesLen] at hn
    by_cases hlt : ct2Full.length < 128
    · have heq : ckx2_RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen (some ct2Full) = FreeOnlyEvs := by
        funext evs; simp [ckx2_RecvCt2ChunkTailEnv', hlt]
      rw [heq]
      exact hFree.mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
    · have h1 :
          PhaseCreditSpec fineCostModel (· = recvCt2AllocMacCt2Events ct2Full.length)
            10527 0 0 128 := by
        unfold recvCt2AllocMacCt2Events
        have ha :
            PhaseCreditSpec fineCostModel
              (· = if ct2Full.length = 128 then [] else rustAllocEvents (ct2Full.length - 128) 1)
              738 0 0 32 := by
          split
          · exact (PhaseCreditSpec.nil fineCostModel).mono
              (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
          · have hsm : ct2Full.length - 128 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
              rw [fineCostModel_smallMaxReq_eq]; omega
            exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
              (req := ct2Full.length - 128) (al := 1) (by decide) hsm).mono
              (smallAllocCost_le_738_of_le_44 (by omega))
              (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
        have hb := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
          (req := 128) (al := 1) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
          (fineSmallAllocCost_le_9789_of_le_1280 (by decide))
          (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 128)
        exact (PhaseCreditSpec.append_eq ha hb).mono
          (by decide) (by decide) (by decide) (by decide)
      by_cases hpan : (ct1Len != 960 || dkLen != 2400) = true
      · have heq :
            ckx2_RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen (some ct2Full) =
              SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length) FreeOnlyEvs := by
          funext evs; simp [ckx2_RecvCt2ChunkTailEnv', hlt, hpan]
        rw [heq]
        exact (h1.seq hFree).mono (by omega) (by decide) (by decide) (by omega)
      · have heq :
            ckx2_RecvCt2ChunkTailEnv' rootKeyLen ct1Len dkLen (some ct2Full) =
              SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length)
                (SeqEnv (· = rustAllocEvents 32 1)
                  (SeqEnv (· = sliceConcat2Events 41)
                    (SeqEnv (· = rustAllocEvents 32 1)
                      (SeqEnv (AuthUpdateEnv rootKeyLen 32)
                        (SeqEnv (SendCt2Reserve128Env ct1Len)
                          (SeqEnv (· = sendCt2ConcatHmacEvents ct1Len)
                            (SeqEnv FreeOnlyEvs
                              (SeqEnv OptSecret32AllocEnv FreeOnlyEvs)))))))) := by
          funext evs
          simp [ckx2_RecvCt2ChunkTailEnv', hlt, hpan,
            LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlacedBudget.OptSecret32AllocEnv]
        rw [heq]
        have h32 := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
          (req := 32) (al := 1) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
          (smallAllocCost_le_738_of_le_44 (by decide))
          (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 32)
        have h41 := sliceConcat2Events_fine_le_44 (n := 41) (by decide)
        have h5 := authUpdate_fine_two_mul_phaseCreditSpec hrk
        have h6 := sendCt2Reserve128_fine_le_1088_phaseCreditSpec hct1
        have h7 :
            PhaseCreditSpec fineCostModel (· = sendCt2ConcatHmacEvents ct1Len)
              15348 0 0 1280 := by
          unfold sendCt2ConcatHmacEvents
          have hsm : 35 + 8 + (ct1Len + 128) ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
            rw [fineCostModel_smallMaxReq_eq]; omega
          have hc := (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps
            (req := 35 + 8 + (ct1Len + 128)) (al := 1) (by decide) hsm).mono
            (fineSmallAllocCost_le_9789_of_le_1280 (by omega))
            (Nat.le_refl 0) (Nat.le_refl 0) (show 35 + 8 + (ct1Len + 128) ≤ 1280 by omega)
          exact (PhaseCreditSpec.append_eq hc libcruxHmacSha256_fine_phaseCreditSpec).mono
            (by decide) (by decide) (by decide) (by decide)
        have hOpt := optSecret32Alloc_fine_phaseCreditSpec
        exact (h1.seq (h32.seq (h41.seq (h32.seq (h5.seq (h6.seq
          (h7.seq (hFree.seq (hOpt.seq hFree))))))))).mono
          (by omega) (by decide) (by decide) (by omega)

private theorem recvEkChunkSendCt2Tail'_fine_le_1088_phaseCreditSpec {F : ShaCompress} (K : MlKem)
    (sendCt2OnDone : Bool)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hct1 : uc.ct1.length ≤ 1088) (optEk : Option Bytes) :
    PhaseCreditSpec fineCostModel (ckx2_RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc optEk)
      205872 0 0 2430 := by
  have hFree := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  cases optEk with
  | none =>
    exact hFree.mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  | some ekBytes =>
    by_cases hsd : (!sendCt2OnDone) = true
    · have heq : ckx2_RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) = FreeOnlyEvs := by
        funext evs; simp [ckx2_RecvEkChunkSendCt2TailEnv', hsd]
      rw [heq]
      exact hFree.mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
    · cases hrek : uc.recv_ek K uc.epoch ekBytes with
      | error _ =>
        have heq : ckx2_RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) = FreeOnlyEvs := by
          funext evs; simp [ckx2_RecvEkChunkSendCt2TailEnv', hsd, hrek]
        rw [heq]
        exact hFree.mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
      | ok uc1 =>
        have hct1' : uc1.ct1.length ≤ 1088 := by
          rw [uc_recv_ek_ct1_eq K hrek]
          exact hct1
        cases hsc : uc1.send_ct2 K with
        | error _ =>
          have heq : ckx2_RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) =
              SeqEnv FreeOnlyEvs FreeOnlyEvs := by
            funext evs; simp [ckx2_RecvEkChunkSendCt2TailEnv', hsd, hrek, hsc]
          rw [heq]
          exact (hFree.seq hFree).mono
            (by decide) (by decide) (by decide) (by decide)
        | ok val =>
          rcases val with ⟨_, _, _⟩
          have heq : ckx2_RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) =
              SeqEnv FreeOnlyEvs
                (SeqEnv (UnchunkedSendCt2BySizesEnv uc1.es uc1.ct1.length)
                  (SendCt2EncoderEnv 128 32)) := by
            funext evs; simp [ckx2_RecvEkChunkSendCt2TailEnv', hsd, hrek, hsc]
          rw [heq]
          have h1 := unchunkedSendCt2BySizes_fine_le_1088_phaseCreditSpec uc1.es hct1'
          have h2 := sendCt2Encoder_fine_128_32_phaseCreditSpec
          exact (hFree.seq (h1.seq h2)).mono
            (by decide) (by decide) (by decide) (by decide)

private theorem raw46880_dec_cum_le {ptsSum rawDec : Nat}
    (hraw : rawDec = 4 * ptsSum + 22 * 16)
    (hle : rawDec ≤ 46880) :
    16 * ptsSum + 9571 * 16 ≤ 339248 := by
  have hp : ptsSum ≤ 11632 := by omega
  have hm : 16 * ptsSum ≤ 16 * 11632 := Nat.mul_le_mul_left 16 hp
  exact Nat.le_trans (Nat.add_le_add_right hm _) (by decide)

private theorem raw46880_dec_req_le {ptsSum rawDec : Nat}
    (hraw : rawDec = 4 * ptsSum + 22 * 16)
    (hle : rawDec ≤ 46880) :
    8 * ptsSum + 16 ≤ 93072 := by
  omega

private theorem raw46880_ct2'_cum_le {ptsSum rk rawDec : Nat}
    (hraw : rawDec = 4 * ptsSum + 22 * 16)
    (hsum : (rk + 960) + rawDec ≤ 46880) :
    (16 * ptsSum + 9571 * 16) + (1022346 + (2 * rk + 53867)) ≤ statesRecvTightDeltaCum := by
  have hcomb : 4 * ptsSum + rk ≤ 45568 := by omega
  have hlin : 16 * ptsSum + 2 * rk ≤ 4 * 45568 := by omega
  have hconst : 4 * 45568 + 9571 * 16 + 1022346 + 53867 ≤ statesRecvTightDeltaCum := by decide
  have h1 : (16 * ptsSum + 9571 * 16) + (1022346 + (2 * rk + 53867)) =
      (16 * ptsSum + 2 * rk) + (9571 * 16 + 1022346 + 53867) := by omega
  rw [h1]
  exact Nat.le_trans (Nat.add_le_add_right hlin _) (by
    simpa only [Nat.add_assoc] using hconst)

private theorem statesRecv'_tight_of_protocolSizes_46880_phaseCreditSpec {F : ShaCompress}
    (K : MlKem)
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hproto : StatesProtocolSizes st)
    (hpts : StatesDecPtsNeededBound st)
    (hraw46 : rawV1State st.into_pb ≤ 46880) :
    PhaseCreditSpec fineCostModel (ckx2_StatesRecvEnv' K st msg)
      statesRecvTightDeltaCum
      statesRecvTightDeltaLive
      statesRecvTightDeltaPeak
      statesRecvTightRawMaxReq := by
  have hFree :
      PhaseCreditSpec fineCostModel FreeOnlyEvs
        statesRecvTightDeltaCum 0 0 statesRecvTightRawMaxReq :=
    (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  cases st with
  | keysUnsampled _ => exact hFree
  | keysSampled s =>
    dsimp only [ckx2_StatesRecvEnv']
    split
    · cases msg.payload <;> try exact hFree
      dsimp only [StatesProtocolSizes] at hproto
      have h1 := addChunkSlots_fine_replicate16_phaseCreditSpec
      have h2 : PhaseCreditSpec fineCostModel (EncodeBytesEnv s.uc.ek.length) 33744 0 0 1152 := by
        rw [hproto]
        exact encodeBytes_fine_1152_phaseCreditSpec
      exact (seq_freeOnly fineCostModel_modelHyps (h1.seq h2)).mono
        (by decide) (by decide) (by decide) (by decide)
    · exact hFree
  | headerSent s =>
    dsimp only [ckx2_StatesRecvEnv']
    split
    · cases msg.payload with
      | ct1 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have hraw := rawPolyDec_intoPb_eq s.receiving_ct1
        rw [hproto] at hraw
        have hdec_le :
            rawPolyDec (protoPolyDecoderToPb s.receiving_ct1.intoPb) ≤ 46880 := by
          refine Nat.le_trans ?_ hraw46
          dsimp only [States.into_pb, HeaderSent.into_pb, spqrPolyApi,
            rawV1State, rawInnerState, rawChHeaderSent, optRaw]
          omega
        have hreq93 := raw46880_dec_req_le hraw hdec_le
        have h1 := (hproto ▸ addChunkSlots_fine_two_mul_phaseCreditSpec s.receiving_ct1.pts
          (by omega)).mono (raw46880_dec_cum_le hraw hdec_le)
          (Nat.le_refl 0) (Nat.le_refl 0) hreq93
        let rCt1 := addChunkTotal s.receiving_ct1 chunk
        have hr_pts : rCt1.ptsNeeded ≤ 480 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rCt1) (by omega)).mono
          (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
          (show max 256 (2 * rCt1.ptsNeeded) ≤ 960 by omega)
        exact (seq_freeOnly fineCostModel_modelHyps (h1.seq h2)).mono
          (by decide) (by decide) (by decide) (by decide)
      | _ => exact hFree
    · exact hFree
  | ct1Received _ =>
    dsimp only [ckx2_StatesRecvEnv']
    split
    · cases msg.payload <;> try exact hFree
      exact (seq_freeOnly fineCostModel_modelHyps
        addChunkSlots_fine_replicate16_phaseCreditSpec).mono
        (by decide) (by decide) (by decide) (by decide)
    · exact hFree
  | ekSentCt1Received s =>
    dsimp only [ckx2_StatesRecvEnv']
    split
    · cases msg.payload with
      | ct2 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        obtain ⟨hlen16, hct1⟩ := hproto
        have hraw := rawPolyDec_intoPb_eq s.receiving_ct2
        rw [hlen16] at hraw
        have hsum_le :
            (s.uc.auth.rootKey.length + 960) +
              rawPolyDec (protoPolyDecoderToPb s.receiving_ct2.intoPb) ≤ 46880 := by
          refine Nat.le_trans ?_ hraw46
          dsimp only [States.into_pb, EkSentCt1Received.into_pb,
            CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.into_pb,
            spqrAuthApi, Authenticator.intoPb, spqrPolyApi,
            rawV1State, rawInnerState, rawChEkSentCt1Received, rawUcEkSentCt1Received,
            rawAuth, optRaw]
          omega
        have hbody :
            PhaseCreditSpec fineCostModel
              (ckx2_EkSentCt1ReceivedRecvCt2ChunkEnv' s msg.epoch chunk)
              statesRecvTightDeltaCum 0 0 statesRecvTightRawMaxReq := by
          unfold ckx2_EkSentCt1ReceivedRecvCt2ChunkEnv'
          split
          · exact (PhaseCreditSpec.nil fineCostModel).mono
              (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
          · dsimp only
            let rCt2 := addChunkTotal s.receiving_ct2 chunk
            have hr_pts : rCt2.ptsNeeded ≤ 80 :=
              Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
            have h1 :
                PhaseCreditSpec fineCostModel (AddChunkSlotsEnv s.receiving_ct2.pts)
                  (16 * ptsLenSum s.receiving_ct2.pts + 9571 * 16) 0 0 91152 := by
              have hb := addChunkSlots_fine_two_mul_phaseCreditSpec s.receiving_ct2.pts
                (by omega)
              rw [hlen16] at hb
              exact hb.mono (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
            have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rCt2) (by omega)).mono
              (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
              (show max 256 (2 * rCt2.ptsNeeded) ≤ 256 by omega)
            have hn160 : optBytesLen (decodedMessageTotal rCt2) ≤ 160 := by
              have := optBytesLen_decodedMessageTotal_le rCt2; omega
            have h3 := (recvCt2ChunkTail'_fine_two_mul_phaseCreditSpec
              (rootKeyLen := s.uc.auth.rootKey.length) (ct1Len := s.uc.ct1.length)
              s.uc.dk.length (by omega) (by omega) hn160).mono
              (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
              (show max (s.uc.auth.rootKey.length + 64) 2430 ≤ 45632 by omega)
            exact (h1.seq (h2.seq h3)).mono
              (raw46880_ct2'_cum_le hraw hsum_le)
              (by decide) (by decide) (by decide)
        exact seq_freeOnly fineCostModel_modelHyps hbody
      | _ => exact hFree
    · exact hFree
  | noHeaderReceived s =>
    dsimp only [ckx2_StatesRecvEnv']
    split
    · cases msg.payload with
      | hdr chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have hraw := rawPolyDec_intoPb_eq s.receiving_hdr
        rw [hproto] at hraw
        have hdec_le :
            rawPolyDec (protoPolyDecoderToPb s.receiving_hdr.intoPb) ≤ 46880 := by
          refine Nat.le_trans ?_ hraw46
          dsimp only [States.into_pb, NoHeaderReceived.into_pb, spqrPolyApi,
            rawV1State, rawInnerState, rawChNoHeaderReceived, optRaw]
          omega
        have hbody :
            PhaseCreditSpec fineCostModel
              (NoHeaderReceivedRecvHdrChunkBodyEnv s msg.epoch chunk)
              statesRecvTightDeltaCum 0 0 statesRecvTightRawMaxReq := by
          unfold NoHeaderReceivedRecvHdrChunkBodyEnv
          split
          · exact (PhaseCreditSpec.nil fineCostModel).mono
              (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
          · dsimp only
            let rHdr := addChunkTotal s.receiving_hdr chunk
            have hr_pts : rHdr.ptsNeeded ≤ 48 :=
              Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
            have h1 := (hproto ▸ addChunkSlots_fine_two_mul_phaseCreditSpec s.receiving_hdr.pts
              (by omega)).mono (raw46880_dec_cum_le hraw hdec_le)
              (Nat.le_refl 0) (Nat.le_refl 0) (raw46880_dec_req_le hraw hdec_le)
            have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rHdr) (by omega)).mono
              (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
              (show max 256 (2 * rHdr.ptsNeeded) ≤ 256 by omega)
            have hn96 : optBytesLen (decodedMessageTotal rHdr) ≤ 96 := by
              have := optBytesLen_decodedMessageTotal_le rHdr; omega
            have h3 := recvHdrChunkTail_fine_le_96_phaseCreditSpec hn96
            exact (h1.seq (h2.seq h3)).mono (by decide) (by decide) (by decide) (by decide)
        exact seq_freeOnly fineCostModel_modelHyps hbody
      | _ => exact hFree
    · exact hFree
  | headerReceived _ => exact hFree
  | ct1Sampled s =>
    dsimp only [ckx2_StatesRecvEnv']
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
      obtain ⟨hlen16, hct1⟩ := hproto
      have hraw := rawPolyDec_intoPb_eq s.receiving_ek
      rw [hlen16] at hraw
      have hdec_le :
          rawPolyDec (protoPolyDecoderToPb s.receiving_ek.intoPb) ≤ 46880 := by
        refine Nat.le_trans ?_ hraw46
        dsimp only [States.into_pb, Ct1Sampled.into_pb,
          CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.into_pb,
          spqrPolyApi, rawV1State, rawInnerState, rawChCt1Sampled, rawUcCt1Sent, optRaw]
        omega
      have hArm : ∀ (chunk : spqrPolyApi.Chunk) (ack : Bool),
          PhaseCreditSpec fineCostModel
            (SeqEnv
              (SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
                (SeqEnv (DecodedMessageEnv (addChunkTotal s.receiving_ek chunk))
                  (ckx2_RecvEkChunkSendCt2TailEnv' K ack s.uc
                    (decodedMessageTotal (addChunkTotal s.receiving_ek chunk)))))
              FreeOnlyEvs)
            statesRecvTightDeltaCum 0 0 statesRecvTightRawMaxReq := fun chunk ack => by
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := (hlen16 ▸ addChunkSlots_fine_two_mul_phaseCreditSpec s.receiving_ek.pts
          (by omega)).mono (raw46880_dec_cum_le hraw hdec_le)
          (Nat.le_refl 0) (Nat.le_refl 0) (raw46880_dec_req_le hraw hdec_le)
        have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rEk) hr_pts).mono
          (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
          (show max 256 (2 * rEk.ptsNeeded) ≤ 1152 by omega)
        have h3 := recvEkChunkSendCt2Tail'_fine_le_1088_phaseCreditSpec K ack s.uc
          (by omega) (decodedMessageTotal rEk)
        exact seq_freeOnly fineCostModel_modelHyps
          ((h1.seq (h2.seq h3)).mono (by decide) (by decide) (by decide) (by decide))
      cases msg.payload <;> dsimp only <;> first | exact hFree | exact hArm _ _
    · exact hFree
  | ekReceivedCt1Sampled s =>
    dsimp only [ckx2_StatesRecvEnv']
    split
    · cases isEkReceivedCt1AckMsg msg
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hFree
      · simp only [↓reduceIte]
        cases s.uc.send_ct2 K with
        | error _ => exact hFree
        | ok val =>
          rcases val with ⟨_, _, _⟩
          dsimp only [StatesProtocolSizes] at hproto
          have h1 := unchunkedSendCt2BySizes_fine_le_1088_phaseCreditSpec s.uc.es
            (ct1Len := s.uc.ct1.length) (by omega)
          have h2 := sendCt2Encoder_fine_128_32_phaseCreditSpec
          exact (seq_freeOnly fineCostModel_modelHyps (h1.seq h2)).mono
            (by decide) (by decide) (by decide) (by decide)
    · exact hFree
  | ct1Acknowledged s =>
    dsimp only [ckx2_StatesRecvEnv']
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
      obtain ⟨hlen16, hct1⟩ := hproto
      have hraw := rawPolyDec_intoPb_eq s.receiving_ek
      rw [hlen16] at hraw
      have hdec_le :
          rawPolyDec (protoPolyDecoderToPb s.receiving_ek.intoPb) ≤ 46880 := by
        refine Nat.le_trans ?_ hraw46
        dsimp only [States.into_pb, Ct1Acknowledged.into_pb,
          CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.into_pb,
          spqrPolyApi, rawV1State, rawInnerState, rawChCt1Acknowledged, rawUcCt1Sent, optRaw]
        omega
      cases msg.payload <;> dsimp only <;> try exact hFree
      all_goals
        rename_i chunk
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := (hlen16 ▸ addChunkSlots_fine_two_mul_phaseCreditSpec s.receiving_ek.pts
          (by omega)).mono (raw46880_dec_cum_le hraw hdec_le)
          (Nat.le_refl 0) (Nat.le_refl 0) (raw46880_dec_req_le hraw hdec_le)
        have h2 := (decodedMessage_fine_tight_phaseCreditSpec (dec := rEk) hr_pts).mono
          (Nat.le_refl _) (Nat.le_refl 0) (Nat.le_refl 0)
          (show max 256 (2 * rEk.ptsNeeded) ≤ 1152 by omega)
        have h3 := recvEkChunkSendCt2Tail'_fine_le_1088_phaseCreditSpec K true s.uc
          (by omega) (decodedMessageTotal rEk)
        exact seq_freeOnly fineCostModel_modelHyps
          ((h1.seq (h2.seq h3)).mono (by decide) (by decide) (by decide) (by decide))
    · exact hFree
  | ct2Sampled _ => exact hFree

private theorem ckx2_statesRecvProtoEnv'_tight_creditSpec {F : ShaCompress} (K : MlKem)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hpts : StatesDecPtsNeededBound st0)
    (_hpts640 : StatesPtsBoundedAt 640 st0)
    (hraw46 : rawV1State st0.into_pb ≤ 46880) :
    PhaseCreditSpec fineCostModel (ckx2_StatesRecvProtoEnv' K st0 msg)
      statesRecvTightDeltaCum 0 0 statesRecvTightRawMaxReq := by
  by_cases hb : isStatesProtoSized st0 = true
  · have hproto := (isStatesProtoSized_eq_true_iff st0).mp hb
    rw [ckx2_statesRecvProtoEnv'_eq_of_protocolSizes K hproto msg]
    exact statesRecv'_tight_of_protocolSizes_46880_phaseCreditSpec K st0 msg hproto hpts hraw46
  · have heq : ckx2_StatesRecvProtoEnv' K st0 msg = FreeOnlyEvs := by
      unfold ckx2_StatesRecvProtoEnv'; simp [hb]
    rw [heq]
    exact (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)


private theorem append_eq_groupSpec
    {a b : List AllocEvent} {g₁ g₂ : Nat}
    (h₁ : PhaseGroupSpec fineCostModel (· = a) g₁) (h₂ : PhaseGroupSpec fineCostModel (· = b) g₂) :
    PhaseGroupSpec fineCostModel (· = a ++ b) (g₁ + g₂) :=
  (h₁.concat h₂).of_imp fun _ h => ⟨a, b, h, rfl, rfl⟩

private theorem seq_freeOnly_right {E : List AllocEvent → Prop} {g : Nat}
    (h : PhaseGroupSpec fineCostModel E g) :
    PhaseGroupSpec fineCostModel (SeqEnv E FreeOnlyEvs) g :=
  (h.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero g))

private theorem addChunkSlot_fine_phaseGroupSpec (s : SortedSetPt) :
    PhaseGroupSpec fineCostModel (AddChunkSlotEnv s) 140011 := by
  unfold AddChunkSlotEnv
  have hgrow : PhaseGroupSpec fineCostModel (· = growOnePtEvents s.vec.length) 140011 := by
    unfold growOnePtEvents
    split
    · exact rustAlloc_align16_fine_groupSpec (by decide)
    · exact rustRealloc_align16_fine_groupSpec (by decide)
  exact ((PhaseGroupSpec.nil fineCostModel).or hgrow).mono
    (Nat.max_le.mpr ⟨Nat.zero_le 140011, Nat.le_refl 140011⟩)

private theorem addChunkSlots_fine_phaseGroupSpec :
    ∀ (pts : List SortedSetPt),
      PhaseGroupSpec fineCostModel (AddChunkSlotsEnv pts) (140011 * pts.length)
  | [] => (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | s :: rest => by
    dsimp only [AddChunkSlotsEnv]
    have h1 := addChunkSlot_fine_phaseGroupSpec s
    have h2 := addChunkSlots_fine_phaseGroupSpec rest
    refine (h1.seq h2).mono ?_
    rw [List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm]

private theorem replicate_flatten_groupSpec {evs0 : List AllocEvent} {g : Nat}
    (h : PhaseGroupSpec fineCostModel (· = evs0) g) :
    ∀ n : Nat, PhaseGroupSpec fineCostModel (· = (List.replicate n evs0).flatten) (n * g)
  | 0 => by simpa using PhaseGroupSpec.nil fineCostModel
  | n + 1 => by
    simp only [List.replicate_succ, List.flatten_cons, Nat.succ_mul]
    exact (append_eq_groupSpec h (replicate_flatten_groupSpec h n)).mono
      (Nat.le_of_eq (Nat.add_comm g (n * g)))

private theorem encodeBytes_160_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (EncodeBytesEnv 160) 2083248 := by
  have hcond : 160 ≤ 1048576 ∧ 160 % 2 = 0 ∧ 0 < 160 := by decide
  unfold EncodeBytesEnv encodeBytesAllocEvents
  simp only [hcond, and_self, ↓reduceIte]
  have h160 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 160 2) 130203 :=
    (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 160) (align := 2)
      (by decide) (by decide)).mono (by decide)
  exact (replicate_flatten_groupSpec h160 16).mono (by decide)

private theorem encodeBytes_1152_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (EncodeBytesEnv 1152) 524288 := by
  have hcond : 1152 ≤ 1048576 ∧ 1152 % 2 = 0 ∧ 0 < 1152 := by decide
  unfold EncodeBytesEnv encodeBytesAllocEvents
  simp only [hcond, and_self, ↓reduceIte]
  have h1152 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 1152 2) 32768 :=
    (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 1152) (align := 2)
      (by decide) (by decide)).mono (by decide)
  exact (replicate_flatten_groupSpec h1152 16).mono (by decide)

private theorem sliceConcat2Events_align16_phaseGroupSpec (n : Nat) :
    PhaseGroupSpec fineCostModel (· = sliceConcat2Events n) 140011 := by
  unfold sliceConcat2Events
  split
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le 140011)
  · exact rustAlloc_align16_fine_groupSpec (by decide)

private theorem libcruxHmacSha256_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (· = libcruxHmacSha256Events) 121290 := by
  unfold libcruxHmacSha256Events
  have ha64 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 64 1) 34877 :=
    (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 64) (align := 1)
      (by decide) (by decide)).mono (by decide)
  have hd64 := PhaseGroupSpec.rustDealloc fineCostModel 64 1
  have ha32 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 32 1) 16659 :=
    (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 32) (align := 1)
      (by decide) (by decide)).mono (by decide)
  exact (append_eq_groupSpec
    (append_eq_groupSpec
      (append_eq_groupSpec
        (append_eq_groupSpec
          (append_eq_groupSpec
            (append_eq_groupSpec ha64 ha64) ha64) hd64) hd64) hd64) ha32).mono (by decide)

private theorem sendCt2Seg23_fine_phaseGroupSpec (es : Bytes) :
    PhaseGroupSpec fineCostModel (· = sendCt2Seg23Events es) 205547 := by
  unfold sendCt2Seg23Events sendCt2FlipAllocEvents sendCt2FlipDeallocEvents
  have h128 := rustAlloc_align16_fine_groupSpec (sz := 128) (al := 1) (by decide)
  split
  · have h2080 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 2080 1) 65536 :=
      (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 2080) (align := 1)
        (by decide) (by decide)).mono (by decide)
    have hd2080 := PhaseGroupSpec.rustDealloc fineCostModel 2080 1
    exact (append_eq_groupSpec (append_eq_groupSpec h2080 h128) hd2080).mono (by decide)
  · simpa only [List.nil_append, List.append_nil] using h128.mono (by decide)

private theorem sendCt2Reserve128_fine_phaseGroupSpec (ct1Len : Nat) :
    PhaseGroupSpec fineCostModel (SendCt2Reserve128Env ct1Len) 140011 where
  groups_le b {evs} := by
    rintro (rfl | ⟨cap, _, _, rfl⟩)
    · simp [AllocCostModel.stepEvents_nil]
    · unfold sendCt2Reserve128Events
      dsimp only
      split
      · exact (rustAlloc_align16_fine_groupSpec (by decide)).groups_le b rfl
      · exact (rustRealloc_align16_fine_groupSpec (by decide)).groups_le b rfl

private theorem sendCt2ConcatHmac_960_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (· = sendCt2ConcatHmacEvents 960) 154058 := by
  unfold sendCt2ConcatHmacEvents
  have hc : PhaseGroupSpec fineCostModel (· = rustAllocEvents (35 + 8 + (960 + 128)) 1) 32768 :=
    (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 35 + 8 + (960 + 128)) (align := 1)
      (by decide) (by decide)).mono (by decide)
  exact (append_eq_groupSpec hc libcruxHmacSha256_fine_phaseGroupSpec).mono (by decide)

private theorem unchunkedSendCt2BySizes_960_fine_phaseGroupSpec (es : Bytes) :
    PhaseGroupSpec fineCostModel (UnchunkedSendCt2BySizesEnv es 960) 499616 := by
  unfold UnchunkedSendCt2BySizesEnv
  have h1 := sendCt2Seg23_fine_phaseGroupSpec es
  have h2 := sendCt2Reserve128_fine_phaseGroupSpec 960
  have h3 := sendCt2ConcatHmac_960_fine_phaseGroupSpec
  have h4 := PhaseGroupSpec.freeOnly fineCostModel
  exact (((h1.concat h2).concat h3).concat h4).mono (by decide)

private theorem sendCt2EncoderGrow_128_32_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (SendCt2EncoderGrowEnv 128 32) 140011 where
  groups_le b {evs} := by
    rintro (⟨_, rfl⟩ | ⟨newCap, _, _, rfl⟩)
    · simp [AllocCostModel.stepEvents_nil]
    · split
      · exact (rustAlloc_align16_fine_groupSpec (by decide)).groups_le b rfl
      · exact (rustRealloc_align16_fine_groupSpec (by decide)).groups_le b rfl

private theorem sendCt2Encoder_128_32_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel (SendCt2EncoderEnv 128 32) 2363270 := by
  unfold SendCt2EncoderEnv
  have h1 := sliceConcat2Events_align16_phaseGroupSpec 128
  have h2 := sendCt2EncoderGrow_128_32_fine_phaseGroupSpec
  have h3 := encodeBytes_160_fine_phaseGroupSpec
  have h4 := PhaseGroupSpec.freeOnly fineCostModel
  exact (h1.seq (h2.seq (h3.seq h4))).mono (by decide)

private theorem recvEkChunkSendCt2Tail'_960_fine_phaseGroupSpec {F : ShaCompress} (K : MlKem)
    (sendCt2OnDone : Bool)
    (uc : CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (hct1 : uc.ct1.length = 960) (optEk : Option Bytes) :
    PhaseGroupSpec fineCostModel (ckx2_RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc optEk) 2862886 := by
  have hFree := PhaseGroupSpec.freeOnly fineCostModel
  cases optEk with
  | none => exact hFree.mono (Nat.zero_le _)
  | some ekBytes =>
    by_cases hsd : (!sendCt2OnDone) = true
    · have heq : ckx2_RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) = FreeOnlyEvs := by
        funext evs; simp [ckx2_RecvEkChunkSendCt2TailEnv', hsd]
      rw [heq]
      exact hFree.mono (Nat.zero_le _)
    · cases hrek : uc.recv_ek K uc.epoch ekBytes with
      | error _ =>
        have heq : ckx2_RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) = FreeOnlyEvs := by
          funext evs; simp [ckx2_RecvEkChunkSendCt2TailEnv', hsd, hrek]
        rw [heq]
        exact hFree.mono (Nat.zero_le _)
      | ok uc1 =>
        have hct1' : uc1.ct1.length = 960 := by
          rw [uc_recv_ek_ct1_eq K hrek]
          exact hct1
        cases hsc : uc1.send_ct2 K with
        | error _ =>
          have heq : ckx2_RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) =
              SeqEnv FreeOnlyEvs FreeOnlyEvs := by
            funext evs; simp [ckx2_RecvEkChunkSendCt2TailEnv', hsd, hrek, hsc]
          rw [heq]
          exact (hFree.seq hFree).mono (by decide)
        | ok val =>
          rcases val with ⟨_, _, _⟩
          have heq : ckx2_RecvEkChunkSendCt2TailEnv' K sendCt2OnDone uc (some ekBytes) =
              SeqEnv FreeOnlyEvs
                (SeqEnv (UnchunkedSendCt2BySizesEnv uc1.es uc1.ct1.length)
                  (SendCt2EncoderEnv 128 32)) := by
            funext evs; simp [ckx2_RecvEkChunkSendCt2TailEnv', hsd, hrek, hsc]
          rw [heq]
          have h1 : PhaseGroupSpec fineCostModel
              (UnchunkedSendCt2BySizesEnv uc1.es uc1.ct1.length) 499616 := by
            rw [hct1']
            exact unchunkedSendCt2BySizes_960_fine_phaseGroupSpec uc1.es
          exact (hFree.seq (h1.seq sendCt2Encoder_128_32_fine_phaseGroupSpec)).mono (by decide)

private theorem authUpdate_fine_phaseGroupSpec (rootKeyLen kLen : Nat) :
    PhaseGroupSpec fineCostModel (AuthUpdateEnv rootKeyLen kLen) 700055 := by
  unfold AuthUpdateEnv
  have h1 := sliceConcat2Events_align16_phaseGroupSpec (rootKeyLen + kLen)
  have h2 := sliceConcat2Events_align16_phaseGroupSpec (Authenticator.updateLabel.length + 8)
  have h3 := rustAlloc_align16_fine_groupSpec (sz := 64) (al := 1) (by decide)
  have h4 := rustAlloc_align16_fine_groupSpec (sz := 32) (al := 1) (by decide)
  have hf := PhaseGroupSpec.freeOnly fineCostModel
  exact (h1.seq (h2.seq (h3.seq (h4.seq (hf.seq (h4.seq hf)))))).mono (by decide)

private theorem optSecret32Alloc_fine_phaseGroupSpec :
    PhaseGroupSpec fineCostModel OptSecret32AllocEnv 16659 := by
  unfold OptSecret32AllocEnv
  have h32 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 32 1) 16659 :=
    (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 32) (align := 1)
      (by decide) (by decide)).mono (by decide)
  exact ((PhaseGroupSpec.nil fineCostModel).or h32).mono (by decide)

private theorem recvCt2ChunkTail'_960_fine_phaseGroupSpec (rootKeyLen dkLen : Nat)
    (optCt2 : Option Bytes) :
    PhaseGroupSpec fineCostModel (ckx2_RecvCt2ChunkTailEnv' rootKeyLen 960 dkLen optCt2) 1590815 := by
  have hFree := PhaseGroupSpec.freeOnly fineCostModel
  cases optCt2 with
  | none => exact hFree.mono (Nat.zero_le _)
  | some ct2Full =>
    by_cases hlt : ct2Full.length < 128
    · have heq : ckx2_RecvCt2ChunkTailEnv' rootKeyLen 960 dkLen (some ct2Full) = FreeOnlyEvs := by
        funext evs; simp [ckx2_RecvCt2ChunkTailEnv', hlt]
      rw [heq]
      exact hFree.mono (Nat.zero_le _)
    · have h1 : PhaseGroupSpec fineCostModel
          (· = recvCt2AllocMacCt2Events ct2Full.length) 280022 := by
        unfold recvCt2AllocMacCt2Events
        have ha : PhaseGroupSpec fineCostModel
            (· = if ct2Full.length = 128 then [] else rustAllocEvents (ct2Full.length - 128) 1)
            140011 := by
          split
          · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
          · exact rustAlloc_align16_fine_groupSpec (by decide)
        have hb := rustAlloc_align16_fine_groupSpec (sz := 128) (al := 1) (by decide)
        exact append_eq_groupSpec ha hb
      by_cases hpan : (dkLen != 2400) = true
      · have heq :
            ckx2_RecvCt2ChunkTailEnv' rootKeyLen 960 dkLen (some ct2Full) =
              SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length) FreeOnlyEvs := by
          funext evs; simp [ckx2_RecvCt2ChunkTailEnv', hlt, hpan]
        rw [heq]
        exact (h1.seq hFree).mono (by decide)
      · have heq :
            ckx2_RecvCt2ChunkTailEnv' rootKeyLen 960 dkLen (some ct2Full) =
              SeqEnv (· = recvCt2AllocMacCt2Events ct2Full.length)
                (SeqEnv (· = rustAllocEvents 32 1)
                  (SeqEnv (· = sliceConcat2Events 41)
                    (SeqEnv (· = rustAllocEvents 32 1)
                      (SeqEnv (AuthUpdateEnv rootKeyLen 32)
                        (SeqEnv (SendCt2Reserve128Env 960)
                          (SeqEnv (· = sendCt2ConcatHmacEvents 960)
                            (SeqEnv FreeOnlyEvs
                              (SeqEnv OptSecret32AllocEnv FreeOnlyEvs)))))))) := by
          funext evs
          simp [ckx2_RecvCt2ChunkTailEnv', hlt, hpan,
            LibsignalBinary.Proofs.SpqrV1.States.RecvCt2Chunk.DefsPlacedBudget.OptSecret32AllocEnv]
        rw [heq]
        have h32 : PhaseGroupSpec fineCostModel (· = rustAllocEvents 32 1) 16659 :=
          (PhaseGroupSpec.rustAlloc_small fineCostModel (size := 32) (align := 1)
            (by decide) (by decide)).mono (by decide)
        have h41 := sliceConcat2Events_align16_phaseGroupSpec 41
        have h5 := authUpdate_fine_phaseGroupSpec rootKeyLen 32
        have h6 := sendCt2Reserve128_fine_phaseGroupSpec 960
        have h7 := sendCt2ConcatHmac_960_fine_phaseGroupSpec
        have hOpt := optSecret32Alloc_fine_phaseGroupSpec
        exact (h1.seq (h32.seq (h41.seq (h32.seq (h5.seq (h6.seq
          (h7.seq (hFree.seq (hOpt.seq hFree))))))))).mono (by decide)

private theorem statesRecv'_tight_phaseGroupSpec_split {F : ShaCompress} (K : MlKem)
    (st : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hproto : StatesProtocolSizes st)
    (hpts : StatesDecPtsNeededBound st) :
    PhaseGroupSpec fineCostModel (ckx2_StatesRecvEnv' K st msg) statesRecvTightGroupS_split := by
  have hFree : PhaseGroupSpec fineCostModel FreeOnlyEvs statesRecvTightGroupS_split :=
    (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
  have hSlots16 : ∀ (pts : List SortedSetPt), pts.length = 16 →
      PhaseGroupSpec fineCostModel (AddChunkSlotsEnv pts) 2240176 := fun pts hlen => by
    have h := addChunkSlots_fine_phaseGroupSpec pts
    rw [hlen] at h
    exact h.mono (by decide)
  cases st with
  | keysUnsampled _ => exact hFree
  | keysSampled s =>
    dsimp only [ckx2_StatesRecvEnv']
    split
    · cases msg.payload <;> try exact hFree
      dsimp only [StatesProtocolSizes] at hproto
      have h1 := hSlots16 (List.replicate 16 SortedSetPt.new) (by simp)
      have h2 : PhaseGroupSpec fineCostModel (EncodeBytesEnv s.uc.ek.length) 524288 := by
        rw [hproto]
        exact encodeBytes_1152_fine_phaseGroupSpec
      exact (seq_freeOnly_right (h1.seq h2)).mono (by decide)
    · exact hFree
  | headerSent s =>
    dsimp only [ckx2_StatesRecvEnv']
    split
    · cases msg.payload with
      | ct1 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have hr_pts : (addChunkTotal s.receiving_ct1 chunk).ptsNeeded ≤ 576 := by
          have := addChunkTotal_ptsNeeded_uncond s.receiving_ct1 chunk; omega
        have h1 := hSlots16 s.receiving_ct1.pts hproto
        have h2 := decodedMessage_fine_phaseGroupSpec_split hr_pts
        exact (seq_freeOnly_right (h1.seq h2)).mono (by decide)
      | _ => exact hFree
    · exact hFree
  | ct1Received _ =>
    dsimp only [ckx2_StatesRecvEnv']
    split
    · cases msg.payload <;> try exact hFree
      exact (seq_freeOnly_right (hSlots16 (List.replicate 16 SortedSetPt.new) (by simp))).mono
        (by decide)
    · exact hFree
  | ekSentCt1Received s =>
    dsimp only [ckx2_StatesRecvEnv']
    split
    · cases msg.payload with
      | ct2 chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        obtain ⟨hlen16, hct1⟩ := hproto
        have hbody : PhaseGroupSpec fineCostModel
            (ckx2_EkSentCt1ReceivedRecvCt2ChunkEnv' s msg.epoch chunk) statesRecvTightGroupS_split := by
          unfold ckx2_EkSentCt1ReceivedRecvCt2ChunkEnv'
          split
          · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
          · dsimp only
            let rCt2 := addChunkTotal s.receiving_ct2 chunk
            have hr_pts : rCt2.ptsNeeded ≤ 576 :=
              Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond s.receiving_ct2 chunk))
                (Nat.le_trans hpts (by decide))
            have h1 := hSlots16 s.receiving_ct2.pts hlen16
            have h2 := decodedMessage_fine_phaseGroupSpec_split hr_pts
            have h3 : PhaseGroupSpec fineCostModel
                (ckx2_RecvCt2ChunkTailEnv' s.uc.auth.rootKey.length s.uc.ct1.length s.uc.dk.length
                  (decodedMessageTotal rCt2)) 1590815 := by
              rw [hct1]
              exact recvCt2ChunkTail'_960_fine_phaseGroupSpec s.uc.auth.rootKey.length s.uc.dk.length
                (decodedMessageTotal rCt2)
            exact (h1.seq (h2.seq h3)).mono (by decide)
        exact seq_freeOnly_right hbody
      | _ => exact hFree
    · exact hFree
  | noHeaderReceived s =>
    dsimp only [ckx2_StatesRecvEnv']
    split
    · cases msg.payload with
      | hdr chunk =>
        dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
        have hbody : PhaseGroupSpec fineCostModel
            (NoHeaderReceivedRecvHdrChunkBodyEnv s msg.epoch chunk) statesRecvTightGroupS_split := by
          unfold NoHeaderReceivedRecvHdrChunkBodyEnv
          split
          · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
          · dsimp only
            let rHdr := addChunkTotal s.receiving_hdr chunk
            have hr_pts : rHdr.ptsNeeded ≤ 576 :=
              Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond s.receiving_hdr chunk))
                (Nat.le_trans hpts (by decide))
            have h1 := hSlots16 s.receiving_hdr.pts hproto
            have h2 := decodedMessage_fine_phaseGroupSpec_split hr_pts
            have h3 := PhaseGroupSpec.of_nonFreeBound fineCostModel
              (recvHdrChunkTail_nonFreeBound (decodedMessageTotal rHdr))
            exact (h1.seq (h2.seq h3)).mono (by decide)
        exact seq_freeOnly_right hbody
      | _ => exact hFree
    · exact hFree
  | headerReceived _ => exact hFree
  | ct1Sampled s =>
    dsimp only [ckx2_StatesRecvEnv']
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
      obtain ⟨hlen16, hct1⟩ := hproto
      have hArm : ∀ (chunk : spqrPolyApi.Chunk) (ack : Bool),
          PhaseGroupSpec fineCostModel
            (SeqEnv
              (SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
                (SeqEnv (DecodedMessageEnv (addChunkTotal s.receiving_ek chunk))
                  (ckx2_RecvEkChunkSendCt2TailEnv' K ack s.uc
                    (decodedMessageTotal (addChunkTotal s.receiving_ek chunk)))))
              FreeOnlyEvs)
            statesRecvTightGroupS_split := fun chunk ack => by
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := hSlots16 s.receiving_ek.pts hlen16
        have h2 := decodedMessage_fine_phaseGroupSpec_split hr_pts
        have h3 := recvEkChunkSendCt2Tail'_960_fine_phaseGroupSpec K ack s.uc hct1
          (decodedMessageTotal rEk)
        exact seq_freeOnly_right ((h1.seq (h2.seq h3)).mono (by decide))
      cases msg.payload <;> dsimp only <;> first | exact hFree | exact hArm _ _
    · exact hFree
  | ekReceivedCt1Sampled s =>
    dsimp only [ckx2_StatesRecvEnv']
    split
    · cases isEkReceivedCt1AckMsg msg
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hFree
      · simp only [↓reduceIte]
        cases s.uc.send_ct2 K with
        | error _ => exact hFree
        | ok val =>
          rcases val with ⟨_, _, _⟩
          dsimp only [StatesProtocolSizes] at hproto
          have h1 : PhaseGroupSpec fineCostModel
              (UnchunkedSendCt2BySizesEnv s.uc.es s.uc.ct1.length) 499616 := by
            rw [hproto]
            exact unchunkedSendCt2BySizes_960_fine_phaseGroupSpec s.uc.es
          exact (seq_freeOnly_right (h1.seq sendCt2Encoder_128_32_fine_phaseGroupSpec)).mono
            (by decide)
    · exact hFree
  | ct1Acknowledged s =>
    dsimp only [ckx2_StatesRecvEnv']
    split
    · dsimp only [StatesDecPtsNeededBound, StatesProtocolSizes] at hpts hproto
      obtain ⟨hlen16, hct1⟩ := hproto
      have hArm : ∀ (chunk : spqrPolyApi.Chunk),
          PhaseGroupSpec fineCostModel
            (SeqEnv
              (SeqEnv (AddChunkSlotsEnv s.receiving_ek.pts)
                (SeqEnv (DecodedMessageEnv (addChunkTotal s.receiving_ek chunk))
                  (ckx2_RecvEkChunkSendCt2TailEnv' K true s.uc
                    (decodedMessageTotal (addChunkTotal s.receiving_ek chunk)))))
              FreeOnlyEvs)
            statesRecvTightGroupS_split := fun chunk => by
        let rEk := addChunkTotal s.receiving_ek chunk
        have hr_pts : rEk.ptsNeeded ≤ 576 :=
          Nat.le_trans (Nat.le_of_eq (addChunkTotal_ptsNeeded_uncond _ _)) hpts
        have h1 := hSlots16 s.receiving_ek.pts hlen16
        have h2 := decodedMessage_fine_phaseGroupSpec_split hr_pts
        have h3 := recvEkChunkSendCt2Tail'_960_fine_phaseGroupSpec K true s.uc hct1
          (decodedMessageTotal rEk)
        exact seq_freeOnly_right ((h1.seq (h2.seq h3)).mono (by decide))
      cases msg.payload <;> dsimp only <;> first | exact hFree | exact hArm _
    · exact hFree
  | ct2Sampled _ => exact hFree

private theorem ckx2_statesRecvProtoEnv'_tight_split_groupSpec {F : ShaCompress} (K : MlKem)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hpts : StatesDecPtsNeededBound st0)
    (hpts640 : StatesPtsBoundedAt 640 st0)
    (hraw46 : rawV1State st0.into_pb ≤ 46880) :
    PhaseGroupSpec fineCostModel (ckx2_StatesRecvProtoEnv' K st0 msg) statesRecvTightGroupS_split := by
  have _ : StatesPtsBoundedAt 640 st0 ∧ rawV1State st0.into_pb ≤ 46880 := ⟨hpts640, hraw46⟩
  by_cases hb : isStatesProtoSized st0 = true
  · have hproto := (isStatesProtoSized_eq_true_iff st0).mp hb
    rw [ckx2_statesRecvProtoEnv'_eq_of_protocolSizes K hproto msg]
    exact statesRecv'_tight_phaseGroupSpec_split K st0 msg hproto hpts
  · have heq : ckx2_StatesRecvProtoEnv' K st0 msg = FreeOnlyEvs := by
      unfold ckx2_StatesRecvProtoEnv'; simp [hb]
    rw [heq]
    exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)

/-! ## `try_decrypt` Segment Constants and Leaf Specs -/

/-- Tight `dh_ratchet_step` (`S3`) bounds at `rc ≤ 5`. -/
private abbrev w4cTdS3Cum : Nat := 15309
private abbrev w4cTdS3MaxReq : Nat := 1040
private abbrev w4cTdS3GrpS : Nat := 5 * 16659 + 3 * FineScale

/-- Tight `CmkLoopAdvanceEvs` (`S4`) bounds at `maxJumps = 25,000`, `mk ≤ 2,000`. -/
private abbrev w4cTdS4Cum : Nat := cmkLoop25000TightCum
private abbrev w4cTdS4Live : Nat := cmkLoop25000Live
private abbrev w4cTdS4Peak : Nat := cmkLoop25000Peak
private abbrev w4cTdS4MaxReq : Nat := cmkLoop25000MaxReq
private abbrev w4cTdS4GrpS : Nat := cmkLoop25000TightGrpS

/-- Tight linked `spqr::recv` (`S5`) bounds. -/
private abbrev w4cTdS5Cum : Nat := 23313687
private abbrev w4cTdS5Live : Nat := 605066
private abbrev w4cTdS5Peak : Nat := 621350
private abbrev w4cTdS5MaxReq : Nat := 302480
private abbrev w4cTdS5GrpSOf (maxOps : Nat) : Nat :=
  140011 * maxOps + (statesFromPbTightGroupS_split + statesRecvTightGroupS_split +
    (421107504 + statesIntoPbTightGroupS_split))

/-- Tight `verify_mac_with_addresses` + `23`-B error box (`S7`) bounds. -/
private abbrev w4cTdS7Cum : Nat := 2952
private abbrev w4cTdS7MaxReq : Nat := 36
private abbrev w4cTdS7GrpS : Nat := 3 * 16659 + 11056

/-- Tight `aes_cbc_decrypt` (`S8`) and `apply_to_session_state` (`S9`) bounds. -/
private abbrev w4cTdS8CumOf (maxCt : Nat) : Nat := 2 * maxCt + 9539
private abbrev w4cTdS8LiveOf (maxCt : Nat) : Nat := maxCt + 8195
private abbrev w4cTdS8PeakOf (maxCt : Nat) : Nat := maxCt + 8195
private abbrev w4cTdS8GrpS : Nat := 3 * FineScale

private abbrev w4cTdS9Cum : Nat := 4428
private abbrev w4cTdS9MaxReq : Nat := 33
private abbrev w4cTdS9GrpS : Nat := 6 * 16659

private abbrev w4cTdCumOf (maxCt : Nat) : Nat :=
  w4cTdS3Cum + w4cTdS4Cum + w4cTdS5Cum + w4cTdS7Cum + w4cTdS8CumOf maxCt + w4cTdS9Cum

private abbrev w4cTdLiveOf (maxCt : Nat) : Nat :=
  w4cTdS4Live + w4cTdS5Live + w4cTdS8LiveOf maxCt

private abbrev w4cTdPeakOf (maxCt : Nat) : Nat :=
  max w4cTdS4Peak (w4cTdS4Live + max w4cTdS5Peak (w4cTdS5Live + w4cTdS8PeakOf maxCt))

private abbrev w4cTdMaxReqOf (maxCt : Nat) : Nat :=
  max w4cTdS4MaxReq maxCt

private abbrev w4cTdGrpSOf (maxOps : Nat) : Nat :=
  w4cTdS3GrpS + w4cTdS4GrpS + w4cTdS5GrpSOf maxOps + w4cTdS7GrpS + w4cTdS8GrpS + w4cTdS9GrpS

private theorem td0_rustAlloc_le_44_credit {sz : Nat} (hsz : sz ≤ 44) :
    PhaseCreditSpec fineCostModel (· = rustAllocEvents sz 1) 738 0 0 sz := by
  have hb : PhaseCreditSpec fineCostModel (BoundedFreshEvs 1 1 sz) 738 0 0 sz := by
    simpa using phaseCreditSpec_boundedFresh_fine_44 (k := 1) (maxLen := 1) hsz
  refine hb.of_imp fun evs heq => ?_
  subst heq
  unfold BoundedFreshEvs
  by_cases h0 : sz = 0
  · subst h0
    simp [rustAllocEvents, LibsignalBinary.Proofs.PeakBudget.GroupCreditKit.nonFreeCount,
      eventStepReq, eventStepAlign]
  · have h1 : 1 ≤ sz := Nat.one_le_iff_ne_zero.mpr h0
    simp [rustAllocEvents, h1, LibsignalBinary.Proofs.PeakBudget.GroupCreditKit.nonFreeCount,
      eventStepReq, eventStepAlign]

private theorem td0_dhStepPairEvents_credit (C : Crypto) (their : PublicKey)
    (our : CryptoGames.LibsignalSession.PrivateKey) :
    PhaseCreditSpec fineCostModel (· = dhStepPairEvents C their our) 738 0 0 32 := by
  have hb : PhaseCreditSpec fineCostModel (BoundedFreshEvs 1 2 32) 738 0 0 32 := by
    simpa using phaseCreditSpec_boundedFresh_fine_44 (k := 1) (maxLen := 2) (maxReq := 32) (by decide)
  refine hb.of_imp fun evs heq => ?_
  subst heq
  unfold dhStepPairEvents
  cases CryptoVerification.LibsignalTripleRatchet.calculateAgreement C.X their our with
  | none =>
    simp [BoundedFreshEvs, LibsignalBinary.Proofs.PeakBudget.GroupCreditKit.nonFreeCount]
  | some _ =>
    simp [BoundedFreshEvs, rustAllocEvents, rustDeallocEvents,
      LibsignalBinary.Proofs.PeakBudget.GroupCreditKit.nonFreeCount,
      eventStepReq, eventStepAlign]

private theorem td0_dhStepPairEvents_group (C : Crypto) (their : PublicKey)
    (our : CryptoGames.LibsignalSession.PrivateKey) :
    PhaseGroupSpec fineCostModel (· = dhStepPairEvents C their our) 16659 := by
  unfold dhStepPairEvents
  cases CryptoVerification.LibsignalTripleRatchet.calculateAgreement C.X their our with
  | none => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | some _ =>
    have ha := fine_rustAlloc_le_44 (sz := 32) (al := 1) (by decide) (by decide)
    have hd := PhaseGroupSpec.rustDealloc fineCostModel 32 1
    exact ((ha.concat hd).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩).mono (by omega)

private theorem td0_dhCommitStep12Events_eq : dhCommitStep12Events = dhCommitStep12Evs :=
  rfl

private theorem td0_s3Commit_credit (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8)))
    (hrc : tr.ratchet.receiverChains.length ≤ 5) :
    PhaseCreditSpec fineCostModel (s3CommitDefaultEnv x trG tr) 13833 0 0 1040 := by
  unfold s3CommitDefaultEnv DhCommitEnv dhCommitAllocEvents
  have h33 : 33 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hc33 := smallAllocCost_le_738_of_le_44 (req := 33) (by decide)
  have hc32 := smallAllocCost_le_738_of_le_44 (req := 32) (by decide)
  have h12 : PhaseCreditSpec fineCostModel (· = dhCommitStep12Events) 2214 0 0 33 := by
    rw [td0_dhCommitStep12Events_eq]
    exact (phaseCreditSpec_dhCommitStep12 fineCostModel h33).mono
      (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 33)
  let rcBv := BitVec.ofNat 64 tr.ratchet.receiverChains.length
  have h3 : PhaseCreditSpec fineCostModel (DhCommitStep3Env trG.ratchet.chainsCap rcBv)
      11619 0 0 1040 := by
    by_cases heq : rcBv = trG.ratchet.chainsCap
    · have hcap5 : trG.ratchet.chainsCap.toNat ≤ 5 := by
        rw [← heq, BitVec.toNat_ofNat]
        exact Nat.le_trans (Nat.mod_le _ _) hrc
      have hsm : max (2 * 5) 4 * 104 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
        rw [fineCostModel_smallMaxReq_eq]; decide
      exact (phaseCredit_dhCommitStep3_small fineCostModel_modelHyps hcap5 hsm).mono
        (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
    · have hd33 := PhaseCreditSpec.rustDealloc_align16 fineCostModel (req := 33) (al := 1) (by decide)
      have himp : ∀ evs, DhCommitStep3Env trG.ratchet.chainsCap rcBv evs →
          evs = rustDeallocEvents 33 1 := by
        rintro _ rfl
        simp [dhCommitStep3Events, dhCommitStep3aEvents, heq]
      exact (hd33.of_imp himp).mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  have h123 : PhaseCreditSpec fineCostModel
      (· = dhCommitStep12Events ++ dhCommitStep3Events trG.ratchet.chainsCap rcBv)
      13833 0 0 1040 :=
    ((h12.concat h3).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  exact (h123.seq (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)).mono
    (by omega) (by omega) (by omega) (by decide)

private theorem td0_s3Commit_group (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    PhaseGroupSpec fineCostModel (s3CommitDefaultEnv x trG tr) (3 * 16659 + 3 * FineScale) := by
  unfold s3CommitDefaultEnv DhCommitEnv dhCommitAllocEvents
  have h12 : PhaseGroupSpec fineCostModel (· = dhCommitStep12Events) (3 * 16659) := by
    rw [td0_dhCommitStep12Events_eq]; exact dhCommitStep12Evs_fine_groupSpec
  let rcBv := BitVec.ofNat 64 tr.ratchet.receiverChains.length
  have h3a : PhaseGroupSpec fineCostModel
      (· = dhCommitStep3aEvents trG.ratchet.chainsCap rcBv) (3 * FineScale) := by
    unfold dhCommitStep3aEvents
    split
    · exact growOne104Env_groupSpec fineCostModel trG.ratchet.chainsCap
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  have h3 : PhaseGroupSpec fineCostModel (· = dhCommitStep3Events trG.ratchet.chainsCap rcBv)
      (3 * FineScale) := by
    unfold dhCommitStep3Events
    exact ((h3a.concat (PhaseGroupSpec.rustDealloc fineCostModel 33 1)).of_imp
      fun _ h => ⟨_, _, h, rfl, rfl⟩).mono (Nat.le_of_eq (Nat.add_zero _))
  have h123 := (h12.concat h3).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩
  exact (h123.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by omega)

private theorem td0_s3DefaultEnv_credit (C : Crypto) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8)))
    (hrc : tr.ratchet.receiverChains.length ≤ 5) :
    PhaseCreditSpec fineCostModel (s3DefaultEnv C x trG tr) w4cTdS3Cum 0 0 w4cTdS3MaxReq := by
  unfold s3DefaultEnv s3EnvOf
  cases tr.ratchet.senderChain with
  | none =>
    exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  | some sc =>
    dsimp only
    have hp1 := td0_dhStepPairEvents_credit C x.msg.senderRatchetKey sc.ratchetKey.privateKey
    cases rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | error _ =>
      exact hp1.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
    | ok p1 =>
      rcases p1 with ⟨rk1, _⟩
      dsimp only
      have hp2 := td0_dhStepPairEvents_credit C x.msg.senderRatchetKey
        (CryptoGames.LibsignalSession.KeyPair.generate C (coinsOf x.rest)).privateKey
      cases rootCreateChain C rk1 x.msg.senderRatchetKey
          (CryptoGames.LibsignalSession.KeyPair.generate C (coinsOf x.rest)).privateKey with
      | error _ =>
        exact (hp1.seq hp2).mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
      | ok _ =>
        exact (hp1.seq (hp2.seq (td0_s3Commit_credit x trG tr hrc))).mono
          (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

private theorem td0_s3DefaultEnv_group (C : Crypto) (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) :
    PhaseGroupSpec fineCostModel (s3DefaultEnv C x trG tr) w4cTdS3GrpS := by
  unfold s3DefaultEnv s3EnvOf
  cases tr.ratchet.senderChain with
  | none => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  | some sc =>
    dsimp only
    have hp1 := td0_dhStepPairEvents_group C x.msg.senderRatchetKey sc.ratchetKey.privateKey
    cases rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | error _ => exact hp1.mono (by decide)
    | ok p1 =>
      rcases p1 with ⟨rk1, _⟩
      dsimp only
      have hp2 := td0_dhStepPairEvents_group C x.msg.senderRatchetKey
        (CryptoGames.LibsignalSession.KeyPair.generate C (coinsOf x.rest)).privateKey
      cases rootCreateChain C rk1 x.msg.senderRatchetKey
          (CryptoGames.LibsignalSession.KeyPair.generate C (coinsOf x.rest)).privateKey with
      | error _ => exact (hp1.seq hp2).mono (by decide)
      | ok _ =>
        exact (hp1.seq (hp2.seq (td0_s3Commit_group x trG tr))).mono (by decide)

private theorem td0_pqRecvEnv_credit {S : SpqrModel}
    {RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {c l p r : Nat} {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    (hlp : l ≤ p)
    (hR : PhaseCreditSpec fineCostModel (RecvEnv tr.pqrState x.msg.pqRatchet) c l p r) :
    PhaseCreditSpec fineCostModel (PqRecvEnv S RecvEnv FormatInnerEnv x tr) c l p r := by
  unfold PqRecvEnv
  cases S.recv tr.pqrState x.msg.pqRatchet with
  | ok _ => exact hR
  | error _ =>
    have hf : PhaseCreditSpec fineCostModel FormatInnerEnv 0 0 0 0 :=
      PhaseCreditSpec.nil fineCostModel
    have hfr := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
    exact ((hR.seq hf).seq hfr).mono
      (by omega) (by omega)
      (by have := Nat.max_eq_left hlp; omega)
      (by omega)

private theorem td0_pqRecvEnv_group {S : SpqrModel}
    {RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {g : Nat} {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    (hR : PhaseGroupSpec fineCostModel (RecvEnv tr.pqrState x.msg.pqRatchet) g) :
    PhaseGroupSpec fineCostModel (PqRecvEnv S RecvEnv FormatInnerEnv x tr) g := by
  unfold PqRecvEnv
  cases S.recv tr.pqrState x.msg.pqRatchet with
  | ok _ => exact hR
  | error _ =>
    have hf : PhaseGroupSpec fineCostModel FormatInnerEnv 0 := PhaseGroupSpec.nil fineCostModel
    have hfr := PhaseGroupSpec.freeOnly fineCostModel
    exact ((hR.seq hf).seq hfr).mono (by omega)

private theorem td0_s7Env_credit (F : ShaCompress) (x : TryDecryptGhost)
    (tr : TripleRatchet (List (BitVec 8))) (mks : MessageKeys) (pqr : List (BitVec 8)) :
    PhaseCreditSpec fineCostModel (s7Env F uuidTryParse x tr mks pqr) w4cTdS7Cum 0 0 w4cTdS7MaxReq := by
  unfold s7Env
  have hvm : PhaseCreditSpec fineCostModel (· = vmacEvents F uuidTryParse x tr mks) 2214 0 0 36 := by
    have hb : PhaseCreditSpec fineCostModel (BoundedFreshEvs 3 6 36) 2214 0 0 36 := by
      simpa using phaseCreditSpec_boundedFresh_fine_44 (k := 3) (maxLen := 6) (maxReq := 36) (by decide)
    refine hb.of_imp fun evs heq => ?_
    subst heq
    unfold vmacEvents verifyMacWithAddressesEvents computeMacEvents
    dsimp only
    split <;>
      simp [BoundedFreshEvs, rustAllocEvents, rustDeallocEvents,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.publicKeySerializeEvents,
        LibsignalBinary.Proofs.PeakBudget.GroupCreditKit.nonFreeCount,
        eventStepReq, eventStepAlign]
  have h23 := td0_rustAlloc_le_44_credit (sz := 23) (by decide)
  have hfr := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  exact ((hvm.seq h23).seq hfr).mono
    (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

private theorem td0_s7Env_group (F : ShaCompress) (x : TryDecryptGhost)
    (tr : TripleRatchet (List (BitVec 8))) (mks : MessageKeys) (pqr : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (s7Env F uuidTryParse x tr mks pqr) w4cTdS7GrpS := by
  unfold s7Env
  have hvm : PhaseGroupSpec fineCostModel (· = vmacEvents F uuidTryParse x tr mks) (3 * 16659) := by
    unfold vmacEvents verifyMacWithAddressesEvents computeMacEvents
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.publicKeySerializeEvents
    dsimp only
    have h33 := fine_rustAlloc_le_44 (sz := 33) (al := 1) (by decide) (by decide)
    have hd33 := PhaseGroupSpec.rustDealloc fineCostModel 33 1
    have h36 := fine_rustAlloc_le_44 (sz := 36) (al := 1) (by decide) (by decide)
    have hd36 := PhaseGroupSpec.rustDealloc fineCostModel 36 1
    have ht33 : PhaseGroupSpec fineCostModel
        (· = rustAllocEvents 33 1 ++ rustDeallocEvents 33 1) 16659 :=
      ((h33.concat hd33).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩).mono
        (by decide : 16659 + 0 ≤ 16659)
    have hcm : PhaseGroupSpec fineCostModel
        (· = rustAllocEvents 33 1 ++ rustDeallocEvents 33 1 ++
          (rustAllocEvents 33 1 ++ rustDeallocEvents 33 1)) (2 * 16659) :=
      ((ht33.concat ht33).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩).mono
        (by decide : 16659 + 16659 ≤ 2 * 16659)
    split
    · have ht36 : PhaseGroupSpec fineCostModel
          (· = rustAllocEvents 36 1 ++ rustDeallocEvents 36 1) 16659 :=
        ((h36.concat hd36).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩).mono
          (by decide : 16659 + 0 ≤ 16659)
      exact ((hcm.concat ht36).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩).mono
        (by decide : 2 * 16659 + 16659 ≤ 3 * 16659)
    · exact hcm.mono (by decide : 2 * 16659 ≤ 3 * 16659)
  have h23 := fine_rustAlloc_le_28 (sz := 23) (al := 1) (by decide) (by decide)
  have hfr := PhaseGroupSpec.freeOnly fineCostModel
  exact ((hvm.seq h23).seq hfr).mono (by unfold w4cTdS7GrpS; omega)

private theorem td0_s8Env_credit {maxCt : Nat} (x : TryDecryptGhost)
    (mks : MessageKeys) (pqr : List (BitVec 8))
    (hct : x.msg.ciphertext.length ≤ maxCt) :
    PhaseCreditSpec fineCostModel (s8Env x mks pqr)
      (w4cTdS8CumOf maxCt) (w4cTdS8LiveOf maxCt) (w4cTdS8PeakOf maxCt) maxCt := by
  unfold s8Env
  have haes : PhaseCreditSpec fineCostModel (AesDecCtEnv x.msg.ciphertext.length)
      (2 * maxCt + 9539) (maxCt + 8195) (maxCt + 8195) maxCt := by
    refine (phaseCreditSpec_aesDecCt fineCostModel_modelHyps hct).of_imp fun evs h => ?_
    unfold AesDecCtEnv at h
    unfold AesDecCtShape
    split at h
    · exact Or.inl h
    · exact Or.inr h
  exact (haes.seq (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)).mono
    (by unfold w4cTdS8CumOf; omega) (by unfold w4cTdS8LiveOf; omega)
    (by unfold w4cTdS8PeakOf; omega) (by omega)

private theorem td0_s8Env_group (x : TryDecryptGhost)
    (mks : MessageKeys) (pqr : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (s8Env x mks pqr) w4cTdS8GrpS := by
  unfold s8Env
  have haes : PhaseGroupSpec fineCostModel (AesDecCtEnv x.msg.ciphertext.length) (3 * FineScale) := by
    refine (aesDecCtShape_groupSpec fineCostModel x.msg.ciphertext.length).of_imp fun evs h => ?_
    unfold AesDecCtEnv at h
    unfold AesDecCtShape
    split at h
    · exact Or.inl h
    · exact Or.inr h
  exact (haes.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by unfold w4cTdS8GrpS; omega)

private theorem td0_s9Env_credit (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (pqr : List (BitVec 8)) :
    PhaseCreditSpec fineCostModel (s9Env x trG tr st1 pqr) w4cTdS9Cum 0 0 w4cTdS9MaxReq := by
  unfold s9Env s9From6d0Env TrApplyEnv TrApplySenderAllocEnv
  have h32 := td0_rustAlloc_le_44_credit (sz := 32) (by decide)
  have h33 := td0_rustAlloc_le_44_credit (sz := 33) (by decide)
  have hfr := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hnil := PhaseCreditSpec.nil fineCostModel
  have hsa := h33.seq (h33.seq (h32.seq (h32.seq h32)))
  have hopt := hnil.or hsa
  have htr := h32.seq (hfr.seq (hopt.seq hfr))
  exact (hfr.seq (htr.seq hfr)).mono
    (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

private theorem td0_s9Env_group (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (pqr : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (s9Env x trG tr st1 pqr) w4cTdS9GrpS := by
  unfold s9Env s9From6d0Env TrApplyEnv TrApplySenderAllocEnv
  have h32 := fine_rustAlloc_le_44 (sz := 32) (al := 1) (by decide) (by decide)
  have h33 := fine_rustAlloc_le_44 (sz := 33) (al := 1) (by decide) (by decide)
  have hfr := PhaseGroupSpec.freeOnly fineCostModel
  have hnil := PhaseGroupSpec.nil fineCostModel
  have hsa := h33.seq (h33.seq (h32.seq (h32.seq h32)))
  have hopt := hnil.or hsa
  have htr := h32.seq (hfr.seq (hopt.seq hfr))
  exact (hfr.seq (htr.seq hfr)).mono (by decide)

section GroupSeamComposition

variable {C : Crypto} {parse : UuidParser} {S : SpqrModel}
  {aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8))}
  {s3Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
  {s4Env : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
    List AllocEvent → Prop}
  {s5Env : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
  {s6Env : MessageKeyGenerator → List AllocEvent → Prop}
  {s7Env' : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
    List (BitVec 8) → List AllocEvent → Prop}
  {s8Env' : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
  {s9Env' : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
    SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}

private theorem td0_phaseGroup_fromS8GenEnv {g8 g9 : Nat}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {mks : MessageKeys} {newPqr : List (BitVec 8)}
    (hS8 : PhaseGroupSpec fineCostModel (s8Env' x mks newPqr) g8)
    (hS9 : PhaseGroupSpec fineCostModel (s9Env' x trG tr st1 newPqr) g9) :
    PhaseGroupSpec fineCostModel (FromS8GenEnv aesOpt s8Env' s9Env' x trG tr st1 mks newPqr)
      (g8 + g9) := by
  unfold FromS8GenEnv
  cases aesOpt mks x.msg with
  | some _ => exact hS8.seq hS9
  | none => exact (hS8.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by omega)

private theorem td0_phaseGroup_fromS7GenEnv {g7 g8 g9 : Nat}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {mks : MessageKeys} {newPqr : List (BitVec 8)}
    (hS7 : PhaseGroupSpec fineCostModel (s7Env' x tr mks newPqr) g7)
    (hS8 : PhaseGroupSpec fineCostModel (s8Env' x mks newPqr) g8)
    (hS9 : PhaseGroupSpec fineCostModel (s9Env' x trG tr st1 newPqr) g9) :
    PhaseGroupSpec fineCostModel (FromS7GenEnv C parse aesOpt s7Env' s8Env' s9Env' x trG tr st1 mks newPqr)
      (g7 + (g8 + g9)) := by
  unfold FromS7GenEnv
  split
  · exact hS7.seq (td0_phaseGroup_fromS8GenEnv hS8 hS9)
  · exact (hS7.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by omega)

private theorem td0_phaseGroup_fromS6GenEnv {g6 g7 g8 g9 : Nat}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {mkg : MessageKeyGenerator}
    {newPqr : List (BitVec 8)} {pqrKey : Salt}
    (hS6 : PhaseGroupSpec fineCostModel (s6Env mkg) g6)
    (hS7 : ∀ mks, PhaseGroupSpec fineCostModel (s7Env' x tr mks newPqr) g7)
    (hS8 : ∀ mks, PhaseGroupSpec fineCostModel (s8Env' x mks newPqr) g8)
    (hS9 : PhaseGroupSpec fineCostModel (s9Env' x trG tr st1 newPqr) g9) :
    PhaseGroupSpec fineCostModel
      (FromS6GenEnv C parse aesOpt s6Env s7Env' s8Env' s9Env' x trG tr st1 mkg newPqr pqrKey)
      (g6 + (g7 + (g8 + g9))) := by
  unfold FromS6GenEnv
  exact hS6.seq (td0_phaseGroup_fromS7GenEnv (hS7 _) (hS8 _) hS9)

private theorem td0_phaseGroup_fromS5GenEnv {g5 g6 g7 g8 g9 : Nat}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {mkg : MessageKeyGenerator}
    (hS5 : PhaseGroupSpec fineCostModel (s5Env x tr) g5)
    (hS6 : PhaseGroupSpec fineCostModel (s6Env mkg) g6)
    (hS7 : ∀ mks pqr, PhaseGroupSpec fineCostModel (s7Env' x tr mks pqr) g7)
    (hS8 : ∀ mks pqr, PhaseGroupSpec fineCostModel (s8Env' x mks pqr) g8)
    (hS9 : ∀ pqr, PhaseGroupSpec fineCostModel (s9Env' x trG tr st1 pqr) g9) :
    PhaseGroupSpec fineCostModel
      (FromS5GenEnv C parse S aesOpt s5Env s6Env s7Env' s8Env' s9Env' x trG tr st1 mkg)
      (g5 + (g6 + (g7 + (g8 + g9)))) := by
  unfold FromS5GenEnv
  cases S.recv tr.pqrState x.msg.pqRatchet with
  | ok pair =>
    exact hS5.seq (td0_phaseGroup_fromS6GenEnv hS6
      (fun mks => hS7 mks pair.1) (fun mks => hS8 mks pair.1) (hS9 pair.1))
  | error _ =>
    exact (hS5.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by omega)

end GroupSeamComposition

/-! ## Ratchet Invariants Across `fromSessionState`, `dhRatchetStep`, and `consumeMessageKey` -/

private theorem td0_fromSessionState_ok {st st1 : SessionState (List (BitVec 8))}
    {tr0 : TripleRatchet (List (BitVec 8))}
    (h : Mut.exec TripleRatchet.fromSessionState st = (.ok tr0, st1)) :
    tr0.pqrState = st.pqRatchetState ∧
    tr0.ratchet.receiverChains = st.receiverChains ∧
    tr0.ratchet.maxForwardJumps = 25000 := by
  rw [fromSessionState_exec] at h
  cases hrem : st.remoteIdentity
  · rw [hrem] at h; cases h
  · rw [hrem] at h
    injection h with hok _
    injection hok with htr
    subst htr
    exact ⟨rfl, rfl, rfl⟩

private theorem td0_dhRatchetStep_ok {C : Crypto} {their : PublicKey} {coins : BitVec 256}
    {r0 r1 : RatchetState} {ck : ChainKey}
    (h : Mut.exec (RatchetState.dhRatchetStep C their coins) r0 = (.ok ck, r1))
    (hjumps : r0.maxForwardJumps ≤ 25000)
    (hmk : ∀ c ∈ r0.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    r1.maxForwardJumps ≤ 25000 ∧
    ∀ c ∈ r1.receiverChains, c.messageKeys.length ≤ maxMessageKeys := by
  cases hsc : r0.senderChain with
  | none =>
    rw [dhRatchetStep_none C their coins r0 hsc] at h
    cases h
  | some sc =>
    rw [dhRatchetStep_some_eq C their coins r0 sc hsc] at h
    cases hcc1 : rootCreateChain C r0.rootKey their sc.ratchetKey.privateKey with
    | error e =>
      rw [hcc1] at h
      cases h
    | ok p1 =>
      rcases p1 with ⟨rk1, rck⟩
      rw [hcc1] at h
      dsimp only at h
      cases hcc2 : rootCreateChain C rk1 their
          (CryptoGames.LibsignalSession.KeyPair.generate C coins).privateKey with
      | error e =>
        rw [hcc2] at h
        cases h
      | ok p2 =>
        rcases p2 with ⟨rk2, sck⟩
        rw [hcc2] at h
        dsimp only at h
        injection h with _ hr1
        subst hr1
        refine ⟨hjumps, fun c hc => ?_⟩
        unfold RatchetState.evictReceiverChains at hc
        have hmem := List.mem_of_mem_drop hc
        rw [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with h0 | rfl
        · exact hmk c h0
        · exact Nat.zero_le _


/-! ## `ckx2_SpqrRecvC07C09aBytesEnvOf` and `ckx2_TryDecryptCliLinkedEnvOf` Tight Specs -/

private theorem td0_phaseCredit_of_and_right {P : List AllocEvent → Prop} {Q : Prop}
    {c l p r : Nat}
    (h : Q → PhaseCreditSpec fineCostModel P c l p r) :
    PhaseCreditSpec fineCostModel (fun evs => P evs ∧ Q) c l p r where
  req_align evs hpq ev hev := (h hpq.2).req_align evs hpq.1 ev hev
  credit_le st0 {_} hpq := (h hpq.2).credit_le st0 hpq.1

private theorem td0_phaseGroup_exists {α : Type}
    {E : α → List AllocEvent → Prop} {g : Nat}
    (h : ∀ a, PhaseGroupSpec fineCostModel (E a) g) :
    PhaseGroupSpec fineCostModel (fun evs => ∃ a, E a evs) g where
  groups_le st0 {_} hex := by
    obtain ⟨a, ha⟩ := hex
    exact (h a).groups_le st0 ha

private theorem td0_phaseGroup_of_and_right {P : List AllocEvent → Prop} {Q : Prop} {g : Nat}
    (h : Q → PhaseGroupSpec fineCostModel P g) :
    PhaseGroupSpec fineCostModel (fun evs => P evs ∧ Q) g where
  groups_le st0 {_} hpq := (h hpq.2).groups_le st0 hpq.1

private theorem ckx2_c07TightCreditSpec_inst (F : ShaCompress) (maxOps : Nat) :
    C07TightCreditSpec F
      (fun _ : Bytes => ckx2_DecodeStateTightEnvOf maxOps)
      (fun _ : V1State => StatesFromPbTightEnv)
      (fun _ : StatesIntoPbGhost F => StatesIntoPbTightEnv)
      1307216 79236 359623 2560 376193 2400 :=
  ⟨fun _ _ _ _ => spqrTightEvs_fine_phaseCreditSpec maxOps 1307216 (Nat.le_refl 79236),
   fun _ _ _ => statesFromPb_fine_phaseCreditSpec_tight,
   fun _ _ _ _ => statesIntoPb_fine_phaseCreditSpec_tight⟩

private theorem ckx2_c07TightGroupSpec_split_inst (F : ShaCompress) (maxOps : Nat) :
    C07TightGroupSpec F
      (fun _ : Bytes => ckx2_DecodeStateTightEnvOf maxOps)
      (fun _ : V1State => StatesFromPbTightEnv)
      (fun _ : StatesIntoPbGhost F => StatesIntoPbTightEnv)
      (140011 * maxOps)
      statesFromPbTightGroupS_split
      statesIntoPbTightGroupS_split :=
  ⟨fun _ _ _ _ => spqrTightEvs_fine_phaseGroupSpec_align16 maxOps 1307216 79236,
   fun _ _ _ => statesFromPbTight_fine_phaseGroupSpec_split,
   fun _ _ _ _ => statesIntoPbTight_fine_phaseGroupSpec_split⟩

private theorem ckx2_statesRecvProtoEnv'_creditSpec_inst (F : ShaCompress) (K : MlKem) :
    StatesRecvTightCreditSpec F (ckx2_StatesRecvProtoEnv' K) 1647247 93776 :=
  ⟨ckx2_statesRecvProtoEnv'_tight_creditSpec K⟩

private theorem ckx2_statesRecvProtoEnv'_split_groupSpec_inst (F : ShaCompress) (K : MlKem) :
    StatesRecvTightGroupSpec F (ckx2_StatesRecvProtoEnv' K) statesRecvTightGroupS_split :=
  ⟨ckx2_statesRecvProtoEnv'_tight_split_groupSpec K⟩

private theorem ckx2_spqrRecvC07C09aBytesEnvOf_phaseCreditSpec
    {F : ShaCompress} {K : MlKem} (maxOps : Nat)
    {stBs msgBs : Bytes} (hTop : TopStateTight F K stBs) :
    PhaseCreditSpec fineCostModel (ckx2_SpqrRecvC07C09aBytesEnvOf maxOps F K stBs msgBs)
      w4cTdS5Cum w4cTdS5Live w4cTdS5Peak w4cTdS5MaxReq := by
  let _ := msgBs
  unfold ckx2_SpqrRecvC07C09aBytesEnvOf ckx2_SpqrRecvC07C09aTightLinkedEnvOf
    ckx2_SpqrRecvC07C09aTightLinkedEnvRecvOf SpqrRecvTightLinkedEnv
  refine
    phaseCredit_exists fun pre_pb =>
    phaseCredit_exists fun vn =>
    phaseCredit_exists fun pb =>
    phaseCredit_exists fun st0 =>
    phaseCredit_exists fun sckaMsg =>
    phaseCredit_exists fun v =>
    phaseCredit_exists fun xInit =>
    phaseCredit_exists fun xNew =>
    phaseCredit_exists fun xAdd =>
    phaseCredit_exists fun xRk =>
    phaseCredit_exists fun xSInto =>
    phaseCredit_exists fun xCInto => ?_
  refine td0_phaseCredit_of_and_right fun hLink => ?_
  exact (spqrRecvParts_phaseCreditSpec_tight_uncondHist
    F K (ckx2_c07TightCreditSpec_inst F maxOps) (ckx2_statesRecvProtoEnv'_creditSpec_inst F K)
    (by decide) stBs pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto
    (spqrRecvTightDomain_of_topStateTight_and_link hTop hLink)).mono
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by decide)

private theorem ckx2_spqrRecvC07C09aBytesEnvOf_phaseGroupSpec_split
    {F : ShaCompress} {K : MlKem} (maxOps : Nat)
    {stBs msgBs : Bytes} (hTop : TopStateTight F K stBs) :
    PhaseGroupSpec fineCostModel (ckx2_SpqrRecvC07C09aBytesEnvOf maxOps F K stBs msgBs)
      (w4cTdS5GrpSOf maxOps) := by
  let _ := msgBs
  unfold ckx2_SpqrRecvC07C09aBytesEnvOf ckx2_SpqrRecvC07C09aTightLinkedEnvOf
    ckx2_SpqrRecvC07C09aTightLinkedEnvRecvOf SpqrRecvTightLinkedEnv
  refine
    td0_phaseGroup_exists fun pre_pb =>
    td0_phaseGroup_exists fun vn =>
    td0_phaseGroup_exists fun pb =>
    td0_phaseGroup_exists fun st0 =>
    td0_phaseGroup_exists fun sckaMsg =>
    td0_phaseGroup_exists fun v =>
    td0_phaseGroup_exists fun xInit =>
    td0_phaseGroup_exists fun xNew =>
    td0_phaseGroup_exists fun xAdd =>
    td0_phaseGroup_exists fun xRk =>
    td0_phaseGroup_exists fun xSInto =>
    td0_phaseGroup_exists fun xCInto => ?_
  refine td0_phaseGroup_of_and_right fun hLink => ?_
  exact spqrRecvParts_phaseGroupSpec_tight F K
    (ckx2_c07TightGroupSpec_split_inst F maxOps)
    (ckx2_statesRecvProtoEnv'_split_groupSpec_inst F K)
    stBs pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto
    (spqrRecvTightDomain_of_topStateTight_and_link hTop hLink)

private theorem ckx2_fromS4_credit
    {C : Crypto} {K : MlKem} {maxOps maxCt : Nat}
    {aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8))}
    {s8Env' : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9Env' : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {l8 c9 : Nat}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey}
    (hjumps : tr.ratchet.maxForwardJumps ≤ 25000)
    (hmk : ∀ c ∈ tr.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys)
    (hTop : TopStateTight C.F K tr.pqrState)
    (hS8 : ∀ mks pqr, PhaseCreditSpec fineCostModel (s8Env' x mks pqr)
      (w4cTdS8CumOf maxCt) l8 (w4cTdS8PeakOf maxCt) maxCt)
    (hS9 : ∀ trG' tr' pqr, PhaseCreditSpec fineCostModel (s9Env' x trG' tr' st1 pqr)
      c9 0 0 w4cTdS9MaxReq) :
    PhaseCreditSpec fineCostModel
      (FromS4GenEnv C uuidTryParse (spqrV1 C.F K) aesOpt
        (ckx2_tryDecryptCmkSeg4EnvOf CmkLoopAdvanceEvs FmtWriteEnv)
        (PqRecvEnv (spqrV1 C.F K) (ckx2_SpqrRecvC07C09aBytesEnvOf maxOps C.F K) FormatInnerEnv)
        s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env' s9Env' x trG tr st1 ck)
      (w4cTdS4Cum + (w4cTdS5Cum + (0 + (w4cTdS7Cum + (w4cTdS8CumOf maxCt + c9)))))
      (w4cTdS4Live + (w4cTdS5Live + (0 + (0 + (l8 + 0)))))
      (max w4cTdS4Peak (w4cTdS4Live + max w4cTdS5Peak (w4cTdS5Live +
        max 0 (0 + max 0 (0 + max (w4cTdS8PeakOf maxCt) (l8 + 0))))))
      (max w4cTdS4MaxReq (max w4cTdS5MaxReq (max 0 (max w4cTdS7MaxReq (max maxCt w4cTdS9MaxReq))))) := by
  unfold FromS4GenEnv
  have hS4 : PhaseCreditSpec fineCostModel
      (ckx2_tryDecryptCmkSeg4EnvOf CmkLoopAdvanceEvs FmtWriteEnv x trG tr ck)
      w4cTdS4Cum w4cTdS4Live w4cTdS4Peak w4cTdS4MaxReq := by
    rw [ckx2_tryDecryptCmkSeg4EnvOf_cmk_eq]
    exact tryDecryptCmkSeg4Env_fine_phaseCreditSpec_tight x trG tr ck hjumps hmk
  split
  · next mkg r2 _ =>
    have hS5 : PhaseCreditSpec fineCostModel
        (PqRecvEnv (spqrV1 C.F K) (ckx2_SpqrRecvC07C09aBytesEnvOf maxOps C.F K) FormatInnerEnv
          x { tr with ratchet := r2 })
        w4cTdS5Cum w4cTdS5Live w4cTdS5Peak w4cTdS5MaxReq :=
      td0_pqRecvEnv_credit (by decide)
        (ckx2_spqrRecvC07C09aBytesEnvOf_phaseCreditSpec maxOps hTop)
    have hS6 : PhaseCreditSpec fineCostModel (s6FreeOnlyEnv mkg) 0 0 0 0 :=
      PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
    exact hS4.seq (LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak.phaseCredit_fromS5GenEnv
      fineCostModel_modelHyps hS5 hS6 (td0_s7Env_credit C.F x _) hS8 (hS9 trG _))
  · exact (phaseCredit_seq_freeOnly
      fineCostModel_modelHyps hS4).mono
      (by omega) (by omega) (Nat.le_max_left _ _) (Nat.le_max_left _ _)

private theorem ckx2_fromS4_group
    {C : Crypto} {K : MlKem} {maxOps : Nat}
    {aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8))}
    {s8Env' : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9Env' : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    {g9 : Nat}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey}
    (hjumps : tr.ratchet.maxForwardJumps ≤ 25000)
    (hmk : ∀ c ∈ tr.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys)
    (hTop : TopStateTight C.F K tr.pqrState)
    (hS8 : ∀ mks pqr, PhaseGroupSpec fineCostModel (s8Env' x mks pqr) w4cTdS8GrpS)
    (hS9 : ∀ trG' tr' pqr, PhaseGroupSpec fineCostModel (s9Env' x trG' tr' st1 pqr) g9) :
    PhaseGroupSpec fineCostModel
      (FromS4GenEnv C uuidTryParse (spqrV1 C.F K) aesOpt
        (ckx2_tryDecryptCmkSeg4EnvOf CmkLoopAdvanceEvs FmtWriteEnv)
        (PqRecvEnv (spqrV1 C.F K) (ckx2_SpqrRecvC07C09aBytesEnvOf maxOps C.F K) FormatInnerEnv)
        s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env' s9Env' x trG tr st1 ck)
      (w4cTdS4GrpS + (w4cTdS5GrpSOf maxOps + (0 + (w4cTdS7GrpS + (w4cTdS8GrpS + g9))))) := by
  unfold FromS4GenEnv
  have hS4 : PhaseGroupSpec fineCostModel
      (ckx2_tryDecryptCmkSeg4EnvOf CmkLoopAdvanceEvs FmtWriteEnv x trG tr ck) w4cTdS4GrpS := by
    rw [ckx2_tryDecryptCmkSeg4EnvOf_cmk_eq]
    exact tryDecryptCmkSeg4Env_fine_groupSpec_tight x trG tr ck hjumps hmk
  split
  · next mkg r2 _ =>
    have hS5 : PhaseGroupSpec fineCostModel
        (PqRecvEnv (spqrV1 C.F K) (ckx2_SpqrRecvC07C09aBytesEnvOf maxOps C.F K) FormatInnerEnv
          x { tr with ratchet := r2 })
        (w4cTdS5GrpSOf maxOps) :=
      td0_pqRecvEnv_group (ckx2_spqrRecvC07C09aBytesEnvOf_phaseGroupSpec_split maxOps hTop)
    have hS6 : PhaseGroupSpec fineCostModel (s6FreeOnlyEnv mkg) 0 :=
      PhaseGroupSpec.freeOnly fineCostModel
    exact hS4.seq (td0_phaseGroup_fromS5GenEnv hS5 hS6 (td0_s7Env_group C.F x _) hS8 (hS9 trG _))
  · exact (hS4.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by omega)

private theorem td0_grp_s4_le (s3 s4 s5 s7 s8 s9 : Nat) :
    s4 + (s5 + (0 + (s7 + (s8 + s9)))) ≤ s3 + s4 + s5 + s7 + s8 + s9 := by omega

private theorem td0_grp_s3_le (s3 s4 s5 s7 s8 s9 : Nat) :
    s3 + 0 ≤ s3 + s4 + s5 + s7 + s8 + s9 := by omega

private theorem td0_grp_s34_le (s3 s4 s5 s7 s8 s9 : Nat) :
    s3 + (s4 + (s5 + (0 + (s7 + (s8 + s9))))) ≤ s3 + s4 + s5 + s7 + s8 + s9 := by omega

private theorem td0_seq_fr_left_credit {E : List AllocEvent → Prop} {c l p r : Nat}
    (hfr : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0)
    (h : PhaseCreditSpec fineCostModel E c l p r) :
    PhaseCreditSpec fineCostModel (SeqEnv FreeOnlyEvs E) c l p r :=
  (hfr.seq h).mono
    (Nat.le_of_eq (Nat.zero_add c))
    (Nat.le_of_eq (Nat.zero_add l))
    (by omega)
    (Nat.le_of_eq (Nat.zero_max r))

private theorem td0_seq_zero_lp_credit {E1 E2 : List AllocEvent → Prop}
    {c1 m1 c2 l2 p2 m2 c l p m : Nat}
    (h1 : PhaseCreditSpec fineCostModel E1 c1 0 0 m1)
    (h2 : PhaseCreditSpec fineCostModel E2 c2 l2 p2 m2)
    (hc : c1 + c2 ≤ c) (hl : l2 ≤ l) (hp : p2 ≤ p) (hm : max m1 m2 ≤ m) :
    PhaseCreditSpec fineCostModel (SeqEnv E1 E2) c l p m :=
  (h1.seq h2).mono hc (by omega) (by omega) hm

private theorem ckx2_tryDecryptCliLinkedEnvOf_phaseCreditSpec
    {C : Crypto} {K : MlKem} (maxOps maxCt : Nat)
    (a : TryDecryptEnvArgs)
    (hrc_a : a.st.receiverChains.length ≤ 5)
    (hmk_a : ∀ c ∈ a.st.receiverChains, c.messageKeys.length ≤ maxMessageKeys)
    (hTop_a : TopStateTight C.F K a.st.pqRatchetState)
    (hct_a : (tryDecryptEnvArgsToGhost a).msg.ciphertext.length ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (ckx2_TryDecryptCliLinkedEnvOf maxOps C K a)
      (w4cTdCumOf maxCt) (w4cTdLiveOf maxCt) (w4cTdPeakOf maxCt) (w4cTdMaxReqOf maxCt) := by
  unfold ckx2_TryDecryptCliLinkedEnvOf ckx2_TryDecryptCliLinkedLoopEnvOf
  dsimp only
  cases hfs : Mut.exec TripleRatchet.fromSessionState a.st with
  | mk res st1 =>
    cases res with
    | error _ =>
      exact (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok tr0 =>
      obtain ⟨hpqr, hrc_eq, hjumps0⟩ := td0_fromSessionState_ok hfs
      have hrc : tr0.ratchet.receiverChains.length ≤ 5 := hrc_eq ▸ hrc_a
      have hmk0 : ∀ c ∈ tr0.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys := by
        rw [hrc_eq]; exact hmk_a
      have hj0 : tr0.ratchet.maxForwardJumps ≤ 25000 := Nat.le_of_eq hjumps0
      have hTop0 : TopStateTight C.F K tr0.pqrState := hpqr ▸ hTop_a
      let x := tryDecryptEnvArgsToGhost a
      have hct : x.msg.ciphertext.length ≤ maxCt := hct_a
      have hfr := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
      have hS2 : PhaseCreditSpec fineCostModel
          (FromS2GenEnv C uuidTryParse (spqrV1 C.F K) (stdAesOpt C)
            (s3DefaultEnv C) (ckx2_tryDecryptCmkSeg4EnvOf CmkLoopAdvanceEvs FmtWriteEnv)
            (PqRecvEnv (spqrV1 C.F K) (ckx2_SpqrRecvC07C09aBytesEnvOf maxOps C.F K) FormatInnerEnv)
            s6FreeOnlyEnv (s7Env C.F uuidTryParse)
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
            x (s1InitTrGhost a.G) tr0 st1)
          (w4cTdCumOf maxCt) (w4cTdLiveOf maxCt) (w4cTdPeakOf maxCt) (w4cTdMaxReqOf maxCt) := by
        unfold FromS2GenEnv
        split
        · next ck _ =>
          exact (ckx2_fromS4_credit (maxOps := maxOps) (aesOpt := stdAesOpt C) hj0 hmk0 hTop0
            (fun mks pqr => td0_s8Env_credit x mks pqr hct)
            (fun trG' tr' pqr => td0_s9Env_credit x trG' tr' st1 pqr)).mono
            (by unfold w4cTdCumOf w4cTdS3Cum w4cTdS4Cum w4cTdS5Cum w4cTdS7Cum w4cTdS8CumOf
                  w4cTdS9Cum cmkLoop25000TightCum; omega)
            (by unfold w4cTdLiveOf w4cTdS8LiveOf; omega)
            (by unfold w4cTdPeakOf w4cTdS4Live w4cTdS4Peak w4cTdS5Live w4cTdS5Peak
                  w4cTdS8LiveOf w4cTdS8PeakOf cmkLoop25000Live cmkLoop25000Peak; omega)
            (by unfold w4cTdMaxReqOf w4cTdS4MaxReq w4cTdS5MaxReq w4cTdS7MaxReq w4cTdS9MaxReq
                  cmkLoop25000MaxReq; omega)
        · unfold FromS3GenEnv
          have hS3 := td0_s3DefaultEnv_credit C x (s1InitTrGhost a.G) tr0 hrc
          cases hs3 : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet with
          | mk rres r1 =>
            cases rres with
            | error _ =>
              exact (phaseCredit_seq_freeOnly
                fineCostModel_modelHyps hS3).mono
                (by unfold w4cTdCumOf; omega) (Nat.zero_le _) (Nat.zero_le _)
                (by unfold w4cTdMaxReqOf w4cTdS3MaxReq w4cTdS4MaxReq cmkLoop25000MaxReq; omega)
            | ok ck =>
              obtain ⟨hj1, hmk1⟩ := td0_dhRatchetStep_ok hs3 hj0 hmk0
              have h4 := ckx2_fromS4_credit (maxOps := maxOps) (aesOpt := stdAesOpt C)
                (trG := s3AfterTrGhost
                  (s1InitTrGhost a.G) tr0.ratchet.receiverChains.length)
                (tr := { tr0 with ratchet := r1 }) (ck := ck)
                hj1 hmk1 hTop0
                (fun mks pqr => td0_s8Env_credit x mks pqr hct)
                (fun trG' tr' pqr => td0_s9Env_credit x trG' tr' st1 pqr)
              exact td0_seq_zero_lp_credit hS3 h4
                (by unfold w4cTdCumOf; omega)
                (by unfold w4cTdLiveOf w4cTdS8LiveOf; omega)
                (by unfold w4cTdPeakOf w4cTdS4Live w4cTdS4Peak w4cTdS5Live w4cTdS5Peak
                      w4cTdS8LiveOf w4cTdS8PeakOf cmkLoop25000Live cmkLoop25000Peak; omega)
                (by unfold w4cTdMaxReqOf w4cTdS3MaxReq w4cTdS4MaxReq w4cTdS5MaxReq w4cTdS7MaxReq
                      w4cTdS9MaxReq cmkLoop25000MaxReq; omega)
        · exact hfr.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      exact td0_seq_fr_left_credit hfr hS2

private theorem ckx2_tryDecryptCliLinkedEnvOf_phaseGroupSpec
    {C : Crypto} {K : MlKem} (maxOps : Nat)
    (a : TryDecryptEnvArgs)
    (hmk_a : ∀ c ∈ a.st.receiverChains, c.messageKeys.length ≤ maxMessageKeys)
    (hTop_a : TopStateTight C.F K a.st.pqRatchetState) :
    PhaseGroupSpec fineCostModel
      (ckx2_TryDecryptCliLinkedEnvOf maxOps C K a)
      (w4cTdGrpSOf maxOps) := by
  unfold ckx2_TryDecryptCliLinkedEnvOf ckx2_TryDecryptCliLinkedLoopEnvOf
  dsimp only
  cases hfs : Mut.exec TripleRatchet.fromSessionState a.st with
  | mk res st1 =>
    cases res with
    | error _ => exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
    | ok tr0 =>
      obtain ⟨hpqr, hrc_eq, hjumps0⟩ := td0_fromSessionState_ok hfs
      have hmk0 : ∀ c ∈ tr0.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys := by
        rw [hrc_eq]; exact hmk_a
      have hj0 : tr0.ratchet.maxForwardJumps ≤ 25000 := Nat.le_of_eq hjumps0
      have hTop0 : TopStateTight C.F K tr0.pqrState := hpqr ▸ hTop_a
      let x := tryDecryptEnvArgsToGhost a
      have hfr := PhaseGroupSpec.freeOnly fineCostModel
      have hS2 : PhaseGroupSpec fineCostModel
          (FromS2GenEnv C uuidTryParse (spqrV1 C.F K) (stdAesOpt C)
            (s3DefaultEnv C) (ckx2_tryDecryptCmkSeg4EnvOf CmkLoopAdvanceEvs FmtWriteEnv)
            (PqRecvEnv (spqrV1 C.F K) (ckx2_SpqrRecvC07C09aBytesEnvOf maxOps C.F K) FormatInnerEnv)
            s6FreeOnlyEnv (s7Env C.F uuidTryParse)
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget.s8Env
            LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget.s9Env
            x (s1InitTrGhost a.G) tr0 st1)
          (w4cTdGrpSOf maxOps) := by
        unfold FromS2GenEnv
        split
        · next ck _ =>
          exact (ckx2_fromS4_group (maxOps := maxOps) (aesOpt := stdAesOpt C) hj0 hmk0 hTop0
            (fun mks pqr => td0_s8Env_group x mks pqr)
            (fun trG' tr' pqr => td0_s9Env_group x trG' tr' st1 pqr)).mono
            (td0_grp_s4_le _ _ _ _ _ _)
        · unfold FromS3GenEnv
          have hS3 := td0_s3DefaultEnv_group C x (s1InitTrGhost a.G) tr0
          cases hs3 : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet with
          | mk rres r1 =>
            cases rres with
            | error _ =>
              exact (hS3.seq hfr).mono (td0_grp_s3_le _ _ _ _ _ _)
            | ok ck =>
              obtain ⟨hj1, hmk1⟩ := td0_dhRatchetStep_ok hs3 hj0 hmk0
              have h4 := ckx2_fromS4_group (maxOps := maxOps) (aesOpt := stdAesOpt C)
                (trG := s3AfterTrGhost
                  (s1InitTrGhost a.G) tr0.ratchet.receiverChains.length)
                (tr := { tr0 with ratchet := r1 }) (ck := ck)
                hj1 hmk1 hTop0
                (fun mks pqr => td0_s8Env_group x mks pqr)
                (fun trG' tr' pqr => td0_s9Env_group x trG' tr' st1 pqr)
              exact (hS3.seq h4).mono (td0_grp_s34_le _ _ _ _ _ _)
        · exact hfr.mono (Nat.zero_le _)
      exact (hfr.seq hS2).mono (Nat.le_of_eq (Nat.zero_add _))

/-! ## `*BudgetFixed` to `*Budget` Slot Bridge -/

private theorem ckx2_cliDecryptSignalSlotEnv_fixed_eq_plain [LibsignalPlacement] {M : AllocCostModel}
    {P : PEParams} {i : Inputs} (hi : CliPqxdhInputs P i)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) (A : RustCliAllocBudget M) (B : RunBudgets)
    {x : DecSigGhost} (hx : x.F = runFiles i) :
    CliDecryptSignalSlotEnv P A B tdEnv
        (decBinarySessKitPlacedBudgetFixed A.repAlloc B)
        (decBinaryIdKitPlacedBudgetFixed A.repAlloc B) x =
      CliDecryptSignalSlotEnv P A B tdEnv
        (decBinarySessKitPlacedBudget A.repAlloc B)
        (decBinaryIdKitPlacedBudget A.repAlloc B) x := by
  have hload :
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer).loadPollEnv
          StoresGhost.opened.sessions (toDecryptGhost x).rem.val =
        (decBinarySessKitPlacedBudget A.repAlloc B x.F x.peer).loadPollEnv
          StoresGhost.opened.sessions (toDecryptGhost x).rem.val := by
    change cliSessionKitLoadPollEnv _ _ _ _ _ x.F _ _ = cliSessionKitLoadPollEnv _ _ _ _ _ x.F _ _
    unfold cliSessionKitLoadPollEnv
    rw [hx, dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_sessions hi _)]
  have htrust : ∀ k,
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer).trustPollEnv
          StoresGhost.opened.identity (toDecryptGhost x).rem.val k .receiving =
        (decBinaryIdKitPlacedBudget A.repAlloc B x.F x.peer).trustPollEnv
          StoresGhost.opened.identity (toDecryptGhost x).rem.val k .receiving := by
    intro k
    change cliIdentityKitTrustPollEnv _ x.F _ _ k .receiving =
      cliIdentityKitTrustPollEnv _ x.F _ _ k .receiving
    unfold cliIdentityKitTrustPollEnv
    rw [hx, dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_identities hi _)]
  have hsave : ∀ k,
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer).savePollEnv
          ((decIdKitPlaced A.repAlloc x.F x.peer B).trustUpdate StoresGhost.opened.identity
            (toDecryptGhost x).rem.val k .receiving (.ok true))
          (toDecryptGhost x).rem.val k =
        (decBinaryIdKitPlacedBudget A.repAlloc B x.F x.peer).savePollEnv
          ((decIdKitPlaced A.repAlloc x.F x.peer B).trustUpdate StoresGhost.opened.identity
            (toDecryptGhost x).rem.val k .receiving (.ok true))
          (toDecryptGhost x).rem.val k := by
    intro k
    change cliIdentityKitSavePollEnv _ _ _ x.F StoresGhost.opened.identity _ _ =
      cliIdentityKitSavePollEnv _ _ _ x.F StoresGhost.opened.identity _ _
    unfold cliIdentityKitSavePollEnv
    rw [hx, dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_identities hi _)]
  have hstore :
      (decBinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer).storePollEnv =
        (decBinarySessKitPlacedBudget A.repAlloc B x.F x.peer).storePollEnv := rfl
  have hkr : ∀ r' k,
      FromKeyReadyEnv (decSessKitPlaced A.repAlloc x.F x.peer B)
          (decBinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer)
          StoresGhost.opened.sessions
          (decIdKitPlaced A.repAlloc x.F x.peer B)
          (decBinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer)
          StoresGhost.opened.identity (toDecryptGhost x) r' k =
        FromKeyReadyEnv (decSessKitPlaced A.repAlloc x.F x.peer B)
          (decBinarySessKitPlacedBudget A.repAlloc B x.F x.peer)
          StoresGhost.opened.sessions
          (decIdKitPlaced A.repAlloc x.F x.peer B)
          (decBinaryIdKitPlacedBudget A.repAlloc B x.F x.peer)
          StoresGhost.opened.identity (toDecryptGhost x) r' k := by
    intro r' k
    funext evs
    unfold FromKeyReadyEnv
      LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.TrustStepEnv
      FromTrustedTrueEnv
      LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.SaveStepEnv
      LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget.FromStoreCallEnv
      LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.StoreStepEnv
    rw [htrust k, hsave k, hstore]
  have hps : ∀ r,
      FromPostSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse
          (decSessKitPlaced A.repAlloc x.F x.peer B)
          (decBinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer)
          StoresGhost.opened.sessions
          (decIdKitPlaced A.repAlloc x.F x.peer B)
          (decBinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer)
          StoresGhost.opened.identity (toDecryptGhost x) r =
        FromPostSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse
          (decSessKitPlaced A.repAlloc x.F x.peer B)
          (decBinarySessKitPlacedBudget A.repAlloc B x.F x.peer)
          StoresGhost.opened.sessions
          (decIdKitPlaced A.repAlloc x.F x.peer B)
          (decBinaryIdKitPlacedBudget A.repAlloc B x.F x.peer)
          StoresGhost.opened.identity (toDecryptGhost x) r := by
    intro r
    funext evs
    unfold FromPostSomeEnv
    simp only [hkr]
  have hrs : ∀ r G ses_st,
      FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse tdEnv
          (decSessKitPlaced A.repAlloc x.F x.peer B)
          (decBinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer)
          StoresGhost.opened.sessions
          (decIdKitPlaced A.repAlloc x.F x.peer B)
          (decBinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer)
          StoresGhost.opened.identity (toDecryptGhost x) r G ses_st =
        FromRegionSomeEnv P.C (pqxdhSpqrModel P) uuidTryParse tdEnv
          (decSessKitPlaced A.repAlloc x.F x.peer B)
          (decBinarySessKitPlacedBudget A.repAlloc B x.F x.peer)
          StoresGhost.opened.sessions
          (decIdKitPlaced A.repAlloc x.F x.peer B)
          (decBinaryIdKitPlacedBudget A.repAlloc B x.F x.peer)
          StoresGhost.opened.identity (toDecryptGhost x) r G ses_st := by
    intro r G ses_st
    funext evs
    unfold FromRegionSomeEnv
    rw [hps r]
  have hlp :
      FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse tdEnv
          (decSessKitPlaced A.repAlloc x.F x.peer B)
          (decBinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer)
          StoresGhost.opened.sessions
          (decIdKitPlaced A.repAlloc x.F x.peer B)
          (decBinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer)
          StoresGhost.opened.identity scopeKit (toDecryptGhost x) =
        FromLoadPolledEnv P.C (pqxdhSpqrModel P) uuidTryParse tdEnv
          (decSessKitPlaced A.repAlloc x.F x.peer B)
          (decBinarySessKitPlacedBudget A.repAlloc B x.F x.peer)
          StoresGhost.opened.sessions
          (decIdKitPlaced A.repAlloc x.F x.peer B)
          (decBinaryIdKitPlacedBudget A.repAlloc B x.F x.peer)
          StoresGhost.opened.identity scopeKit (toDecryptGhost x) := by
    funext evs
    unfold FromLoadPolledEnv
    simp only [hrs]
  funext evs
  unfold CliDecryptSignalSlotEnv WithStoresDecEnv LoadPollStepEnv
  rw [hload, hlp]


/-! ## Outer `WithStoresDecEnv` Store Helpers and Curried `W2` Exact Slot Specs -/

private theorem s2b_dirPutTail_opened_credit {dir : DirGhost} (hch : dir.changed = [])
    (name : List (BitVec 8)) :
    PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux.DirPutTailEnv dir name)
      9789 0 0 192 := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux.DirPutTailEnv
  split
  · have hgrow :
        LibsignalBinary.Heap.RustStdAllocBudgetBridge.rawVecGrowEvents 48 4 8
          (BitVec.ofNat 64 dir.changed.length) =
        LibsignalBinary.Heap.rustAllocEvents 192 8 := by
      rw [hch]; rfl
    rw [hgrow]
    have h192 : PhaseCreditSpec fineCostModel
        (· = LibsignalBinary.Heap.rustAllocEvents 192 8) 9789 0 0 192 :=
      (PhaseCreditSpec.rustAlloc_small fineCostModel (req := 192) (al := 8)
        (by decide) (by decide)
        (by rw [LibsignalBinary.Heap.Fine.ClientBounds.fineCostModel_smallMaxReq_eq]; decide)).mono
        (LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit.fineSmallAllocCost_le_9789_of_le_192
          (by decide))
        (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
    exact ((PhaseCreditSpec.nil fineCostModel).or h192).mono
      (by decide) (by decide) (by decide) (by decide)
  · exact (PhaseCreditSpec.freeOnly
      LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas.fineCostModel_freeNonInc).mono
      (by decide) (by decide) (by decide) (by decide)

private theorem s2b_dirPutTail_opened_group {dir : DirGhost} (hch : dir.changed = [])
    (name : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux.DirPutTailEnv dir name)
      (3 * FineScale) := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux.DirPutTailEnv
  split
  · have hgrow :
        LibsignalBinary.Heap.RustStdAllocBudgetBridge.rawVecGrowEvents 48 4 8
          (BitVec.ofNat 64 dir.changed.length) =
        LibsignalBinary.Heap.rustAllocEvents 192 8 := by
      rw [hch]; rfl
    rw [hgrow]
    exact ((PhaseGroupSpec.nil fineCostModel).or
      (PhaseGroupSpec.rustAlloc_any fineCostModel 192 8)).mono (by decide)
  · exact (PhaseGroupSpec.freeOnly fineCostModel).mono (by decide)

private theorem s2b_dirPutStr_opened_credit {dir : DirGhost} (hch : dir.changed = [])
    (name bytes : List (BitVec 8)) (hname : name.length ≤ 40) :
    PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux.DirPutStrEnv
        dir name bytes)
      11396 0 0 192 := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux.DirPutStrEnv
  have ht := s2b_dirPutTail_opened_credit hch name
  split_ifs with hz
  · exact ht.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
  · have hpos : 0 < name.length := Nat.pos_of_ne_zero (List.length_eq_zero_iff.not.mpr hz)
    have hn64 : name.length ≤ 64 := Nat.le_trans hname (by decide)
    have hsm : name.length ≤
        LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq
          fineCostModel := by
      rw [LibsignalBinary.Heap.Fine.ClientBounds.fineCostModel_smallMaxReq_eq]
      exact Nat.le_trans hname (by decide)
    have ha : PhaseCreditSpec fineCostModel
        (· = LibsignalBinary.Heap.rustAllocEvents name.length 1) 1607 0 0 192 :=
      (PhaseCreditSpec.rustAlloc_small fineCostModel (req := name.length) (al := 1)
        (by decide) hpos hsm).mono
        (LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit.fineSmallAllocCost_le_1607_of_le_64 hn64)
        (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_trans hname (by decide))
    exact (ha.seq ht).mono (by decide) (by decide) (by decide) (by decide)

private theorem s2b_dirPutStr_opened_group {dir : DirGhost} (hch : dir.changed = [])
    (name bytes : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux.DirPutStrEnv
        dir name bytes)
      (6 * FineScale) := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux.DirPutStrEnv
  have ht := s2b_dirPutTail_opened_group hch name
  split
  · exact ht.mono (by decide)
  · exact ((PhaseGroupSpec.rustAlloc_any fineCostModel name.length 1).seq ht).mono (by decide)

private abbrev s2b_idGet64Cum : Nat :=
  21185 + max 738 (LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec.fineReadFileCum (max 0 64))

private abbrev s2b_idGet64MaxReq : Nat :=
  max 256 (LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec.fineReadFileMaxReq (max 0 64))

private theorem s2b_idTrustPoll_credit (F0 : FsFiles)
    (rem : CryptoVerification.LibsignalPublicApiRepr.AddrVal)
    (k : CryptoGames.LibsignalSession.IdentityKey)
    (hrem40 : rem.name.length ≤ 40)
    (hcap64 : ∀ bs,
      cliIo.rd F0 (pathOf StoresGhost.opened.identity.peers.path rem.name) = .ok bs →
      bs.length ≤ 64) :
    PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitTrustPollEnv
        (DirGetEnv PathEnv
          (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.ReadFileRuleEnv cliIo.rd)
          cliIo.rd)
        F0 StoresGhost.opened.identity rem k .receiving)
      s2b_idGet64Cum 0 0 s2b_idGet64MaxReq := by
  have hget :=
    LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux.dirGetEnv_path_readFile_fine_phaseCredit_tight
      cliIo.rd F0 StoresGhost.opened.identity.peers rem.name
      (LibsignalBinary.Proofs.PeakBudget.CliDomainCaps.dirDomainCaps_opened_peers.mono
        (by decide) (Nat.le_refl 0) (Nat.le_refl 0))
      (Nat.le_trans hrem40 (by decide)) hcap64
  exact (LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux.seq_freeOnly_phaseCredit
    LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas.fineCostModel_freeNonInc hget).mono
    (Nat.le_refl _) (by decide) (by decide) (Nat.le_refl _)

private theorem s2b_idTrustPoll_group (F0 : FsFiles)
    (rem : CryptoVerification.LibsignalPublicApiRepr.AddrVal)
    (k : CryptoGames.LibsignalSession.IdentityKey) :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitTrustPollEnv
        (DirGetEnv PathEnv
          (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.ReadFileRuleEnv cliIo.rd)
          cliIo.rd)
        F0 StoresGhost.opened.identity rem k .receiving)
      (39 * FineScale) :=
  ((LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux.dirGetEnv_path_readFile_groupSpec
      fineCostModel cliIo.rd F0 StoresGhost.opened.identity.peers rem.name).seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (by decide)

private theorem s2b_idSavePoll_credit (F0 : FsFiles)
    (rem : CryptoVerification.LibsignalPublicApiRepr.AddrVal)
    (k : CryptoGames.LibsignalSession.IdentityKey)
    (hrem40 : rem.name.length ≤ 40)
    (hcap64 : ∀ bs,
      cliIo.rd F0 (pathOf StoresGhost.opened.identity.peers.path rem.name) = .ok bs →
      bs.length ≤ 64) :
    PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSavePollEnv
        cliIo.rd
        (DirGetEnv PathEnv
          (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.ReadFileRuleEnv cliIo.rd)
          cliIo.rd)
        LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux.DirPutStrEnv
        F0 StoresGhost.opened.identity rem k)
      (s2b_idGet64Cum + 13003) 0 0 s2b_idGet64MaxReq := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSavePollEnv
  have hget : PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv
        (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.ReadFileRuleEnv cliIo.rd)
        cliIo.rd F0 StoresGhost.opened.identity.peers rem.name)
      s2b_idGet64Cum 0 0 s2b_idGet64MaxReq :=
    (LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux.dirGetEnv_path_readFile_fine_phaseCredit_tight
      cliIo.rd F0 StoresGhost.opened.identity.peers rem.name
      (LibsignalBinary.Proofs.PeakBudget.CliDomainCaps.dirDomainCaps_opened_peers.mono
        (by decide) (Nat.le_refl 0) (Nat.le_refl 0))
      (Nat.le_trans hrem40 (by decide)) hcap64).mono
      (Nat.le_refl _) (by decide) (by decide) (Nat.le_refl _)
  have htail : PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSaveTailEnv
        LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux.DirPutStrEnv
        StoresGhost.opened.identity rem k
        (StoresGhost.opened.identity.peers.get cliIo.rd F0 rem.name))
      13003 0 0 256 := by
    unfold LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSaveTailEnv
    cases StoresGhost.opened.identity.peers.get cliIo.rd F0 rem.name with
    | error u =>
      cases u
      exact (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
    | ok _ =>
      have hfr := PhaseCreditSpec.freeOnly
        LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas.fineCostModel_freeNonInc
      have hpk : PhaseCreditSpec fineCostModel
          LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.PublicKeySerializeEnv
          1607 0 0 256 :=
        (PhaseCreditSpec.rustAlloc_small fineCostModel (req := 33) (al := 1)
          (by decide) (by decide)
          (by rw [LibsignalBinary.Heap.Fine.ClientBounds.fineCostModel_smallMaxReq_eq]; decide)).mono
          (LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit.fineSmallAllocCost_le_1607_of_le_64
            (by decide))
          (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
      have hput := s2b_dirPutStr_opened_credit (dir := StoresGhost.opened.identity.peers) rfl
        rem.name k.serialize hrem40
      exact (hfr.seq (hpk.seq hput)).mono (by decide) (by decide) (by decide) (by decide)
  exact (hget.seq htail).mono (Nat.le_refl _) (by decide) (by decide) (by decide)

private theorem s2b_idSavePoll_group (F0 : FsFiles)
    (rem : CryptoVerification.LibsignalPublicApiRepr.AddrVal)
    (k : CryptoGames.LibsignalSession.IdentityKey) :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSavePollEnv
        cliIo.rd
        (DirGetEnv PathEnv
          (LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget.ReadFileRuleEnv cliIo.rd)
          cliIo.rd)
        LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux.DirPutStrEnv
        F0 StoresGhost.opened.identity rem k)
      (48 * FineScale) := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSavePollEnv
  have hget :=
    LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux.dirGetEnv_path_readFile_groupSpec
      fineCostModel cliIo.rd F0 StoresGhost.opened.identity.peers rem.name
  have htail : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSaveTailEnv
        LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux.DirPutStrEnv
        StoresGhost.opened.identity rem k
        (StoresGhost.opened.identity.peers.get cliIo.rd F0 rem.name))
      (9 * FineScale) := by
    unfold LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSaveTailEnv
    cases StoresGhost.opened.identity.peers.get cliIo.rd F0 rem.name with
    | error u =>
      cases u
      exact (PhaseGroupSpec.nil fineCostModel).mono (by decide)
    | ok _ =>
      have hfr := PhaseGroupSpec.freeOnly fineCostModel
      have hpk : PhaseGroupSpec fineCostModel
          LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.PublicKeySerializeEnv
          (3 * FineScale) :=
        PhaseGroupSpec.rustAlloc_any fineCostModel 33 1
      have hput := s2b_dirPutStr_opened_group (dir := StoresGhost.opened.identity.peers) rfl
        rem.name k.serialize
      exact (hfr.seq (hpk.seq hput)).mono (by decide)
  exact (hget.seq htail).mono (by decide)

private abbrev s2b_w2StoreLivePeak : Nat :=
  1080975 +
    LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit.optLargeCost fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 1128000) +
    LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit.optLargeCost fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 3225192)

private theorem s2b_storePoll_credit
    (rem : CryptoVerification.LibsignalPublicApiRepr.AddrVal)
    (rec' : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)))
    (hrem40 : rem.name.length ≤ 40)
    (hDom : ∀ ses, rec'.currentSession = some ses →
      LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.SessionCloneDom
        (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 1128000) ses)
    (hEnc : (CryptoVerification.E2E.Record.encodeRecord rec').length ≤
      LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 3225192) :
    PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget.cliSessionKitStorePollEnv
        (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget.AddrTextValEnv
          LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget.DecimalEnv)
        LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.RecordSerializeSeqFreeValidEnv
        LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux.DirPutEnv
        StoresGhost.opened.sessions rem rec')
      8441994 s2b_w2StoreLivePeak s2b_w2StoreLivePeak 5322344 := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget.cliSessionKitStorePollEnv
  have had :=
    LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux.addrTextValEnv_decimal_fine_phaseCredit_tight
      rem hrem40
  have hser : PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.RecordSerializeSeqFreeValidEnv rec')
      8420940 s2b_w2StoreLivePeak s2b_w2StoreLivePeak 5322344 :=
    { req_align := fun evs ⟨g, hgv, hs⟩ => by
        have hValid : ∀ G ses, g.cur = some G → rec'.currentSession = some ses →
            LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget.SessionGhostValid G ses ∧
            LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.SessionCloneDom
              (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 1128000) ses := by
          intro G ses hg hr
          unfold LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.RecordGhostValid at hgv
          rw [hg, hr] at hgv
          exact ⟨hgv, hDom ses hr⟩
        have hm := (LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit.PhaseCreditSpec.recordSerialize_seqFree_tight
          LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas.fineCostModel_modelHyps g rec').mono
          (LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordSerializeTightCum_fine_le_of_dom hValid)
          (LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordSerializePeak_fine_le_of_dom hValid hEnc)
          (LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordSerializePeak_fine_le_of_dom hValid hEnc)
          (Nat.le_trans
            (LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordSerializeMaxReq_le_of_dom hValid hEnc)
            (by decide : max (max 208000 (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 1128000))
              (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 3225192) ≤ 5322344))
        exact hm.req_align evs hs
      credit_le := fun st0 {_} ⟨g, hgv, hs⟩ => by
        have hValid : ∀ G ses, g.cur = some G → rec'.currentSession = some ses →
            LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget.SessionGhostValid G ses ∧
            LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.SessionCloneDom
              (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 1128000) ses := by
          intro G ses hg hr
          unfold LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.RecordGhostValid at hgv
          rw [hg, hr] at hgv
          exact ⟨hgv, hDom ses hr⟩
        have hm := (LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit.PhaseCreditSpec.recordSerialize_seqFree_tight
          LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas.fineCostModel_modelHyps g rec').mono
          (LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordSerializeTightCum_fine_le_of_dom hValid)
          (LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordSerializePeak_fine_le_of_dom hValid hEnc)
          (LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordSerializePeak_fine_le_of_dom hValid hEnc)
          (Nat.le_trans
            (LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordSerializeMaxReq_le_of_dom hValid hEnc)
            (by decide : max (max 208000 (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 1128000))
              (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 3225192) ≤ 5322344))
        exact hm.credit_le st0 hs }
  have hput := s2b_dirPutTail_opened_credit (dir := StoresGhost.opened.sessions) rfl
    (CryptoVerification.SignalSession.Cli.addressText rem)
  exact (had.seq (hser.seq hput)).mono (by decide) (by decide) (by decide) (by decide)

private theorem s2b_storePoll_group
    (rem : CryptoVerification.LibsignalPublicApiRepr.AddrVal)
    (rec' : CryptoGames.LibsignalSessionApi.SessionRecord (List (BitVec 8)))
    (hrem40 : rem.name.length ≤ 40)
    (hDom : ∀ ses, rec'.currentSession = some ses →
      LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.SessionCloneDom
        (LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux.sessionCapBytes + 1128000) ses) :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget.cliSessionKitStorePollEnv
        (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget.AddrTextValEnv
          LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget.DecimalEnv)
        LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.RecordSerializeSeqFreeValidEnv
        LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux.DirPutEnv
        StoresGhost.opened.sessions rem rec')
      (9 * FineScale +
        LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.recordSerializeDomFineGrpS) := by
  unfold LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget.cliSessionKitStorePollEnv
  have had :=
    LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux.addrTextValEnv_decimal_fine_groupSpec
      rem hrem40
  have hser : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.RecordSerializeSeqFreeValidEnv rec')
      LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.recordSerializeDomFineGrpS :=
    { groups_le := fun st0 {_} ⟨g, hgv, hs⟩ =>
        (LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.recordSerializeSeqFreeEnv_dom_fine_groupSpec
          hgv hDom).groups_le st0 hs }
  have hput := s2b_dirPutTail_opened_group (dir := StoresGhost.opened.sessions) rfl
    (CryptoVerification.SignalSession.Cli.addressText rem)
  exact (had.seq (hser.seq hput)).mono (by decide)


private theorem exists_mem_zip_of_mem_right {α β : Type} :
    ∀ {xs : List α} {ys : List β} {y : β},
      xs.length = ys.length → y ∈ ys → ∃ x, (x, y) ∈ xs.zip ys
  | [], [], _, _, hy => nomatch hy
  | x :: xs, _ :: ys, y, hlen, hy => by
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨x, List.mem_cons_self ..⟩
    · obtain ⟨x', hx'⟩ := exists_mem_zip_of_mem_right (Nat.succ.inj hlen) hy'
      exact ⟨x', List.mem_cons_of_mem _ hx'⟩

private theorem mk_len_le_of_sessionGhostValid
    {G : SessionGhost} {ses : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hgv : SessionGhostValid G ses) :
    ∀ c ∈ ses.state.receiverChains, c.messageKeys.length ≤ maxMessageKeys := by
  have hgcv := ghostCloneValid_of_sessionGhostValid hgv
  intro c hc
  obtain ⟨gc, hgc⟩ := exists_mem_zip_of_mem_right hgcv.chains_len hc
  exact (hgcv.chains_ok (gc, c) hgc).2.2

/-- Curried `W2` (`decryptSignal` `@109`) `PhaseCreditSpec` for `ckx2_cliDecryptSignalBinaryKitSlotEnvExact`. -/
theorem ckx2_w2DecSigExact_phaseCredit [LibsignalPlacement] (W : CliHooks) :
    ckx2_w2DecSigExact_phaseCredit_Stmt W := by
  intro g peerV M A w2R hi hp _hc hrep hdom
  obtain ⟨hpeerVal, hxpeer, hrem, hct, hF⟩ := hdom peerV rfl
  have hPeerTight : PeerSpqrStateTight640 W.C.F W.Q.K w2R.x.F w2R.x.peer.val := by
    rw [hF, hxpeer, hpeerVal]
    exact peerSpqrStateTight640_of_cliPqInputs_recv hi hp
  refine PhaseCreditSpec.of_imp (fun _ h => h hPeerTight) ?_
  change PhaseCreditSpec fineCostModel
    (CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A w2R.B
      (ckx2_TryDecryptCliLinkedEnvOf 109 W.C W.Q.K)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc w2R.B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc w2R.B)
      w2R.x)
    w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq
  rw [ckx2_cliDecryptSignalSlotEnv_fixed_eq_plain hi
    (ckx2_TryDecryptCliLinkedEnvOf 109 W.C W.Q.K) A w2R.B hF]
  unfold CliDecryptSignalSlotEnv
  rw [← hrep, hF, hxpeer]
  set x := toDecryptGhost w2R.x
  have ⟨_, hremName, _⟩ :=
    LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot.peer_and_rem_name_le_40_of_recv
      hp hpeerVal hrem
  have hrem40 : x.rem.val.name.length ≤ 40 := hremName
  have hSessFileCap : ∀ bs,
      cliIo.rd (runFiles g.i)
        (pathOf StoresGhost.opened.sessions.path
          (CryptoVerification.SignalSession.Cli.addressText w2R.peer.val)) = .ok bs →
      bs.length ≤ sessionCapBytes :=
    fun bs hbs =>
      LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs.cliIo_rd_ok_length_le_sessionCapBytes
        (runFiles g.i) _ bs hbs
  have hSessRemCap : ∀ bs,
      cliIo.rd (runFiles g.i)
        (pathOf StoresGhost.opened.sessions.path
          (CryptoVerification.SignalSession.Cli.addressText x.rem.val)) = .ok bs →
      bs.length ≤ sessionCapBytes :=
    fun bs hbs =>
      LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs.cliIo_rd_ok_length_le_sessionCapBytes
        (runFiles g.i) _ bs hbs
  have hIdCap64 : ∀ bs,
      cliIo.rd (runFiles g.i)
        (pathOf StoresGhost.opened.identity.peers.path x.rem.val.name) = .ok bs →
      bs.length ≤ 64 := by
    have h0 :=
      LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot.idPeers_rd_length_le_64_of_cliPqInputs_recv
        hi hp hpeerVal
    have hnm : x.rem.val.name = w2R.peer.name.bytes := congrArg (·.name) hrem
    rw [hnm]
    exact h0
  have hStateTight : PeerSpqrStateTight640 W.C.F W.Q.K (runFiles g.i) x.rem.val := by
    rw [hrem, hpeerVal]
    exact peerSpqrStateTight640_of_cliPqInputs_recv hi hp
  have hLoad :=
    LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.defaultLoadPollEnv_dcan_byBytes_2MiB_fine_phaseCredit_tight
      (Scope := scopeKit)
      LibsignalBinary.Proofs.PeakBudget.CliDomainCaps.dirDomainCaps_opened_sess
      (by decide) hrem40 hSessRemCap (by decide)
  let kit0 :=
    CryptoVerification.SignalSession.Cli.KitInst.cliSessionStoreSpec w2R.repAlloc 0#64 cliIo.rd
      (runFiles g.i) CryptoVerification.SignalSession.Cli.MainHops.cliWrOk
      scopeKit w2R.peer
      CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadShimNeed
      (CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadPollNeed w2R.B.readFile)
      CryptoVerification.SignalSession.Cli.KitInst.SessKit.storeShimNeed
      CryptoVerification.SignalSession.Cli.KitInst.SessKit.storePollNeedX
  have hcr :=
    LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak.withStoresDec_fine_creditSpec_tight
      (kit := decSessKitPlaced w2R.repAlloc (runFiles g.i) w2R.peer w2R.B)
      (kitEnv := decBinarySessKitPlacedBudget w2R.repAlloc w2R.B (runFiles g.i) w2R.peer)
      (st0 := StoresGhost.opened.sessions)
      (ikit := decIdKitPlaced w2R.repAlloc (runFiles g.i) w2R.peer w2R.B)
      (ikitEnv := decBinaryIdKitPlacedBudget w2R.repAlloc w2R.B (runFiles g.i) w2R.peer)
      (ist0 := StoresGhost.opened.identity)
      (C := W.C) (S := pqxdhSpqrModel ⟨W.C, W.Q⟩) (parse := uuidTryParse)
      (tdEnv := ckx2_TryDecryptCliLinkedEnvOf 109 W.C W.Q.K)
      (Scope := scopeKit) (x := x)
      (nameCap := 40)
      rfl rfl rfl rfl hremName (by decide)
      hLoad
      (fun rec ses G hsc hcur hgv => by
        have hsc0 : kit0.ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val rec := hsc
        obtain ⟨_, hDom⟩ :=
          LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak.opened_scopeAt_sessionCloneDom
            hrem hSessFileCap hsc0 hcur
        have hTop :=
          LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.peerSpqrStateTight640_of_cliSessionStoreSpec
            hsc0 hcur rfl hStateTight
        have hmk := mk_len_le_of_sessionGhostValid hgv
        exact LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordDecrypt_dom_phaseCredit_tight
          (x := recGhostOf x 0#64 G ses.state)
          (ses := ses) rfl hgv hDom
          (fun G₁ _ =>
            ckx2_tryDecryptCliLinkedEnvOf_phaseCreditSpec 109 msgCapBytes
              (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.recordTryDecryptEnvArgs
                (recGhostOf x 0#64 G ses.state) G₁)
              hDom.rc_len hmk hTop hct))
      (fun _ _ _ _ k _ _ _ _ => s2b_idTrustPoll_credit (runFiles g.i) x.rem.val k hrem40 hIdCap64)
      (fun _ _ _ _ k _ _ _ _ => s2b_idSavePoll_credit (runFiles g.i) x.rem.val k hrem40 hIdCap64)
      (fun rec _ rec' ses' _ hsc hdec hc' _ => by
        have hsc0 : kit0.ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val rec := hsc
        have hRecTight :=
          LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.recordSpqrStateTight640_of_cliSessionStoreSpec
            hsc0 hStateTight
        have hIn :=
          LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWrappers.scopeIn_of_scopeKit_and_recordSpqrStateTight640
            hsc0.1 hRecTight
        have hEncPre :=
          LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak.opened_scopeAt_encodeRecord_le
            hrem hSessFileCap hsc0
        obtain ⟨_, hPostDom, hEncPost⟩ :=
          LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak.decryptRecord_post_caps_of_scopeIn
            hIn hEncPre hdec
        obtain ⟨_, hDomPost⟩ := hPostDom ses' hc'
        exact s2b_storePoll_credit x.rem.val rec' hrem40
          (fun s hs => by rw [hc'] at hs; injection hs with hs; subst hs; exact hDomPost)
          hEncPost)
  exact hcr.mono (by decide) (by decide) (by decide) (by decide)

/-- Curried `W2` (`decryptSignal` `@109`) `PhaseGroupSpec` for `ckx2_cliDecryptSignalBinaryKitSlotEnvExact`. -/
theorem ckx2_w2DecSigExact_groupSpec [LibsignalPlacement] (W : CliHooks) :
    ckx2_w2DecSigExact_groupSpec_Stmt W := by
  intro g peerV M A w2R hi hp _hc hrep hdom
  obtain ⟨hpeerVal, hxpeer, hrem, _, hF⟩ := hdom peerV rfl
  have hPeerTight : PeerSpqrStateTight640 W.C.F W.Q.K w2R.x.F w2R.x.peer.val := by
    rw [hF, hxpeer, hpeerVal]
    exact peerSpqrStateTight640_of_cliPqInputs_recv hi hp
  refine PhaseGroupSpec.of_imp ?_ (fun _ h => h hPeerTight)
  change PhaseGroupSpec fineCostModel
    (CliDecryptSignalSlotEnv ⟨W.C, W.Q⟩ A w2R.B
      (ckx2_TryDecryptCliLinkedEnvOf 109 W.C W.Q.K)
      (decBinarySessKitPlacedBudgetFixed A.repAlloc w2R.B)
      (decBinaryIdKitPlacedBudgetFixed A.repAlloc w2R.B)
      w2R.x)
    w2DecSigExactGrpS
  rw [ckx2_cliDecryptSignalSlotEnv_fixed_eq_plain hi
    (ckx2_TryDecryptCliLinkedEnvOf 109 W.C W.Q.K) A w2R.B hF]
  unfold CliDecryptSignalSlotEnv
  rw [← hrep, hF, hxpeer]
  set x := toDecryptGhost w2R.x
  have ⟨_, hremName, _⟩ :=
    LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot.peer_and_rem_name_le_40_of_recv
      hp hpeerVal hrem
  have hrem40 : x.rem.val.name.length ≤ 40 := hremName
  have hSessFileCap : ∀ bs,
      cliIo.rd (runFiles g.i)
        (pathOf StoresGhost.opened.sessions.path
          (CryptoVerification.SignalSession.Cli.addressText w2R.peer.val)) = .ok bs →
      bs.length ≤ sessionCapBytes :=
    fun bs hbs =>
      LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs.cliIo_rd_ok_length_le_sessionCapBytes
        (runFiles g.i) _ bs hbs
  have hStateTight : PeerSpqrStateTight640 W.C.F W.Q.K (runFiles g.i) x.rem.val := by
    rw [hrem, hpeerVal]
    exact peerSpqrStateTight640_of_cliPqInputs_recv hi hp
  have hLoad :=
    LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.defaultLoadPollEnv_dcan_byBytes_fine_groupSpec
      (rd := cliIo.rd) (Scope := scopeKit)
      (F0 := runFiles g.i) (dir := StoresGhost.opened.sessions) (rem := x.rem.val) hrem40
  let kit0 :=
    CryptoVerification.SignalSession.Cli.KitInst.cliSessionStoreSpec w2R.repAlloc 0#64 cliIo.rd
      (runFiles g.i) CryptoVerification.SignalSession.Cli.MainHops.cliWrOk
      scopeKit w2R.peer
      CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadShimNeed
      (CryptoVerification.SignalSession.Cli.KitInst.SessKit.loadPollNeed w2R.B.readFile)
      CryptoVerification.SignalSession.Cli.KitInst.SessKit.storeShimNeed
      CryptoVerification.SignalSession.Cli.KitInst.SessKit.storePollNeedX
  have hgrp :=
    LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak.withStoresDec_phaseGroupSpec
      (kit := decSessKitPlaced w2R.repAlloc (runFiles g.i) w2R.peer w2R.B)
      (kitEnv := decBinarySessKitPlacedBudget w2R.repAlloc w2R.B (runFiles g.i) w2R.peer)
      (st0 := StoresGhost.opened.sessions)
      (ikit := decIdKitPlaced w2R.repAlloc (runFiles g.i) w2R.peer w2R.B)
      (ikitEnv := decBinaryIdKitPlacedBudget w2R.repAlloc w2R.B (runFiles g.i) w2R.peer)
      (ist0 := StoresGhost.opened.identity)
      (C := W.C) (S := pqxdhSpqrModel ⟨W.C, W.Q⟩) (parse := uuidTryParse)
      (tdEnv := ckx2_TryDecryptCliLinkedEnvOf 109 W.C W.Q.K)
      (Scope := scopeKit) (x := x)
      hLoad
      (fun rec ses G hsc hcur hgv => by
        have hsc0 : kit0.ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val rec := hsc
        obtain ⟨_, hDom⟩ :=
          LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak.opened_scopeAt_sessionCloneDom
            hrem hSessFileCap hsc0 hcur
        have hTop :=
          LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.peerSpqrStateTight640_of_cliSessionStoreSpec
            hsc0 hcur rfl hStateTight
        have hmk := mk_len_le_of_sessionGhostValid hgv
        exact LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.recordDecrypt_dom_phaseGroup
          (x := recGhostOf x 0#64 G ses.state)
          (ses := ses) rfl hgv hDom
          (fun G₁ _ =>
            ckx2_tryDecryptCliLinkedEnvOf_phaseGroupSpec 109
              (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.recordTryDecryptEnvArgs
                (recGhostOf x 0#64 G ses.state) G₁)
              hmk hTop))
      (fun _ _ _ _ k _ _ _ _ => s2b_idTrustPoll_group (runFiles g.i) x.rem.val k)
      (fun _ _ _ _ k _ _ _ _ => s2b_idSavePoll_group (runFiles g.i) x.rem.val k)
      (fun rec _ rec' ses' _ hsc hdec hc' _ => by
        have hsc0 : kit0.ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val rec := hsc
        have hRecTight :=
          LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift.recordSpqrStateTight640_of_cliSessionStoreSpec
            hsc0 hStateTight
        have hIn :=
          LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWrappers.scopeIn_of_scopeKit_and_recordSpqrStateTight640
            hsc0.1 hRecTight
        have hEncPre :=
          LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak.opened_scopeAt_encodeRecord_le
            hrem hSessFileCap hsc0
        obtain ⟨_, hPostDom, _⟩ :=
          LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak.decryptRecord_post_caps_of_scopeIn
            hIn hEncPre hdec
        obtain ⟨_, hDomPost⟩ := hPostDom ses' hc'
        exact s2b_storePoll_group x.rem.val rec' hrem40
          (fun s hs => by rw [hc'] at hs; injection hs with hs; subst hs; exact hDomPost))
  exact hgrp.mono (by decide)

/-- Bundled `SingleSlotFineSpec` for `ckx2_cliDecryptSignalBinaryKitSlotEnvExact`. -/
def ckx2_w2DecSigExact_singleSlotFineSpec [LibsignalPlacement] (W : CliHooks)
    (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV))
    (hc : g.c = .recv peerV)
    (hrep : w2R.repAlloc = A.repAlloc)
    (hdom : W2BinaryWhisperDom (.recv peerV) g.i w2R) :
    SingleSlotFineSpec (ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A w2R.B w2R.x) :=
  ckx2_w2DecSigExact_singleSlotFineSpec_of_stmts W
    (ckx2_w2DecSigExact_phaseCredit W)
    (ckx2_w2DecSigExact_groupSpec W)
    g peerV M A w2R hi hp hc hrep hdom

end LibsignalBinary.Proofs.PeakBudget.CliKitW2RecvExactAuxR2Race
