/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactSplit
import LibsignalBinary.Heap.Fine.ClientBounds
import LibsignalBinary.Heap.Fine.CreditInst
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
import LibsignalBinary.Proofs.E2E.Epochs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
import LibsignalBinary.Proofs.E2E.RecordX.ScopeP
import LibsignalBinary.Proofs.E2E.V1.SpqrV1FactsPure
import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps
import LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
import LibsignalBinary.Proofs.PeakBudget.SpqrSendTieLemmas
import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
import LibsignalBinary.Proofs.PeakBudget.W1EncryptPeakSpec
import LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments
import LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak
import LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
import LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak
import LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Callees
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefs
import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr

/-!
# Guarded-Tight `W1` (`encrypt` `@109`) Credit Core

**Checked by Lean.**

Proves `w1x_creditCore_Stmt W` from placed session/identity kit, wire-message, and
`W1EncryptSlotPeak` credit bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactC

open Arm64.Process (bytesOfString)
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession
  (Crypto IdentityKey Mut OutgoingTripleRatchet PublicKey SessionState ShaCompress
   SignalMessage Spqr aesCbcEncrypt serializeContent)
open CryptoGames.LibsignalSessionApi
  (Direction KyberPayload PendingPreKey PreKeySignalMessage ProtoPreKeySignalMessage Session
   SessionRecord execOk)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams pqxdhSpqrModel)
open CryptoVerification.E2E.Epochs
  (exec_bind exec_get exec_liftE exec_map exec_modifyGet exec_pure exec_set exec_throw)
open CryptoVerification.E2E.Record (RecordRepr encodeRecord)
open CryptoVerification.E2E.RecordX (RecordInScopeP SessionScopeP)
open CryptoVerification.E2E.V1 (spqrV1Send_msg_len_le)
open CryptoVerification.LibsignalProtoCodec
  (WireType encodeBytesField encodeKey encodeUint32Field encodeVarint encodeVarintAux
   protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (PreKeyMsgNewCall WithStoresEncGhost storedRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SignalMessageNewGhost)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost addrBytes serializeAddresses serviceIdParse uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs Inputs)
open CryptoVerification.SignalSession.Cli (DirGhost StoresGhost addressText pathOf)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (EncGhost runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1EncGhost)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs RustCliAllocBudget SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel fineSmallAllocCost)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineCostModel_largeCost_eq fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
  (toTempTwinsIkitEnv toTempTwinsKitEnv)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (DirDomainCaps dirDomainCaps_opened_peers dirDomainCaps_opened_sess)
open LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact
  (w1EncExactCum w1EncExactLive w1EncExactMaxReq w1EncExactPeak)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactSplit
  (W1X_WithStoresEncTight w1x_PkCallGuard w1x_SigGuard w1x_creditCore_Stmt w1x_sendEnv109)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1SpqrSendAuxR2
  (ckx2_spqrSendCoins109_phaseCredit_of_stateTight640)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (RecordSerializeSeqFreeValidEnv W1BinarySendDom W1BinarySendParams
   w1BinaryIdKitPlacedBudget w1BinarySessKitPlacedBudget)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
  (cliIo_rd_ok_length_le_sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (dirGetEnv_fixed_eq_of_not_overCap not_overCapFile_runFiles_identities
   not_overCapFile_runFiles_sessions w1BinaryIdKitPlacedBudgetFixed
   w1BinarySessKitPlacedBudgetFixed)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (fineReadFileCum fineReadFileLive fineReadFileMaxReq fineReadFilePeak optLargeCost)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (fineSmallAllocCost_le_1607_of_le_64 rustAllocTightCum rustAllocTightCum_fine_le_738)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (PhaseCreditSpec.recordSerialize_seqFree_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps
  (msgCapBytes sessionCapBytes spqrStateTightCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
  (spqrSendTightDeltaCum spqrSendTightDeltaLive spqrSendTightDeltaPeak spqrSendTightMaxReq)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTieLemmas
  (peerSpqrStateTight640_of_cliSessionStoreSpecPlaced)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (TopStateTight topStateTight_length_le topStateTight_spqrV1_send)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptPeakSpec
  (tryCloneLargeDelta_fineCostModel_le_add tryCloneSmallDelta_fineCostModel_le_143484)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments
  (FromKeySegEnv OtrEncryptStepEnv WithStoresEncSegEnv otrEncryptStep_creditSpec_tight
   phaseCreditSpec_exists)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak
  (FromOtrTightEnv WithStoresEncTightEnv otrAfterNone otrAfterSome
   withStoresEncTight_creditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
  (peer_and_rem_name_le_40_of_send w1CtLenCap w1PkCumCap w1PkLiveCap w1PkOutCap w1PkPeakCap
   w1PkReqCap w1PostPqCap w1SigCumCap w1SigLiveCap w1SigPeakCap w1SigReqCap w1SmSerCap
   w1StoreEncCap)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (RecordGhostValid SessionCloneDom recordSerializeMaxReq_le_of_dom
   recordSerializePeak_fine_le_of_dom recordSerializeTightCum_fine_le_of_dom
   sessionCloneDom_of_scopeKit_pq)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak
  (encodeRecord_length_le_of_scopeKit)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (PreKeyMsgNewEnv PreKeyMsgNewRawEnv kyberPayloadLen preKeyMsgNewDeltaCum preKeyMsgNewDeltaLive
   preKeyMsgNewDeltaPeak preKeyMsgNewMaxReq preKeyMsgNewRawDeltaCum preKeyMsgNewRawDeltaLive
   preKeyMsgNewRawDeltaPeak preKeyMsgNewRawMaxReq preKeyMsgNew_phaseCredit
   signalMessageNewDeltaCum signalMessageNewDeltaLive signalMessageNewDeltaPeak
   signalMessageNewMaxReq signalMessageNewSerLen signalMessageNew_phaseCredit)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
  (FromApplyEnv FromCmEnv FromKeyEnv FromOtrEnv FromSaveEnv PreKeyPostEncryptEnv SaveStepEnv
   TrustStepEnv WithStoresEncEnv pendingKyberPayload preKeyMsgFromItems)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (deserCancelFineCum deserCancelFineLive deserCancelFineMaxReq deserCancelFinePeak)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv DirPutTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSavePollEnv cliIdentityKitSaveTailEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitLoadPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
  (CliEncryptSlotEnv w1IdKitPlaced w1SessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
  (defaultLoadPollEnv_dcan_byBytes_fine_phaseCredit_tight defaultLoadPollTightDeltaCum ofBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
  (addrTextValEnv_decimal_fine_phaseCredit_tight dirGetEnv_path_readFile_fine_phaseCredit_tight
   seq_freeOnly_phaseCredit)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
  (OtrEncryptCoreEnv SpqrSendBudgetEnv otrSignalMsgGhost)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
  (SignalMessageNewEnv)

attribute [local simp]
  exec_bind exec_get exec_liftE exec_map exec_modifyGet exec_pure exec_set exec_throw

/-! ## `*BudgetFixed` to `*Budget` Reduction on `runFiles` -/

private theorem w1c_sessLoadPoll_fixed_eq {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (a : AddrVal) :
    cliSessionKitLoadPollEnv cliIo.rd scopeKit (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        (ofBytesEnv RecordDeserializeCancelEnv) (runFiles i) StoresGhost.opened.sessions a =
      cliSessionKitLoadPollEnv cliIo.rd scopeKit (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        (ofBytesEnv RecordDeserializeCancelEnv) (runFiles i) StoresGhost.opened.sessions a := by
  unfold cliSessionKitLoadPollEnv
  rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_sessions hi _)]

private theorem w1c_idTrustPoll_fixed_eq {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (a : AddrVal) (k : IdentityKey) (d : Direction) :
    cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        (runFiles i) StoresGhost.opened.identity a k d =
      cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        (runFiles i) StoresGhost.opened.identity a k d := by
  unfold cliIdentityKitTrustPollEnv
  rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_identities hi _)]

private theorem w1c_idSavePoll_fixed_eq {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (a : AddrVal) (k : IdentityKey) :
    cliIdentityKitSavePollEnv cliIo.rd (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        DirPutStrEnv (runFiles i) StoresGhost.opened.identity a k =
      cliIdentityKitSavePollEnv cliIo.rd (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        DirPutStrEnv (runFiles i) StoresGhost.opened.identity a k := by
  unfold cliIdentityKitSavePollEnv
  rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_identities hi _)]

private theorem w1c_cliEncryptSlotEnv_fixed_eq_plain [LibsignalPlacement] {M : AllocCostModel}
    {P : PEParams} {i : Inputs} (hi : CliPqxdhInputs P i)
    (A : RustCliAllocBudget M) (B : RunBudgets) (sendEnv : SpqrSendBudgetEnv)
    {x : EncGhost} (hx : x.F = runFiles i) :
    CliEncryptSlotEnv P A B sendEnv
        (w1BinarySessKitPlacedBudgetFixed A.repAlloc B)
        (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B) x =
      CliEncryptSlotEnv P A B sendEnv
        (w1BinarySessKitPlacedBudget A.repAlloc B)
        (w1BinaryIdKitPlacedBudget A.repAlloc B) x := by
  have hload :
      (toTempTwinsKitEnv
          (w1BinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer)).loadPollEnv
          StoresGhost.opened.sessions (w1EncGhost x).rem.val =
        (toTempTwinsKitEnv
          (w1BinarySessKitPlacedBudget A.repAlloc B x.F x.peer)).loadPollEnv
          StoresGhost.opened.sessions (w1EncGhost x).rem.val := by
    change cliSessionKitLoadPollEnv _ _ _ _ _ x.F _ _ = cliSessionKitLoadPollEnv _ _ _ _ _ x.F _ _
    rw [hx]
    exact w1c_sessLoadPoll_fixed_eq hi _
  have htrust : ∀ k,
      (toTempTwinsIkitEnv
          (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer)).trustPollEnv
          StoresGhost.opened.identity (w1EncGhost x).rem.val k .sending =
        (toTempTwinsIkitEnv
          (w1BinaryIdKitPlacedBudget A.repAlloc B x.F x.peer)).trustPollEnv
          StoresGhost.opened.identity (w1EncGhost x).rem.val k .sending := by
    intro k
    change cliIdentityKitTrustPollEnv _ x.F _ _ k .sending =
      cliIdentityKitTrustPollEnv _ x.F _ _ k .sending
    rw [hx]
    exact w1c_idTrustPoll_fixed_eq hi _ k .sending
  have hsave : ∀ k,
      (toTempTwinsIkitEnv
          (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer)).savePollEnv
          ((w1IdKitPlaced A.repAlloc B x.F x.peer).trustUpdate StoresGhost.opened.identity
            (w1EncGhost x).rem.val k .sending (.ok true))
          (w1EncGhost x).rem.val k =
        (toTempTwinsIkitEnv
          (w1BinaryIdKitPlacedBudget A.repAlloc B x.F x.peer)).savePollEnv
          ((w1IdKitPlaced A.repAlloc B x.F x.peer).trustUpdate StoresGhost.opened.identity
            (w1EncGhost x).rem.val k .sending (.ok true))
          (w1EncGhost x).rem.val k := by
    intro k
    change cliIdentityKitSavePollEnv _ _ _ x.F StoresGhost.opened.identity _ _ =
      cliIdentityKitSavePollEnv _ _ _ x.F StoresGhost.opened.identity _ _
    rw [hx]
    exact w1c_idSavePoll_fixed_eq hi _ k
  have hstore :
      (toTempTwinsKitEnv
          (w1BinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer)).storePollEnv =
        (toTempTwinsKitEnv
          (w1BinarySessKitPlacedBudget A.repAlloc B x.F x.peer)).storePollEnv := rfl
  have hcm : ∀ sess (otr' : OutgoingTripleRatchet (List (BitVec 8))) taken k,
      FromCmEnv (w1SessKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsKitEnv (w1BinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer))
          StoresGhost.opened.sessions
          (w1IdKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsIkitEnv (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer))
          StoresGhost.opened.identity (w1EncGhost x) sess otr' taken k =
        FromCmEnv (w1SessKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsKitEnv (w1BinarySessKitPlacedBudget A.repAlloc B x.F x.peer))
          StoresGhost.opened.sessions
          (w1IdKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsIkitEnv (w1BinaryIdKitPlacedBudget A.repAlloc B x.F x.peer))
          StoresGhost.opened.identity (w1EncGhost x) sess otr' taken k := by
    intro sess otr' taken k
    funext evs
    unfold FromCmEnv TrustStepEnv FromSaveEnv SaveStepEnv FromApplyEnv
    rw [htrust k, hsave k, hstore]
  have hotr : ∀ sess otr taken,
      FromOtrEnv P.C (pqxdhSpqrModel P) sendEnv uuidTryParse
          (w1SessKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsKitEnv (w1BinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer))
          StoresGhost.opened.sessions
          (w1IdKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsIkitEnv (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer))
          StoresGhost.opened.identity (w1EncGhost x) sess otr taken =
        FromOtrEnv P.C (pqxdhSpqrModel P) sendEnv uuidTryParse
          (w1SessKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsKitEnv (w1BinarySessKitPlacedBudget A.repAlloc B x.F x.peer))
          StoresGhost.opened.sessions
          (w1IdKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsIkitEnv (w1BinaryIdKitPlacedBudget A.repAlloc B x.F x.peer))
          StoresGhost.opened.identity (w1EncGhost x) sess otr taken := by
    intro sess otr taken
    funext evs
    unfold FromOtrEnv FromKeyEnv PreKeyPostEncryptEnv
    simp only [hcm]
  funext evs
  unfold CliEncryptSlotEnv WithStoresEncEnv
  rw [hload]
  simp only [hotr]

/-! ## Wire-Message Length Bounds and `WithStoresEncTightEnv` Containment -/

private theorem w1c_seqEnv_mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h₁ : ∀ e, E₁ e → E₁' e) (h₂ : ∀ e, E₂ e → E₂' e) :
    ∀ evs, SeqEnv E₁ E₂ evs → SeqEnv E₁' E₂' evs
  | _, Or.inl h => Or.inl (h₁ _ h)
  | _, Or.inr ⟨u, v, rfl, hu, hv⟩ => Or.inr ⟨u, v, rfl, h₁ u hu, h₂ v hv⟩

private theorem w1c_encodeVarintAux_len_le :
    ∀ (k : Nat) (v : BitVec 64), (encodeVarintAux k v).length ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, v => by
    unfold encodeVarintAux
    split_ifs
    · simp
    · simp only [List.length_cons]
      exact Nat.add_le_add_right (w1c_encodeVarintAux_len_le k (v >>> 7)) 1

private theorem w1c_encodeVarint_len_le (v : BitVec 64) : (encodeVarint v).length ≤ 10 :=
  w1c_encodeVarintAux_len_le 10 v

private theorem w1c_encodeKey_len_le (tag : Nat) (wt : WireType) : (encodeKey tag wt).length ≤ 10 :=
  w1c_encodeVarint_len_le _

private theorem w1c_encodeUint32Field_len_le (tag : Nat) (ov : Option (BitVec 32)) :
    (encodeUint32Field tag ov).length ≤ 20 := by
  cases ov with
  | none => simp [encodeUint32Field]
  | some v =>
    simp only [encodeUint32Field, List.length_append]
    have h1 := w1c_encodeKey_len_le tag .varint
    have h2 := w1c_encodeVarint_len_le (v.zeroExtend 64)
    omega

private theorem w1c_encodeBytesField_some_len_le (tag : Nat) (bs : List (BitVec 8)) :
    (encodeBytesField tag (some bs)).length ≤ 20 + bs.length := by
  simp only [encodeBytesField, List.length_append]
  have h1 := w1c_encodeKey_len_le tag .lengthDelimited
  have h2 := w1c_encodeVarint_len_le (BitVec.ofNat 64 bs.length)
  omega

private theorem w1c_serializeAddresses_len_36 {sender recipient : AddrGhost} {ad : List (BitVec 8)}
    (h : serializeAddresses (serviceIdParse uuidTryParse) sender recipient = some ad) :
    ad.length = 36 := by
  unfold serializeAddresses at h
  rcases hs : serviceIdParse uuidTryParse sender.name.bytes with _ | vs <;> rw [hs] at h
  · cases h
  · dsimp only [bind, Option.bind] at h
    rcases hr : serviceIdParse uuidTryParse recipient.name.bytes with _ | vr <;> rw [hr] at h
    · cases h
    · simp only [pure, Option.some.injEq] at h
      subst h
      simp only [addrBytes, List.length_append, List.length_cons, List.Vector.toList_length,
        List.length_nil]

private theorem w1c_aesCbcEncrypt_len (C : Crypto)
    (k : CryptoGames.CBC.AesKey) (iv : CryptoGames.CBC.Block)
    (ptext : List (BitVec 8)) :
    (aesCbcEncrypt C.E k iv ptext).length = (ptext.length / 16 + 1) * 16 := by
  have hblk : ∀ l : List (BitVec 128),
      (l.flatMap CryptoGames.CBC.blockToBytesLE).length = 16 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons b t ih =>
      have hb : (CryptoGames.CBC.blockToBytesLE b).length = 16 := by
        simp [CryptoGames.CBC.blockToBytesLE]
      simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, hb]
      omega
  unfold aesCbcEncrypt
  rw [hblk, List.Vector.toList_length]
  change 16 * (ptext.length / 16 + 1) = (ptext.length / 16 + 1) * 16
  exact Nat.mul_comm _ _

private theorem w1c_otrSignalMsgGhost_sigGuard
    (P : PEParams)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    {pq' : List (BitVec 8)} {pqrKey : Salt} {pqrMsg : List (BitVec 8)}
    {ptext : List (BitVec 8)} (locOpt : Option AddrGhost) (rem : AddrGhost)
    {rest : List (BitVec 8)}
    (hptext : ptext.length ≤ msgCapBytes)
    (hs : (pqxdhSpqrModel P).send otr.pqrState rest = some (pq', pqrKey, pqrMsg)) :
    w1x_SigGuard r sess otr taken
      (otrSignalMsgGhost P.C otr pqrKey pqrMsg ptext locOpt rem) := by
  set g := otrSignalMsgGhost P.C otr pqrKey pqrMsg ptext locOpt rem
  have hpmlen : pqrMsg.length ≤ 64 :=
    spqrV1Send_msg_len_le P.C.F P.Q.K otr.pqrState rest pq' pqrKey pqrMsg hs
  have hct_eq : g.ciphertext.length = (ptext.length / 16 + 1) * 16 := by
    dsimp only [g, otrSignalMsgGhost]
    exact w1c_aesCbcEncrypt_len P.C _ _ ptext
  have hct_le : g.ciphertext.length ≤ w1CtLenCap := by
    rw [hct_eq]
    unfold w1CtLenCap
    have hdiv : ptext.length / 16 ≤ msgCapBytes / 16 := Nat.div_le_div_right hptext
    omega
  have hpq_le : g.pqRatchet.length ≤ 4096 := by
    dsimp only [g, otrSignalMsgGhost]
    omega
  refine ⟨hct_le, hpq_le, ?_⟩
  unfold signalMessageNewSerLen SignalMessageNewGhost.protoMsg
  dsimp only [CryptoVerification.LibsignalProtoCodec.encode]
  simp only [List.length_append]
  have hrk : g.senderRatchetKey.serialize.length = 33 := by
    simp [PublicKey.serialize, List.Vector.toList_length]
  have h1 := w1c_encodeBytesField_some_len_le 1 g.senderRatchetKey.serialize
  have h2 := w1c_encodeUint32Field_len_le 2 (some g.counter)
  have h3 := w1c_encodeUint32Field_len_le 3 (some g.previousCounter)
  have h4 := w1c_encodeBytesField_some_len_le 4 g.ciphertext
  have h5 : (encodeBytesField 5 (if g.pqRatchet.isEmpty then none else some g.pqRatchet)).length ≤
      20 + g.pqRatchet.length := by
    split <;> [simp [encodeBytesField]; exact w1c_encodeBytesField_some_len_le 5 g.pqRatchet]
  have h6 : (encodeBytesField 6 (g.addresses uuidTryParse)).length ≤ 56 := by
    unfold SignalMessageNewGhost.addresses
    dsimp only [g, otrSignalMsgGhost]
    cases locOpt with
    | none => simp [encodeBytesField]
    | some l =>
      dsimp only [Option.bind]
      cases had : serializeAddresses (serviceIdParse uuidTryParse) l rem with
      | none => simp [encodeBytesField]
      | some ad =>
        have hlen36 := w1c_serializeAddresses_len_36 had
        have hb6 := w1c_encodeBytesField_some_len_le 6 ad
        omega
  have hgpq : g.pqRatchet.length ≤ 64 := hpmlen
  unfold w1SmSerCap
  omega

private theorem w1c_otrEncrypt_serialized_len_le (P : PEParams)
    (ptext : List (BitVec 8)) (addrs : Option (List (BitVec 8))) (coins : List (BitVec 8))
    (otr otr' : OutgoingTripleRatchet (List (BitVec 8))) (msg : SignalMessage)
    (haddrs : ∀ ad, addrs = some ad → ad.length ≤ 36)
    (he : execOk (OutgoingTripleRatchet.encrypt P.C protoSignalCodec (pqxdhSpqrModel P).spqr
      ptext addrs coins) otr = .ok (msg, otr')) :
    msg.serialized.length ≤ ptext.length + 300 := by
  unfold OutgoingTripleRatchet.encrypt execOk at he
  simp only [exec_bind, exec_get] at he
  cases hpan : (pqxdhSpqrModel P).spqr.sendPanics otr.pqrState coins
  case true => simp [hpan] at he
  simp only [hpan, Bool.false_eq_true, ↓reduceIte] at he
  rcases hs : (pqxdhSpqrModel P).spqr.send otr.pqrState coins with _ | ⟨pq', key, pm⟩
  · simp [hs] at he
  · have hpmlen : pm.length ≤ 64 :=
      spqrV1Send_msg_len_le P.C.F P.Q.K otr.pqrState coins pq' key pm hs
    simp only [hs, exec_pure, exec_bind] at he
    rcases hn : otr.senderChainKey.nextChainKey P.C.F with _ | next
    · simp [hn] at he
    · simp only [hn, exec_liftE, exec_set, Except.ok.injEq, Prod.mk.injEq] at he
      rcases he with ⟨rfl, rfl⟩
      have had6 : (encodeBytesField 6 addrs).length ≤ 56 := by
        cases h_a : addrs with
        | none => simp [encodeBytesField]
        | some ad =>
          have h1 := w1c_encodeBytesField_some_len_le 6 ad
          have h2 := haddrs ad h_a
          omega
      have hrk : otr.senderRatchetKey.publicKey.serialize.length = 33 := by
        simp [PublicKey.serialize, List.Vector.toList_length]
      have h5 : (encodeBytesField 5 (if pm.isEmpty then none else some pm)).length ≤
          20 + pm.length := by
        split <;> [simp [encodeBytesField]; exact w1c_encodeBytesField_some_len_le 5 pm]
      dsimp only [SignalMessage.new]
      rw [List.length_append]
      refine Nat.le_trans (Nat.add_le_add_left (List.length_take_le 8 _) _) ?_
      dsimp only [serializeContent, protoSignalCodec, CryptoVerification.LibsignalProtoCodec.encode]
      simp only [List.length_append, List.length_cons]
      have h1 := w1c_encodeBytesField_some_len_le 1 otr.senderRatchetKey.publicKey.serialize
      have h2 := w1c_encodeUint32Field_len_le 2 (some otr.senderChainKey.index)
      have h3 := w1c_encodeUint32Field_len_le 3 (some otr.previousCounter)
      have h4 := w1c_encodeBytesField_some_len_le 4 (aesCbcEncrypt P.C.E
        ((otr.senderChainKey.messageKeys P.C.F).generateKeys P.C.F key).cipherKey
        ((otr.senderChainKey.messageKeys P.C.F).generateKeys P.C.F key).iv ptext)
      have h4' := w1c_aesCbcEncrypt_len P.C
        ((otr.senderChainKey.messageKeys P.C.F).generateKeys P.C.F key).cipherKey
        ((otr.senderChainKey.messageKeys P.C.F).generateKeys P.C.F key).iv ptext
      omega

private theorem w1c_prost_varint_len_le (k : Nat) :
    ∀ n : Nat, n < 128 ^ (k + 1) →
      (CryptoGames.LibsignalSessionApi.Prost.varint n).length ≤ k + 1 := by
  induction k with
  | zero =>
    intro n hn
    rw [CryptoGames.LibsignalSessionApi.Prost.varint.eq_1]
    simp [show n < 128 by omega]
  | succ k ih =>
    intro n hn
    rw [CryptoGames.LibsignalSessionApi.Prost.varint.eq_1]
    split_ifs with hlt
    · simp
    · simp only [List.length_cons]
      have hpow : 128 ^ (k + 1 + 1) = 128 * 128 ^ (k + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have hdiv : n / 128 < 128 ^ (k + 1) := by omega
      have := ih (n / 128) hdiv
      omega

private theorem w1c_prost_uint32Field_len_le {tag : Nat} (ht : tag ≤ 8) (v? : Option (BitVec 32)) :
    (CryptoGames.LibsignalSessionApi.Prost.uint32Field tag v?).length ≤ 10 := by
  cases v? with
  | none => simp [CryptoGames.LibsignalSessionApi.Prost.uint32Field]
  | some v =>
    simp only [CryptoGames.LibsignalSessionApi.Prost.uint32Field,
      CryptoGames.LibsignalSessionApi.Prost.key, List.length_append]
    have h1 := w1c_prost_varint_len_le 0 (8 * tag + 0) (by omega)
    have h2 := w1c_prost_varint_len_le 4 v.toNat (by have := v.isLt; omega)
    omega

private theorem w1c_prost_bytesField_opt_len_le {tag : Nat} (ht : tag ≤ 8)
    (bs? : Option (List (BitVec 8))) (B : Nat)
    (hB : ∀ bs, bs? = some bs → bs.length ≤ B ∧ bs.length < 2 ^ 32) :
    (CryptoGames.LibsignalSessionApi.Prost.bytesField tag bs?).length ≤ 10 + B := by
  cases hbs : bs? with
  | none => simp [CryptoGames.LibsignalSessionApi.Prost.bytesField]
  | some bs =>
    obtain ⟨hle, hlt⟩ := hB bs hbs
    simp only [CryptoGames.LibsignalSessionApi.Prost.bytesField,
      CryptoGames.LibsignalSessionApi.Prost.key, List.length_append]
    have h1 := w1c_prost_varint_len_le 0 (8 * tag + 2) (by omega)
    have h2 := w1c_prost_varint_len_le 4 bs.length (by omega)
    omega

private theorem w1c_preKeyMsgNew_serialized_len_le
    (ver : BitVec 8) (regId : BitVec 32) (preKeyId : Option (BitVec 32)) (spk : BitVec 32)
    (kp : Option KyberPayload) (baseKey : PublicKey) (ik : IdentityKey) (msg : SignalMessage)
    (hkp : ∀ k, kp = some k → k.ciphertext.length ≤ 1569)
    (hmsg : msg.serialized.length < 2 ^ 32) :
    (PreKeySignalMessage.new ver regId preKeyId spk kp baseKey ik msg).serialized.length ≤
      msg.serialized.length + 1717 := by
  have hbk : baseKey.serialize.length = 33 := by
    simp [PublicKey.serialize, List.Vector.toList_length]
  have hik : ik.serialize.length = 33 := by
    simp [IdentityKey.serialize, PublicKey.serialize, List.Vector.toList_length]
  have hf1 := w1c_prost_uint32Field_len_le (tag := 1) (by omega) preKeyId
  have hf2 := w1c_prost_bytesField_opt_len_le (tag := 2) (by omega)
    (some baseKey.serialize) 33 (by
      intro bs hbs; injection hbs with hbs'; subst hbs'; omega)
  have hf3 := w1c_prost_bytesField_opt_len_le (tag := 3) (by omega)
    (some ik.serialize) 33 (by
      intro bs hbs; injection hbs with hbs'; subst hbs'; omega)
  have hf4 := w1c_prost_bytesField_opt_len_le (tag := 4) (by omega)
    (some msg.serialized) msg.serialized.length (by
      intro bs hbs; injection hbs with hbs'; subst hbs'; exact ⟨Nat.le_refl _, hmsg⟩)
  have hf5 := w1c_prost_uint32Field_len_le (tag := 5) (by omega) (some regId)
  have hf6 := w1c_prost_uint32Field_len_le (tag := 6) (by omega) (some spk)
  have hf7 := w1c_prost_uint32Field_len_le (tag := 7) (by omega) (kp.map (·.preKeyId))
  have hf8 := w1c_prost_bytesField_opt_len_le (tag := 8) (by omega)
    (kp.map (·.ciphertext)) 1569 (by
      intro bs hbs
      rcases h_k : kp with _ | k <;> rw [h_k] at hbs
      · cases hbs
      · simp only [Option.map_some, Option.some.injEq] at hbs
        subst hbs
        have hlen := hkp k h_k
        omega)
  simp only [PreKeySignalMessage.new, ProtoPreKeySignalMessage.encode, List.length_cons,
    List.length_append]
  omega

private theorem w1c_scopeKit_kyber_ciphertext_eq_1569
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    (hKit : scopeKit r) (hs : r.currentSession = some sess) :
    ∀ ct, sess.pendingKyberPreKey.map (·.ciphertext) = some ct → ct.length = 1569 := by
  obtain ⟨s', hs', hsp⟩ := hKit.2
  cases hs.symm.trans hs'
  intro ct hct
  rcases hky : sess.pendingKyberPreKey with _ | k
  · simp [hky] at hct
  · simp only [hky, Option.map_some, Option.some.injEq] at hct
    subst hct
    exact hsp.2.2.1 k hky

private theorem w1c_otrEncryptCore_imp_step
    (P : PEParams) (sendEnv : SpqrSendBudgetEnv)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (ptext : List (BitVec 8)) (locOpt : Option AddrGhost)
    (rem : AddrGhost) (rest : List (BitVec 8))
    (hptext : ptext.length ≤ msgCapBytes)
    {evs : List AllocEvent}
    (h : OtrEncryptCoreEnv P.C (pqxdhSpqrModel P) sendEnv uuidTryParse otr ptext locOpt rem rest evs) :
    OtrEncryptStepEnv (sendEnv otr.pqrState rest) ptext.length
      (fun evs' => ∃ g0, w1x_SigGuard r sess otr taken g0 ∧ SignalMessageNewEnv uuidTryParse g0 evs')
      evs := by
  unfold OtrEncryptCoreEnv at h
  unfold OtrEncryptStepEnv
  refine w1c_seqEnv_mono (fun _ => id) ?_ evs h
  intro evs' hevs'
  cases hs : (pqxdhSpqrModel P).send otr.pqrState rest with
  | none =>
    rw [hs] at hevs'
    have hnil : evs' = [] := hevs'
    subst hnil
    exact Or.inl FreeOnlyEvs.nil
  | some val =>
    rcases val with ⟨pq', pqrKey, pqrMsg⟩
    rw [hs] at hevs'
    have hsg :=
      w1c_otrSignalMsgGhost_sigGuard P r sess otr taken locOpt rem hptext hs
    exact Or.inr
      (w1c_seqEnv_mono (fun _ => id)
        (w1c_seqEnv_mono (fun _ => id)
          (w1c_seqEnv_mono
            (fun _ hsm =>
              ⟨otrSignalMsgGhost P.C otr pqrKey pqrMsg ptext locOpt rem, hsg, hsm⟩)
            (fun _ => id)))
        evs' hevs')

private theorem w1c_withStoresEnc_imp_tight {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (P : PEParams) (sendEnv : SpqrSendBudgetEnv)
    (x : WithStoresEncGhost)
    (hScopeImp : ∀ r, kit.ScopeAt scopeKit st0 x.rem.val r → scopeKit r)
    (hptext : x.ptext.length ≤ msgCapBytes)
    {evs : List AllocEvent}
    (h : WithStoresEncEnv kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 scopeKit P.C (pqxdhSpqrModel P) sendEnv uuidTryParse x evs) :
    WithStoresEncTightEnv scopeKit kit kitEnv st0 ikit ikitEnv ist0 P.C (pqxdhSpqrModel P) uuidTryParse x
      (fun r sess otr taken =>
        OtrEncryptStepEnv (sendEnv otr.pqrState x.rest) x.ptext.length
          (fun evs' => ∃ g0, w1x_SigGuard r sess otr taken g0 ∧ SignalMessageNewEnv uuidTryParse g0 evs'))
      (fun r sess otr taken =>
        OtrEncryptStepEnv (sendEnv otr.pqrState x.rest) x.ptext.length
          (fun evs' => ∃ g0, w1x_SigGuard r sess otr taken g0 ∧ SignalMessageNewEnv uuidTryParse g0 evs'))
      (fun r sess otr taken evs' =>
        ∃ call, w1x_PkCallGuard r sess otr taken call ∧ PreKeyMsgNewEnv call evs')
      evs := by
  unfold WithStoresEncEnv at h
  unfold WithStoresEncTightEnv
  dsimp only [WithStoresEncSegEnv]
  refine w1c_seqEnv_mono (fun _ hld => hld) ?_ evs h
  intro evs1 hevs1
  rcases hevs1 with hf | hstr | hcur
  · exact Or.inl hf
  · exact Or.inr (Or.inl hstr)
  · refine Or.inr (Or.inr (w1c_seqEnv_mono (fun _ => id) ?_ evs1 hcur))
    intro evs2 hevs2
    rcases hevs2 with hf2 | ⟨r, sess, otr, taken, hScAt, hcurSess, hfrom, hotr⟩
    · exact Or.inl hf2
    · refine Or.inr ⟨r, sess, otr, taken, hScAt, hcurSess, hfrom, ?_⟩
      have hKit : scopeKit r := hScopeImp r hScAt
      unfold FromOtrEnv at hotr
      dsimp only [FromOtrTightEnv]
      rcases hotr with hf3 | ⟨k, hremId, hkey⟩
      · exact Or.inl hf3
      · refine Or.inr ⟨k, hremId, ?_⟩
        unfold FromKeyEnv at hkey
        dsimp only [FromKeySegEnv]
        rcases hkey with ⟨hnone, hseqNone⟩ | ⟨items, hsome, hpkBranch⟩
        · exact Or.inl ⟨hnone, w1c_seqEnv_mono
            (fun _ ho =>
              w1c_otrEncryptCore_imp_step P sendEnv r sess otr taken x.ptext none x.rem x.rest hptext ho)
            (fun _ htail => htail) _ hseqNone⟩
        · refine Or.inr ⟨by simp [hsome], ?_⟩
          rcases hpkBranch with hstr2 | hkybSeq
          · exact Or.inl hstr2
          · refine Or.inr (w1c_seqEnv_mono (fun _ hk => hk)
              (w1c_seqEnv_mono
                (fun _ ho =>
                  w1c_otrEncryptCore_imp_step P sendEnv r sess otr taken x.ptext (some x.loc) x.rem x.rest hptext ho)
                (fun _ hpost => ?_))
              _ hkybSeq)
            unfold PreKeyPostEncryptEnv at hpost
            dsimp only at hpost
            rcases hpost with hf5 | hresMatch
            · exact Or.inl hf5
            · refine Or.inr ?_
              let res := Mut.exec (OutgoingTripleRatchet.encrypt P.C protoSignalCodec
                (pqxdhSpqrModel P).spqr x.ptext
                (serializeAddresses (serviceIdParse uuidTryParse) x.loc x.rem) x.rest) otr
              cases hres1 : res.1 with
              | error _ =>
                rw [hres1] at hresMatch
                exact False.elim hresMatch
              | ok sm =>
                rw [hres1] at hresMatch
                dsimp only at hresMatch
                refine w1c_seqEnv_mono (fun evs_pk hraw => ?_) (fun _ htail => htail) _ hresMatch
                let call : PreKeyMsgNewCall :=
                  { ret := 0#64
                    ver := res.2.sessionVersion
                    regId := sess.localRegistrationId
                    preKeyId := items.preKeyId
                    spk := items.signedPreKeyId
                    kyA := 0#64
                    kyPtr := 0#64
                    kp := pendingKyberPayload sess
                    bkA := 0#64
                    baseKey := items.baseKey
                    ikA := 0#64
                    ik := res.2.localIdentityKey
                    msgA := 0#64
                    msgG := ⟨0#64, 0#64, 0#64, 0#64, 0#64⟩
                    msg := sm }
                have h_pair :
                    Mut.exec (OutgoingTripleRatchet.encrypt P.C protoSignalCodec
                      (pqxdhSpqrModel P).spqr x.ptext
                      (serializeAddresses (serviceIdParse uuidTryParse) x.loc x.rem) x.rest) otr =
                      (.ok sm, res.2) :=
                  Prod.ext hres1 rfl
                have he_ok :
                    execOk (OutgoingTripleRatchet.encrypt P.C protoSignalCodec (pqxdhSpqrModel P).spqr
                      x.ptext (serializeAddresses (serviceIdParse uuidTryParse) x.loc x.rem) x.rest) otr =
                      .ok (sm, res.2) := by
                  unfold execOk
                  rw [h_pair]
                have hsm_le300 : sm.serialized.length ≤ x.ptext.length + 300 :=
                  w1c_otrEncrypt_serialized_len_le P x.ptext _ x.rest otr res.2 sm
                    (fun ad had => Nat.le_of_eq (w1c_serializeAddresses_len_36 had)) he_ok
                have hsm_cap : sm.serialized.length ≤ w1SmSerCap := by
                  unfold w1SmSerCap w1CtLenCap
                  omega
                have hsm_lt32 : sm.serialized.length < 2 ^ 32 := by
                  have : msgCapBytes = 1048576 := by unfold msgCapBytes; decide
                  omega
                have hkp_fn : ∀ kp0, pendingKyberPayload sess = some kp0 →
                    kp0.ciphertext.length ≤ 1569 := by
                  intro kp0 hkp0
                  unfold pendingKyberPayload at hkp0
                  rcases hky : sess.pendingKyberPreKey with _ | ky <;> rw [hky] at hkp0
                  · cases hkp0
                  · simp only [Option.map_some, Option.some.injEq] at hkp0
                    subst hkp0
                    have heq1569 :=
                      w1c_scopeKit_kyber_ciphertext_eq_1569 hKit hcurSess ky.ciphertext
                        (by simp [hky])
                    simpa using Nat.le_of_eq heq1569
                have hkp_cap : kyberPayloadLen call.kp ≤ 1569 := by
                  change kyberPayloadLen (pendingKyberPayload sess) ≤ 1569
                  rcases hkp0 : pendingKyberPayload sess with _ | kp0
                  · simp [kyberPayloadLen]
                  · simpa [kyberPayloadLen] using hkp_fn kp0 hkp0
                have hout_le : call.model.serialized.length ≤ sm.serialized.length + 1717 :=
                  w1c_preKeyMsgNew_serialized_len_le res.2.sessionVersion sess.localRegistrationId
                    items.preKeyId items.signedPreKeyId (pendingKyberPayload sess) items.baseKey
                    res.2.localIdentityKey sm hkp_fn hsm_lt32
                have hout_cap : call.model.serialized.length ≤ w1PkOutCap := by
                  unfold w1PkOutCap
                  omega
                exact ⟨call, ⟨hkp_cap, hsm_cap, hout_cap⟩, hraw⟩

/-! ## Poll and Wire `PhaseCreditSpec` Helpers -/

private theorem w1c_dirPut_opened_credit {dir : DirGhost} (hch : dir.changed = [])
    (name bytes : List (BitVec 8)) :
    PhaseCreditSpec fineCostModel (DirPutEnv dir name bytes) 9789 0 0 192 := by
  have himp : ∀ evs, DirPutEnv dir name bytes evs →
      evs = [] ∨ evs = rustAllocEvents 192 8 := by
    intro evs h
    unfold DirPutEnv DirPutTailEnv at h
    simp only [hch, List.not_mem_nil, IsEmpty.forall_iff, implies_true, ↓reduceIte,
      List.length_nil] at h
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hnil : PhaseCreditSpec fineCostModel (· = ([] : List AllocEvent)) 9789 0 0 192 :=
    (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
  have hgrow : PhaseCreditSpec fineCostModel (· = rustAllocEvents 192 8) 9789 0 0 192 := by
    have ha := PhaseCreditSpec.rustAlloc_small fineCostModel (req := 192) (al := 8)
      (by decide) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)
    have hc : HasFineReallocCredit.smallAllocCost fineCostModel 192 ≤ 9789 := by
      change fineSmallAllocCost 192 ≤ 9789
      decide
    exact ha.mono hc (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
  exact (hnil.or hgrow).of_imp himp

private theorem w1c_dirPutStr_opened_credit {dir : DirGhost} (hch : dir.changed = [])
    {name : List (BitVec 8)} (hname : name.length ≤ 64) (bytes : List (BitVec 8)) :
    PhaseCreditSpec fineCostModel (DirPutStrEnv dir name bytes) 11396 0 0 192 := by
  unfold DirPutStrEnv
  split_ifs with hnil
  · exact (w1c_dirPut_opened_credit hch name bytes).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
  · have hpos : 0 < name.length :=
      Nat.pos_of_ne_zero (fun h0 => hnil (List.eq_nil_of_length_eq_zero h0))
    have ha := PhaseCreditSpec.rustAlloc_small fineCostModel (req := name.length) (al := 1)
      (by decide) hpos (by rw [fineCostModel_smallMaxReq_eq]; omega)
    have hc : HasFineReallocCredit.smallAllocCost fineCostModel name.length ≤ 1607 :=
      fineSmallAllocCost_le_1607_of_le_64 hname
    have hown : PhaseCreditSpec fineCostModel (· = rustAllocEvents name.length 1) 1607 0 0 64 :=
      ha.mono hc (Nat.le_refl 0) (Nat.le_refl 0) hname
    exact (hown.seq (w1c_dirPut_opened_credit hch name bytes)).mono
      (by decide) (by decide) (by decide) (by decide)

private theorem w1c_saveTail_credit {rem : AddrVal} (hrem : rem.name.length ≤ 64)
    (k : IdentityKey) (gr : Except Unit (List (BitVec 8))) :
    PhaseCreditSpec fineCostModel
      (cliIdentityKitSaveTailEnv DirPutStrEnv StoresGhost.opened.identity rem k gr)
      13003 0 0 192 := by
  unfold cliIdentityKitSaveTailEnv
  cases gr with
  | error u =>
    cases u
    exact (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
  | ok _ =>
    have hPk : PhaseCreditSpec fineCostModel PublicKeySerializeEnv 1607 0 0 33 := by
      unfold PublicKeySerializeEnv publicKeySerializeEvents
      have ha := PhaseCreditSpec.rustAlloc_small fineCostModel (req := 33) (al := 1)
        (by decide) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)
      exact ha.mono (fineSmallAllocCost_le_1607_of_le_64 (by decide))
        (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 33)
    have hPut :=
      w1c_dirPutStr_opened_credit (dir := StoresGhost.opened.identity.peers) rfl hrem k.serialize
    exact ((PhaseCreditSpec.freeOnly fineCostModel_modelHyps.freeNonInc).seq (hPk.seq hPut)).mono
      (by decide) (by decide) (by decide) (by decide)

private theorem w1c_w1SigGuard_bounds {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {g : SignalMessageNewGhost}
    (hg : w1x_SigGuard r sess otr taken g) :
    signalMessageNewDeltaCum uuidTryParse g ≤ w1SigCumCap ∧
      signalMessageNewDeltaLive uuidTryParse g ≤ w1SigLiveCap ∧
      signalMessageNewDeltaPeak uuidTryParse g ≤ w1SigPeakCap ∧
      signalMessageNewMaxReq uuidTryParse g ≤ w1SigReqCap := by
  rcases hg with ⟨hct, hpq, hser⟩
  have h36 : 36 ≤ w1SmSerCap := by unfold w1SmSerCap w1CtLenCap msgCapBytes; decide
  have hct_sm : w1CtLenCap ≤ w1SmSerCap := by unfold w1SmSerCap w1CtLenCap msgCapBytes; decide
  have hpq_sm : 4096 ≤ w1SmSerCap := by unfold w1SmSerCap w1CtLenCap msgCapBytes; decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold signalMessageNewDeltaCum w1SigCumCap
    exact Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left 4 hct) (Nat.mul_le_mul_left 4 hpq))
        (Nat.mul_le_mul_left 2 hser))
      (Nat.le_refl _)
  · unfold signalMessageNewDeltaLive w1SigLiveCap
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hct hpq) hser) (Nat.le_refl _)
  · unfold signalMessageNewDeltaPeak w1SigPeakCap
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 2 hct) (Nat.mul_le_mul_left 2 hpq)) hser)
      (Nat.le_refl _)
  · unfold signalMessageNewMaxReq w1SigReqCap
    exact Nat.max_le.mpr
      ⟨Nat.max_le.mpr ⟨h36, Nat.le_trans hct hct_sm⟩,
       Nat.max_le.mpr ⟨Nat.le_trans hpq hpq_sm, hser⟩⟩

private theorem w1c_w1PkCallGuard_bounds {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {call : PreKeyMsgNewCall}
    (hc : w1x_PkCallGuard r sess otr taken call) :
    preKeyMsgNewDeltaCum call ≤ w1PkCumCap ∧
      preKeyMsgNewDeltaLive call ≤ w1PkLiveCap ∧
      preKeyMsgNewDeltaPeak call ≤ w1PkPeakCap ∧
      preKeyMsgNewMaxReq call ≤ w1PkReqCap := by
  rcases hc with ⟨hkp, hsm, hout⟩
  have h33 : 33 ≤ w1PkOutCap := by unfold w1PkOutCap w1SmSerCap w1CtLenCap msgCapBytes; decide
  have hkp_pk : 1569 ≤ w1PkOutCap := by unfold w1PkOutCap w1SmSerCap w1CtLenCap msgCapBytes; decide
  have hsm_pk : w1SmSerCap ≤ w1PkOutCap := by unfold w1PkOutCap w1SmSerCap w1CtLenCap msgCapBytes; decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold preKeyMsgNewDeltaCum preKeyMsgNewRawDeltaCum w1PkCumCap
    exact Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add (Nat.mul_le_mul_left 2 hkp) (Nat.mul_le_mul_left 2 hsm))
        (Nat.mul_le_mul_left 2 hout))
      (Nat.le_refl _)
  · unfold preKeyMsgNewDeltaLive preKeyMsgNewRawDeltaLive w1PkLiveCap
    exact Nat.add_le_add_right hout 8195
  · unfold preKeyMsgNewDeltaPeak preKeyMsgNewRawDeltaPeak w1PkPeakCap
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hkp hsm) hout) (Nat.le_refl _)
  · unfold preKeyMsgNewMaxReq preKeyMsgNewRawMaxReq w1PkReqCap
    exact Nat.max_le.mpr
      ⟨Nat.max_le.mpr ⟨Nat.le_trans hkp hkp_pk, h33⟩,
       Nat.max_le.mpr ⟨Nat.le_trans hsm hsm_pk, hout⟩⟩

private theorem w1c_fromSessionState_pqr_and_taken
    {st : SessionState (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))}
    (h : execOk OutgoingTripleRatchet.fromSessionState st = .ok (otr, taken)) :
    otr.pqrState = st.pqRatchetState ∧ taken = { st with pqRatchetState := [] } := by
  unfold execOk OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState at h
  rcases hsc : st.senderChain with _ | sc
  · simp [hsc] at h
  · simp only [hsc, exec_bind, exec_get, exec_modifyGet] at h
    split_ifs at h
    · simp at h
    · rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at h
      · simp only [hrem, exec_pure, Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine ⟨rfl, ?_⟩
        cases st
        dsimp only at hsc hrem
        subst hsc hrem
        rfl

private theorem w1c_otr_encrypt_pqrState_cases {PQC : Type}
    (C : Crypto) (S : Spqr (List (BitVec 8)) PQC)
    (ptext : List (BitVec 8)) (addrs : Option (List (BitVec 8))) (coins : PQC)
    (otr : OutgoingTripleRatchet (List (BitVec 8))) :
    (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S ptext addrs coins) otr).2.pqrState =
      otr.pqrState ∨
    ∃ newPqr pqrKey pqrMsg,
      S.send otr.pqrState coins = some (newPqr, pqrKey, pqrMsg) ∧
      (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S ptext addrs coins) otr).2.pqrState =
        newPqr := by
  unfold OutgoingTripleRatchet.encrypt
  simp only [exec_bind, exec_get]
  cases S.sendPanics otr.pqrState coins
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases S.send otr.pqrState coins with _ | ⟨newPqr, pqrKey, pqrMsg⟩
    · left; simp
    · dsimp only
      rcases otr.senderChainKey.nextChainKey C.F with _ | _
      · left; simp
      · right; refine ⟨newPqr, pqrKey, pqrMsg, rfl, ?_⟩; simp
  · left; simp

private theorem w1c_otr_encrypt_topStateTight
    {F : ShaCompress} {K : MlKem} (C : Crypto) (hF : C.F = F)
    (ptext : List (BitVec 8)) (addrs : Option (List (BitVec 8))) (coins : List (BitVec 8))
    (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (hTop : TopStateTight F K otr.pqrState) :
    TopStateTight F K
      (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec (spqrV1 F K).spqr
        ptext addrs coins) otr).2.pqrState := by
  subst hF
  rcases w1c_otr_encrypt_pqrState_cases C (spqrV1 C.F K).spqr ptext addrs coins otr with
    heq | ⟨newPqr, _, _, hs, heq⟩
  · rw [heq]; exact hTop
  · rw [heq]; exact topStateTight_spqrV1_send hTop hs

private theorem w1c_storedRecord_cloneDom_and_enc
    {F : ShaCompress} {K : MlKem}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))}
    (hKit : scopeKit r)
    (hcur : r.currentSession = some sess)
    (htaken : taken = { sess.state with pqRatchetState := [] })
    (hTop' : TopStateTight F K otr'.pqrState) :
    (∀ ses, (storedRecord sess otr' taken).currentSession = some ses →
      SessionCloneDom w1PostPqCap ses) ∧
    (encodeRecord (storedRecord sess otr' taken)).length ≤ w1StoreEncCap := by
  subst htaken
  have hpqCap : otr'.pqrState.length ≤ w1PostPqCap := by
    have hle := topStateTight_length_le hTop'
    have heq : spqrStateTightCapBytes = w1PostPqCap := by
      unfold spqrStateTightCapBytes w1PostPqCap spqrSendTightMaxReq
      decide
    rwa [heq] at hle
  have hotr'_lt32 : otr'.pqrState.length < 2 ^ 32 :=
    Nat.lt_of_le_of_lt hpqCap (by unfold w1PostPqCap spqrSendTightMaxReq; decide)
  obtain ⟨⟨hInP, _, hRepr⟩, s0, hs0, hSessP⟩ := hKit
  have hsess_eq : s0 = sess := Option.some.inj (hs0.symm.trans hcur)
  subst hsess_eq
  have hInSess := hInP s0 hcur
  have hReprSess := hRepr s0 hcur
  have hRecIn' :
      RecordInScopeP (storedRecord s0 otr' { s0.state with pqRatchetState := [] }) := by
    intro s' hs'
    simp only [storedRecord, Option.some.injEq] at hs'
    subst hs'
    unfold OutgoingTripleRatchet.applyToSessionState
    exact ⟨hInSess.1, hInSess.2.1, hInSess.2.2⟩
  have hRepr' :
      RecordRepr (storedRecord s0 otr' { s0.state with pqRatchetState := [] }) := by
    intro s' hs'
    simp only [storedRecord, Option.some.injEq] at hs'
    subst hs'
    refine ⟨hReprSess.1, ?_, ?_, hReprSess.2.2.2⟩
    · intro sc' hsc'
      simp only [OutgoingTripleRatchet.applyToSessionState, Option.map_eq_some_iff] at hsc'
      obtain ⟨sc, hsc, rfl⟩ := hsc'
      exact hReprSess.2.1 sc hsc
    · simpa [Session.Wf, OutgoingTripleRatchet.applyToSessionState] using hReprSess.2.2.1
  have hSessP' :
      SessionScopeP
        { s0 with state := otr'.applyToSessionState { s0.state with pqRatchetState := [] } } :=
    ⟨hSessP.1, hSessP.2.1, hSessP.2.2.1, hSessP.2.2.2⟩
  have hScope' :
      scopeKit (storedRecord s0 otr' { s0.state with pqRatchetState := [] }) := by
    refine ⟨⟨hRecIn', ?_, hRepr'⟩, _, rfl, hSessP'⟩
    intro s' hs'
    simp only [storedRecord, Option.some.injEq] at hs'
    subst hs'
    exact hotr'_lt32
  have hPq' : ∀ ses,
      (storedRecord s0 otr' { s0.state with pqRatchetState := [] }).currentSession = some ses →
      ses.state.pqRatchetState.length ≤ w1PostPqCap := by
    intro ses hses
    simp only [storedRecord, Option.some.injEq] at hses
    subst hses
    exact hpqCap
  exact ⟨fun ses hses => sessionCloneDom_of_scopeKit_pq hScope' hses (hPq' ses hses),
    encodeRecord_length_le_of_scopeKit hScope' hPq'⟩

private def w1c_storeSerPeak : Nat :=
  1080975 + (w1PostPqCap + 8195) + (w1StoreEncCap + 8195)

private def w1c_storeSerMaxReq : Nat :=
  max (max 208000 w1PostPqCap) w1StoreEncCap

private theorem w1c_optLargeCost_w1PostPqCap :
    optLargeCost fineCostModel w1PostPqCap = w1PostPqCap + 8195 := by
  unfold optLargeCost
  rw [fineCostModel_smallMaxReq_eq, fineCostModel_largeCost_eq]
  have hnot : ¬ (w1PostPqCap ≤ 135167) := by
    unfold w1PostPqCap spqrSendTightMaxReq
    decide
  simp only [hnot, ↓reduceIte]

private theorem w1c_optLargeCost_w1StoreEncCap :
    optLargeCost fineCostModel w1StoreEncCap = w1StoreEncCap + 8195 := by
  unfold optLargeCost
  rw [fineCostModel_smallMaxReq_eq, fineCostModel_largeCost_eq]
  have hnot : ¬ (w1StoreEncCap ≤ 135167) := by
    unfold w1StoreEncCap w1PostPqCap spqrSendTightMaxReq
    decide
  simp only [hnot, ↓reduceIte]

private theorem w1c_storePoll_credit [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    {rem : AddrVal} (hremName : rem.name.length ≤ 40)
    {r' : SessionRecord (List (BitVec 8))}
    (hDom : ∀ ses, r'.currentSession = some ses → SessionCloneDom w1PostPqCap ses)
    (hEnc : (encodeRecord r').length ≤ w1StoreEncCap) :
    PhaseCreditSpec fineCostModel
      ((w1BinarySessKitPlacedBudget A B F0 peer).storePollEnv
        StoresGhost.opened.sessions rem r')
      (11265 + (8420940 + 9789))
      w1c_storeSerPeak
      w1c_storeSerPeak
      (max 80 (max w1c_storeSerMaxReq 192)) := by
  change PhaseCreditSpec fineCostModel
    (SeqEnv (AddrTextValEnv DecimalEnv rem)
      (SeqEnv (RecordSerializeSeqFreeValidEnv r')
        (DirPutEnv StoresGhost.opened.sessions (addressText rem) (encodeRecord r'))))
    (11265 + (8420940 + 9789))
    w1c_storeSerPeak
    w1c_storeSerPeak
    (max 80 (max w1c_storeSerMaxReq 192))
  have hAddr := addrTextValEnv_decimal_fine_phaseCredit_tight rem hremName
  have hSer : PhaseCreditSpec fineCostModel (RecordSerializeSeqFreeValidEnv r')
      8420940 w1c_storeSerPeak w1c_storeSerPeak w1c_storeSerMaxReq := by
    refine phaseCreditSpec_exists fun g hgv => ?_
    have hValid : ∀ G ses, g.cur = some G → r'.currentSession = some ses →
        SessionGhostValid G ses ∧ SessionCloneDom w1PostPqCap ses := by
      intro G ses hg hr
      unfold RecordGhostValid at hgv
      rw [hg, hr] at hgv
      exact ⟨hgv, hDom ses hr⟩
    have hbase := PhaseCreditSpec.recordSerialize_seqFree_tight fineCostModel_modelHyps g r'
    have hcum := recordSerializeTightCum_fine_le_of_dom hValid
    have hpk := recordSerializePeak_fine_le_of_dom hValid hEnc
    rw [w1c_optLargeCost_w1PostPqCap, w1c_optLargeCost_w1StoreEncCap] at hpk
    have hreq := recordSerializeMaxReq_le_of_dom hValid hEnc
    exact hbase.mono hcum hpk hpk hreq
  have hPut :=
    w1c_dirPut_opened_credit (dir := StoresGhost.opened.sessions) rfl
      (addressText rem) (encodeRecord r')
  exact (hAddr.seq (hSer.seq hPut)).mono
    (Nat.le_refl _)
    (by omega)
    (by omega)
    (Nat.le_refl _)

/-! ## Main Credit Theorem -/

/-- Credit core `PhaseCreditSpec` for the unguarded `@109` `CliEncryptSlotEnv`. -/
theorem w1x_creditCore [LibsignalPlacement] (W : CliHooks) : w1x_creditCore_Stmt W := by
  intro g peerV M A w1R hi hp hGuard hrep hdom
  obtain ⟨hpeerVal, hxPeer, hrem, hptext, hxF⟩ := hdom peerV rfl
  rw [w1c_cliEncryptSlotEnv_fixed_eq_plain hi A w1R.B (w1x_sendEnv109 W) hxF]
  let F0 := runFiles g.i
  let gx := w1EncGhost w1R.x
  have hremName : gx.rem.val.name.length ≤ 40 :=
    (peer_and_rem_name_le_40_of_send hp hpeerVal hrem).2
  have hremBytes : gx.rem.name.bytes.length ≤ 40 := hremName
  have hidKeyLen : gx.rem.val.name.length ≤ 64 := Nat.le_trans hremName (by decide)
  have hTopRem : PeerSpqrStateTight640 W.C.F W.Q.K F0 gx.rem.val := by
    have hGuard' : PeerSpqrStateTight640 W.C.F W.Q.K F0 w1R.peer.val := by
      rwa [hxF, hxPeer] at hGuard
    rwa [hrem]
  have hle1569 : 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    decide
  have hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq fineCostModel :=
    Nat.le_trans (by decide) hle1569
  have hle40 : 40 ≤ HasFineReallocCredit.smallMaxReq fineCostModel :=
    Nat.le_trans (by decide) hle1569
  have hBoxLdEq : (w1SessKitPlaced w1R.repAlloc w1R.B F0 w1R.peer).loadBoxSize = 24 := rfl
  have hBoxStEq : (w1SessKitPlaced w1R.repAlloc w1R.B F0 w1R.peer).storeBoxSize = 32 := rfl
  have hBoxSvEq : (w1IdKitPlaced w1R.repAlloc w1R.B F0 w1R.peer).saveBoxSize = 32 := rfl
  have hBoxTrEq : (w1IdKitPlaced w1R.repAlloc w1R.B F0 w1R.peer).trustBoxSize = 32 := rfl
  have hBoxLd :
      (w1SessKitPlaced w1R.repAlloc w1R.B F0 w1R.peer).loadBoxSize ≤
        HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [hBoxLdEq, fineCostModel_smallMaxReq_eq]; decide
  have hBoxSt :
      (w1SessKitPlaced w1R.repAlloc w1R.B F0 w1R.peer).storeBoxSize ≤
        HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [hBoxStEq]; exact hle32
  have hBoxSv :
      (w1IdKitPlaced w1R.repAlloc w1R.B F0 w1R.peer).saveBoxSize ≤
        HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [hBoxSvEq]; exact hle32
  have hBoxTr :
      (w1IdKitPlaced w1R.repAlloc w1R.B F0 w1R.peer).trustBoxSize ≤
        HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [hBoxTrEq]; exact hle32
  have hNameCum : ∀ n, 0 < n → n ≤ 40 →
      HasFineReallocCredit.smallAllocCost fineCostModel n ≤ 738 := by
    intro n _ hn40
    have h738 := rustAllocTightCum_fine_le_738 (req := n) (by omega)
    unfold rustAllocTightCum at h738
    rw [fineCostModel_smallMaxReq_eq] at h738
    have hsm : n ≤ 135167 := by omega
    simpa [hsm] using h738
  have hLoad :
      PhaseCreditSpec fineCostModel
        ((w1BinarySessKitPlacedBudget w1R.repAlloc w1R.B F0 w1R.peer).loadPollEnv
          StoresGhost.opened.sessions gx.rem.val)
        (defaultLoadPollTightDeltaCum (max 0 sessionCapBytes) deserCancelFineCum)
        (fineReadFileLive (max 0 sessionCapBytes) + deserCancelFineLive)
        (max (fineReadFilePeak (max 0 sessionCapBytes))
          (fineReadFileLive (max 0 sessionCapBytes) + deserCancelFinePeak))
        (max (max 256 (fineReadFileMaxReq (max 0 sessionCapBytes))) deserCancelFineMaxReq) :=
    defaultLoadPollEnv_dcan_byBytes_fine_phaseCredit_tight
      dirDomainCaps_opened_sess (by decide) hremName
      (fun bs hbs => cliIo_rd_ok_length_le_sessionCapBytes F0 _ bs hbs)
      (by unfold sessionCapBytes; decide)
  have hCost24 : HasFineReallocCredit.smallAllocCost fineCostModel 24 = 488 := by
    change fineSmallAllocCost 24 = 488; decide
  have hCost32 : HasFineReallocCredit.smallAllocCost fineCostModel 32 = 738 := by
    change fineSmallAllocCost 32 = 738; decide
  have hCost1569 : HasFineReallocCredit.smallAllocCost fineCostModel 1569 = 2792 := by
    change fineSmallAllocCost 1569 = 2792; decide
  have hOtr : ∀ r sess otr taken,
      (w1SessKitPlaced w1R.repAlloc w1R.B F0 w1R.peer).ScopeAt scopeKit
        StoresGhost.opened.sessions gx.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseCreditSpec fineCostModel
        (OtrEncryptStepEnv (w1x_sendEnv109 W otr.pqrState gx.rest) gx.ptext.length
          (fun evs => ∃ g0, w1x_SigGuard r sess otr taken g0 ∧ SignalMessageNewEnv uuidTryParse g0 evs))
        (spqrSendTightDeltaCum + 738 + 143484 + w1SigCumCap)
        (spqrSendTightDeltaLive + (w1CtLenCap + 8195) + w1SigLiveCap)
        (max spqrSendTightDeltaPeak (spqrSendTightDeltaLive + (w1CtLenCap + 8195) + w1SigPeakCap))
        (max spqrSendTightMaxReq (max 32 (max w1CtLenCap w1SigReqCap))) := by
    intro r sess otr taken hScAt hcur hfrom
    obtain ⟨hpqr, _⟩ := w1c_fromSessionState_pqr_and_taken hfrom
    have hTopOtr : TopStateTight W.C.F W.Q.K otr.pqrState :=
      peerSpqrStateTight640_of_cliSessionStoreSpecPlaced hScAt hcur hpqr hTopRem
    have hSend := ckx2_spqrSendCoins109_phaseCredit_of_stateTight640 (rest := gx.rest) (Or.inr hTopOtr)
    have hSigEx :
        PhaseCreditSpec fineCostModel
          (fun evs => ∃ g0, w1x_SigGuard r sess otr taken g0 ∧ SignalMessageNewEnv uuidTryParse g0 evs)
          w1SigCumCap w1SigLiveCap w1SigPeakCap w1SigReqCap :=
      phaseCreditSpec_exists fun g0 hg0 =>
        let ⟨hc, hl, hp0, hr⟩ := w1c_w1SigGuard_bounds hg0
        (signalMessageNew_phaseCredit fineCostModel_modelHyps uuidTryParse g0).mono hc hl hp0 hr
    have hStep := otrEncryptStep_creditSpec_tight fineCostModel_modelHyps hle32
      (ptextLen := gx.ptext.length) hSend hSigEx
    set ctLen := (gx.ptext.length / 16 + 1) * 16
    have hct_le : ctLen ≤ w1CtLenCap := by
      dsimp only [ctLen]
      unfold w1CtLenCap
      have hdiv : gx.ptext.length / 16 ≤ msgCapBytes / 16 := Nat.div_le_div_right hptext
      omega
    have hsm143 := tryCloneSmallDelta_fineCostModel_le_143484 ctLen
    have hlg := tryCloneLargeDelta_fineCostModel_le_add hct_le
    exact hStep.mono
      (by rw [hCost32]; omega)
      (by omega)
      (Nat.max_le.mpr ⟨Nat.le_max_left _ _,
        Nat.le_trans (by omega) (Nat.le_max_right _ _)⟩)
      (Nat.max_le.mpr ⟨Nat.le_max_left _ _,
        Nat.le_trans
          (Nat.max_le.mpr ⟨Nat.le_max_left 32 _,
            Nat.le_trans
              (Nat.max_le.mpr ⟨Nat.le_trans hct_le (Nat.le_max_left _ _), Nat.le_max_right _ _⟩)
              (Nat.le_max_right 32 _)⟩)
          (Nat.le_max_right _ _)⟩)
  have hPk : ∀ r sess otr taken,
      (w1SessKitPlaced w1R.repAlloc w1R.B F0 w1R.peer).ScopeAt scopeKit
        StoresGhost.opened.sessions gx.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseCreditSpec fineCostModel
        (fun evs => ∃ call, w1x_PkCallGuard r sess otr taken call ∧ PreKeyMsgNewEnv call evs)
        w1PkCumCap w1PkLiveCap w1PkPeakCap w1PkReqCap := by
    intro r sess otr taken _ _ _
    exact phaseCreditSpec_exists fun call hcall =>
      let ⟨hc, hl, hp0, hr⟩ := w1c_w1PkCallGuard_bounds hcall
      (preKeyMsgNew_phaseCredit fineCostModel_modelHyps call).mono hc hl hp0 hr
  have hTrust : ∀ k : IdentityKey,
      PhaseCreditSpec fineCostModel
        ((w1BinaryIdKitPlacedBudget w1R.repAlloc w1R.B F0 w1R.peer).trustPollEnv
          StoresGhost.opened.identity gx.rem.val k .sending)
        (21185 + max 738 (fineReadFileCum (max 0 sessionCapBytes)))
        (fineReadFileLive (max 0 sessionCapBytes))
        (fineReadFilePeak (max 0 sessionCapBytes))
        (max 256 (fineReadFileMaxReq (max 0 sessionCapBytes))) := by
    intro k
    change PhaseCreditSpec fineCostModel
      (cliIdentityKitTrustPollEnv
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        F0 StoresGhost.opened.identity gx.rem.val k .sending) _ _ _ _
    unfold cliIdentityKitTrustPollEnv
    exact seq_freeOnly_phaseCredit fineCostModel_modelHyps.freeNonInc
      (dirGetEnv_path_readFile_fine_phaseCredit_tight cliIo.rd F0
        StoresGhost.opened.identity.peers gx.rem.val.name
        (dirDomainCaps_opened_peers.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0)) hidKeyLen
        (fun bs hbs => cliIo_rd_ok_length_le_sessionCapBytes F0 _ bs hbs))
  have hSave : ∀ k : IdentityKey,
      PhaseCreditSpec fineCostModel
        ((w1BinaryIdKitPlacedBudget w1R.repAlloc w1R.B F0 w1R.peer).savePollEnv
          ((w1IdKitPlaced w1R.repAlloc w1R.B F0 w1R.peer).trustUpdate StoresGhost.opened.identity
            gx.rem.val k .sending (.ok true))
          gx.rem.val k)
        ((21185 + max 738 (fineReadFileCum (max 0 sessionCapBytes))) + 13003)
        (fineReadFileLive (max 0 sessionCapBytes))
        (fineReadFilePeak (max 0 sessionCapBytes))
        (max (max 256 (fineReadFileMaxReq (max 0 sessionCapBytes))) 192) := by
    intro k
    change PhaseCreditSpec fineCostModel
      (cliIdentityKitSavePollEnv cliIo.rd
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        DirPutStrEnv F0 StoresGhost.opened.identity gx.rem.val k) _ _ _ _
    unfold cliIdentityKitSavePollEnv
    have hGet := dirGetEnv_path_readFile_fine_phaseCredit_tight cliIo.rd F0
      StoresGhost.opened.identity.peers gx.rem.val.name
      (dirDomainCaps_opened_peers.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0)) hidKeyLen
      (fun bs hbs => cliIo_rd_ok_length_le_sessionCapBytes F0 _ bs hbs)
    have hTail := w1c_saveTail_credit hidKeyLen k
      (StoresGhost.opened.identity.peers.get cliIo.rd F0 gx.rem.val.name)
    exact (hGet.seq hTail).mono
      (Nat.le_refl _)
      (Nat.le_of_eq (Nat.add_zero _))
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_trans (Nat.le_of_eq (Nat.add_zero _))
        (by decide : fineReadFileLive (max 0 sessionCapBytes) ≤
          fineReadFilePeak (max 0 sessionCapBytes))⟩)
      (Nat.le_refl _)
  have hStoreNone : ∀ r sess otr taken (_k : IdentityKey),
      (w1SessKitPlaced w1R.repAlloc w1R.B F0 w1R.peer).ScopeAt scopeKit
        StoresGhost.opened.sessions gx.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some _k →
      PhaseCreditSpec fineCostModel
        ((w1BinarySessKitPlacedBudget w1R.repAlloc w1R.B F0 w1R.peer).storePollEnv
          StoresGhost.opened.sessions gx.rem.val
          (storedRecord sess (otrAfterNone W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) gx otr) taken))
        (11265 + (8420940 + 9789))
        w1c_storeSerPeak
        w1c_storeSerPeak
        (max 80 (max w1c_storeSerMaxReq 192)) := by
    intro r sess otr taken _ hScAt hcur hfrom _
    obtain ⟨hpqr, htaken⟩ := w1c_fromSessionState_pqr_and_taken hfrom
    have hTopOtr : TopStateTight W.C.F W.Q.K otr.pqrState :=
      peerSpqrStateTight640_of_cliSessionStoreSpecPlaced hScAt hcur hpqr hTopRem
    have hTop' :
        TopStateTight W.C.F W.Q.K
          (otrAfterNone W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) gx otr).pqrState :=
      w1c_otr_encrypt_topStateTight W.C rfl gx.ptext none gx.rest otr hTopOtr
    obtain ⟨hDom, hEnc⟩ := w1c_storedRecord_cloneDom_and_enc hScAt.1 hcur htaken hTop'
    exact w1c_storePoll_credit w1R.repAlloc w1R.B F0 w1R.peer hremName hDom hEnc
  have hStoreSome : ∀ r sess otr taken (_k : IdentityKey),
      (w1SessKitPlaced w1R.repAlloc w1R.B F0 w1R.peer).ScopeAt scopeKit
        StoresGhost.opened.sessions gx.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some _k →
      PhaseCreditSpec fineCostModel
        ((w1BinarySessKitPlacedBudget w1R.repAlloc w1R.B F0 w1R.peer).storePollEnv
          StoresGhost.opened.sessions gx.rem.val
          (storedRecord sess (otrAfterSome W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse gx otr) taken))
        (11265 + (8420940 + 9789))
        w1c_storeSerPeak
        w1c_storeSerPeak
        (max 80 (max w1c_storeSerMaxReq 192)) := by
    intro r sess otr taken _ hScAt hcur hfrom _
    obtain ⟨hpqr, htaken⟩ := w1c_fromSessionState_pqr_and_taken hfrom
    have hTopOtr : TopStateTight W.C.F W.Q.K otr.pqrState :=
      peerSpqrStateTight640_of_cliSessionStoreSpecPlaced hScAt hcur hpqr hTopRem
    have hTop' :
        TopStateTight W.C.F W.Q.K
          (otrAfterSome W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse gx otr).pqrState :=
      w1c_otr_encrypt_topStateTight W.C rfl gx.ptext _ gx.rest otr hTopOtr
    obtain ⟨hDom, hEnc⟩ := w1c_storedRecord_cloneDom_and_enc hScAt.1 hcur htaken hTop'
    exact w1c_storePoll_credit w1R.repAlloc w1R.B F0 w1R.peer hremName hDom hEnc
  have hTight :=
    withStoresEncTight_creditSpec_tight fineCostModel_modelHyps scopeKit
      (w1SessKitPlaced w1R.repAlloc w1R.B F0 w1R.peer)
      (w1BinarySessKitPlacedBudget w1R.repAlloc w1R.B F0 w1R.peer)
      StoresGhost.opened.sessions
      (w1IdKitPlaced w1R.repAlloc w1R.B F0 w1R.peer)
      (w1BinaryIdKitPlacedBudget w1R.repAlloc w1R.B F0 w1R.peer)
      StoresGhost.opened.identity
      W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse gx
      (nameCap := 40) (nameCum := 738) (kyberLen := 1569)
      hle32 hBoxLd hBoxSt hBoxSv hBoxTr hremBytes hle40 hNameCum hle1569
      hLoad
      (fun _ _ _ _ hsc hcur _ => w1c_scopeKit_kyber_ciphertext_eq_1569 hsc.1 hcur)
      hOtr hOtr hPk
      (fun _ _ _ _ k _ _ _ _ => hTrust k)
      (fun _ _ _ _ k _ _ _ _ => hSave k)
      hStoreNone hStoreSome
  dsimp only at hTight
  rw [hBoxLdEq, hBoxStEq, hBoxSvEq, hBoxTrEq, hCost24, hCost32, hCost1569] at hTight
  have hTightCapped :
      PhaseCreditSpec fineCostModel (W1X_WithStoresEncTight W g w1R)
        w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq :=
    hTight.mono (by decide) (by decide) (by decide) (by decide)
  unfold CliEncryptSlotEnv
  rw [hxF, hxPeer, ← hrep]
  exact hTightCapped.of_imp
    (fun _ hevs =>
      w1c_withStoresEnc_imp_tight
        (w1SessKitPlaced w1R.repAlloc w1R.B F0 w1R.peer)
        (w1BinarySessKitPlacedBudget w1R.repAlloc w1R.B F0 w1R.peer)
        StoresGhost.opened.sessions
        (w1IdKitPlaced w1R.repAlloc w1R.B F0 w1R.peer)
        (w1BinaryIdKitPlacedBudget w1R.repAlloc w1R.B F0 w1R.peer)
        StoresGhost.opened.identity
        ⟨W.C, W.Q⟩ (w1x_sendEnv109 W) gx
        (fun _ hsc => hsc.1) hptext hevs)

end LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactC
