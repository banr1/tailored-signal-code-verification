/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5aReach
import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm
import LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
import LibsignalBinary.Proofs.PeakBudget.CliKitW2RecvExactAuxR2Race
import LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapFixed
import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired
import LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
import LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf
import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
import LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvCPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsTightCliInst
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget

/-!
# Untyped D3 `MainEntryBudgetFitsCapOf` Closure

**Checked by Lean.**

Proves `hole_g5a_untyped_fitsCap_closed`, establishing `MainEntryBudgetFitsCapOf` at
`binaryKitRunSlotEnvsExact` and `DecPkD3UntypedEnvOf` under `pqD3ScopedRun`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinG5A

open Arm64.Obj (Image)
open Arm64.Process (bytesOfString)
open CryptoGames (Party)
open CryptoGames.LibsignalSession (Crypto IdentityKey Mut SessionState ShaCompress SignalMessage TripleRatchet)
open CryptoGames.LibsignalSessionApi
  (PreKeySignalMessage SessionRecord StoreCall fullTrace messageDecryptSignal_trace_prefix)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E
  (PEParams UnreachedPqxdhPrimitives partyAddressName pqxdhSessionParams pqxdhSpqrModel
   pqxdhSpqrSession recvPrekeyState wirePrekey wireWhisper)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal serializeAddrVals)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchetRepr (coinsOf serviceIdParse uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession
  (Address.text CliHooks CliPqxdhInputs Cmd Inputs PqParty baseKeysFile identityFile
   oneTimeKyberPreKeyFile oneTimePreKeyFile partyAddress pqRecvInputs sessionFile stdinCapBytes)
open CryptoVerification.SignalSession.Cli
  (DirGhost IdGhost KyberGhost StoresGhost addressText baseKeysName decimalText keyName pathOf
   removePreKey utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV CallV DirWrOk RunCall StoreCallPeerPlaced StoresWrOk addrParse cliIo cliRunBudgets
   cliRunBudgets_placed inputOf keyName_length messageDecryptSignal_calls_peer_placed namedWrites
   namedWrites_ascii okPeerPath parseArgs pathStr saveUpd_own saveUpd_peers_path)
open CryptoVerification.SignalSession.Cli.RunCompose
  (RunSem SlotAns finish readBundleV runAns runFiles runRel)
open CryptoVerification.SignalSession.Cli.RunProofs
  (SessMatchesPm cliAnswers cliFinal cliStep decPkDef decPkDefD2c
   decPkDefD2c_eq_decPkDef_of_match decPkDefD2c_eq_decPkDef_of_noCurrent
   decPkDefD2c_eq_decPkDef_of_untrusted decPkDefD2c_namedWrites_sub decSigDef decSigKey
   encDef initDef initParty pkRecvCoins pkStoreKeys pkToE?)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
  (cliKitStk cliPollIdKitPlaced cliPollSessKitPlaced)
open CryptoVerification.SignalSession.Cli.RunRefine
  (addrValE parseArgs_recv runAns_pqRecvBad runAns_pqRecvPrekey_eq runAns_pqRecvWhisper_eq)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (loadRec scopeIn scopeKit)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FitsEnv RustCliAllocBudget)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith (cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactAsm
  (ckx2_w1EncExact_groupSpec ckx2_w1EncExact_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1W2ExactSlotSpecR2
  (ckx2_DecodeStateTightEnv ckx2_DecodeStateTightEnvOf
   ckx2_EkSentCt1ReceivedRecvCt2ChunkEnv' ckx2_RecvCt2ChunkTailEnv'
   ckx2_RecvEkChunkSendCt2TailEnv' ckx2_SpqrRecvC07C09aBytesEnvOf
   ckx2_SpqrRecvC07C09aTightLinkedEnvOf ckx2_SpqrRecvC07C09aTightLinkedEnvRecvOf
   ckx2_SpqrSendCoinsOfDecodeFromPbBytesEnv ckx2_StatesRecvEnv' ckx2_StatesRecvProtoEnv'
   ckx2_TryDecryptCliLinkedEnvOf ckx2_TryDecryptCliLinkedLoopEnvOf
   ckx2_cliDecryptSignalBinaryKitSlotEnvExact ckx2_cliEncryptBinaryKitSlotEnvExact
   ckx2_tryDecryptCmkSeg4EnvOf ckx2_tryDecryptCmkStepEnvOf)
open LibsignalBinary.Proofs.PeakBudget.CliKitW2RecvExactAuxR2Race
  (ckx2_w2DecSigExact_groupSpec ckx2_w2DecSigExact_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv RealCliMainBinaryEnvOf cliMainArmEnvs cliRunCalleesEnvs preEnv_sub_r0BinaryEnv
   r3bRecvPEnv_sub_r3bEnv runEnv_to_cliRunBinaryEnv_of_slots)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.D3MainEntryBudgetFitsCapFixed
  (boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo mkD3BinaryKitCalleeEnvsWithDecPk
   realCliMainD3RecvWithDecPk_fitsEnv_cliBudgetLimits)
open LibsignalBinary.Proofs.PeakBudget.MainEntryBudgetFitsCapReal
  (mainEntryBudgetFitsCapOf_domScopedRun_cliBudgetLimits_of_kitEnvFits pqRunAns_namedWrites_bounds
   stdin_le_msgCapBytes_of_pqInputs_and_inputOf stdin_le_msgCapBytes_of_pqRecvInputs_and_inputOf)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (dirGetEnv_fixed_eq_of_not_overCap not_overCapFile_runFiles_identities
   not_overCapFile_runFiles_kyberLastResort_keyName not_overCapFile_runFiles_kyberOneTime
   not_overCapFile_runFiles_oneTime not_overCapFile_runFiles_own_address
   not_overCapFile_runFiles_own_ikp not_overCapFile_runFiles_sessions
   not_overCapFile_runFiles_signed realCliInitBinarySlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
  (cliPqxdhInputs_pqRecvInputs_nil d3RecvW4ExtCum d3RecvW4ExtGrpS d3RecvW4ExtLive
   d3RecvW4ExtMaxReq d3RecvW4ExtPeak)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec (StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired
  (EkSentCt1ReceivedRecvCt2ChunkEnv' RecvCt2ChunkTailEnv' RecvEkChunkSendCt2TailEnv'
   StatesRecvEnv' StatesRecvProtoEnv')
open LibsignalBinary.Proofs.PeakBudget.SpqrTightLeafBridges
  (tlb_DecodeStateTightEnv tlb_DecodeStateTightEnvOf)
open LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf
  (SpqrRecvC07C09aBytesEnvOf SpqrRecvC07C09aTightLinkedEnvOf SpqrRecvC07C09aTightLinkedEnvRecvOf
   TryDecryptCliLinkedEnvOf TryDecryptCliLinkedLoopEnvOf tryDecryptCmkSeg4EnvOf
   tryDecryptCmkStepEnvOf)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot (w4RecvPrekeyRealGrpS)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (w4RecvPrekeyReal1MiB_i_Cum w4RecvPrekeyReal1MiB_i_Live w4RecvPrekeyReal1MiB_i_MaxReq
   w4RecvPrekeyReal1MiB_i_Peak)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (TrustStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (LoadStepEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvAPlacedBudget
  (DecPkD3UntypedEnv DecPkD3UntypedEnvOf PqxdhAcceptBadKemErrEnv StageP2BadKemRejectEnv
   StageP2UntypedRejectEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.Budget.D3BadKemEnvCPlacedBudget
  (decPkD3UntypedCum decPkD3UntypedEnv_r3b_singleSlotFineSpec decPkD3UntypedGrpS
   decPkD3UntypedLive decPkD3UntypedMaxReq decPkD3UntypedPeak decPkD3Untyped_caps_le_1MiB)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3ParseRejectF3
  (CliPqOrD3RecvInputs defaultExtrasF3 pqD3ScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.D3.F3.D3UntypedElfF3 (cliRunSemD3)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitBudgetEnv cliIdentityKitDefaultBudgetEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (cliSessionKitBudgetEnv cliSessionKitDefaultBudgetEnv cliSessionKitLoadPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainEntryBudgetFitsInst
  (MainEntryBudgetFitsCapOf domScopedRun)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.MainOkCliExtB2NeedLocksInst (cliRunSemD2c_placed)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R0ProofPlacedBudget (PreEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget (r3bDecPkGhost)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunOkPlacedBudget (RunEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (RunSlotEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.StagesOverCliPlacedBudget
  (cliPollSelfBudgetEnv cliPollSelfKpPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureStageDefsPlacedBudget
  (StageP1OkEnv StageP1UntrustedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
  (CliDpPollUntrustedEnv cliIdStoreFullBudgetEnv cliPollIdBudgetEnv cliPollSessBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1KitsPlacedBudgetAux
  (cliPollKpkFullBudgetEnv cliPollKpkGetPollEnv cliPollPkFullBudgetEnv cliPollPkGetPollEnv
   cliPollSpkFullBudgetEnv cliPollSpkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W8bAssemblyPlacedBudget
  (PksmTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpqrSendCoinsTightCliInst
  (hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget
  (CliKpkGetPollEnv KpkPassEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget (CliPkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (CliSpkGetPollEnv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomG5aReach
  (g5ar_hole_g5a_of_slots)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomHole3Cut
  (binaryKitRunSlotEnvsExact cliDecryptSignalBinaryKitSlotEnvExact cliEncryptBinaryKitSlotEnvExact)

private theorem tjg5a_decPkD3UntypedEnvOf_fixed_sub_plain
    [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks)
    (call : RunCall) (meV peerV : AddrV) (pm : PreKeySignalMessage)
    (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ call.i)
    (evs : List AllocEvent)
    (hevs : DecPkD3UntypedEnvOf (A := A) cliRunBudgets_placed
      (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv
      (r3bDecPkGhost call meV peerV pm) evs) :
    DecPkD3UntypedEnv A W cliRunBudgets (r3bDecPkGhost call meV peerV pm) evs := by
  let g := r3bDecPkGhost call meV peerV pm
  have ⟨i₀, hi₀, hF⟩ : ∃ i₀, CliPqxdhInputs ⟨W.C, W.Q⟩ i₀ ∧ g.F = runFiles i₀ := by
    rcases hi with hi_pq | ⟨st, _ct, rc, hwf, hgi⟩
    · exact ⟨call.i, hi_pq, rfl⟩
    · refine ⟨pqRecvInputs ⟨W.C, W.Q⟩ st [] rc, cliPqxdhInputs_pqRecvInputs_nil hwf rc, ?_⟩
      show runFiles call.i = _
      rw [hgi]
      rfl
  let B := cliRunBudgets
  let RF := ReadFileRuleEnvFixed cliIo.rd
  let RP := ReadFileRuleEnv cliIo.rd
  have hsess :
      LoadStepEnv (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B))
        (cliPollSessBudgetEnv A g.F g.peer B RF SessDeserializeCancelEnv)
        StoresGhost.opened.sessions g.peer.val =
      LoadStepEnv (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B))
        (cliPollSessBudgetEnv A g.F g.peer B RP SessDeserializeCancelEnv)
        StoresGhost.opened.sessions g.peer.val := by
    unfold LoadStepEnv cliPollSessBudgetEnv cliSessionKitDefaultBudgetEnv cliSessionKitBudgetEnv
      cliSessionKitLoadPollEnv
    dsimp only [RF, RP]
    rw [hF, dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_sessions hi₀ _)]
  have htrust :
      TrustStepEnv (cliPollIdKitPlaced A g.F g.peer (cliKitStk B))
        (cliPollIdBudgetEnv A g.F g.peer B RF)
        StoresGhost.opened.identity g.peer.val g.msg.identityKey .receiving =
      TrustStepEnv (cliPollIdKitPlaced A g.F g.peer (cliKitStk B))
        (cliPollIdBudgetEnv A g.F g.peer B RP)
        StoresGhost.opened.identity g.peer.val g.msg.identityKey .receiving := by
    unfold TrustStepEnv cliPollIdBudgetEnv cliIdStoreFullBudgetEnv cliIdentityKitDefaultBudgetEnv
      cliIdentityKitBudgetEnv cliIdentityKitTrustPollEnv
    dsimp only [RF, RP]
    rw [hF, dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_identities hi₀ _)]
  have hspk : ∀ spkId,
      (cliPollSpkFullBudgetEnv A g.F spkId (cliKitStk B) RF).getPollEnv
        StoresGhost.opened.signed spkId =
      (cliPollSpkFullBudgetEnv A g.F spkId (cliKitStk B) RP).getPollEnv
        StoresGhost.opened.signed spkId := by
    intro spkId
    unfold cliPollSpkFullBudgetEnv cliPollSpkGetPollEnv CliSpkGetPollEnv
    dsimp only [RF, RP]
    rw [hF, dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_signed hi₀ _)]
  have hkpk : ∀ kpkId spkId kbk,
      (cliPollKpkFullBudgetEnv A g.F kpkId spkId kbk (cliKitStk B) RF).getPollEnv
        StoresGhost.opened.kyber kpkId =
      (cliPollKpkFullBudgetEnv A g.F kpkId spkId kbk (cliKitStk B) RP).getPollEnv
        StoresGhost.opened.kyber kpkId := by
    intro kpkId spkId kbk
    unfold cliPollKpkFullBudgetEnv cliPollKpkGetPollEnv CliKpkGetPollEnv KpkPassEnv
    dsimp only [RF, RP]
    rw [hF,
      dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_kyberOneTime hi₀ _),
      dirGetEnv_fixed_eq_of_not_overCap
        (not_overCapFile_runFiles_kyberLastResort_keyName hi₀ kpkId)]
  have hpk : ∀ opkWord,
      (cliPollPkFullBudgetEnv A g.F opkWord (cliKitStk B) RF).getPollEnv
        StoresGhost.opened.oneTime =
      (cliPollPkFullBudgetEnv A g.F opkWord (cliKitStk B) RP).getPollEnv
        StoresGhost.opened.oneTime := by
    intro opkWord; funext id
    unfold cliPollPkFullBudgetEnv cliPollPkGetPollEnv CliPkGetPollEnv
    dsimp only [RF, RP]
    rw [hF, dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_oneTime hi₀ _)]
  have hselfKp :
      (cliPollSelfBudgetEnv A g.F g.peer (cliKitStk B) RF).kpPollEnv StoresGhost.opened.identity =
      (cliPollSelfBudgetEnv A g.F g.peer (cliKitStk B) RP).kpPollEnv StoresGhost.opened.identity := by
    unfold cliPollSelfBudgetEnv cliPollSelfKpPollEnv
    dsimp only [RF, RP]
    rw [hF, dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_own_ikp hi₀)]
  have hp2 : ∀ opt,
      StageP2UntypedRejectEnv (A := A) B RF PqxdhAcceptBadKemErrEnv g opt =
      StageP2UntypedRejectEnv (A := A) B RP PqxdhAcceptBadKemErrEnv g opt := by
    intro opt; funext e
    unfold StageP2UntypedRejectEnv StageP2BadKemRejectEnv
    dsimp only [RF, RP]
    rw [hspk, hkpk, hpk, hselfKp]
  have hp1u :
      CliDpPollUntrustedEnv (A := A) B RF SessDeserializeCancelEnv g =
      CliDpPollUntrustedEnv (A := A) B RP SessDeserializeCancelEnv g := by
    funext e
    unfold CliDpPollUntrustedEnv StageP1UntrustedEnv
    dsimp only [RF, RP]
    rw [hsess, htrust]
  have hp1ok :
      StageP1OkEnv (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B))
        (cliPollSessBudgetEnv A g.F g.peer B RF SessDeserializeCancelEnv)
        StoresGhost.opened.sessions
        (cliPollIdKitPlaced A g.F g.peer (cliKitStk B))
        (cliPollIdBudgetEnv A g.F g.peer B RF)
        StoresGhost.opened.identity g.peer.val g.msg.identityKey =
      StageP1OkEnv (cliPollSessKitPlaced A g.F scopeKit g.peer (cliKitStk B))
        (cliPollSessBudgetEnv A g.F g.peer B RP SessDeserializeCancelEnv)
        StoresGhost.opened.sessions
        (cliPollIdKitPlaced A g.F g.peer (cliKitStk B))
        (cliPollIdBudgetEnv A g.F g.peer B RP)
        StoresGhost.opened.identity g.peer.val g.msg.identityKey := by
    funext e
    unfold StageP1OkEnv
    dsimp only [RF, RP]
    rw [hsess, htrust]
  change DecPkD3UntypedEnvOf (A := A) B RF SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv g evs at hevs
  change DecPkD3UntypedEnvOf (A := A) B RP SessDeserializeCancelEnv PqxdhAcceptBadKemErrEnv g evs
  rcases hevs with hu | ⟨opt, hseq⟩
  · exact Or.inl (hp1u ▸ hu)
  · rw [hp1ok, hp2 opt] at hseq
    exact Or.inr ⟨opt, hseq⟩

private theorem tjg5a_exists_cliPqxdhInputs_same_argv_runFiles
    {P : PEParams}
    {g : RunCall}
    (hi : CliPqOrD3RecvInputs P g.i) :
    ∃ g₀ : RunCall,
      CliPqxdhInputs P g₀.i ∧ g₀.c = g.c ∧
        g₀.i.argv = g.i.argv ∧
        runFiles g₀.i = runFiles g.i := by
  rcases hi with hi_pq | ⟨st, _ct, rc, hwf, hgi⟩
  · exact ⟨g, hi_pq, rfl, rfl, rfl⟩
  · exact ⟨{ g with i := pqRecvInputs P st [] rc },
      cliPqxdhInputs_pqRecvInputs_nil hwf rc,
      rfl, by rw [hgi]; rfl, by rw [hgi]; rfl⟩

private theorem tjg5a_byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private def tjg5a_kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem tjg5a_utf8_eq (s : String) : utf8 s = tjg5a_kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, tjg5a_kutf8, List.utf8Encode, tjg5a_byteArray_toList_eq_data]

private theorem tjg5a_utf8_append (a b : String) : utf8 (a ++ b) = utf8 a ++ utf8 b := by
  rw [tjg5a_utf8_eq, tjg5a_utf8_eq, tjg5a_utf8_eq]
  simp [tjg5a_kutf8, String.toList_append, List.flatMap_append]

private theorem tjg5a_toString_one : toString (1 : Nat) = "1" := by
  have ht1 : toString (1 : Nat) = String.singleton (Nat.digitChar 1) := Nat.repr_of_lt (by omega)
  have hd1 : Nat.digitChar 1 = '1' := Nat.digitChar_eq_one.mpr rfl
  exact String.toList_inj.mp (by rw [ht1, hd1, String.toList_singleton]; rfl)

private theorem tjg5a_sessionFile_partyAddress_eq (P : Party) :
    sessionFile (partyAddress P) = "sessions/" ++ partyAddressName P ++ "." ++ "1" := by
  simp only [sessionFile, partyAddress, Address.text, tjg5a_toString_one, String.append_assoc]

private theorem tjg5a_okPeerPath_id (P : Party) :
    okPeerPath P (pathOf (utf8 "identities") (addrValE P).name) := by
  have hpath : pathOf (utf8 "identities") (addrValE P).name =
      utf8 (identityFile (partyAddressName P)) := by
    have hne : utf8 "identities" ≠ [] := by rw [tjg5a_utf8_eq]; decide
    simp only [pathOf, hne, ↓reduceIte, addrValE, identityFile]
    rw [← tjg5a_utf8_append, ← tjg5a_utf8_append]
    rfl
  rw [hpath]
  refine ⟨?_, .inl ?_⟩
  · rw [tjg5a_utf8_eq]
    intro b hb
    have hall :
        (tjg5a_kutf8 (identityFile (partyAddressName P))).all
          (fun x => decide (x.toNat < 128)) = true := by
      cases P <;> decide
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · unfold pathStr
    rw [tjg5a_utf8_eq]
    cases P <;> decide

private theorem tjg5a_okPeerPath_sess (P : Party) :
    okPeerPath P (pathOf (utf8 "sessions") (addressText (addrValE P))) := by
  have hpath : pathOf (utf8 "sessions") (addressText (addrValE P)) =
      utf8 (sessionFile (partyAddress P)) := by
    have hne : utf8 "sessions" ≠ [] := by rw [tjg5a_utf8_eq]; decide
    have had : addressText (addrValE P) = utf8 (partyAddress P).text := by
      have h1 : (1#8 : BitVec 8).toNat = 1 := rfl
      simp only [addressText, addrValE, decimalText, h1, Address.text, partyAddress]
      rw [← tjg5a_utf8_append, ← tjg5a_utf8_append]
    rw [had]
    simp only [pathOf, hne, ↓reduceIte, sessionFile]
    rw [← tjg5a_utf8_append, ← tjg5a_utf8_append]
    rfl
  rw [hpath]
  refine ⟨?_, .inr ?_⟩
  · rw [tjg5a_utf8_eq, tjg5a_sessionFile_partyAddress_eq]
    intro b hb
    have hall :
        (tjg5a_kutf8 ("sessions/" ++ partyAddressName P ++ "." ++ "1")).all
          (fun x => decide (x.toNat < 128)) = true := by
      cases P <;> decide
    exact of_decide_eq_true (List.all_eq_true.mp hall b hb)
  · unfold pathStr
    rw [tjg5a_utf8_eq, tjg5a_sessionFile_partyAddress_eq]
    cases P <;> decide

private theorem tjg5a_list_length_le_flatMap_utf8EncodeChar :
    ∀ l : List Char, l.length ≤ (l.flatMap String.utf8EncodeChar).length
  | [] => Nat.le_refl 0
  | c :: cs => by
    have hc : 1 ≤ (String.utf8EncodeChar c).length := by
      unfold String.utf8EncodeChar; dsimp only
      by_cases h1 : c.val.toNat ≤ 127
      · simp only [h1, ↓reduceIte, List.length_cons, List.length_nil]; omega
      · by_cases h2 : c.val.toNat ≤ 2047
        · simp only [h1, h2, ↓reduceIte, List.length_cons, List.length_nil]; omega
        · by_cases h3 : c.val.toNat ≤ 65535
          · simp only [h1, h2, h3, ↓reduceIte, List.length_cons, List.length_nil]; omega
          · simp only [h1, h2, h3, ↓reduceIte, List.length_cons, List.length_nil]; omega
    have ih := tjg5a_list_length_le_flatMap_utf8EncodeChar cs
    simp only [List.length_cons, List.flatMap_cons, List.length_append]; omega

private theorem tjg5a_string_length_le_utf8_length (s : String) : s.length ≤ (utf8 s).length := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  rw [String.length_ofList]
  have hutf : (utf8 (String.ofList l)).length = (l.flatMap String.utf8EncodeChar).length := by
    simp [utf8, List.utf8Encode, tjg5a_byteArray_toList_eq_data]
  rw [hutf]
  exact tjg5a_list_length_le_flatMap_utf8EncodeChar l

private theorem tjg5a_u32_toString_len_le_10 (id : BitVec 32) :
    (toString id.toNat).length ≤ 10 :=
  Nat.le_trans (tjg5a_string_length_le_utf8_length (toString id.toNat)) (keyName_length id)

private theorem tjg5a_identityFile_len_le_64 (P : Party) :
    (identityFile (partyAddressName P)).length ≤ 64 := by
  cases P <;> decide

private theorem tjg5a_sessionFile_len_le_64 (P : Party) :
    (sessionFile (partyAddress P)).length ≤ 64 := by
  rw [tjg5a_sessionFile_partyAddress_eq]
  cases P <;> decide

private theorem tjg5a_oneTimeKyberPreKeyFile_len_le_64 (id : BitVec 32) :
    (oneTimeKyberPreKeyFile id).length ≤ 64 := by
  have h := tjg5a_u32_toString_len_le_10 id
  unfold oneTimeKyberPreKeyFile; rw [String.length_append]
  have hp : ("one-time-kyber-pre-keys/").length = 24 := by decide
  omega

private theorem tjg5a_baseKeysFile_len_le_64 (id : BitVec 32) :
    (baseKeysFile id).length ≤ 64 := by
  have h := tjg5a_u32_toString_len_le_10 id
  unfold baseKeysFile; simp only [String.length_append]
  have hp1 : ("last-resort-kyber-pre-keys/").length = 27 := by decide
  have hp2 : (".base-keys").length = 10 := by decide
  omega

private theorem tjg5a_oneTimePreKeyFile_len_le_64 (id : BitVec 32) :
    (oneTimePreKeyFile id).length ≤ 64 := by
  have h := tjg5a_u32_toString_len_le_10 id
  unfold oneTimePreKeyFile; rw [String.length_append]
  have hp : ("one-time-pre-keys/").length = 18 := by decide
  omega

private theorem tjg5a_setOrPush_length_le_succ
    (xs : List (List (BitVec 8) × List (BitVec 8))) (k v : List (BitVec 8)) :
    (DirGhost.setOrPush k v xs).length ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [DirGhost.setOrPush]
  | cons _ _ ih =>
    unfold DirGhost.setOrPush
    split <;> [simp; (simp only [List.length_cons]; omega)]

private theorem tjg5a_dirPut_writes_length_le_succ (d : DirGhost) (k v : List (BitVec 8)) :
    (d.put k v).writes.length ≤ d.writes.length + 1 := by
  simp only [DirGhost.writes, DirGhost.put, List.length_map]
  exact tjg5a_setOrPush_length_le_succ d.changed k v

private theorem tjg5a_saveUpd_peers_writes_length_le_succ (F : FsFiles)
    (idG : IdGhost) (rem : AddrVal) (k : IdentityKey) :
    (idG.saveUpd cliIo.rd F rem k).peers.writes.length ≤ idG.peers.writes.length + 1 ∧
      (idG.saveUpd cliIo.rd F rem k).own = idG.own := by
  refine ⟨?_, saveUpd_own cliIo.rd F idG rem k⟩
  unfold IdGhost.saveUpd
  split
  · exact tjg5a_dirPut_writes_length_le_succ idG.peers rem.name k.serialize
  · exact Nat.le_succ _

private theorem tjg5a_foldl_cliStep_writes_length_le (F : FsFiles) :
    ∀ (calls : List (StoreCall AddrVal (List (BitVec 8)))) (g : StoresGhost),
      (calls.foldl (cliStep F) g).writes.length ≤ g.writes.length + calls.length
  | [], g => by simp
  | c :: cs, g => by
    have h1 : (cliStep F g c).writes.length ≤ g.writes.length + 1 := by
      cases c with
      | loadSession _ | isTrustedIdentity _ _ _ => exact Nat.le_succ _
      | saveIdentity rem k =>
        obtain ⟨hp, ho⟩ := tjg5a_saveUpd_peers_writes_length_le_succ F g.identity rem k
        dsimp only [cliStep, StoresGhost.writes]; rw [ho]; simp only [List.length_append]; omega
      | storeSession rem r =>
        dsimp only [cliStep, StoresGhost.writes]
        have hs := tjg5a_dirPut_writes_length_le_succ g.sessions (addressText rem) (encodeRecord r)
        simp only [List.length_append]; omega
    have h2 := tjg5a_foldl_cliStep_writes_length_le F cs (cliStep F g c)
    dsimp only [List.foldl, List.length_cons]; omega

private theorem tjg5a_storesWrOk_foldl (F : FsFiles) (P : Party) :
    ∀ (cs : List (StoreCall AddrVal (List (BitVec 8)))) (g : StoresGhost),
      (∀ c ∈ cs, StoreCallPeerPlaced (addrValE P) c) →
      StoresWrOk (okPeerPath P) g →
      g.identity.peers.path = utf8 "identities" →
      g.sessions.path = utf8 "sessions" →
      StoresWrOk (okPeerPath P) (cs.foldl (cliStep F) g) := by
  intro cs
  induction cs with
  | nil => intro g _ hg0 _ _; exact hg0
  | cons c cs' ih =>
    intro g hcs hg0 hp hs
    have hc1 := hcs c List.mem_cons_self
    cases c with
    | loadSession _ | isTrustedIdentity _ _ _ =>
      exact ih g (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hg0 hp hs
    | saveIdentity rem k =>
      change rem = addrValE P at hc1; subst hc1
      dsimp only [List.foldl, cliStep]
      exact ih _ (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
        { hg0 with
          own := by rw [saveUpd_own]; exact hg0.own
          peers := DirWrOk.saveUpd hg0.peers (hp ▸ tjg5a_okPeerPath_id P) }
        (by rw [saveUpd_peers_path, hp]) hs
    | storeSession rem r0 =>
      change rem = addrValE P at hc1; subst hc1
      dsimp only [List.foldl, cliStep]
      exact ih _ (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
        { hg0 with sessions := hg0.sessions.put (hs ▸ tjg5a_okPeerPath_sess P) _ } hp hs

private theorem tjg5a_decPkDef_writes_len_le_4 {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal}
    {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)} {g' : StoresGhost} {pt : List (BitVec 8)}
    (h : decPkDef X W Scope F (addrValE P) me pm coins = some (some (g', pt))) :
    g'.writes.length ≤ 4 := by
  unfold decPkDef at h
  dsimp only at h
  cases hload : loadRec Scope F (addrValE P) with
  | error _ => rw [hload] at h; cases h
  | ok r =>
    rw [hload] at h; dsimp only at h
    cases htr : StoresGhost.opened.identity.trusted cliIo.rd F (addrValE P) pm.identityKey with
    | error _ => rw [htr] at h; cases h
    | ok tb =>
      cases tb with
      | false => rw [htr] at h; cases h
      | true =>
        rw [htr] at h; dsimp only at h
        cases hcur : r.bind (·.currentSession) with
        | some s =>
          rw [hcur] at h; dsimp only at h
          split at h
          · split at h
            · cases h
            · cases hdec : SessionState.tryDecryptFromRecord W.C
                  (pqxdhSpqrSession W)
                  ((pqxdhSessionParams W).expectedAddrs (initParty (addrValE P)))
                  pm.message .preKey (pkRecvCoins coins) s.state with
              | mk res st1 =>
                rw [hdec] at h
                cases res with
                | ok _ =>
                  dsimp only at h
                  injection h with h1; injection h1 with h2
                  obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                  obtain ⟨hp, ho⟩ := tjg5a_saveUpd_peers_writes_length_le_succ F
                    StoresGhost.opened.identity (addrValE P) pm.identityKey
                  have hs := tjg5a_dirPut_writes_length_le_succ StoresGhost.opened.sessions
                    (addressText (addrValE P))
                    (encodeRecord
                      { currentSession := some
                          { state := st1, pendingPreKey := none, pendingKyberPreKey := none,
                            localRegistrationId := s.localRegistrationId,
                            remoteRegistrationId := s.remoteRegistrationId,
                            aliceBaseKey := s.aliceBaseKey } })
                  have h0_own : StoresGhost.opened.identity.own.writes.length = 0 := rfl
                  have h0_peers : StoresGhost.opened.identity.peers.writes.length = 0 := rfl
                  have h0_signed : StoresGhost.opened.signed.writes.length = 0 := rfl
                  have h0_kot : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
                  have h0_klr : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
                  have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                  have h0_sess : StoresGhost.opened.sessions.writes.length = 0 := rfl
                  have h0_pub : StoresGhost.opened.pub.writes.length = 0 := rfl
                  dsimp only [StoresGhost.writes]; rw [ho]
                  simp only [List.length_append, h0_own, h0_signed, h0_kot, h0_klr, h0_ot, h0_pub]
                  omega
                | error err => cases err <;> cases h
          · cases h
        | none =>
          rw [hcur] at h; dsimp only at h
          cases hpk : pkToE? pm with
          | none => rw [hpk] at h; cases h
          | some m =>
            rw [hpk] at h; dsimp only at h
            cases hsk : pkStoreKeys F m with
            | none => rw [hsk] at h; cases h
            | some k =>
              rw [hsk] at h
              cases hkp : StoresGhost.opened.identity.keyPair cliIo.rd F with
              | error _ => rw [hkp] at h; cases h
              | ok kp =>
                rw [hkp] at h
                cases hreg : StoresGhost.opened.identity.regId cliIo.rd F with
                | error _ => rw [hreg] at h; cases h
                | ok reg =>
                  rw [hreg] at h; dsimp only at h
                  cases hrecv : recvPrekeyState X W
                      (initParty (addrValE P)) ⟨kp.privateKey.bytes, reg⟩ k m (pkRecvCoins coins) with
                  | none => rw [hrecv] at h; cases h
                  | some o =>
                    rw [hrecv] at h
                    cases o with
                    | none => cases h
                    | some triple =>
                      rcases triple with ⟨x, gs, _⟩
                      dsimp only at h
                      cases hkm : StoresGhost.opened.kyber.mark cliIo.rd F m.kpkId
                          pm.signedPreKeyId pm.baseKey with
                      | mk kres kyber' =>
                        rw [hkm] at h
                        cases kres with
                        | error _ => cases h
                        | ok u =>
                          cases u; dsimp only at h
                          injection h with h1; injection h1 with h2
                          obtain ⟨rfl, _⟩ := Prod.mk.inj h2
                          have hkyb : kyber'.oneTime.writes.length + kyber'.lastResort.writes.length ≤ 1 := by
                            unfold KyberGhost.mark at hkm
                            cases hot : StoresGhost.opened.kyber.oneTime.get cliIo.rd F
                                (keyName m.kpkId) with
                            | error _ => rw [hot] at hkm; cases hkm
                            | ok bs =>
                              rw [hot] at hkm
                              cases bs with
                              | cons _ _ =>
                                dsimp only at hkm; injection hkm with _ hk; subst hk; dsimp only
                                have h1 := tjg5a_dirPut_writes_length_le_succ
                                  StoresGhost.opened.kyber.oneTime (keyName m.kpkId) []
                                have h0a : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
                                have h0b : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
                                omega
                              | nil =>
                                dsimp only at hkm
                                cases hlr : StoresGhost.opened.kyber.lastResort.get cliIo.rd F
                                    (baseKeysName m.kpkId) with
                                | error _ => rw [hlr] at hkm; cases hkm
                                | ok seen =>
                                  rw [hlr] at hkm; dsimp only at hkm
                                  split at hkm
                                  · cases hkm
                                  · split at hkm
                                    · cases hkm
                                    · injection hkm with _ hk; subst hk; dsimp only
                                      have h0a : StoresGhost.opened.kyber.oneTime.writes.length = 0 := rfl
                                      have h0b : StoresGhost.opened.kyber.lastResort.writes.length = 0 := rfl
                                      rw [h0a, Nat.zero_add]
                                      exact Nat.le_trans (tjg5a_dirPut_writes_length_le_succ _ _ _)
                                        (by rw [h0b])
                          obtain ⟨hp_le, ho⟩ := tjg5a_saveUpd_peers_writes_length_le_succ F
                            StoresGhost.opened.identity (addrValE P) pm.identityKey
                          have hs_le := tjg5a_dirPut_writes_length_le_succ StoresGhost.opened.sessions
                            (addressText (addrValE P))
                            (CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) gs)
                          have h0_own : StoresGhost.opened.identity.own.writes.length = 0 := rfl
                          have h0_peers : StoresGhost.opened.identity.peers.writes.length = 0 := rfl
                          have h0_signed : StoresGhost.opened.signed.writes.length = 0 := rfl
                          have h0_sess : StoresGhost.opened.sessions.writes.length = 0 := rfl
                          have h0_pub : StoresGhost.opened.pub.writes.length = 0 := rfl
                          unfold StoresGhost.writes; dsimp only; rw [ho]
                          simp only [List.length_append, h0_own, h0_signed, h0_pub]
                          cases pm.preKeyId with
                          | none =>
                            dsimp only
                            have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                            omega
                          | some j =>
                            dsimp only; unfold removePreKey
                            cases StoresGhost.opened.oneTime.get cliIo.rd F (keyName j) with
                            | error _ =>
                              dsimp only
                              have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                              omega
                            | ok bs =>
                              cases bs with
                              | nil =>
                                dsimp only
                                have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                                omega
                              | cons _ _ =>
                                dsimp only
                                have hot_put := tjg5a_dirPut_writes_length_le_succ
                                  StoresGhost.opened.oneTime (keyName j) []
                                have h0_ot : StoresGhost.opened.oneTime.writes.length = 0 := rfl
                                omega

private theorem tjg5a_decPkDef_some_some_eq_d2c {X : UnreachedPqxdhPrimitives} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrVal} {pm : PreKeySignalMessage}
    {coins : List (BitVec 8)} {g' : StoresGhost} {pt : List (BitVec 8)}
    (h : decPkDef X W Scope F peer me pm coins = some (some (g', pt))) :
    decPkDefD2c X W Scope F peer me pm coins = some (some (g', pt)) := by
  by_cases htr : StoresGhost.opened.identity.trusted cliIo.rd F peer pm.identityKey = .ok true
  · cases hload : loadRec Scope F peer with
    | error _ =>
      unfold decPkDef at h; simp [hload] at h
    | ok opt =>
      cases opt with
      | none =>
        rw [decPkDefD2c_eq_decPkDef_of_noCurrent X W Scope F peer me pm coins
          (fun _ hl => by rw [hload] at hl; cases hl)]
        exact h
      | some r =>
        cases hcur : r.currentSession with
        | none =>
          rw [decPkDefD2c_eq_decPkDef_of_noCurrent X W Scope F peer me pm coins
            (fun _ hl => by
              rw [hload] at hl; injection hl with hr; injection hr with hr; subst hr; exact hcur)]
          exact h
        | some s =>
          by_cases hm : SessMatchesPm s pm
          · rw [decPkDefD2c_eq_decPkDef_of_match X W Scope F peer me pm coins hload hcur hm]
            exact h
          · unfold decPkDef at h
            simp [hload, htr, hcur, hm] at h
  · rw [decPkDefD2c_eq_decPkDef_of_untrusted X W Scope F peer me pm coins htr]
    exact h

private theorem tjg5a_finish_inv {α : Type} {ans : SlotAns α}
    {outFn : α → List (BitVec 8)} {ws : List (String × List (BitVec 8))} {out : List (BitVec 8)}
    (h : finish ans outFn = some (some (ws, out))) :
    ∃ g' v, ans = some (some (g', v)) ∧ ws = namedWrites g'.writes ∧ out = outFn v := by
  cases ans with
  | none => cases h
  | some o =>
    cases o with
    | none => cases h
    | some gv =>
      rcases gv with ⟨g', v⟩
      dsimp only [finish] at h
      injection h with h1; injection h1 with h2
      obtain ⟨hw, ho⟩ := Prod.mk.inj h2
      exact ⟨g', v, rfl, hw.symm, ho.symm⟩

private theorem tjg5a_runAns_some_some_to_d2c
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {S : RunSem}
    (hinit : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (henc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn)
    (hdecSig : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ scopeIn)
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hpksm : S.pksmParse = pksmParse)
    {i : Inputs} {nw : List (String × List (BitVec 8))} {out : List (BitVec 8)}
    (ha : runAns S i = some (some (nw, out))) :
    runAns (cliRunSemD2c_placed X W) i = some (some (nw, out)) := by
  unfold runAns at ha ⊢
  cases hp : parseArgs uuidTryParse (i.argv.map bytesOfString) with
  | none => rw [hp] at ha; cases ha
  | some c =>
    rw [hp] at ha; dsimp only at ha ⊢
    cases hown : StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "address") with
    | error _ => rw [hown] at ha; cases ha
    | ok ownB =>
      rw [hown] at ha; dsimp only at ha ⊢
      cases had : addrParse uuidTryParse ownB with
      | none => rw [had] at ha; cases ha
      | some meV =>
        rw [had] at ha; dsimp only at ha ⊢
        cases c with
        | keygen _ _ => cases ha
        | init peerV dir =>
          dsimp only at ha ⊢
          cases hbv : readBundleV (runFiles i) dir peerV.device with
          | none => rw [hbv] at ha; cases ha
          | some b =>
            rw [hbv] at ha; dsimp only at ha ⊢
            have hd2c_in : (cliRunSemD2c_placed X W).initiate = initDef X ⟨W.C, W.Q⟩ := rfl
            rw [hinit] at ha; rw [hd2c_in]; exact ha
        | send peerV =>
          dsimp only at ha ⊢
          rw [henc] at ha; exact ha
        | recv peerV =>
          dsimp only at ha ⊢
          cases hst : i.stdin with
          | nil => rw [hst] at ha; cases ha
          | cons t rest =>
            rw [hst] at ha; dsimp only at ha ⊢
            by_cases ht2 : t = 2#8
            · simp only [ht2, ↓reduceIte] at ha ⊢
              rw [hdecSig] at ha; exact ha
            · simp only [ht2, ↓reduceIte] at ha ⊢
              by_cases ht3 : t = 3#8
              · simp only [ht3, ↓reduceIte] at ha ⊢
                have hd2c_pk : (cliRunSemD2c_placed X W).pksmParse = pksmParse := rfl
                have hd2c_dp : (cliRunSemD2c_placed X W).decryptPrekey =
                    decPkDefD2c X ⟨W.C, W.Q⟩ scopeIn := rfl
                rw [hpksm] at ha; rw [hd2c_pk, hd2c_dp]
                cases hpm : pksmParse rest with
                | none => rw [hpm] at ha; cases ha
                | some pm =>
                  rw [hpm] at ha; dsimp only at ha ⊢
                  rw [hdecPk] at ha
                  obtain ⟨g', v, hg, hnw, hout⟩ := tjg5a_finish_inv ha
                  rw [tjg5a_decPkDef_some_some_eq_d2c hg]
                  simp [finish, hnw, hout]
              · simp only [ht3, ↓reduceIte] at ha; cases ha

private theorem tjg5a_decSigDef_writes_bounds {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {msg : SignalMessage} {coins : List (BitVec 8)}
    {g' : StoresGhost} {v : List (BitVec 8)}
    (h : decSigDef W Scope F (addrValE P) me msg coins = some (some (g', v))) :
    g'.writes.length ≤ 4 := by
  unfold decSigDef at h
  split at h
  · next pt calls heq =>
    injection h with h1; injection h1 with h2
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    obtain ⟨k, r, -, hpref⟩ :=
      messageDecryptSignal_trace_prefix W.C (pqxdhSpqrModel W).spqr
        (serializeAddrVals (serviceIdParse uuidTryParse))
        (cliAnswers Scope F (addrValE P) (decSigKey W Scope F (addrValE P) me msg coins))
        msg (addrValE P) me (coinsOf coins)
    rw [heq] at hpref
    have hclen : calls.length ≤ 4 := Nat.le_trans hpref.length_le (by simp [fullTrace])
    have hf := tjg5a_foldl_cliStep_writes_length_le F calls StoresGhost.opened
    have h0 : StoresGhost.opened.writes.length = 0 := rfl
    dsimp only [cliFinal]; omega
  · cases h
  · cases h

private theorem tjg5a_storesWrOk_decSigDef {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {P : Party} {me : AddrVal} {msg : SignalMessage} {coins : List (BitVec 8)}
    {g' : StoresGhost} {v : List (BitVec 8)}
    (h : decSigDef W Scope F (addrValE P) me msg coins = some (some (g', v))) :
    StoresWrOk (okPeerPath P) g' := by
  unfold decSigDef at h
  split at h
  · next pt calls heq =>
    injection h with h1; injection h1 with h2
    obtain ⟨rfl, _⟩ := Prod.mk.inj h2
    have hc := messageDecryptSignal_calls_peer_placed
      W.C (pqxdhSpqrModel W).spqr
      (serializeAddrVals (serviceIdParse uuidTryParse))
      (cliAnswers Scope F (addrValE P) (decSigKey W Scope F (addrValE P) me msg coins))
      msg (addrValE P) me (coinsOf coins)
    rw [heq] at hc
    exact tjg5a_storesWrOk_foldl F P calls StoresGhost.opened hc (StoresWrOk.opened _) rfl rfl
  · cases h
  · cases h

private theorem tjg5a_nwDom_pqD3Recv
    {X : UnreachedPqxdhPrimitives} {W : CliHooks}
    {S : RunSem}
    (hinit : S.initiate = initDef X ⟨W.C, W.Q⟩)
    (henc : S.encrypt = encDef ⟨W.C, W.Q⟩ scopeIn)
    (hdecSig : S.decryptSignal = decSigDef ⟨W.C, W.Q⟩ scopeIn)
    (hdecPk : S.decryptPrekey = decPkDef X ⟨W.C, W.Q⟩ scopeIn)
    (hpksm : S.pksmParse = pksmParse)
    (i : Inputs)
    (nw : List (String × List (BitVec 8))) (out : List (BitVec 8))
    (hi : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ i)
    (ha : runAns S i = some (some (nw, out))) :
    nw.length ≤ 4 ∧ ∀ pw ∈ nw, pw.1.length ≤ 64 := by
  have ha_d2c := tjg5a_runAns_some_some_to_d2c hinit henc hdecSig hdecPk hpksm ha
  rcases hi with hi_pq | ⟨st, ct, rc, _hwf, rfl⟩
  · exact pqRunAns_namedWrites_bounds hi_pq ha_d2c
  · cases ct with
    | nil =>
      rw [runAns_pqRecvBad S ⟨W.C, W.Q⟩ st [] rc (by decide) (by decide)] at ha; cases ha
    | cons t rest =>
      by_cases ht2 : t = wireWhisper
      · subst ht2
        rw [runAns_pqRecvWhisper_eq S ⟨W.C, W.Q⟩ st rest rc, hdecSig] at ha
        cases hsm : SignalMessage.tryFrom protoSignalCodec rest with
        | error _ => rw [hsm] at ha; cases ha
        | ok msg =>
          rw [hsm] at ha; dsimp only at ha
          obtain ⟨g', v, hg, rfl, _⟩ := tjg5a_finish_inv ha
          have hlen4 : g'.writes.length ≤ 4 := tjg5a_decSigDef_writes_bounds hg
          have hwr : StoresWrOk (okPeerPath st.party.other) g' := tjg5a_storesWrOk_decSigDef hg
          refine ⟨Nat.le_trans (Nat.le_of_eq (List.length_map _)) hlen4, fun q hq => ?_⟩
          have hasc : ∀ w ∈ g'.writes, ∀ b ∈ w.1, b.toNat < 128 :=
            fun w hw => (hwr.writes w hw).1
          rw [namedWrites_ascii g'.writes hasc] at hq
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hq
          rcases (hwr.writes w hw).2 with hp | hp <;> rw [hp]
          · exact tjg5a_identityFile_len_le_64 st.party.other
          · exact tjg5a_sessionFile_len_le_64 st.party.other
      · by_cases ht3 : t = wirePrekey
        · subst ht3
          rw [runAns_pqRecvPrekey_eq S ⟨W.C, W.Q⟩ st rest rc, hpksm, hdecPk] at ha
          cases hpm : pksmParse rest with
          | none => rw [hpm] at ha; cases ha
          | some pm =>
            rw [hpm] at ha; dsimp only at ha
            obtain ⟨g', v, hg, rfl, _⟩ := tjg5a_finish_inv ha
            have hg_d2c := tjg5a_decPkDef_some_some_eq_d2c hg
            obtain ⟨kpkId, opkId, hsub⟩ := decPkDefD2c_namedWrites_sub hg_d2c
            have hlen4 := tjg5a_decPkDef_writes_len_le_4 hg
            refine ⟨Nat.le_trans (Nat.le_of_eq (List.length_map _)) hlen4, fun q hq => ?_⟩
            rcases hsub q hq with h | h | h | h | h <;> rw [h]
            · exact tjg5a_identityFile_len_le_64 st.party.other
            · exact tjg5a_sessionFile_len_le_64 st.party.other
            · exact tjg5a_oneTimeKyberPreKeyFile_len_le_64 kpkId
            · exact tjg5a_baseKeysFile_len_le_64 kpkId
            · exact tjg5a_oneTimePreKeyFile_len_le_64 opkId
        · rw [runAns_pqRecvBad S ⟨W.C, W.Q⟩ st (t :: rest) rc
            (fun h => ht2 (Option.some.inj h)) (fun h => ht3 (Option.some.inj h))] at ha
          cases ha

private theorem tjg5a_parseArgs_pqRecvInputs_is_recv {P : PEParams} {st : PqParty}
    {ct : List (BitVec 8)} {rc : BitVec 256} {c : CallV}
    (hp : parseArgs uuidTryParse ((pqRecvInputs P st ct rc).argv.map bytesOfString) = some c) :
    ∃ peerV : AddrV, c = .recv peerV := by
  have ha : (pqRecvInputs P st ct rc).argv = (Cmd.recv (partyAddress st.party.other)).argv := rfl
  rw [ha, parseArgs_recv] at hp
  injection hp with hc
  exact ⟨_, hc.symm⟩

private theorem tjg5a_cliPqxdhInputs_of_pqOrD3Recv_nonPrekey
    {WP : PEParams} {i : Inputs} {c : CallV}
    (hi : CliPqOrD3RecvInputs WP i)
    (hp : parseArgs uuidTryParse (i.argv.map bytesOfString) = some c)
    (hin : (inputOf i c).length ≤ stdinCapBytes)
    (hnp : ∀ (peerV : AddrV) (rest : List (BitVec 8)),
      c = .recv peerV → i.stdin ≠ 3#8 :: rest) :
    CliPqxdhInputs WP i := by
  rcases hi with hi_pq | ⟨st, ct, rc, hst, rfl⟩
  · exact hi_pq
  · obtain ⟨peerV, rfl⟩ := tjg5a_parseArgs_pqRecvInputs_is_recv hp
    have hct_le : (pqRecvInputs WP st ct rc).stdin.length ≤ msgCapBytes :=
      stdin_le_msgCapBytes_of_pqRecvInputs_and_inputOf hp hin
    have hct_lt : ct.length < 2 ^ 32 :=
      Nat.lt_of_le_of_lt hct_le (by decide : msgCapBytes < 2 ^ 32)
    cases ct with
    | nil =>
      exact ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inr
        ⟨[], rc, by decide, by decide, by decide, rfl⟩)))⟩
    | cons b rest =>
      by_cases hb2 : b = wireWhisper
      · subst hb2
        exact ⟨st, hst, Or.inr (Or.inr (Or.inl
          ⟨rest, rc, Nat.lt_of_succ_lt hct_lt, rfl⟩))⟩
      · have hb3 : b ≠ wirePrekey := fun h =>
          hnp peerV rest rfl (by rw [h]; rfl)
        exact ⟨st, hst, Or.inr (Or.inr (Or.inr (Or.inr
          ⟨b :: rest, rc, hct_lt,
            fun h => hb2 (Option.some.inj h),
            fun h => hb3 (Option.some.inj h), rfl⟩)))⟩

private def tjg5a_untypedDecPkCallEnv [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (g : RunCall) (evs : List AllocEvent) : Prop :=
  match g.c, g.i.stdin with
  | .recv peerV, b :: rest =>
    if b = 3#8 then
      match pksmParse rest with
      | some pm => ∃ meV : AddrV, DecPkD3UntypedEnv A W cliRunBudgets (r3bDecPkGhost g meV peerV pm) evs
      | none => False
    else False
  | _, _ => False

private def tjg5a_falseSlotSpec {P : List AllocEvent → Prop}
    (hfalse : ∀ evs, P evs → False) :
    { S : SingleSlotFineSpec P //
      S.cum ≤ d3RecvW4ExtCum ∧ S.live ≤ d3RecvW4ExtLive ∧
      S.peak ≤ d3RecvW4ExtPeak ∧ S.maxReq ≤ d3RecvW4ExtMaxReq ∧
      S.grpS ≤ d3RecvW4ExtGrpS } :=
  ⟨{ cum := 0
     live := 0
     peak := 0
     maxReq := 0
     grpS := 0
     credit :=
       { req_align := fun evs hP => False.elim (hfalse evs hP)
         credit_le := fun _ {evs} hP => False.elim (hfalse evs hP) }
     live_le_peak := Nat.le_refl 0
     groups := { groups_le := fun _ {evs} hP => False.elim (hfalse evs hP) } },
   ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩⟩

private theorem tjg5a_untypedDecPkCallEnv_caps_le :
    decPkD3UntypedCum ≤ d3RecvW4ExtCum ∧
    decPkD3UntypedLive ≤ d3RecvW4ExtLive ∧
    decPkD3UntypedPeak ≤ d3RecvW4ExtPeak ∧
    decPkD3UntypedMaxReq ≤ d3RecvW4ExtMaxReq ∧
    decPkD3UntypedGrpS ≤ d3RecvW4ExtGrpS := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := decPkD3Untyped_caps_le_1MiB
  exact
    ⟨Nat.le_trans h1 (by decide : w4RecvPrekeyReal1MiB_i_Cum ≤ d3RecvW4ExtCum),
     Nat.le_trans h2 (by decide : w4RecvPrekeyReal1MiB_i_Live ≤ d3RecvW4ExtLive),
     Nat.le_trans h3 (by decide : w4RecvPrekeyReal1MiB_i_Peak ≤ d3RecvW4ExtPeak),
     Nat.le_trans h4 (by decide : w4RecvPrekeyReal1MiB_i_MaxReq ≤ d3RecvW4ExtMaxReq),
     Nat.le_trans h5 (by decide : w4RecvPrekeyRealGrpS ≤ d3RecvW4ExtGrpS)⟩

private def tjg5a_untypedDecPkCallEnv_slotSpecWithCaps [LibsignalPlacement]
    (A : RustAlloc) (W : CliHooks) (g : RunCall)
    (hi_g : CliPqOrD3RecvInputs ⟨W.C, W.Q⟩ g.i)
    (_hstdin : g.i.stdin.length ≤ msgCapBytes)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
    { S : SingleSlotFineSpec (tjg5a_untypedDecPkCallEnv A W g) //
      S.cum ≤ d3RecvW4ExtCum ∧ S.live ≤ d3RecvW4ExtLive ∧
      S.peak ≤ d3RecvW4ExtPeak ∧ S.maxReq ≤ d3RecvW4ExtMaxReq ∧
      S.grpS ≤ d3RecvW4ExtGrpS } := by
  cases hc : g.c with
  | keygen _ _ =>
    exact tjg5a_falseSlotSpec (by
      intro evs hP; unfold tjg5a_untypedDecPkCallEnv at hP; simp [hc] at hP)
  | init _ _ =>
    exact tjg5a_falseSlotSpec (by
      intro evs hP; unfold tjg5a_untypedDecPkCallEnv at hP; simp [hc] at hP)
  | send _ =>
    exact tjg5a_falseSlotSpec (by
      intro evs hP; unfold tjg5a_untypedDecPkCallEnv at hP; simp [hc] at hP)
  | recv peerV =>
    cases hst : g.i.stdin with
    | nil =>
      exact tjg5a_falseSlotSpec (by
        intro evs hP; unfold tjg5a_untypedDecPkCallEnv at hP; simp [hc, hst] at hP)
    | cons b rest =>
      by_cases hb : b = 3#8
      · cases hpk : pksmParse rest with
        | none =>
          exact tjg5a_falseSlotSpec (by
            intro evs hP; unfold tjg5a_untypedDecPkCallEnv at hP; simp [hc, hst, hb, hpk] at hP)
        | some pm =>
          have hparse_recv :
              parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
            hc ▸ hparse
          refine ⟨{ cum := decPkD3UntypedCum
                    live := decPkD3UntypedLive
                    peak := decPkD3UntypedPeak
                    maxReq := decPkD3UntypedMaxReq
                    grpS := decPkD3UntypedGrpS
                    credit :=
                      { req_align := fun evs hP ev hev => by
                          have hex : ∃ meV : AddrV,
                              DecPkD3UntypedEnv A W cliRunBudgets (r3bDecPkGhost g meV peerV pm) evs := by
                            unfold tjg5a_untypedDecPkCallEnv at hP
                            simpa [hc, hst, hb, hpk] using hP
                          obtain ⟨meV, hmeV⟩ := hex
                          exact
                            (decPkD3UntypedEnv_r3b_singleSlotFineSpec A W cliRunBudgets g meV peerV pm
                              hi_g hparse_recv).credit.req_align evs hmeV ev hev
                        credit_le := fun st0 {evs} hP => by
                          have hex : ∃ meV : AddrV,
                              DecPkD3UntypedEnv A W cliRunBudgets (r3bDecPkGhost g meV peerV pm) evs := by
                            unfold tjg5a_untypedDecPkCallEnv at hP
                            simpa [hc, hst, hb, hpk] using hP
                          obtain ⟨meV, hmeV⟩ := hex
                          exact
                            (decPkD3UntypedEnv_r3b_singleSlotFineSpec A W cliRunBudgets g meV peerV pm
                              hi_g hparse_recv).credit.credit_le st0 hmeV }
                    live_le_peak :=
                      (decPkD3UntypedEnv_r3b_singleSlotFineSpec A W cliRunBudgets g peerV peerV pm
                        hi_g hparse_recv).live_le_peak
                    groups :=
                      { groups_le := fun st0 {evs} hP => by
                          have hex : ∃ meV : AddrV,
                              DecPkD3UntypedEnv A W cliRunBudgets (r3bDecPkGhost g meV peerV pm) evs := by
                            unfold tjg5a_untypedDecPkCallEnv at hP
                            simpa [hc, hst, hb, hpk] using hP
                          obtain ⟨meV, hmeV⟩ := hex
                          exact
                            (decPkD3UntypedEnv_r3b_singleSlotFineSpec A W cliRunBudgets g meV peerV pm
                              hi_g hparse_recv).groups.groups_le st0 hmeV } },
                  tjg5a_untypedDecPkCallEnv_caps_le⟩
      · exact tjg5a_falseSlotSpec (by
          intro evs hP; unfold tjg5a_untypedDecPkCallEnv at hP; simp [hc, hst, hb] at hP)

private def tjg5a_DomPrekey (WP : PEParams) (i : Inputs) : Prop :=
  CliPqOrD3RecvInputs WP i ∧
    ∃ (peerV : AddrV) (rest : List (BitVec 8)),
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV) ∧
      i.stdin = 3#8 :: rest

private theorem tjg5a_d3Prekey_fitsCap [LibsignalPlacement]
    (W : CliHooks) (A : RustCliAllocBudget fineCostModel)
    (sEnvs : RunSlotEnvs)
    (hs_dp : sEnvs.decryptPrekey =
      DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
        (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
        PqxdhAcceptBadKemErrEnv := by rfl) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          sEnvs PksmTryFromEnv (cliRunSemD3 W)))
      (domScopedRun (tjg5a_DomPrekey ⟨W.C, W.Q⟩) (runRel (cliRunSemD3 W))) := by
  let S := cliRunSemD3 W
  let X := defaultExtrasF3
  let decPkEnv := tjg5a_untypedDecPkCallEnv A.repAlloc W
  let E := mkD3BinaryKitCalleeEnvsWithDecPk (default : Image) S X W decPkEnv
  have hMain := realCliMainD3RecvWithDecPk_fitsEnv_cliBudgetLimits (default : Image) S X W decPkEnv
    (fun g hi hs hp => (tjg5a_untypedDecPkCallEnv_slotSpecWithCaps A.repAlloc W g hi hs hp).1)
    (fun g hi hs hp => (tjg5a_untypedDecPkCallEnv_slotSpecWithCaps A.repAlloc W g hi hs hp).2)
  exact mainEntryBudgetFitsCapOf_domScopedRun_cliBudgetLimits_of_kitEnvFits
    boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo
    (fun i ⟨hi, _⟩ => hMain i hi)
    (fun i c ⟨hi, _⟩ hp hin => by
      rcases hi with hi_pq | ⟨st, ct, rc, _, rfl⟩
      · exact stdin_le_msgCapBytes_of_pqInputs_and_inputOf hi_pq hp hin
      · exact stdin_le_msgCapBytes_of_pqRecvInputs_and_inputOf hp hin)
    (fun i nw out ⟨hi, _⟩ ha => tjg5a_nwDom_pqD3Recv rfl rfl rfl rfl rfl i nw out hi ha)
    (fun g ⟨hi, peerV₀, rest₀, hp₀, hst₀⟩ hparse _hin _hrel evs hrun => by
      have hc₀ : g.c = .recv peerV₀ := Option.some.inj (hparse.symm.trans hp₀)
      obtain ⟨g₀, hi₀, _, _, hfiles₀⟩ := tjg5a_exists_cliPqxdhInputs_same_argv_runFiles hi
      have hpeq : PreEnv (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd)) g =
          PreEnv (cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) g := by
        funext e
        unfold PreEnv cliRunCalleesEnvs
        dsimp only
        rw [← hfiles₀, dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_own_address hi₀)]
      exact runEnv_to_cliRunBinaryEnv_of_slots (E := E g)
        (fun _ hp =>
          preEnv_sub_r0BinaryEnv (cEnvs := cliRunCalleesEnvs (ReadFileRuleEnv cliIo.rd)) rfl g
            (Eq.mp (congrFun hpeq _) hp))
        (fun _ _ _ _ hc => by rw [hc₀] at hc; cases hc)
        (fun _ _ _ _ hc => by rw [hc₀] at hc; cases hc)
        (fun _ _ _ _ hc => by rw [hc₀] at hc; cases hc)
        (fun _ _ _ hc => by rw [hc₀] at hc; cases hc)
        (fun _ _ _ _ _ hst _ => by rw [hst₀] at hst; cases hst)
        (fun _ peerV rest _ hc hst hrp =>
          r3bRecvPEnv_sub_r3bEnv
            (fun _ hpk => hpk)
            (fun meV _meG pm e _hme hp hd => by
              have hp' : pksmParse rest = some pm := hp
              rw [hs_dp] at hd
              have hd' : DecPkD3UntypedEnv A.repAlloc W cliRunBudgets
                  (r3bDecPkGhost g meV peerV pm) e :=
                tjg5a_decPkD3UntypedEnvOf_fixed_sub_plain A.repAlloc W g meV peerV pm hi e hd
              dsimp only [E, mkD3BinaryKitCalleeEnvsWithDecPk, decPkEnv, tjg5a_untypedDecPkCallEnv]
              simp only [hc, hst, ↓reduceIte, hp']
              exact ⟨meV, hd'⟩)
            hrp)
        evs hrun)

private theorem tjg5a_untyped_fitsCap_of_exactKitFits [LibsignalPlacement]
    (W : CliHooks) (A : RustCliAllocBudget fineCostModel)
    (sEnvs : RunSlotEnvs)
    (hs_dp : sEnvs.decryptPrekey =
      DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
        (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
        PqxdhAcceptBadKemErrEnv)
    (E_pq : RunCall → CliRunCalleeEnvs)
    (hMainPq : ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel cliBudgetLimits fineCostModel.init (RealCliMainBinaryEnvOf E_pq i))
    (hRunSubPq : ∀ g : RunCall,
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      (inputOf g.i g.c).length ≤ stdinCapBytes →
      (∀ (peerV : AddrV) (rest : List (BitVec 8)),
        g.c = .recv peerV → g.i.stdin ≠ 3#8 :: rest) →
      ∀ evs : List AllocEvent,
        RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            sEnvs PksmTryFromEnv (cliRunSemD3 W))
          g evs →
        CliRunBinaryEnv cliIo.rd (E_pq g) sessionCapBytes g evs) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          sEnvs PksmTryFromEnv (cliRunSemD3 W)))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))) := by
  have hPre := tjg5a_d3Prekey_fitsCap W A sEnvs hs_dp
  let DomNP (i : Inputs) : Prop :=
    CliPqxdhInputs ⟨W.C, W.Q⟩ i ∧
      ¬ ∃ (peerV : AddrV) (rest : List (BitVec 8)),
          parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV) ∧
          i.stdin = 3#8 :: rest
  have hNP :
      MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
        (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
        (RunEnv
          (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
            sEnvs PksmTryFromEnv (cliRunSemD3 W)))
        (domScopedRun DomNP (runRel (cliRunSemD3 W))) :=
    mainEntryBudgetFitsCapOf_domScopedRun_cliBudgetLimits_of_kitEnvFits
      boundedReadFileEnv_of_readFileRuleEnvFixed_cliIo
      (fun i ⟨hi_pq, _⟩ => hMainPq i hi_pq)
      (fun i c ⟨hi_pq, _⟩ hp hin => stdin_le_msgCapBytes_of_pqInputs_and_inputOf hi_pq hp hin)
      (fun i nw out ⟨hi_pq, _⟩ ha =>
        tjg5a_nwDom_pqD3Recv rfl rfl rfl rfl rfl i nw out (Or.inl hi_pq) ha)
      (fun g ⟨hi_pq, hnp⟩ hparse hin _hrel evs hrun =>
        hRunSubPq g hi_pq hparse hin
          (fun peerV rest hc hst => hnp ⟨peerV, rest, hc ▸ hparse, hst⟩) evs hrun)
  intro i hok
  refine ⟨(hPre i hok).1, fun hne => ?_⟩
  refine ⟨((hPre i hok).2 hne).1, fun vcap evs_c c hc hv hp => ?_⟩
  have hm2_pre := ((hPre i hok).2 hne).2 vcap evs_c c hc hv hp
  have hm2_np := ((hNP i hok).2 hne).2 vcap evs_c c hc hv hp
  refine ⟨hm2_pre.1, fun evs_m3 hm3 => ?_⟩
  have hm3_pre := hm2_pre.2 evs_m3 hm3
  have hm3_np := hm2_np.2 evs_m3 hm3
  refine ⟨hm3_pre.1, fun hin a resP callP storesP inpP coinsP ⟨hi, hrel⟩ => ?_⟩
  by_cases hex : ∃ (peerV : AddrV) (rest : List (BitVec 8)),
      parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV) ∧
      i.stdin = 3#8 :: rest
  · exact hm3_pre.2 hin a resP callP storesP inpP coinsP ⟨⟨hi, hex⟩, hrel⟩
  · have hi_pq : CliPqxdhInputs ⟨W.C, W.Q⟩ i :=
      tjg5a_cliPqxdhInputs_of_pqOrD3Recv_nonPrekey hi hp hin
        (fun peerV rest hc hst => hex ⟨peerV, rest, hc ▸ hp, hst⟩)
    exact hm3_np.2 hin a resP callP storesP inpP coinsP ⟨⟨hi_pq, hex⟩, hrel⟩

private theorem tjg5a_decodeState_eq :
    tlb_DecodeStateTightEnvOf = ckx2_DecodeStateTightEnvOf := rfl

private theorem tjg5a_sendCoins_eq :
    @hpt_SpqrSendCoinsOfDecodeFromPbBytesEnv = @ckx2_SpqrSendCoinsOfDecodeFromPbBytesEnv := rfl

private theorem tjg5a_encSlot_eq [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets) :
    cliEncryptBinaryKitSlotEnvExact W A B = ckx2_cliEncryptBinaryKitSlotEnvExact W A B := by
  unfold cliEncryptBinaryKitSlotEnvExact ckx2_cliEncryptBinaryKitSlotEnvExact
    tlb_DecodeStateTightEnv ckx2_DecodeStateTightEnv
  dsimp only
  rw [tjg5a_sendCoins_eq, tjg5a_decodeState_eq]

private theorem tjg5a_recvCt2Tail_eq :
    RecvCt2ChunkTailEnv' = ckx2_RecvCt2ChunkTailEnv' := by
  funext rk ct1 dk opt evs
  cases opt <;> rfl

private theorem tjg5a_ekSentRecvCt2_eq :
    @EkSentCt1ReceivedRecvCt2ChunkEnv' = @ckx2_EkSentCt1ReceivedRecvCt2ChunkEnv' := by
  funext F s ep ch evs
  unfold EkSentCt1ReceivedRecvCt2ChunkEnv' ckx2_EkSentCt1ReceivedRecvCt2ChunkEnv'
  rw [tjg5a_recvCt2Tail_eq]

private theorem tjg5a_recvEkTail_eq :
    @RecvEkChunkSendCt2TailEnv' = @ckx2_RecvEkChunkSendCt2TailEnv' := by
  funext F K sendCt2OnDone uc opt evs
  cases opt <;> rfl

private theorem tjg5a_statesRecv_eq :
    @StatesRecvEnv' = @ckx2_StatesRecvEnv' := by
  funext F K st msg evs
  cases st with
  | keysUnsampled _ | headerReceived _ | ct2Sampled _ => rfl
  | keysSampled s | headerSent s | ct1Received s | noHeaderReceived s =>
    dsimp only [StatesRecvEnv', ckx2_StatesRecvEnv']
    cases msg.payload <;> rfl
  | ekSentCt1Received s =>
    dsimp only [StatesRecvEnv', ckx2_StatesRecvEnv']
    rw [tjg5a_ekSentRecvCt2_eq]
    cases msg.payload <;> rfl
  | ct1Sampled s | ct1Acknowledged s =>
    dsimp only [StatesRecvEnv', ckx2_StatesRecvEnv']
    rw [tjg5a_recvEkTail_eq]
    cases msg.payload <;> rfl
  | ekReceivedCt1Sampled s =>
    dsimp only [StatesRecvEnv', ckx2_StatesRecvEnv']
    cases s.uc.send_ct2 K with
    | error _ => rfl
    | ok t => rcases t with ⟨_, _, _⟩; rfl

private theorem tjg5a_statesRecvProto_eq :
    @StatesRecvProtoEnv' = @ckx2_StatesRecvProtoEnv' := by
  funext F K st msg evs
  unfold StatesRecvProtoEnv' ckx2_StatesRecvProtoEnv'
  rw [tjg5a_statesRecv_eq]

private theorem tjg5a_spqrTightLinkedRecv_eq :
    SpqrRecvC07C09aTightLinkedEnvRecvOf = ckx2_SpqrRecvC07C09aTightLinkedEnvRecvOf := by
  funext maxOps F K RecvProto stB p vn pb st0 sm v xI xN xA xR xSI xCI evs
  unfold SpqrRecvC07C09aTightLinkedEnvRecvOf ckx2_SpqrRecvC07C09aTightLinkedEnvRecvOf
  rw [tjg5a_decodeState_eq]

private theorem tjg5a_spqrTightLinked_eq :
    SpqrRecvC07C09aTightLinkedEnvOf = ckx2_SpqrRecvC07C09aTightLinkedEnvOf := by
  funext maxOps F K stB p vn pb st0 sm v xI xN xA xR xSI xCI evs
  unfold SpqrRecvC07C09aTightLinkedEnvOf ckx2_SpqrRecvC07C09aTightLinkedEnvOf
  rw [tjg5a_spqrTightLinkedRecv_eq, tjg5a_statesRecvProto_eq]

private theorem tjg5a_spqrBytes_eq :
    SpqrRecvC07C09aBytesEnvOf = ckx2_SpqrRecvC07C09aBytesEnvOf := by
  funext maxOps F K stBs msgBs evs
  unfold SpqrRecvC07C09aBytesEnvOf ckx2_SpqrRecvC07C09aBytesEnvOf
  rw [tjg5a_spqrTightLinked_eq]

private theorem tjg5a_cmkStep_eq :
    tryDecryptCmkStepEnvOf = ckx2_tryDecryptCmkStepEnvOf := rfl

private theorem tjg5a_cmkSeg4_eq :
    tryDecryptCmkSeg4EnvOf = ckx2_tryDecryptCmkSeg4EnvOf := by
  funext LoopAdv fmt x trG tr ck evs
  unfold tryDecryptCmkSeg4EnvOf ckx2_tryDecryptCmkSeg4EnvOf
  rw [tjg5a_cmkStep_eq]

private theorem tjg5a_tryDecryptLoop_eq :
    TryDecryptCliLinkedLoopEnvOf = ckx2_TryDecryptCliLinkedLoopEnvOf := by
  funext LoopAdv maxOps C K a evs
  unfold TryDecryptCliLinkedLoopEnvOf ckx2_TryDecryptCliLinkedLoopEnvOf
  cases Mut.exec TripleRatchet.fromSessionState a.st with
  | mk res st1 =>
    cases res with
    | error _ => rfl
    | ok tr0 => rw [tjg5a_cmkSeg4_eq, tjg5a_spqrBytes_eq]

private theorem tjg5a_tryDecrypt_eq :
    TryDecryptCliLinkedEnvOf = ckx2_TryDecryptCliLinkedEnvOf := by
  funext maxOps C K
  unfold TryDecryptCliLinkedEnvOf ckx2_TryDecryptCliLinkedEnvOf
  rw [tjg5a_tryDecryptLoop_eq]

private theorem tjg5a_decSigSlot_eq [LibsignalPlacement] {M : AllocCostModel}
    (W : CliHooks) (A : RustCliAllocBudget M) (B : RunBudgets) :
    cliDecryptSignalBinaryKitSlotEnvExact W A B =
      ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A B := by
  unfold cliDecryptSignalBinaryKitSlotEnvExact ckx2_cliDecryptSignalBinaryKitSlotEnvExact
  rw [tjg5a_tryDecrypt_eq]

/-- `MainEntryBudgetFitsCapOf` at `binaryKitRunSlotEnvsExact` and `DecPkD3UntypedEnvOf` under `pqD3ScopedRun`. -/
theorem hole_g5a_untyped_fitsCap_closed
    [LibsignalPlacement]
    (W : CliHooks) (A : RustCliAllocBudget fineCostModel) :
    MainEntryBudgetFitsCapOf fineCostModel cliBudgetLimits fineCostModel.init cliIo
      (ReadFileRuleEnvFixed cliIo.rd) uuidTryParse
      (RunEnv
        (cliMainArmEnvs (cliRunCalleesEnvs (ReadFileRuleEnvFixed cliIo.rd))
          (binaryKitRunSlotEnvsExact W A cliRunBudgets_placed
            (realCliInitBinarySlotEnvFixed W)
            (DecPkD3UntypedEnvOf (A := A.repAlloc) cliRunBudgets_placed
              (ReadFileRuleEnvFixed cliIo.rd) SessDeserializeCancelEnv
              PqxdhAcceptBadKemErrEnv))
          PksmTryFromEnv (cliRunSemD3 W)))
      (pqD3ScopedRun ⟨W.C, W.Q⟩ (runRel (cliRunSemD3 W))) := by
  exact g5ar_hole_g5a_of_slots W A
    (fun {_M'} A' B' => ckx2_cliEncryptBinaryKitSlotEnvExact W A' B')
    (fun {_M'} A' B' => ckx2_cliDecryptSignalBinaryKitSlotEnvExact W A' B')
    _
    (tjg5a_untyped_fitsCap_of_exactKitFits W A _ rfl)
    rfl
    (tjg5a_encSlot_eq W A cliRunBudgets_placed)
    (tjg5a_decSigSlot_eq W A cliRunBudgets_placed)
    (ckx2_w1EncExact_phaseCredit W)
    (ckx2_w1EncExact_groupSpec W)
    (ckx2_w2DecSigExact_phaseCredit W)
    (ckx2_w2DecSigExact_groupSpec W)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfTopJoinG5A
