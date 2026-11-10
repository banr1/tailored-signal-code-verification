/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
public import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
public import LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
public import LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvGroupSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec
public import LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
public import LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
public import LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux

/-!
# Post-Bob `Dom0'` (`archivedTrials = []`, `rc_len1 ≤ 1`) Slot Caps, Dischargers, & `1 GiB` Checks

Closed-`Nat` post-Bob `Dom0'` (`PostBobPrev1Dom`) stage-level, slot-level, call-site, and whole-`main`
`1 GiB` (`cliOneGiB`) budget bounds built on `W4PostBobPrev1Dom`:
- Closed `Dom0'` 5-tuple (`w4CmkDom0'*` / `fits2_zbDom0'*`):
  `cum = 140,230,427` B, `live = 29,726,017` B, `peak = 29,726,017` B, `maxReq = 4,194,368` B, and
  `grpS = 2,730,214,888` (`@83`) / `2,737,495,460` (`@109`) / `2,742,815,878` (`@128`).
- `StatesRecvProtoEnv'` `SingleSlotFineSpec` instances and `cliDecPkCanonSlotEnvExact'` dischargers
  establishing `PeerSpqrStateTight640` and `SessionGetPrev0Guard` on `CliPqOrD3RecvDom`.
- Whole-`main` `1 GiB` (`1,073,741,824` B) and `2 ^ 48` VA `decide` checks for both canonical
  (`PksmCanonSliceEnv`) and adversarial outer wire (`PksmTryFromWireSliceEnv`) inputs.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

namespace LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0PostBob

open Arm64.Obj (Image)
open Arm64.Process (bytesOfString)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (UnreachedPqxdhPrimitives)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs Inputs)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule StoresGhost pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (RunSem runFiles)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits FitsEnv)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (DirDomainCaps)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDefaultStaticBytes cliDefaultStaticCount cliOneGiB)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W3BinaryInitDom W3BinaryInitParams mkBinaryKitRealCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak (CliRunCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge (RealCliMainBinaryEnvOf)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
  (w3InitRealCum w3InitRealGrpS w3InitRealLive w3InitRealMaxReq w3InitRealPeak
   w3InitReal_caps_le)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (HasFineGroupCredit PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W3InitBinaryKitSlotEnvFixed mkBinaryKitRealCalleeEnvsFixed realCliMainBinaryKitEnvOfFixed)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
  (d3RecvW4ExtCum d3RecvW4ExtGrpS d3RecvW4ExtLive d3RecvW4ExtMaxReq d3RecvW4ExtPeak
   d3RecvW4Ext_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (fineReadFileCum fineReadFileLive fineReadFileMaxReq fineReadFilePeak)
open LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
  (w1SendRealDcanCum w1SendRealDcanGrpS w1SendRealDcanLive w1SendRealDcanMaxReq
   w1SendRealDcanPeak w1SendRealDcan_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
  (w2RecvWhisperRealDcanCum w2RecvWhisperRealDcanGrpS w2RecvWhisperRealDcanLive
   w2RecvWhisperRealDcanMaxReq w2RecvWhisperRealDcanPeak w2RecvWhisperRealDcan_live_le_peak)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Direction Session)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSpqrV1 (Message MlKem States V1State spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.SignalSession.Cli (keyName)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV CallV)
open CryptoVerification.SignalSession.Cli.RunCompose (addrValOf)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.S1PlacedBudget (VerNeS1Env)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux (VerNeTailEnv)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins
  (m2rg_StatesRecvEnvFam m2rg_StatesRecvSub m2rg_TryDecryptCliLinkedEnvOf'
   m2rg_TryDecryptCliLinkedFailEnvOf' m2rg_W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf'
   m2rg_W4BinaryRecvPrekeyPathBWideCmkEnvOf' m2rg_W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed'
   m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf'
   m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf' m2rg_W4FailedTdCancelCmkEnvOf'
   m2rg_W4RecvPrekeyTryDecACCmkEnvOf' m2rg_W4TrialRunWideCmkEnvOf'
   m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf' m2rg_tryDecryptCliLinkedEnvOf'_mono
   m2rg_verNePrev1P3PathCEnv' m2rg_verNePrev1P3PathCEnvOf'
   m2rg_wideSlotEnvCmkWithP3CAllFixed'_eq_fixed)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
  (CliPqOrD3RecvDom cliPqxdhInputs_pqRecvInputs_nil)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvGroupSpec (StatesRecvTightGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches (StatesRecvTightCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit (statesRecvTightGroupS_split)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired
  (StatesRecvProtoEnv' statesRecvExactTightEnv_sub_statesRecvProtoEnv')
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4DecryptPrekeySlotParams W4StageP3WideEnv)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage)
open CryptoVerification.SignalSession (pqRecvInputs)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliDecoupledRamNeed cliDecoupledVaNeed cliMaxAddrTextBytes cliMaxDirPathBytes
   cliMaxDirtyEntries)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec (m3PhaseDeltaCum_tight m6DeltaCum)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (pksmSliceCum pksmSliceLive pksmSliceMaxReq pksmSlicePeak)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (cliRunBinary1MiBCustomPksmCum cliRunBinary1MiBCustomPksmMaxReq)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
  (cliRun1MiBCustomPksmLive cliRun1MiBCustomPksmPeak cliRunOpenedCustomPksmGrpS)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
  (cliMainTightLiveOf cliMainTightPeakOf cliMainTightReqOf)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3 (runFiles_pqRecvInputs_eq_nil)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter (cliMainWidenedSetupFineGrpS)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
  (PeerSpqrStateTight640 peerSpqrStateTight640_of_cliPqInputs_recv)
open LibsignalBinary.Proofs.PeakBudget.W4PostBobPrev1Dom
  (PostBobPrev1Dom SessionGetPrev0Guard W4BinaryCallSiteDomCmk0' W4BinaryRecvPrekeyDomCmk0'
   W4DecryptPrekeyTightDom' W4RecvPrekeyCmkDom0' W4RecvPrekeyCmkDom0Of'
   W4RecvPrekeyRealDomCmkSrOf' cliDecPkCanonSlotEnvExact'
   postBobTotalPrev1Cap286K realCliDecPkBinaryWideSlotEnvCmkDom0'Fixed
   realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf
   realCliDecPkBinaryWideSlotEnvCmkDom0'GuardedFixed
   realCliDecPkBinaryWideSlotEnvCmkDom0'GuardedFixedOf
   realCliDecPkBinaryWideSlotEnvCmkDom0'Prev0GuardedFixed
   realCliDecPkBinaryWideSlotEnvCmkDom0'Prev0GuardedFixedOf
   segCloneEnv_postBobPrev1Dom_fine_groupSpec segClonePostBob1FineGrpS
   serializePrev1MaxReq_postBob_le serializePrev1Peak_fine_postBob_le
   serializePrev1TightCum_fine_postBob_le sessionGetPrev0Guard_of_cliPqOrD3RecvDom
   w4PostBobOneChainLarge w4PostBobPqCap w4PostBobSerializePrev1TightCum)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
  (pksmCanonSliceCum pksmCanonSliceGrpS pksmCanonSliceLive pksmCanonSliceMaxReq
   pksmCanonSlicePeak)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromCredit (pksmTryFromCapDeltaGrpS)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
  (r3bDecPkGhost)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
  (VerNeSessionCancelEnv VerNeTightTopEnv VerNeTightTopEnvOf
   W4StageP3Prev1WideEnv W4StageP3Prev1WideEnvOf verNeSessionCancelEnv_fine_groupSpec
   verNeSessionCancelEnv_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
  (W4FailedTdCancelCmkSrEnvOf W4StatesRecvEnv w4FailedTdCancelCmkSrEnvOf_phaseCreditSpec
   w4FailedTdCancelCmkSrEnvOf_phaseGroupSpec w4cTdCumOf w4cTdFailCumOf w4cTdFailGrpSOf
   w4cTdFailPeakOf w4cTdGrpSOf w4cTdLiveOf w4cTdMaxReqOf w4cTdPeakOf
   w4c_TryDecryptCliLinkedSrEnvOf w4c_repairedStatesRecvEnvFam
   w4c_repairedStatesRecv_creditSpec w4c_repairedStatesRecv_split_groupSpec
   w4c_tryDecryptCliLinkedSrEnvOf_cmk_phaseCreditSpec
   w4c_tryDecryptCliLinkedSrEnvOf_cmk_phaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
  (W4ArchivedTrialCmk W4ArchivedTrialDomCmkOf W4BinaryCallSiteDomCmk W4BinaryRecvPrekeyParamsCmk
   W4FailedTdDomCmkOf W4LoopAdvEnv W4LoopAdvSub W4RecvPrekeyRealParamsCmk W4TrialDecCmkEnv
   W4TrialDropCmkEnv W4TryDecryptCallDomCmkOf W4TryDecryptPathACDomCmkOf w4c_defaultDecodeMaxOps)

section PreHelpers
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_largeCost_eq fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (optLargeCost)
private theorem optLargeCost_fine_eq (n : Nat) :
    optLargeCost fineCostModel n = if n ≤ 135167 then 0 else n + 8195 := by
  unfold optLargeCost
  rw [fineCostModel_smallMaxReq_eq, fineCostModel_largeCost_eq]

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
end PreHelpers


section S3aHelpers

open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.SignalSession.Cli (addressText)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap
  (FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_largeCost_eq fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Heap.SpecBudget (allocBytes1Events)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (addressText_length_le dirDomainCaps_opened_own dirDomainCaps_opened_peers
   dirDomainCaps_opened_sess)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (allocBytes1Events_groupSpec cliIoReadFileEnv_nonFreeBound initialStateEnv_groupSpec
   optTailCloneEvents_groupSpec readFileRuleEnv_nonFreeBound recordSerializeDomFineGrpS
   serializeSomeSeqFreeEnv_groupSpec vecCloneEvents_groupSpec w3BoxedStoreStepEnv_groupSpec
   w3InitiateFullEnv_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit (specCliIoReadSchedule_events_eq)
open LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers
  (cliIoCapEvents cliIoReadCaps phaseCreditSpec_cliIoReadFile_tight)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (NonFreeBound nonFreeCount nonFreeCount_append nonFreeCount_nil nonFreeCount_rustAllocEvents
   nonFreeCount_rustDeallocEvents nonFreeCount_rustReallocEvents)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (DeallocCreditSpec ModelHyps)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (allocBytes1_fine_phaseCredit_tight optLargeCost_fine_of_le)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (rustAllocTightCum rustAllocTightCum_fine_le_738)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (PhaseCreditSpec.recordSerialize_seqFree_tight RecordSerializeSeqFreeEnv
   recordSerializeMaxReq recordSerializeTightCum)
open LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec
  (w3BoxedStoreStep_phaseCredit w3SpqrInit32_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
  (phaseCreditSpec_seq_freeOnly phaseCreditSpec_w3InitiateFull_small)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec
  (AliceInitiatedBounds RecordAliceInitiatedBounds recordSerializeMaxReq_aliceInitiated_le_3820
   recordSerializeTightCum_aliceInitiated_le_31747)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (IdentityKeyPairTryFromEnv IkpSubEnv RecordCodecErrStep RecordCodecLoopEnv
   ikpSubEnv_phaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (deserCancelFineCum deserCancelFineGrpS deserCancelFineLive deserCancelFineMaxReq
   deserCancelFinePeak recordDeserializeCancelEnv_fine_groupSpec
   recordDeserializeCancelEnv_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
  (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
  (DirGetAfterReadEnv DirGetErrAllocEnv DirGetMissEnv DirGetPathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
  (pathAppendNameEvents pathEvents pathPushSlashEvents pathToOwnedEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv DirPutTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (OverCapFile cliRd_ok_le_fileCap readFileOverCapEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSaveTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
  (OptIkpTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
  (OptRegIdMalformedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget (OptLoadDeserEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
  (addrTextValEnv_decimal_fine_phaseCredit_tight addrTextValEnv_decimal_groupSpec
   dirGetEnv_path_readFile_fine_phaseCredit_tight pathEnv_fine_phaseCredit_tight)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
  (chainCloneEvents senderChainAsProtoGhost senderChainCloneEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (SegCloneEnv segCloneEvents)

private theorem s3_byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
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

private theorem s3_utf8_length (s : String) :
    (utf8 s).length = (s.toList.flatMap String.utf8EncodeChar).length := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, List.utf8Encode, s3_byteArray_toList_eq_data]

private theorem s3_seqEnv_mono {A₁ A₂ B₁ B₂ : List AllocEvent → Prop}
    (hA : ∀ evs, A₁ evs → A₂ evs) (hB : ∀ evs, B₁ evs → B₂ evs) :
    ∀ {evs}, SeqEnv A₁ B₁ evs → SeqEnv A₂ B₂ evs
  | _, Or.inl ha => Or.inl (hA _ ha)
  | _, Or.inr ⟨e1, e2, rfl, ha, hb⟩ => Or.inr ⟨e1, e2, rfl, hA _ ha, hB _ hb⟩

private theorem s3_phaseGroupSpec_append_eq (M : AllocCostModel) [HasFineGroupCredit M]
    {e₁ e₂ : List AllocEvent} {g₁ g₂ : Nat}
    (h₁ : PhaseGroupSpec M (· = e₁) g₁) (h₂ : PhaseGroupSpec M (· = e₂) g₂) :
    PhaseGroupSpec M (· = e₁ ++ e₂) (g₁ + g₂) :=
  (h₁.concat h₂).of_imp fun _ h => ⟨e₁, e₂, h, rfl, rfl⟩

/-- Tight credit bound for `DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd`. -/
private theorem s3_dirGetFixed_credit
    (rd : ReadRule) (F0 : FsFiles) (dir : DirGhost) (name : List (BitVec 8))
    {maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps 64 maxEntries maxVal dir)
    (hname : name.length ≤ 64)
    (hcap : ∀ bs, rd F0 (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    let fc := max maxVal fileCap
    PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd F0 dir name)
      (21185 + max (573818 + 738) (fineReadFileCum fc))
      (fineReadFileLive fc)
      (max 3162118 (fineReadFilePeak fc))
      (max 2097152 (fineReadFileMaxReq fc)) := by
  dsimp only
  have hbase := dirGetEnv_path_readFile_fine_phaseCredit_tight rd F0 dir name hdc hname hcap
  dsimp only at hbase
  unfold DirGetEnv at hbase ⊢
  cases hfind : dir.changed.find? (fun e => e.1 == name) with
  | some e =>
    rw [hfind] at hbase
    exact hbase.mono (by omega) (Nat.le_refl _) (Nat.le_max_right _ _)
      (by have := Nat.le_max_right 256 (fineReadFileMaxReq (max maxVal fileCap)); omega)
  | none =>
    rw [hfind] at hbase
    cases hrd : rd F0 (pathOf dir.path name) with
    | ok bs =>
      have himp : ∀ evs,
          DirGetMissEnv PathEnv (ReadFileRuleEnvFixed rd) rd F0 dir name evs →
          DirGetMissEnv PathEnv (ReadFileRuleEnv rd) rd F0 dir name evs := by
        intro evs hm
        unfold DirGetMissEnv at hm ⊢
        exact s3_seqEnv_mono (fun _ h => h)
          (fun _ hr => s3_seqEnv_mono
            (fun _ hrf => hrf.elim id fun ⟨herr, _, _⟩ => by rw [hrd] at herr; cases herr)
            (fun _ h => h) hr) hm
      exact (hbase.of_imp himp).mono (by omega) (Nat.le_refl _) (Nat.le_max_right _ _)
        (by have := Nat.le_max_right 256 (fineReadFileMaxReq (max maxVal fileCap)); omega)
    | error u =>
      cases u
      unfold DirGetMissEnv
      have hp : PhaseCreditSpec fineCostModel
          (DirGetPathEnv PathEnv dir.path name) 21185 0 0 256 := by
        unfold DirGetPathEnv
        split_ifs
        · have hab := allocBytes1_fine_phaseCredit_tight hname
          rw [optLargeCost_fine_of_le (by decide)] at hab
          exact hab.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
        · exact pathEnv_fine_phaseCredit_tight hdc.path_len_le hname
      have hrFix : PhaseCreditSpec fineCostModel
          (ReadFileRuleEnvFixed rd F0 (pathOf dir.path name)) 573818 0 3162118 2097152 := by
        have hr0 : PhaseCreditSpec fineCostModel
            (ReadFileRuleEnv rd F0 (pathOf dir.path name)) 0 0 0 0 :=
          PhaseCreditSpec.of_eq_nil (fun _ h => by unfold ReadFileRuleEnv at h; rw [hrd] at h; exact h)
        have hlc2M : 2105347 ≤ 0 + HasFineReallocCredit.largeCost fineCostModel 2097152 := by
          rw [fineCostModel_largeCost_eq]
        have hcio : PhaseCreditSpec fineCostModel
            (· = cliIoCapEvents (cliIoReadCaps 9 2097152))
            573818 (0 + HasFineReallocCredit.largeCost fineCostModel 2097152) 3162118 2097152 :=
          (phaseCreditSpec_cliIoReadFile_tight fineCostModel_modelHyps
            (by rw [fineCostModel_smallMaxReq_eq]; decide)
            (by rw [fineCostModel_smallMaxReq_eq]; decide)
            2097152).mono (Nat.le_refl _) hlc2M (Nat.le_refl _) (Nat.le_refl _)
        have hfree : DeallocCreditSpec fineCostModel
            (· = rustDeallocEvents 2097152 1)
            (HasFineReallocCredit.largeCost fineCostModel 2097152) :=
          DeallocCreditSpec.free_large fineCostModel (req := 2097152) (al := 1)
            (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)
        have hover : PhaseCreditSpec fineCostModel
            (fun evs => rd F0 (pathOf dir.path name) = .error () ∧
              OverCapFile F0 (pathOf dir.path name) ∧ evs = readFileOverCapEvents)
            573818 0 3162118 2097152 :=
          (hcio.concat_dealloc_cancel hfree).of_imp fun _ ⟨_, _, heq⟩ => by
            rw [heq]; unfold readFileOverCapEvents
            rw [specCliIoReadSchedule_events_eq 9 2097152]
            exact ⟨_, _, rfl, rfl, rfl⟩
        exact (hr0.or hover).mono (by decide) (Nat.le_refl 0) (by decide) (by decide)
      have herr22 : PhaseCreditSpec fineCostModel
          (DirGetAfterReadEnv rd F0 (pathOf dir.path name)) 738 0 0 22 := by
        unfold DirGetAfterReadEnv DirGetErrAllocEnv
        rw [hrd]
        have ha22 := PhaseCreditSpec.rustAlloc_small fineCostModel
          (req := 22) (al := 1) (by decide) (by decide)
          (by rw [fineCostModel_smallMaxReq_eq]; decide)
        have hc22 : HasFineReallocCredit.smallAllocCost fineCostModel 22 ≤ 738 := by
          have h738 := rustAllocTightCum_fine_le_738 (req := 22) (by decide)
          unfold rustAllocTightCum at h738
          rw [fineCostModel_smallMaxReq_eq] at h738
          simpa using h738
        exact phaseCreditSpec_seq_freeOnly fineCostModel_modelHyps
          (ha22.mono hc22 (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 22))
      exact (hp.seq (hrFix.seq herr22)).mono
        (by omega) (Nat.zero_le _) (Nat.le_max_left 3162118 _)
        (Nat.max_le.mpr ⟨Nat.le_trans (by decide : 256 ≤ 2097152) (Nat.le_max_left 2097152 _),
          Nat.le_trans (by decide : max 2097152 22 ≤ 2097152) (Nat.le_max_left 2097152 _)⟩)

/-- Group bound for `DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd`. -/
private theorem s3_dirGetFixed_groups (M : AllocCostModel) [HasFineGroupCredit M]
    (rd : ReadRule) (F0 : FsFiles) (dir : DirGhost) (name : List (BitVec 8)) :
    PhaseGroupSpec M (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd F0 dir name)
      (42 * FineScale) := by
  have hPath : PhaseGroupSpec M (DirGetPathEnv PathEnv dir.path name) (9 * FineScale) := by
    unfold DirGetPathEnv
    split_ifs
    · exact (allocBytes1Events_groupSpec M name).mono (by omega)
    · unfold PathEnv pathEvents
      have p1 : PhaseGroupSpec M (· = pathToOwnedEvents dir.path.length) (3 * FineScale) := by
        unfold pathToOwnedEvents
        split
        · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
        · exact PhaseGroupSpec.rustAlloc_any M _ 1
      have p2 : PhaseGroupSpec M (· = pathPushSlashEvents dir.path.length) (3 * FineScale) := by
        unfold pathPushSlashEvents
        split
        · exact PhaseGroupSpec.rustAlloc_any M _ 1
        · exact PhaseGroupSpec.rustRealloc_any M _ _ 1
      have p3 : PhaseGroupSpec M
          (· = pathAppendNameEvents dir.path.length name.length) (3 * FineScale) := by
        unfold pathAppendNameEvents
        dsimp only
        split
        · exact PhaseGroupSpec.rustRealloc_any M _ _ 1
        · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
      exact (s3_phaseGroupSpec_append_eq M p1 (s3_phaseGroupSpec_append_eq M p2 p3)).mono (by omega)
  have hRead : PhaseGroupSpec M (ReadFileRuleEnvFixed rd F0 (pathOf dir.path name))
      (30 * FineScale) := by
    have hnf : NonFreeBound (ReadFileRuleEnvFixed rd F0 (pathOf dir.path name)) 10 := by
      rintro evs (h1 | ⟨_, _, rfl⟩)
      · exact readFileRuleEnv_nonFreeBound rd F0 (pathOf dir.path name) evs h1
      · unfold readFileOverCapEvents
        rw [nonFreeCount_append, nonFreeCount_rustDeallocEvents, Nat.add_zero,
            specCliIoReadSchedule_events_eq 9 2097152]
        exact cliIoReadFileEnv_nonFreeBound 2097152 _ rfl
    exact (PhaseGroupSpec.of_nonFreeBound M hnf).mono (by omega)
  have hAfter : PhaseGroupSpec M (DirGetAfterReadEnv rd F0 (pathOf dir.path name))
      (3 * FineScale) := by
    unfold DirGetAfterReadEnv DirGetErrAllocEnv
    cases rd F0 (pathOf dir.path name) with
    | ok _ =>
      exact ((PhaseGroupSpec.nil M).seq (PhaseGroupSpec.freeOnly M)).mono (Nat.zero_le _)
    | error u =>
      cases u
      exact ((PhaseGroupSpec.rustAlloc_any M 22 1).seq (PhaseGroupSpec.freeOnly M)).mono (by omega)
  unfold DirGetEnv
  cases dir.changed.find? (fun e => e.1 == name) with
  | some e => exact (allocBytes1Events_groupSpec M e.2).mono (by omega)
  | none =>
    unfold DirGetMissEnv
    exact (hPath.seq (hRead.seq hAfter)).mono (by omega)

private theorem s3_stepEvents_small_live_peak_nonInc
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {maxReq : Nat} (hsmall : maxReq ≤ HasFineReallocCredit.smallMaxReq M) :
    ∀ (evs : List AllocEvent) (st : M.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤ HasFineReallocCredit.liveLarge st ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤ HasFineReallocCredit.peakLarge st
  | [], st, _ => ⟨Nat.le_refl _, Nat.le_refl _⟩
  | ev :: tl, st, ha => by
    have hev := ha ev List.mem_cons_self
    have htl : ∀ e ∈ tl, eventStepReq e ≤ maxReq ∧ eventStepAlign e ≤ 16 :=
      fun e he => ha e (List.mem_cons_of_mem _ he)
    have h1 :
        HasFineReallocCredit.liveLarge (M.step ev st) ≤ HasFineReallocCredit.liveLarge st ∧
        HasFineReallocCredit.peakLarge (M.step ev st) ≤ HasFineReallocCredit.peakLarge st := by
      cases ev with
      | free al sz =>
        obtain ⟨_, hl, hp⟩ := hM.freeNonInc al sz st
        exact ⟨hl, hp⟩
      | alloc req =>
        simp only [eventStepReq] at hev
        obtain ⟨_, hl, hp⟩ := hM.step_alloc_small_any st (Nat.le_trans hev.1 hsmall)
        exact ⟨hl, hp⟩
      | aligned al req =>
        simp only [eventStepReq, eventStepAlign] at hev
        obtain ⟨_, hl, hp⟩ := hM.step_aligned_small_any st hev.2 (Nat.le_trans hev.1 hsmall)
        exact ⟨hl, hp⟩
      | realloc al old new =>
        simp only [eventStepReq, eventStepAlign] at hev
        have hnew : new ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hev.1 hsmall
        by_cases hold : old ≤ HasFineReallocCredit.smallMaxReq M
        · obtain ⟨_, hl, hp⟩ := hM.step_realloc_small_small_any st hev.2 hold hnew
          exact ⟨hl, hp⟩
        · have hold' : HasFineReallocCredit.smallMaxReq M < old := Nat.lt_of_not_le hold
          obtain ⟨_, hl, hp⟩ := hM.step_realloc_large_small_any st hev.2 hold' hnew
          exact ⟨by omega, hp⟩
    obtain ⟨hl₂, hp₂⟩ := s3_stepEvents_small_live_peak_nonInc hM hsmall tl (M.step ev st) htl
    simp only [AllocCostModel.stepEvents_cons]
    exact ⟨Nat.le_trans hl₂ h1.1, Nat.le_trans hp₂ h1.2⟩

private theorem s3_phaseCreditSpec_zero_live_peak_of_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E : List AllocEvent → Prop} {c l p r : Nat}
    (hspec : PhaseCreditSpec M E c l p r)
    (hsmall : r ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M E c 0 0 r where
  req_align := hspec.req_align
  credit_le st0 {evs} hE := by
    obtain ⟨hc, _, _⟩ := hspec.credit_le st0 hE
    obtain ⟨hl, hp⟩ :=
      s3_stepEvents_small_live_peak_nonInc hM hsmall evs st0 (hspec.req_align evs hE)
    exact ⟨hc, by omega, by omega⟩

private theorem s3_phaseCreditSpec_exists {α : Type}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {P : α → Prop} {E : α → List AllocEvent → Prop} {c l p r : Nat}
    (h : ∀ a, P a → PhaseCreditSpec M (E a) c l p r) :
    PhaseCreditSpec M (fun evs => ∃ a, P a ∧ E a evs) c l p r where
  req_align evs := fun ⟨a, ha, hE⟩ => (h a ha).req_align evs hE
  credit_le st0 := fun ⟨a, ha, hE⟩ => (h a ha).credit_le st0 hE

private theorem s3_phaseGroupSpec_exists {α : Type}
    {M : AllocCostModel} [HasFineGroupCredit M]
    {P : α → Prop} {E : α → List AllocEvent → Prop} {g : Nat}
    (h : ∀ a, P a → PhaseGroupSpec M (E a) g) :
    PhaseGroupSpec M (fun evs => ∃ a, P a ∧ E a evs) g where
  groups_le st0 := fun ⟨a, ha, hE⟩ => (h a ha).groups_le st0 hE

private theorem s3_dirDomainCaps_64 {maxDir maxEntries maxVal : Nat} {dir : DirGhost}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hle : maxDir ≤ 64) :
    DirDomainCaps 64 maxEntries maxVal dir :=
  ⟨Nat.le_trans hdc.path_len_le hle, hdc.changed_len_le, hdc.changed_val_le⟩

private theorem s3_rustAlloc_small_credit {req al : Nat}
    (hal : al ≤ 16) (hsmall : req ≤ 3820) :
    PhaseCreditSpec fineCostModel (· = rustAllocEvents req al) 9789 0 0 req := by
  by_cases hpos : 0 < req
  · have ha := PhaseCreditSpec.rustAlloc_small fineCostModel
      (req := req) (al := al) hal hpos
      (by rw [fineCostModel_smallMaxReq_eq]; omega)
    have hc : HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 9789 :=
      LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.fineSmallAllocCost_le_9789_of_le_3820
        hsmall
    exact ha.mono hc (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl req)
  · have hz : req = 0 := by omega
    subst hz
    refine ⟨?_, ?_⟩
    · intro evs h ev hev
      rw [h] at hev; unfold rustAllocEvents at hev
      split at hev
      · simp only [List.mem_singleton] at hev; subst hev
        simp [eventStepReq, eventStepAlign]
      · simp only [List.mem_singleton] at hev; subst hev
        simp [eventStepReq, eventStepAlign]; omega
    · intro st0 evs h
      rw [h]; unfold rustAllocEvents
      have hc0 : HasFineReallocCredit.smallAllocCost fineCostModel 0 ≤ 9789 :=
        LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec.fineSmallAllocCost_le_9789_of_le_3820
          (Nat.zero_le _)
      split
      · obtain ⟨hc, hl, hp⟩ := fineCostModel_modelHyps.step_alloc_small_any st0 (Nat.zero_le _)
        simp only [AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
        exact ⟨by omega, by omega, by omega⟩
      · obtain ⟨hc, hl, hp⟩ := fineCostModel_modelHyps.step_aligned_small_any st0
          (by omega : max al 8 ≤ 16) (Nat.zero_le _)
        simp only [AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
        exact ⟨by omega, by omega, by omega⟩

private theorem s3_dirPut_opened_credit {dir : DirGhost} (hch : dir.changed = [])
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
  exact ((PhaseCreditSpec.nil fineCostModel).or
    (s3_rustAlloc_small_credit (req := 192) (al := 8) (by decide) (by decide))).of_imp himp
    |>.mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by decide)

private theorem s3_dirPut_opened_groups (M : AllocCostModel) [HasFineGroupCredit M]
    {dir : DirGhost} (hch : dir.changed = []) (name bytes : List (BitVec 8)) :
    PhaseGroupSpec M (DirPutEnv dir name bytes) (3 * FineScale) := by
  have himp : ∀ evs, DirPutEnv dir name bytes evs →
      evs = [] ∨ evs = rustAllocEvents 192 8 := by
    intro evs h
    unfold DirPutEnv DirPutTailEnv at h
    simp only [hch, List.not_mem_nil, IsEmpty.forall_iff, implies_true, ↓reduceIte,
      List.length_nil] at h
    rcases h with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  exact ((PhaseGroupSpec.nil M).or (PhaseGroupSpec.rustAlloc_any M 192 8)).of_imp himp
    |>.mono (by omega)

private theorem s3_dirPutStr_opened_credit {dir : DirGhost} (hch : dir.changed = [])
    {name : List (BitVec 8)} (hname : name.length ≤ 64) (bytes : List (BitVec 8)) :
    PhaseCreditSpec fineCostModel (DirPutStrEnv dir name bytes) 19578 0 0 192 := by
  unfold DirPutStrEnv
  split_ifs with hnil
  · exact (s3_dirPut_opened_credit hch name bytes).mono (by decide)
      (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
  · have ha := s3_rustAlloc_small_credit (req := name.length) (al := 1)
      (by decide) (Nat.le_trans hname (by decide))
    exact (ha.seq (s3_dirPut_opened_credit hch name bytes)).mono
      (by decide : 9789 + 9789 ≤ 19578) (Nat.le_refl 0) (Nat.le_refl 0)
      (Nat.max_le.mpr ⟨Nat.le_trans hname (by decide), Nat.le_refl 192⟩)

private theorem s3_dirPutStr_opened_groups (M : AllocCostModel) [HasFineGroupCredit M]
    {dir : DirGhost} (hch : dir.changed = []) (name bytes : List (BitVec 8)) :
    PhaseGroupSpec M (DirPutStrEnv dir name bytes) (6 * FineScale) := by
  unfold DirPutStrEnv
  split_ifs
  · exact (s3_dirPut_opened_groups M hch name bytes).mono (by omega)
  · exact ((PhaseGroupSpec.rustAlloc_any M name.length 1).seq
      (s3_dirPut_opened_groups M hch name bytes)).mono (by omega)

private theorem s3_recordCodecLoop_nonFree {budget maxLen : Nat} {evs : List AllocEvent}
    (h : RecordCodecLoopEnv budget maxLen evs) : nonFreeCount evs ≤ budget := by
  induction h with
  | nil => exact Nat.zero_le _
  | @step budget _ evs₁ evs₂ h1 _ ih =>
    have hc1 : nonFreeCount evs₁ ≤ 1 := by
      cases h1 with
      | nil => simp [nonFreeCount_nil]
      | fromErr => simp [nonFreeCount_rustAllocEvents]
      | push0 hp =>
        rcases hp with rfl | ⟨_, rfl⟩ | ⟨hpos, _⟩
        · simp [nonFreeCount_nil]
        · simp [nonFreeCount_rustAllocEvents]
        · omega
    rw [nonFreeCount_append]
    omega
  | @bytesStep budget _ wt valCap bs v rest evs₁ evs₂ hm _ heq _ ih =>
    subst heq
    have hc1 : nonFreeCount (bytesMergeEventsCore wt valCap bs) ≤ 2 * v.length + 1 := by
      unfold bytesMergeEventsCore
      rw [hm]
      by_cases hv0 : v.length = 0
      · simp [hv0, nonFreeCount_nil]
      · simp only [hv0, ↓reduceIte, List.append_assoc, nonFreeCount_append]
        have h1 : nonFreeCount (rustAllocEvents v.length 1) = 1 :=
          nonFreeCount_rustAllocEvents v.length 1
        have h2' : nonFreeCount (doReserveClearEvents valCap.toNat v.length) ≤ 1 := by
          unfold doReserveClearEvents
          split
          · simp [nonFreeCount_nil]
          · split <;> simp [nonFreeCount_rustAllocEvents, nonFreeCount_rustReallocEvents]
        have h3 : nonFreeCount (rustDeallocEvents v.length 1) = 0 :=
          nonFreeCount_rustDeallocEvents v.length 1
        omega
    rw [nonFreeCount_append]
    omega

private theorem s3_ikpTryFrom_credit {gr : Except Unit (List (BitVec 8))}
    (hikp : ∀ bs, gr = .ok bs → bs.length ≤ 105) :
    PhaseCreditSpec fineCostModel (OptIkpTryFromEnv gr) 4070430 0 0 218 := by
  unfold OptIkpTryFromEnv
  cases hgr : gr with
  | error u =>
    exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | ok bs =>
    have hbs : bs.length ≤ 105 := hikp bs hgr
    have hsub : ∀ evs, IdentityKeyPairTryFromEnv bs.length evs → IkpSubEnv 213 105 evs := by
      rintro evs ⟨evsL, evsC, hL, hC, rfl⟩
      exact ⟨evsL, evsC, (hL.mono_fuel (by omega)).mono_maxLen hbs, hC, rfl⟩
    have hcr := (ikpSubEnv_phaseCreditSpec fineCostModel_modelHyps 213 105).of_imp hsub
    have hzero := s3_phaseCreditSpec_zero_live_peak_of_small fineCostModel_modelHyps hcr
      (by rw [fineCostModel_smallMaxReq_eq]; decide)
    exact hzero.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

private theorem s3_ikpTryFrom_groups (M : AllocCostModel) [HasFineGroupCredit M]
    {gr : Except Unit (List (BitVec 8))}
    (hikp : ∀ bs, gr = .ok bs → bs.length ≤ 105) :
    PhaseGroupSpec M (OptIkpTryFromEnv gr) (639 * FineScale) := by
  unfold OptIkpTryFromEnv
  cases hgr : gr with
  | error u => exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
  | ok bs =>
    have hbs : bs.length ≤ 105 := hikp bs hgr
    have hnf : NonFreeBound (IdentityKeyPairTryFromEnv bs.length) 213 := by
      rintro evs ⟨evsL, evsC, hL, hC, rfl⟩
      have hcL : nonFreeCount evsL ≤ 2 * bs.length + 3 := s3_recordCodecLoop_nonFree hL
      have hcC : nonFreeCount evsC = 0 := by
        rcases hC with ⟨e1, e2, h1, h2, rfl⟩ | ⟨_, eD, ⟨e1, e2, h1, h2, rfl⟩, hD, rfl⟩
        · have f1 : nonFreeCount e1 = 0 := by
            rcases h1 with rfl | ⟨_, _, _, rfl⟩
            · rfl
            · rfl
          have f2 : nonFreeCount e2 = 0 := by
            rcases h2 with rfl | ⟨_, _, _, rfl⟩
            · rfl
            · rfl
          simp [nonFreeCount_append, f1, f2]
        · have f1 : nonFreeCount e1 = 0 := by
            rcases h1 with rfl | ⟨_, _, _, rfl⟩
            · rfl
            · rfl
          have f2 : nonFreeCount e2 = 0 := by
            rcases h2 with rfl | ⟨_, _, _, rfl⟩
            · rfl
            · rfl
          have fD : nonFreeCount eD = 0 := by
            rcases hD with rfl | ⟨_, _, _, rfl⟩ <;>
              simp [nonFreeCount_append, nonFreeCount_rustDeallocEvents]
          simp [nonFreeCount_append, f1, f2, fD]
      rw [nonFreeCount_append, hcC]
      omega
    exact (PhaseGroupSpec.of_nonFreeBound M hnf).mono (by omega)

end S3aHelpers

private def s3a_spkRank (c : Nat) : Nat :=
  if 4900 ≤ c then 0
  else if 4096 ≤ c then 1
  else if 2048 ≤ c then 2
  else if 1024 ≤ c then 3
  else if 512 ≤ c then 4
  else if 256 ≤ c then 5
  else if 128 ≤ c then 6
  else if 64 ≤ c then 7
  else if 32 ≤ c then 8
  else if 16 ≤ c then 9
  else if 8 ≤ c then 10
  else if 4 ≤ c then 11
  else if 2 ≤ c then 12
  else if 1 ≤ c then 13
  else 14

private theorem s3a_spkRank_spec (c : Nat) :
    (4900 ≤ c ∧ s3a_spkRank c = 0) ∨
    (4096 ≤ c ∧ c < 4900 ∧ s3a_spkRank c = 1) ∨
    (2048 ≤ c ∧ c < 4096 ∧ s3a_spkRank c = 2) ∨
    (1024 ≤ c ∧ c < 2048 ∧ s3a_spkRank c = 3) ∨
    (512 ≤ c ∧ c < 1024 ∧ s3a_spkRank c = 4) ∨
    (256 ≤ c ∧ c < 512 ∧ s3a_spkRank c = 5) ∨
    (128 ≤ c ∧ c < 256 ∧ s3a_spkRank c = 6) ∨
    (64 ≤ c ∧ c < 128 ∧ s3a_spkRank c = 7) ∨
    (32 ≤ c ∧ c < 64 ∧ s3a_spkRank c = 8) ∨
    (16 ≤ c ∧ c < 32 ∧ s3a_spkRank c = 9) ∨
    (8 ≤ c ∧ c < 16 ∧ s3a_spkRank c = 10) ∨
    (4 ≤ c ∧ c < 8 ∧ s3a_spkRank c = 11) ∨
    (2 ≤ c ∧ c < 4 ∧ s3a_spkRank c = 12) ∨
    (1 ≤ c ∧ c < 2 ∧ s3a_spkRank c = 13) ∨
    (c = 0 ∧ s3a_spkRank c = 14) := by
  by_cases h0 : 4900 ≤ c; · left; exact ⟨h0, by simp [s3a_spkRank, h0]⟩
  right; by_cases h1 : 4096 ≤ c; · left; exact ⟨h1, by omega, by simp [s3a_spkRank, h0, h1]⟩
  right; by_cases h2 : 2048 ≤ c; · left; exact ⟨h2, by omega, by simp [s3a_spkRank, h0, h1, h2]⟩
  right; by_cases h3 : 1024 ≤ c; · left; exact ⟨h3, by omega, by simp [s3a_spkRank, h0, h1, h2, h3]⟩
  right; by_cases h4 : 512 ≤ c; · left; exact ⟨h4, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4]⟩
  right; by_cases h5 : 256 ≤ c; · left; exact ⟨h5, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5]⟩
  right; by_cases h6 : 128 ≤ c; · left; exact ⟨h6, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6]⟩
  right; by_cases h7 : 64 ≤ c; · left; exact ⟨h7, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6, h7]⟩
  right; by_cases h8 : 32 ≤ c; · left; exact ⟨h8, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6, h7, h8]⟩
  right; by_cases h9 : 16 ≤ c; · left; exact ⟨h9, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]⟩
  right; by_cases h10 : 8 ≤ c; · left; exact ⟨h10, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]⟩
  right; by_cases h11 : 4 ≤ c; · left; exact ⟨h11, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]⟩
  right; by_cases h12 : 2 ≤ c; · left; exact ⟨h12, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]⟩
  right; by_cases h13 : 1 ≤ c
  · left; exact ⟨h13, by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]⟩
  · right; exact ⟨by omega, by simp [s3a_spkRank, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]⟩

private theorem s3a_spkRank_le_14 (c : Nat) : s3a_spkRank c ≤ 14 := by
  have := s3a_spkRank_spec c
  omega

private theorem s3a_spkRank_step {c v nc : Nat}
    (hcv : c < v) (hv : v ≤ 4900) (h2c : 2 * c ≤ nc) (hvn : v ≤ nc) :
    s3a_spkRank nc + 1 ≤ s3a_spkRank c := by
  have := s3a_spkRank_spec c
  have := s3a_spkRank_spec nc
  omega

private def s3a_spkPot (caps : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps) : Nat :=
  s3a_spkRank caps.pub + s3a_spkRank caps.priv + s3a_spkRank caps.sig

private theorem s3a_spkPot_zero :
    s3a_spkPot LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.zero = 42 := by
  decide

private theorem s3a_spkPot_set_step
    {caps : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps}
    {f : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkField}
    {v nc : Nat}
    (hcv : caps.get f < v) (hv : v ≤ 4900) (h2c : 2 * caps.get f ≤ nc) (hvn : v ≤ nc) :
    s3a_spkPot (caps.set f nc) + 1 ≤ s3a_spkPot caps := by
  have hstep := s3a_spkRank_step hcv hv h2c hvn
  cases f <;> simp only [s3a_spkPot,
    LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.get,
    LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.set] at hstep ⊢ <;> omega

private theorem s3a_optByteFree_freeOnly {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.DepsBudget.OptByteFreeEnv evs) :
    LibsignalBinary.Heap.FreeOnlyEvs evs := by
  rcases h with rfl | ⟨cap, _, _, rfl⟩
  · intro _ hm; nomatch hm
  · intro ev hm
    simp only [LibsignalBinary.Heap.rustDeallocEvents, List.mem_singleton] at hm
    exact ⟨1, cap, hm⟩

private theorem s3a_twoOptByteFree_freeOnly {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.DepsBudget.TwoOptByteFreeEnv evs) :
    LibsignalBinary.Heap.FreeOnlyEvs evs := by
  rcases h with ⟨e1, e2, h1, h2, rfl⟩
  intro ev hm
  rcases List.mem_append.mp hm with hm1 | hm2
  · exact s3a_optByteFree_freeOnly h1 ev hm1
  · exact s3a_optByteFree_freeOnly h2 ev hm2

private theorem s3a_dropDecodeError_freeOnly {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.DropDecodeErrorEnv evs) :
    LibsignalBinary.Heap.FreeOnlyEvs evs := by
  rcases h with rfl | ⟨c, _, _, rfl⟩
  · intro ev hm
    simp only [LibsignalBinary.Heap.rustDeallocEvents, List.mem_singleton] at hm
    exact ⟨8, 72, hm⟩
  · intro ev hm
    simp only [LibsignalBinary.Heap.rustDeallocEvents, List.mem_append, List.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact ⟨8, c * 32, rfl⟩
    · exact ⟨8, 72, rfl⟩

private theorem s3a_signedOptByteFree_freeOnly {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.OptByteFreeEnv evs) :
    LibsignalBinary.Heap.FreeOnlyEvs evs := by
  rcases h with rfl | ⟨cap, _, _, rfl⟩
  · intro _ hm; nomatch hm
  · intro ev hm
    simp only [LibsignalBinary.Heap.rustDeallocEvents, List.mem_singleton] at hm
    exact ⟨1, cap, hm⟩

private theorem s3a_spkEpilogue_freeOnly {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkEpilogueFreeEnv evs) :
    LibsignalBinary.Heap.FreeOnlyEvs evs := by
  rcases h with ⟨e1, e2, e3, h1, h2, h3, rfl⟩
  intro ev hm
  rcases List.mem_append.mp hm with hm12 | hm3
  · rcases List.mem_append.mp hm12 with hm1 | hm2
    · exact s3a_signedOptByteFree_freeOnly h1 ev hm1
    · exact s3a_signedOptByteFree_freeOnly h2 ev hm2
  · exact s3a_signedOptByteFree_freeOnly h3 ev hm3

private theorem s3a_errCleanup_freeOnly {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecErrCleanupEnv evs) :
    LibsignalBinary.Heap.FreeOnlyEvs evs := by
  rcases h with ⟨eF, eD, hF, hD, rfl⟩
  intro ev hm
  rcases List.mem_append.mp hm with hmF | hmD
  · exact s3a_twoOptByteFree_freeOnly hF ev hmF
  · exact s3a_dropDecodeError_freeOnly hD ev hmD

private theorem s3a_ikpPostCleanup_freeOnly {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.DepsBudget.IkpPostCleanupEnv evs) :
    LibsignalBinary.Heap.FreeOnlyEvs evs := by
  rcases h with h1 | h2
  · exact s3a_twoOptByteFree_freeOnly h1
  · exact s3a_errCleanup_freeOnly h2

section S3aHoleAHelpers

open CryptoVerification.SignalSession.Cli (keyName)
open LibsignalBinary.Heap (FreeOnlyEvs SeqEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (CliPkDecodeEnv CliSpkDecodeEnv W4BinaryRecvPrekeyDom W4BinaryRecvPrekeyParams
   W4BinaryRecvPrekeyPathBWideEnv W4BinaryStageP1UntrustedEnv)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W4BinaryKpkMarkStepEnvFixed W4BinaryRecvPrekeyPathAWideEnvFixed
   W4BinaryRecvPrekeyPathCWideEnvFixed W4BinaryRecvPrekeyWideSlotEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_freeNonInc fineCostModel_modelHyps)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
  (OptIkpTryFromEnv)

private def s3a_spkFuel4900 (c : Nat) : Nat :=
  if c < 8 then 11
  else if c < 16 then 10
  else if c < 32 then 9
  else if c < 64 then 8
  else if c < 128 then 7
  else if c < 256 then 6
  else if c < 512 then 5
  else if c < 1024 then 4
  else if c < 2048 then 3
  else if c < 4096 then 2
  else if c < 4900 then 1
  else 0

private theorem s3a_spkFuel4900_spec (c : Nat) :
    (c < 8 ∧ s3a_spkFuel4900 c = 11) ∨
    (8 ≤ c ∧ c < 16 ∧ s3a_spkFuel4900 c = 10) ∨
    (16 ≤ c ∧ c < 32 ∧ s3a_spkFuel4900 c = 9) ∨
    (32 ≤ c ∧ c < 64 ∧ s3a_spkFuel4900 c = 8) ∨
    (64 ≤ c ∧ c < 128 ∧ s3a_spkFuel4900 c = 7) ∨
    (128 ≤ c ∧ c < 256 ∧ s3a_spkFuel4900 c = 6) ∨
    (256 ≤ c ∧ c < 512 ∧ s3a_spkFuel4900 c = 5) ∨
    (512 ≤ c ∧ c < 1024 ∧ s3a_spkFuel4900 c = 4) ∨
    (1024 ≤ c ∧ c < 2048 ∧ s3a_spkFuel4900 c = 3) ∨
    (2048 ≤ c ∧ c < 4096 ∧ s3a_spkFuel4900 c = 2) ∨
    (4096 ≤ c ∧ c < 4900 ∧ s3a_spkFuel4900 c = 1) ∨
    (4900 ≤ c ∧ s3a_spkFuel4900 c = 0) := by
  by_cases h0 : c < 8; · left; exact ⟨h0, by simp [s3a_spkFuel4900, h0]⟩
  right; by_cases h1 : c < 16; · left; exact ⟨by omega, h1, by simp [s3a_spkFuel4900, h0, h1]⟩
  right; by_cases h2 : c < 32; · left; exact ⟨by omega, h2, by simp [s3a_spkFuel4900, h0, h1, h2]⟩
  right; by_cases h3 : c < 64; · left; exact ⟨by omega, h3, by simp [s3a_spkFuel4900, h0, h1, h2, h3]⟩
  right; by_cases h4 : c < 128; · left; exact ⟨by omega, h4, by simp [s3a_spkFuel4900, h0, h1, h2, h3, h4]⟩
  right; by_cases h5 : c < 256; · left; exact ⟨by omega, h5, by simp [s3a_spkFuel4900, h0, h1, h2, h3, h4, h5]⟩
  right; by_cases h6 : c < 512; · left; exact ⟨by omega, h6, by simp [s3a_spkFuel4900, h0, h1, h2, h3, h4, h5, h6]⟩
  right; by_cases h7 : c < 1024; · left; exact ⟨by omega, h7, by simp [s3a_spkFuel4900, h0, h1, h2, h3, h4, h5, h6, h7]⟩
  right; by_cases h8 : c < 2048; · left; exact ⟨by omega, h8, by simp [s3a_spkFuel4900, h0, h1, h2, h3, h4, h5, h6, h7, h8]⟩
  right; by_cases h9 : c < 4096; · left; exact ⟨by omega, h9, by simp [s3a_spkFuel4900, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]⟩
  right; by_cases h10 : c < 4900
  · left; exact ⟨by omega, h10, by simp [s3a_spkFuel4900, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]⟩
  · right; exact ⟨by omega, by simp [s3a_spkFuel4900, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]⟩

private theorem s3a_spkFuel4900_le_12 (c : Nat) : s3a_spkFuel4900 c ≤ 12 := by
  have := s3a_spkFuel4900_spec c
  omega

private theorem s3a_spkFuel4900_step_raw {c nc v : Nat}
    (hv : v ≤ 4900) (hlt : c < v) (hnc : nc = max (max v (2 * c)) 8) :
    s3a_spkFuel4900 nc + 1 ≤ s3a_spkFuel4900 c ∧ nc ≤ 9808 ∧ 1 ≤ nc := by
  have := s3a_spkFuel4900_spec c
  have := s3a_spkFuel4900_spec nc
  omega

private def s3a0_EntriesFromNorm (files : List (String × List (BitVec 8))) (fs : Arm64.FsState) :
    Prop :=
  ∀ k bs, fs.entries k = some (.file bs) → ∃ p, Arm64.normalizePath p = k ∧ (p, bs) ∈ files

private theorem s3a0_entriesFromNorm_empty (files : List (String × List (BitVec 8))) :
    s3a0_EntriesFromNorm files ({} : Arm64.FsState) := by
  intro k bs hk; dsimp only at hk; split at hk <;> cases hk

private theorem s3a0_entriesFromNorm_setEntry_dir {files : List (String × List (BitVec 8))}
    {fs : Arm64.FsState} (h : s3a0_EntriesFromNorm files fs) (pref : Arm64.FsPath) :
    s3a0_EntriesFromNorm files (fs.setEntry pref (some .dir)) := by
  intro k bs hk; unfold Arm64.FsState.setEntry at hk; dsimp only at hk
  split at hk
  · cases hk
  · exact h k bs hk

private theorem s3a0_entriesFromNorm_foldl_dirs {files : List (String × List (BitVec 8))}
    (prefs : List Arm64.FsPath) {fs : Arm64.FsState} (h : s3a0_EntriesFromNorm files fs) :
    s3a0_EntriesFromNorm files (prefs.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs) := by
  induction prefs generalizing fs with
  | nil => exact h
  | cons hd tl ih => exact ih (s3a0_entriesFromNorm_setEntry_dir h hd)

private theorem s3a0_entriesFromNorm_foldl_outer_dirs {files : List (String × List (BitVec 8))}
    (dirs : List String) {fs : Arm64.FsState} (h : s3a0_EntriesFromNorm files fs) :
    s3a0_EntriesFromNorm files
      (dirs.foldl
        (fun acc d => (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath d)).foldl
          (fun a pref => a.setEntry pref (some .dir)) acc) fs) := by
  induction dirs generalizing fs with
  | nil => exact h
  | cons hd tl ih => exact ih (s3a0_entriesFromNorm_foldl_dirs _ h)

private theorem s3a0_entriesFromNorm_setFile {files : List (String × List (BitVec 8))}
    {fs : Arm64.FsState} (h : s3a0_EntriesFromNorm files fs) {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ files) :
    s3a0_EntriesFromNorm files (fs.setFile p (some (.file bs))) := by
  intro k bs' hk; unfold Arm64.FsState.setFile Arm64.FsState.setEntry at hk; dsimp only at hk
  split at hk
  · rename_i heq
    have hk_eq : Arm64.normalizePath p = k := (beq_iff_eq.mp heq).symm
    injection hk with hfile; injection hfile with hbs; subst hbs
    exact ⟨p, hk_eq, hmem⟩
  · exact h k bs' hk

private theorem s3a0_entriesFromNorm_foldl_files {allFiles : List (String × List (BitVec 8))}
    (rem : List (String × List (BitVec 8)))
    (hsub : ∀ x ∈ rem, x ∈ allFiles)
    {fs : Arm64.FsState} (h : s3a0_EntriesFromNorm allFiles fs) :
    s3a0_EntriesFromNorm allFiles
      (rem.foldl
        (fun acc (p, bs) =>
          let withAnc :=
            ((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast).foldl
              (fun a pref => a.setEntry pref (some .dir)) acc
          withAnc.setFile p (some (.file bs))) fs) := by
  induction rem generalizing fs with
  | nil => exact h
  | cons hd tl ih =>
    rcases hd with ⟨p, bs⟩
    have hanc := s3a0_entriesFromNorm_foldl_dirs
      ((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast) h
    have hset := s3a0_entriesFromNorm_setFile hanc (hsub (p, bs) (List.mem_cons_self ..))
    exact ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hset

private theorem s3a0_initFsState_files_mem_norm {inputs : Arm64.Process.ProcessInputs} {q : String}
    {bs : List (BitVec 8)}
    (h : (Arm64.Process.initFsState inputs).files q = some (.file bs)) :
    ∃ p, Arm64.normalizePath p = Arm64.normalizePath q ∧ (p, bs) ∈ inputs.files := by
  have hd := s3a0_entriesFromNorm_foldl_outer_dirs inputs.dirs
    (s3a0_entriesFromNorm_empty inputs.files)
  have hf := s3a0_entriesFromNorm_foldl_files inputs.files (fun _ hx => hx) hd
  unfold Arm64.FsState.files Arm64.FsState.getEntry at h
  split at h
  · cases h
  · exact hf (Arm64.normalizePath q) bs h

private theorem s3a0_cliIo_rd_eq_ok_nil_or_files_some {i : Inputs} {path bs : List (BitVec 8)}
    (hrd : cliIo.rd (runFiles i) path = .ok bs) :
    bs = [] ∨
      (Arm64.Process.initFsState (CryptoVerification.SignalSession.Cli.cliInputs i)).files
        (CryptoVerification.SignalSession.Cli.MainHops.pathStr path) = some (.file bs) := by
  change CryptoVerification.SignalSession.Cli.MainHops.cliRd
      (Arm64.Process.initFsState (CryptoVerification.SignalSession.Cli.cliInputs i)).files path =
        .ok bs at hrd
  unfold CryptoVerification.SignalSession.Cli.MainHops.cliRd at hrd; split at hrd
  · cases hrd
  · rename_i rbs hrv; injection hrd with h; subst h
    unfold CryptoVerification.SignalSession.Cli.MainHops.readViewF at hrv; split at hrv
    · cases hrv
    · injection hrv with h; subst h; exact Or.inl rfl
    · split at hrv
      · rename_i fbs hfp
        split at hrv
        · injection hrv with h; subst h; exact Or.inr hfp
        · cases hrv
      · cases hrv
      · injection hrv with h; subst h; exact Or.inl rfl

private theorem s3a0_splitSlash_go_append_slash (cur a b : List Char) :
    Arm64.splitSlash.go cur (a ++ ('/' :: b)) =
      Arm64.splitSlash.go cur a ++ Arm64.splitSlash.go [] b := by
  induction a generalizing cur with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c = '/'
    · subst hc; simp only [List.cons_append, Arm64.splitSlash.go, ih []]
    · rw [List.cons_append, Arm64.splitSlash.go.eq_3 cur c (cs ++ '/' :: b) hc,
        Arm64.splitSlash.go.eq_3 cur c cs hc, ih (c :: cur)]

private theorem s3a0_normalizePath_append_slash (a b : String) :
    Arm64.normalizePath (a ++ "/" ++ b) = Arm64.normalizePath a ++ Arm64.normalizePath b := by
  have htl : (a ++ "/" ++ b).toList = a.toList ++ ('/' :: b.toList) := by
    simp [String.toList_append]
  unfold Arm64.normalizePath Arm64.splitSlash
  rw [htl, s3a0_splitSlash_go_append_slash [] a.toList b.toList, List.filter_append]

private theorem s3a0_splitSlash_go_no_slash :
    ∀ (cs cur : List Char), '/' ∉ cs →
      Arm64.splitSlash.go cur cs = [String.ofList (cur.reverse ++ cs)]
  | [], cur, _ => by simp [Arm64.splitSlash.go]
  | c :: cs, cur, h => by
    have hc : c ≠ '/' := fun he => h (he ▸ List.Mem.head _)
    rw [Arm64.splitSlash.go.eq_3 cur c cs hc,
      s3a0_splitSlash_go_no_slash cs (c :: cur) (fun hm => h (List.Mem.tail _ hm))]
    simp [List.reverse_cons, List.append_assoc]

private theorem s3a0_ofList_toList (s : String) : String.ofList s.toList = s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp

private theorem s3a0_normalizePath_single {s : String}
    (hns : '/' ∉ s.toList) (hne : s.toList ≠ []) (hnd : s ≠ ".") :
    Arm64.normalizePath s = [s] := by
  have hsp : Arm64.splitSlash s = [s] := by
    unfold Arm64.splitSlash
    rw [s3a0_splitSlash_go_no_slash s.toList [] hns, List.reverse_nil, List.nil_append,
      s3a0_ofList_toList]
  have hne_str : s.isEmpty = false := by
    rw [Bool.eq_false_iff]
    intro he
    have hs : s = "" := by simpa [String.isEmpty_iff] using he
    subst hs; exact hne (by decide)
  have hnd_b : (s != ".") = true := bne_iff_ne.mpr hnd
  unfold Arm64.normalizePath
  rw [hsp]
  simp [hne_str, hnd_b]

private theorem s3a0_cons_head_ne {a b : String} {xs ys : List String}
    (hne : a ≠ b) : a :: xs ≠ b :: ys := by
  intro h; injection h with hab _; exact hne hab

private theorem s3a0_singleton_ne_pair {a d s : String} : ([a] : List String) ≠ [d, s] := by
  intro h; injection h with _ h2; cases h2

private theorem s3a0_norm_subdir_ne_ikp {dir sub : String}
    (hdir : Arm64.normalizePath dir = [dir]) (hne : dir ≠ "identity-key-pair") :
    Arm64.normalizePath ((dir ++ "/") ++ sub) ≠ ["identity-key-pair"] := by
  rw [s3a0_normalizePath_append_slash dir sub, hdir, List.singleton_append]
  intro h; injection h with hd _; exact hne hd

private theorem s3a0_norm_subdir_eq {dir sub : String}
    (hdir : Arm64.normalizePath dir = [dir]) :
    Arm64.normalizePath ((dir ++ "/") ++ sub) = dir :: Arm64.normalizePath sub := by
  rw [s3a0_normalizePath_append_slash dir sub, hdir, List.singleton_append]

private theorem s3a0_norm_subdir_ne_pair {dir sub d s : String}
    (hdir : Arm64.normalizePath dir = [dir]) (hne : dir ≠ d) :
    Arm64.normalizePath ((dir ++ "/") ++ sub) ≠ [d, s] := by
  rw [s3a0_norm_subdir_eq hdir]
  exact s3a0_cons_head_ne hne

private def s3a0_kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem s3a0_byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
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

private theorem s3a0_utf8_eq_kutf8 (s : String) : utf8 s = s3a0_kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, s3a0_kutf8, List.utf8Encode, s3a0_byteArray_toList_eq_data]

private theorem s3a0_ofList_append (l₁ l₂ : List Char) :
    String.ofList (l₁ ++ l₂) = String.ofList l₁ ++ String.ofList l₂ := by
  apply String.ext
  simp [String.toList_append]

private theorem s3a0_pathStr_append (a b : List (BitVec 8)) :
    CryptoVerification.SignalSession.Cli.MainHops.pathStr (a ++ b) =
      CryptoVerification.SignalSession.Cli.MainHops.pathStr a ++
        CryptoVerification.SignalSession.Cli.MainHops.pathStr b := by
  unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
  rw [List.map_append, s3a0_ofList_append]

private theorem s3a0_decimalText_bytes (n : Nat) :
    CryptoVerification.SignalSession.Cli.decimalText n ≠ [] ∧
      ∀ b ∈ CryptoVerification.SignalSession.Cli.decimalText n,
        0x30 ≤ b.toNat ∧ b.toNat ≤ 0x39 := by
  refine Nat.strongRecOn n fun n ih => ?_
  by_cases hn : n < 10
  · rw [CryptoVerification.SignalSession.Cli.Decimal.Helpers.decimalText_digit n hn]
    refine ⟨List.cons_ne_nil _ _, fun b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb
    rw [BitVec.toNat_ofNat]
    omega
  · rw [CryptoVerification.SignalSession.Cli.Decimal.Helpers.decimalText_ge10 n (by omega)]
    obtain ⟨hne, hmem⟩ := ih (n / 10) (by omega)
    refine ⟨fun h => hne (List.append_eq_nil_iff.mp h).1, fun b hb => ?_⟩
    rcases List.mem_append.mp hb with hb1 | hb2
    · exact hmem b hb1
    · rw [List.mem_singleton] at hb2; subst hb2
      rw [BitVec.toNat_ofNat]
      omega

private theorem s3a0_pathStr_keyName_props (id : BitVec 32) :
    let s := CryptoVerification.SignalSession.Cli.MainHops.pathStr (keyName id)
    Arm64.normalizePath s = [s] ∧ '.' ∉ s.toList := by
  intro s
  obtain ⟨hne_b, hdig_b⟩ := s3a0_decimalText_bytes id.toNat
  have hs_list : s.toList =
      (CryptoVerification.SignalSession.Cli.decimalText id.toNat).map
        (fun b => Char.ofNat b.toNat) := by
    simp [s, CryptoVerification.SignalSession.Cli.MainHops.pathStr, keyName]
  have hne : s.toList ≠ [] := by
    rw [hs_list]
    intro h
    exact hne_b (List.map_eq_nil_iff.mp h)
  have hchars : ∀ c ∈ s.toList, c ≠ '/' ∧ c ≠ '.' := by
    rw [hs_list]
    intro c hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    obtain ⟨hlo, hhi⟩ := hdig_b b hb
    have h10 :
        b.toNat = 48 ∨ b.toNat = 49 ∨ b.toNat = 50 ∨ b.toNat = 51 ∨ b.toNat = 52 ∨
          b.toNat = 53 ∨ b.toNat = 54 ∨ b.toNat = 55 ∨ b.toNat = 56 ∨ b.toNat = 57 := by
      omega
    rcases h10 with h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide
  have hns : '/' ∉ s.toList := fun hm => (hchars '/' hm).1 rfl
  have hndot : '.' ∉ s.toList := fun hm => (hchars '.' hm).2 rfl
  have hnd : s ≠ "." := by
    intro heq; rw [heq] at hndot
    exact hndot (by decide)
  exact ⟨s3a0_normalizePath_single hns hne hnd, hndot⟩

private theorem s3a0_pathStr_pathOf_keyName {dir : String}
    (hdir_ne : utf8 dir ≠ [])
    (hdir_str : CryptoVerification.SignalSession.Cli.MainHops.pathStr (utf8 dir) = dir)
    (id : BitVec 32) :
    CryptoVerification.SignalSession.Cli.MainHops.pathStr (pathOf (utf8 dir) (keyName id)) =
      (dir ++ "/") ++ CryptoVerification.SignalSession.Cli.MainHops.pathStr (keyName id) := by
  have hp : pathOf (utf8 dir) (keyName id) = utf8 dir ++ utf8 "/" ++ keyName id := by
    unfold pathOf; simp [hdir_ne]
  have hsl : CryptoVerification.SignalSession.Cli.MainHops.pathStr (utf8 "/") = "/" := by
    unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
    rw [s3a0_utf8_eq_kutf8]; rfl
  rw [hp, s3a0_pathStr_append, s3a0_pathStr_append, hdir_str, hsl]

private theorem s3a0_toString_nat_props (n : Nat) :
    (toString n).toList ≠ [] ∧ '/' ∉ (toString n).toList := by
  obtain ⟨hne, hdig⟩ := s3a0_decimalText_bytes n
  refine ⟨?_, ?_⟩
  · intro hnil
    apply hne
    change utf8 (toString n) = []
    rw [s3a0_utf8_eq_kutf8]
    unfold s3a0_kutf8
    rw [hnil]
    rfl
  · intro hsl
    have hu8 : UInt8.ofNat 47 ∈ (toString n).toList.flatMap String.utf8EncodeChar :=
      List.mem_flatMap.mpr ⟨'/', hsl, by decide⟩
    have hbv : (47#8 : BitVec 8) ∈ s3a0_kutf8 (toString n) :=
      List.mem_map.mpr ⟨UInt8.ofNat 47, hu8, by decide⟩
    rw [← s3a0_utf8_eq_kutf8] at hbv
    have hge := (hdig 47#8 hbv).1
    exact absurd hge (by decide)

private theorem s3a0_baseKeysFile_norm_ne {s : String} (hnodot : '.' ∉ s.toList)
    (id : BitVec 32) (dir : String) :
    Arm64.normalizePath (CryptoVerification.SignalSession.baseKeysFile id) ≠ [dir, s] := by
  obtain ⟨hne_n, hns_n⟩ := s3a0_toString_nat_props id.toNat
  let bk := toString id.toNat ++ ".base-keys"
  have hbk_eq : CryptoVerification.SignalSession.baseKeysFile id =
      ("last-resort-kyber-pre-keys" ++ "/") ++ bk := by
    unfold CryptoVerification.SignalSession.baseKeysFile
    simp [bk, String.append_assoc]
  have hbk_ns : '/' ∉ bk.toList := by
    rw [String.toList_append]
    intro hm
    rcases List.mem_append.mp hm with h1 | h2
    · exact hns_n h1
    · exact absurd h2 (by decide)
  have hbk_ne : bk.toList ≠ [] := by
    rw [String.toList_append]
    intro hm
    exact hne_n (List.append_eq_nil_iff.mp hm).1
  have hbk_nd : bk ≠ "." := by
    intro hd
    have hlen1 : bk.toList.length = 1 := by rw [hd]; decide
    have hlen10 : 10 ≤ bk.toList.length := by
      rw [String.toList_append, List.length_append]
      have hsfx : (".base-keys").toList.length = 10 := by decide
      omega
    omega
  have hbk_norm : Arm64.normalizePath bk = [bk] :=
    s3a0_normalizePath_single hbk_ns hbk_ne hbk_nd
  rw [hbk_eq, s3a0_norm_subdir_eq (by decide), hbk_norm]
  intro heq
  injection heq with _ hseg
  injection hseg with hbks
  apply hnodot
  rw [← hbks, String.toList_append]
  exact List.mem_append_right _ (by decide)

private theorem s3a0_encodeVarintAux_len_le :
    ∀ (k : Nat) (v : BitVec 64),
      (CryptoVerification.LibsignalProtoCodec.encodeVarintAux k v).length ≤ k
  | 0, _ => Nat.le_refl 0
  | k + 1, v => by
    unfold CryptoVerification.LibsignalProtoCodec.encodeVarintAux
    split_ifs
    · simp
    · simp only [List.length_cons]
      have ih := s3a0_encodeVarintAux_len_le k (v >>> 7)
      omega

private theorem s3a0_encodeKey_len_le_10 (tag : Nat)
    (wt : CryptoVerification.LibsignalProtoCodec.WireType) :
    (CryptoVerification.LibsignalProtoCodec.encodeKey tag wt).length ≤ 10 := by
  unfold CryptoVerification.LibsignalProtoCodec.encodeKey
    CryptoVerification.LibsignalProtoCodec.encodeVarint
  exact s3a0_encodeVarintAux_len_le 10 _

private theorem s3a0_encodeProto3Uint32Field_len_le_20 (tag : Nat) (v : BitVec 32) :
    (CryptoVerification.RecordCodecs.encodeProto3Uint32Field tag v).length ≤ 20 := by
  unfold CryptoVerification.RecordCodecs.encodeProto3Uint32Field
    CryptoVerification.LibsignalProtoCodec.encodeUint32Field
    CryptoVerification.LibsignalProtoCodec.encodeVarint
  split_ifs
  · simp
  · simp only [List.length_append]
    have hk := s3a0_encodeKey_len_le_10 tag .varint
    have hv := s3a0_encodeVarintAux_len_le 10 (BitVec.zeroExtend 64 v)
    omega

private theorem s3a0_encodeProto3Fixed64Field_len_le_18 (tag : Nat) (v : BitVec 64) :
    (CryptoVerification.RecordCodecs.encodeProto3Fixed64Field tag v).length ≤ 18 := by
  unfold CryptoVerification.RecordCodecs.encodeProto3Fixed64Field
    CryptoVerification.RecordCodecs.le64Bytes
  split_ifs
  · simp
  · simp only [List.length_append, List.length_cons, List.length_nil]
    have hk := s3a0_encodeKey_len_le_10 tag .sixtyFourBit
    omega

private theorem s3a0_encodeProto3BytesField_len_le (tag : Nat) (v : List (BitVec 8)) :
    (CryptoVerification.RecordCodecs.encodeProto3BytesField tag v).length ≤ 20 + v.length := by
  unfold CryptoVerification.RecordCodecs.encodeProto3BytesField
    CryptoVerification.LibsignalProtoCodec.encodeBytesField
    CryptoVerification.LibsignalProtoCodec.encodeVarint
  split_ifs
  · simp
  · simp only [List.length_append]
    have hk := s3a0_encodeKey_len_le_10 tag .lengthDelimited
    have hv := s3a0_encodeVarintAux_len_le 10 (BitVec.ofNat 64 v.length)
    omega

private theorem s3a0_ikp_encode_len_le_105
    (P : CryptoVerification.E2E.PEParams) (st : CryptoVerification.SignalSession.PqParty) :
    (CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
      ⟨CryptoVerification.E2E.djbKey
        (CryptoVerification.E2E.keyPairOf P.C st.me.idPriv).publicKey.bytes,
        st.me.idPriv.toList⟩).length ≤ 105 := by
  unfold CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
  simp only [List.length_append]
  have h1 := s3a0_encodeProto3BytesField_len_le 1
    (CryptoVerification.E2E.djbKey
      (CryptoVerification.E2E.keyPairOf P.C st.me.idPriv).publicKey.bytes)
  have h2 := s3a0_encodeProto3BytesField_len_le 2 st.me.idPriv.toList
  have hdjb :
      (CryptoVerification.E2E.djbKey
        (CryptoVerification.E2E.keyPairOf P.C st.me.idPriv).publicKey.bytes).length = 33 := by
    simp [CryptoVerification.E2E.djbKey]
  have hpriv : st.me.idPriv.toList.length = 32 := st.me.idPriv.toList_length
  omega

private theorem s3a0_signedRecordBytes_len_le_230
    (P : CryptoVerification.E2E.PEParams) (id : BitVec 32)
    (k : CryptoVerification.SignalSession.PqSignedKey) :
    (CryptoVerification.SignalSession.signedRecordBytes P.C id k).length ≤ 230 := by
  unfold CryptoVerification.SignalSession.signedRecordBytes
    CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := s3a0_encodeProto3Uint32Field_len_le_20 1 id
  have h2 := s3a0_encodeProto3BytesField_len_le 2
    (CryptoVerification.E2E.djbKey (CryptoVerification.E2E.keyPairOf P.C k.priv).publicKey.bytes)
  have h3 := s3a0_encodeProto3BytesField_len_le 3 k.priv.toList
  have h4 := s3a0_encodeProto3BytesField_len_le 4 k.sig.toList
  have h5 := s3a0_encodeProto3Fixed64Field_len_le_18 5 k.timestamp
  have hdjb :
      (CryptoVerification.E2E.djbKey
        (CryptoVerification.E2E.keyPairOf P.C k.priv).publicKey.bytes).length = 33 := by
    simp [CryptoVerification.E2E.djbKey]
  have hpriv : k.priv.toList.length = 32 := k.priv.toList_length
  have hsig : k.sig.toList.length = 64 := k.sig.toList_length
  omega

private theorem s3a0_oneTimeRecordBytes_len_le_125
    (P : CryptoVerification.E2E.PEParams) (id : BitVec 32)
    (sk : List.Vector (BitVec 8) 32) :
    (CryptoVerification.SignalSession.oneTimeRecordBytes P.C id sk).length ≤ 125 := by
  unfold CryptoVerification.SignalSession.oneTimeRecordBytes
    CryptoVerification.RecordCodecs.PreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := s3a0_encodeProto3Uint32Field_len_le_20 1 id
  have h2 := s3a0_encodeProto3BytesField_len_le 2
    (CryptoVerification.E2E.djbKey (CryptoVerification.E2E.keyPairOf P.C sk).publicKey.bytes)
  have h3 := s3a0_encodeProto3BytesField_len_le 3 sk.toList
  have hdjb :
      (CryptoVerification.E2E.djbKey
        (CryptoVerification.E2E.keyPairOf P.C sk).publicKey.bytes).length = 33 := by
    simp [CryptoVerification.E2E.djbKey]
  have hpriv : sk.toList.length = 32 := sk.toList_length
  omega

private theorem s3a0_kyberRecordBytes_len_le_4900
    (id : BitVec 32) (k : CryptoVerification.SignalSession.PqKyberKey) :
    (CryptoVerification.SignalSession.kyberRecordBytes id k).length ≤ 4900 := by
  unfold CryptoVerification.SignalSession.kyberRecordBytes
    CryptoVerification.RecordCodecs.SignedPreKeyRecordStructure.encode
  simp only [List.length_append]
  have h1 := s3a0_encodeProto3Uint32Field_len_le_20 1 id
  have h2 := s3a0_encodeProto3BytesField_len_le 2 (CryptoVerification.E2E.kyberKey k.pub)
  have h3 := s3a0_encodeProto3BytesField_len_le 3 (0x08#8 :: k.sec.toList)
  have h4 := s3a0_encodeProto3BytesField_len_le 4 k.sig.toList
  have h5 := s3a0_encodeProto3Fixed64Field_len_le_18 5 k.timestamp
  have hpub : (CryptoVerification.E2E.kyberKey k.pub).length = 1569 := by
    simp [CryptoVerification.E2E.kyberKey]
  have hsec : (0x08#8 :: k.sec.toList).length = 3169 := by simp [k.sec.toList_length]
  have hsig : k.sig.toList.length = 64 := k.sig.toList_length
  omega

private theorem s3a0_bundle_norm_ne_ikp {b : CryptoVerification.E2E.PreKeyBundleFields}
    {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈
      (CryptoVerification.SignalSession.publicBundleOf b).files
        CryptoVerification.SignalSession.bundleDir) :
    Arm64.normalizePath p ≠ ["identity-key-pair"] := by
  unfold CryptoVerification.SignalSession.PublicBundle.files
    CryptoVerification.SignalSession.publicBundleOf at hmem
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with (h | h | h | h) | hopk
  · injection h with hp _; subst hp; decide
  · injection h with hp _; subst hp; decide
  · injection h with hp _; subst hp; decide
  · injection h with hp _; subst hp; decide
  · cases hb : b.opk with
    | none => simp [hb] at hopk
    | some kv =>
      rcases kv with ⟨_, _⟩
      simp only [hb, Option.map_some, List.mem_singleton] at hopk
      injection hopk with hp _; subst hp; decide

private theorem s3a0_bundle_norm_ne_pair {b : CryptoVerification.E2E.PreKeyBundleFields}
    {p d s : String} {bs : List (BitVec 8)}
    (hd : "bundle" ≠ d)
    (hmem : (p, bs) ∈
      (CryptoVerification.SignalSession.publicBundleOf b).files
        CryptoVerification.SignalSession.bundleDir) :
    Arm64.normalizePath p ≠ [d, s] := by
  unfold CryptoVerification.SignalSession.PublicBundle.files
    CryptoVerification.SignalSession.publicBundleOf at hmem
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with (h | h | h | h) | hopk
  · injection h with hp _; subst hp
    have hn : Arm64.normalizePath (CryptoVerification.SignalSession.bundleDir ++ "/identity-key") =
        ["bundle", "identity-key"] := by decide
    rw [hn]; exact s3a0_cons_head_ne hd
  · injection h with hp _; subst hp
    have hn :
        Arm64.normalizePath (CryptoVerification.SignalSession.bundleDir ++ "/registration-id") =
          ["bundle", "registration-id"] := by decide
    rw [hn]; exact s3a0_cons_head_ne hd
  · injection h with hp _; subst hp
    have hn :
        Arm64.normalizePath (CryptoVerification.SignalSession.bundleDir ++ "/signed-pre-key") =
          ["bundle", "signed-pre-key"] := by decide
    rw [hn]; exact s3a0_cons_head_ne hd
  · injection h with hp _; subst hp
    have hn :
        Arm64.normalizePath (CryptoVerification.SignalSession.bundleDir ++ "/kyber-pre-key") =
          ["bundle", "kyber-pre-key"] := by decide
    rw [hn]; exact s3a0_cons_head_ne hd
  · cases hb : b.opk with
    | none => simp [hb] at hopk
    | some kv =>
      rcases kv with ⟨_, _⟩
      simp only [hb, Option.map_some, List.mem_singleton] at hopk
      injection hopk with hp _; subst hp
      have hn :
          Arm64.normalizePath (CryptoVerification.SignalSession.bundleDir ++ "/one-time-pre-key") =
            ["bundle", "one-time-pre-key"] := by decide
      rw [hn]; exact s3a0_cons_head_ne hd

private theorem s3a0_encodeDir_norm_ikp_len_le_105
    {P : CryptoVerification.E2E.PEParams} {st : CryptoVerification.SignalSession.PqParty}
    {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ CryptoVerification.SignalSession.encodeDir P st)
    (hnorm : Arm64.normalizePath p = ["identity-key-pair"]) :
    bs.length ≤ 105 := by
  unfold CryptoVerification.SignalSession.encodeDir at hmem
  simp only [List.mem_append] at hmem
  rcases hmem with ((((((hf_hdr | hf_peer) | hf_sess) | hf_sig) | hf_ot) | hf_kot) | hf_klr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_hdr
    rcases hf_hdr with h | h | h
    · injection h with hp _; subst hp; exact absurd hnorm (by decide)
    · injection h with _ hbs; subst hbs; exact s3a0_ikp_encode_len_le_105 P st
    · injection h with hp _; subst hp; exact absurd hnorm (by decide)
  · cases hp : st.peerId with
    | none => simp [hp] at hf_peer
    | some k =>
      simp only [hp, List.mem_singleton] at hf_peer
      injection hf_peer with hp_eq _; subst hp_eq
      exact absurd hnorm (s3a0_norm_subdir_ne_ikp (dir := "identities") (by decide) (by decide))
  · cases hs : st.session with
    | none => simp [hs] at hf_sess
    | some xg =>
      rcases xg with ⟨_, _⟩
      simp only [hs, List.mem_singleton] at hf_sess
      injection hf_sess with hp_eq _; subst hp_eq
      exact absurd hnorm (s3a0_norm_subdir_ne_ikp (dir := "sessions") (by decide) (by decide))
  · rw [List.mem_map] at hf_sig
    rcases hf_sig with ⟨⟨_, _⟩, _, h⟩
    injection h with hp_eq _; subst hp_eq
    exact absurd hnorm (s3a0_norm_subdir_ne_ikp (dir := "signed-pre-keys") (by decide) (by decide))
  · rw [List.mem_map] at hf_ot
    rcases hf_ot with ⟨⟨_, _⟩, _, h⟩
    injection h with hp_eq _; subst hp_eq
    exact absurd hnorm
      (s3a0_norm_subdir_ne_ikp (dir := "one-time-pre-keys") (by decide) (by decide))
  · rw [List.mem_map] at hf_kot
    rcases hf_kot with ⟨⟨_, _⟩, _, h⟩
    injection h with hp_eq _; subst hp_eq
    exact absurd hnorm
      (s3a0_norm_subdir_ne_ikp (dir := "one-time-kyber-pre-keys") (by decide) (by decide))
  · rw [List.mem_flatten] at hf_klr
    rcases hf_klr with ⟨sub, hsub, hf_in⟩
    rw [List.mem_map] at hsub
    rcases hsub with ⟨⟨_, _, _⟩, _, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
    rcases hf_in with h1 | h2
    · injection h1 with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_ikp (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))
    · injection h2 with hp_eq _; subst hp_eq
      unfold CryptoVerification.SignalSession.baseKeysFile at hnorm
      rw [String.append_assoc] at hnorm
      exact absurd hnorm
        (s3a0_norm_subdir_ne_ikp (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))

private theorem s3a0_ownIkp_le_105
    {P : CryptoVerification.E2E.PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "identity-key-pair") =
        .ok bs → bs.length ≤ 105 := by
  intro bs hrd
  change cliIo.rd (runFiles i)
      (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) = .ok bs at hrd
  rcases s3a0_cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
  · exact Nat.zero_le 105
  · have hpth :
        CryptoVerification.SignalSession.Cli.MainHops.pathStr
          (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) =
          "identity-key-pair" := by
      change CryptoVerification.SignalSession.Cli.MainHops.pathStr (utf8 "identity-key-pair") =
        "identity-key-pair"
      unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
      rw [s3a0_utf8_eq_kutf8]
      rfl
    rw [hpth] at hfile
    obtain ⟨p, hp_norm, hp_mem⟩ := s3a0_initFsState_files_mem_norm hfile
    have hikp_norm : Arm64.normalizePath "identity-key-pair" = ["identity-key-pair"] := by decide
    rw [hikp_norm] at hp_norm
    have hp_files : (p, bs) ∈ i.files := hp_mem
    obtain ⟨st, _, hcase⟩ := hi
    rcases hcase with ⟨_, b, t, rfl⟩ | ⟨_, r, _, rfl⟩ | ⟨_, rc, _, rfl⟩ |
        ⟨_, rc, _, rfl⟩ | ⟨_, rc, _, _, _, rfl⟩
    · simp only [CryptoVerification.SignalSession.pqInitInputs,
        CryptoVerification.SignalSession.pqInputs, List.mem_append, List.mem_singleton] at hp_files
      rcases hp_files with (hed | hbun) | hcoins
      · exact s3a0_encodeDir_norm_ikp_len_le_105 hed hp_norm
      · exact absurd hp_norm (s3a0_bundle_norm_ne_ikp hbun)
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
    · simp only [CryptoVerification.SignalSession.pqSendInputs,
        CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp_files
      rcases hp_files with hed | hcoins
      · exact s3a0_encodeDir_norm_ikp_len_le_105 hed hp_norm
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
    · simp only [CryptoVerification.SignalSession.pqRecvInputs,
        CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp_files
      rcases hp_files with hed | hcoins
      · exact s3a0_encodeDir_norm_ikp_len_le_105 hed hp_norm
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
    · simp only [CryptoVerification.SignalSession.pqRecvInputs,
        CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp_files
      rcases hp_files with hed | hcoins
      · exact s3a0_encodeDir_norm_ikp_len_le_105 hed hp_norm
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
    · simp only [CryptoVerification.SignalSession.pqRecvInputs,
        CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp_files
      rcases hp_files with hed | hcoins
      · exact s3a0_encodeDir_norm_ikp_len_le_105 hed hp_norm
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)

private theorem s3a0_cliPqInputs_dir_file_mem
    {P : CryptoVerification.E2E.PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i)
    {dir s : String} {bs : List (BitVec 8)}
    (hdir_norm : Arm64.normalizePath dir = [dir])
    (hdir_ne_bundle : "bundle" ≠ dir)
    (hs_norm : Arm64.normalizePath s = [s])
    (hfile : (Arm64.Process.initFsState (CryptoVerification.SignalSession.Cli.cliInputs i)).files
      ((dir ++ "/") ++ s) = some (.file bs)) :
    ∃ st p, (p, bs) ∈ CryptoVerification.SignalSession.encodeDir P st ∧
      Arm64.normalizePath p = [dir, s] := by
  obtain ⟨p, hp_norm, hp_mem⟩ := s3a0_initFsState_files_mem_norm hfile
  rw [s3a0_norm_subdir_eq hdir_norm, hs_norm] at hp_norm
  have hp_files : (p, bs) ∈ i.files := hp_mem
  have hcoins_norm : Arm64.normalizePath CryptoVerification.SignalSession.coinsFile = ["coins"] := by
    decide
  obtain ⟨st, _, hcase⟩ := hi
  rcases hcase with ⟨_, b, t, rfl⟩ | ⟨_, r, _, rfl⟩ | ⟨_, rc, _, rfl⟩ |
      ⟨_, rc, _, rfl⟩ | ⟨_, rc, _, _, _, rfl⟩
  · simp only [CryptoVerification.SignalSession.pqInitInputs,
      CryptoVerification.SignalSession.pqInputs, List.mem_append, List.mem_singleton] at hp_files
    rcases hp_files with (hed | hbun) | hcoins
    · exact ⟨st, p, hed, hp_norm⟩
    · exact absurd hp_norm (s3a0_bundle_norm_ne_pair hdir_ne_bundle hbun)
    · injection hcoins with hp_c _; subst hp_c
      rw [hcoins_norm] at hp_norm; exact absurd hp_norm s3a0_singleton_ne_pair
  · simp only [CryptoVerification.SignalSession.pqSendInputs,
      CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
      List.mem_singleton] at hp_files
    rcases hp_files with hed | hcoins
    · exact ⟨st, p, hed, hp_norm⟩
    · injection hcoins with hp_c _; subst hp_c
      rw [hcoins_norm] at hp_norm; exact absurd hp_norm s3a0_singleton_ne_pair
  · simp only [CryptoVerification.SignalSession.pqRecvInputs,
      CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
      List.mem_singleton] at hp_files
    rcases hp_files with hed | hcoins
    · exact ⟨st, p, hed, hp_norm⟩
    · injection hcoins with hp_c _; subst hp_c
      rw [hcoins_norm] at hp_norm; exact absurd hp_norm s3a0_singleton_ne_pair
  · simp only [CryptoVerification.SignalSession.pqRecvInputs,
      CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
      List.mem_singleton] at hp_files
    rcases hp_files with hed | hcoins
    · exact ⟨st, p, hed, hp_norm⟩
    · injection hcoins with hp_c _; subst hp_c
      rw [hcoins_norm] at hp_norm; exact absurd hp_norm s3a0_singleton_ne_pair
  · simp only [CryptoVerification.SignalSession.pqRecvInputs,
      CryptoVerification.SignalSession.pqInputs, List.append_nil, List.mem_append,
      List.mem_singleton] at hp_files
    rcases hp_files with hed | hcoins
    · exact ⟨st, p, hed, hp_norm⟩
    · injection hcoins with hp_c _; subst hp_c
      rw [hcoins_norm] at hp_norm; exact absurd hp_norm s3a0_singleton_ne_pair

private theorem s3a0_encodeDir_hdr_peer_sess_ne_pair
    {P : CryptoVerification.E2E.PEParams} {st : CryptoVerification.SignalSession.PqParty}
    {p dir s : String} {bs : List (BitVec 8)}
    (hid_ne : "identities" ≠ dir) (hsess_ne : "sessions" ≠ dir)
    (hhps :
      ((p, bs) ∈
        [(CryptoVerification.SignalSession.addressFile,
            CryptoVerification.SignalSession.textBytes
              (CryptoVerification.SignalSession.partyAddress st.party).text),
         (CryptoVerification.SignalSession.identityKeyPairFile,
            CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
              ⟨CryptoVerification.E2E.djbKey
                (CryptoVerification.E2E.keyPairOf P.C st.me.idPriv).publicKey.bytes,
                st.me.idPriv.toList⟩),
         (CryptoVerification.SignalSession.registrationIdFile,
            CryptoVerification.SignalSession.le32 st.me.regId)] ∨
       (p, bs) ∈ (match st.peerId with
         | some k =>
           [(CryptoVerification.SignalSession.identityFile
               (CryptoVerification.E2E.partyAddressName st.party.other), k.serialize)]
         | none => [])) ∨
      (p, bs) ∈ (match st.session with
        | some (x, g) =>
          [(CryptoVerification.SignalSession.sessionFile
              (CryptoVerification.SignalSession.partyAddress st.party.other),
            CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) g)]
        | none => [])) :
    Arm64.normalizePath p ≠ [dir, s] := by
  rcases hhps with (hf_hdr | hf_peer) | hf_sess
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_hdr
    rcases hf_hdr with h | h | h
    · injection h with hp _; subst hp
      have hn : Arm64.normalizePath CryptoVerification.SignalSession.addressFile = ["address"] := by
        decide
      rw [hn]; exact s3a0_singleton_ne_pair
    · injection h with hp _; subst hp
      have hn :
          Arm64.normalizePath CryptoVerification.SignalSession.identityKeyPairFile =
            ["identity-key-pair"] := by decide
      rw [hn]; exact s3a0_singleton_ne_pair
    · injection h with hp _; subst hp
      have hn :
          Arm64.normalizePath CryptoVerification.SignalSession.registrationIdFile =
            ["registration-id"] := by decide
      rw [hn]; exact s3a0_singleton_ne_pair
  · cases hp : st.peerId with
    | none => simp [hp] at hf_peer
    | some k =>
      simp only [hp, List.mem_singleton] at hf_peer
      injection hf_peer with hp_eq _; subst hp_eq
      exact s3a0_norm_subdir_ne_pair (dir := "identities") (by decide) hid_ne
  · cases hs : st.session with
    | none => simp [hs] at hf_sess
    | some xg =>
      rcases xg with ⟨_, _⟩
      simp only [hs, List.mem_singleton] at hf_sess
      injection hf_sess with hp_eq _; subst hp_eq
      exact s3a0_norm_subdir_ne_pair (dir := "sessions") (by decide) hsess_ne

private theorem s3a0_signed_le_230
    {P : CryptoVerification.E2E.PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    ∀ id bs,
      StoresGhost.opened.signed.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 230 := by
  intro id bs hrd
  change cliIo.rd (runFiles i) (pathOf (utf8 "signed-pre-keys") (keyName id)) = .ok bs at hrd
  rcases s3a0_cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
  · exact Nat.zero_le 230
  · have hdir_ne : utf8 "signed-pre-keys" ≠ [] := by rw [s3a0_utf8_eq_kutf8]; decide
    have hdir_str :
        CryptoVerification.SignalSession.Cli.MainHops.pathStr (utf8 "signed-pre-keys") =
          "signed-pre-keys" := by
      unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
      rw [s3a0_utf8_eq_kutf8]; rfl
    rw [s3a0_pathStr_pathOf_keyName hdir_ne hdir_str id] at hfile
    obtain ⟨hs_norm, _⟩ := s3a0_pathStr_keyName_props id
    obtain ⟨st, p, hmem, hnorm⟩ :=
      s3a0_cliPqInputs_dir_file_mem hi (by decide) (by decide) hs_norm hfile
    unfold CryptoVerification.SignalSession.encodeDir at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with (((hf_hps | hf_sig) | hf_ot) | hf_kot) | hf_klr
    · exact absurd hnorm (s3a0_encodeDir_hdr_peer_sess_ne_pair (by decide) (by decide) hf_hps)
    · rw [List.mem_map] at hf_sig
      rcases hf_sig with ⟨⟨id', k⟩, _, h⟩
      injection h with _ hbs; subst hbs
      exact s3a0_signedRecordBytes_len_le_230 P id' k
    · rw [List.mem_map] at hf_ot
      rcases hf_ot with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "one-time-pre-keys") (by decide) (by decide))
    · rw [List.mem_map] at hf_kot
      rcases hf_kot with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "one-time-kyber-pre-keys") (by decide) (by decide))
    · rw [List.mem_flatten] at hf_klr
      rcases hf_klr with ⟨_, hsub, hf_in⟩
      rw [List.mem_map] at hsub
      rcases hsub with ⟨⟨_, _, _⟩, _, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
      rcases hf_in with h1 | h2
      · injection h1 with hp_eq _; subst hp_eq
        exact absurd hnorm
          (s3a0_norm_subdir_ne_pair (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))
      · injection h2 with hp_eq _; subst hp_eq
        unfold CryptoVerification.SignalSession.baseKeysFile at hnorm
        rw [String.append_assoc] at hnorm
        exact absurd hnorm
          (s3a0_norm_subdir_ne_pair (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))

private theorem s3a0_oneTime_le_125
    {P : CryptoVerification.E2E.PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    ∀ id bs,
      StoresGhost.opened.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 125 := by
  intro id bs hrd
  change cliIo.rd (runFiles i) (pathOf (utf8 "one-time-pre-keys") (keyName id)) = .ok bs at hrd
  rcases s3a0_cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
  · exact Nat.zero_le 125
  · have hdir_ne : utf8 "one-time-pre-keys" ≠ [] := by rw [s3a0_utf8_eq_kutf8]; decide
    have hdir_str :
        CryptoVerification.SignalSession.Cli.MainHops.pathStr (utf8 "one-time-pre-keys") =
          "one-time-pre-keys" := by
      unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
      rw [s3a0_utf8_eq_kutf8]; rfl
    rw [s3a0_pathStr_pathOf_keyName hdir_ne hdir_str id] at hfile
    obtain ⟨hs_norm, _⟩ := s3a0_pathStr_keyName_props id
    obtain ⟨st, p, hmem, hnorm⟩ :=
      s3a0_cliPqInputs_dir_file_mem hi (by decide) (by decide) hs_norm hfile
    unfold CryptoVerification.SignalSession.encodeDir at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with (((hf_hps | hf_sig) | hf_ot) | hf_kot) | hf_klr
    · exact absurd hnorm (s3a0_encodeDir_hdr_peer_sess_ne_pair (by decide) (by decide) hf_hps)
    · rw [List.mem_map] at hf_sig
      rcases hf_sig with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "signed-pre-keys") (by decide) (by decide))
    · rw [List.mem_map] at hf_ot
      rcases hf_ot with ⟨⟨id', opt⟩, _, h⟩
      injection h with _ hbs; subst hbs
      cases opt with
      | none => exact Nat.zero_le 125
      | some sk => exact s3a0_oneTimeRecordBytes_len_le_125 P id' sk
    · rw [List.mem_map] at hf_kot
      rcases hf_kot with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "one-time-kyber-pre-keys") (by decide) (by decide))
    · rw [List.mem_flatten] at hf_klr
      rcases hf_klr with ⟨_, hsub, hf_in⟩
      rw [List.mem_map] at hsub
      rcases hsub with ⟨⟨_, _, _⟩, _, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
      rcases hf_in with h1 | h2
      · injection h1 with hp_eq _; subst hp_eq
        exact absurd hnorm
          (s3a0_norm_subdir_ne_pair (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))
      · injection h2 with hp_eq _; subst hp_eq
        unfold CryptoVerification.SignalSession.baseKeysFile at hnorm
        rw [String.append_assoc] at hnorm
        exact absurd hnorm
          (s3a0_norm_subdir_ne_pair (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))

private theorem s3a0_kyberOneTime_le_4900
    {P : CryptoVerification.E2E.PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    ∀ id bs,
      StoresGhost.opened.kyber.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900 := by
  intro id bs hrd
  change cliIo.rd (runFiles i)
      (pathOf (utf8 "one-time-kyber-pre-keys") (keyName id)) = .ok bs at hrd
  rcases s3a0_cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
  · exact Nat.zero_le 4900
  · have hdir_ne : utf8 "one-time-kyber-pre-keys" ≠ [] := by rw [s3a0_utf8_eq_kutf8]; decide
    have hdir_str :
        CryptoVerification.SignalSession.Cli.MainHops.pathStr (utf8 "one-time-kyber-pre-keys") =
          "one-time-kyber-pre-keys" := by
      unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
      rw [s3a0_utf8_eq_kutf8]; rfl
    rw [s3a0_pathStr_pathOf_keyName hdir_ne hdir_str id] at hfile
    obtain ⟨hs_norm, _⟩ := s3a0_pathStr_keyName_props id
    obtain ⟨st, p, hmem, hnorm⟩ :=
      s3a0_cliPqInputs_dir_file_mem hi (by decide) (by decide) hs_norm hfile
    unfold CryptoVerification.SignalSession.encodeDir at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with (((hf_hps | hf_sig) | hf_ot) | hf_kot) | hf_klr
    · exact absurd hnorm (s3a0_encodeDir_hdr_peer_sess_ne_pair (by decide) (by decide) hf_hps)
    · rw [List.mem_map] at hf_sig
      rcases hf_sig with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "signed-pre-keys") (by decide) (by decide))
    · rw [List.mem_map] at hf_ot
      rcases hf_ot with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "one-time-pre-keys") (by decide) (by decide))
    · rw [List.mem_map] at hf_kot
      rcases hf_kot with ⟨⟨id', opt⟩, _, h⟩
      injection h with _ hbs; subst hbs
      cases opt with
      | none => exact Nat.zero_le 4900
      | some k => exact s3a0_kyberRecordBytes_len_le_4900 id' k
    · rw [List.mem_flatten] at hf_klr
      rcases hf_klr with ⟨_, hsub, hf_in⟩
      rw [List.mem_map] at hsub
      rcases hsub with ⟨⟨_, _, _⟩, _, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
      rcases hf_in with h1 | h2
      · injection h1 with hp_eq _; subst hp_eq
        exact absurd hnorm
          (s3a0_norm_subdir_ne_pair (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))
      · injection h2 with hp_eq _; subst hp_eq
        unfold CryptoVerification.SignalSession.baseKeysFile at hnorm
        rw [String.append_assoc] at hnorm
        exact absurd hnorm
          (s3a0_norm_subdir_ne_pair (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))

private theorem s3a0_kyberLastResort_le_4900
    {P : CryptoVerification.E2E.PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) :
    ∀ id bs,
      StoresGhost.opened.kyber.lastResort.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900 := by
  intro id bs hrd
  change cliIo.rd (runFiles i)
      (pathOf (utf8 "last-resort-kyber-pre-keys") (keyName id)) = .ok bs at hrd
  rcases s3a0_cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
  · exact Nat.zero_le 4900
  · have hdir_ne : utf8 "last-resort-kyber-pre-keys" ≠ [] := by rw [s3a0_utf8_eq_kutf8]; decide
    have hdir_str :
        CryptoVerification.SignalSession.Cli.MainHops.pathStr
          (utf8 "last-resort-kyber-pre-keys") =
          "last-resort-kyber-pre-keys" := by
      unfold CryptoVerification.SignalSession.Cli.MainHops.pathStr
      rw [s3a0_utf8_eq_kutf8]; rfl
    rw [s3a0_pathStr_pathOf_keyName hdir_ne hdir_str id] at hfile
    obtain ⟨hs_norm, hs_nodot⟩ := s3a0_pathStr_keyName_props id
    obtain ⟨st, p, hmem, hnorm⟩ :=
      s3a0_cliPqInputs_dir_file_mem hi (by decide) (by decide) hs_norm hfile
    unfold CryptoVerification.SignalSession.encodeDir at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with (((hf_hps | hf_sig) | hf_ot) | hf_kot) | hf_klr
    · exact absurd hnorm (s3a0_encodeDir_hdr_peer_sess_ne_pair (by decide) (by decide) hf_hps)
    · rw [List.mem_map] at hf_sig
      rcases hf_sig with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "signed-pre-keys") (by decide) (by decide))
    · rw [List.mem_map] at hf_ot
      rcases hf_ot with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "one-time-pre-keys") (by decide) (by decide))
    · rw [List.mem_map] at hf_kot
      rcases hf_kot with ⟨⟨_, _⟩, _, h⟩
      injection h with hp_eq _; subst hp_eq
      exact absurd hnorm
        (s3a0_norm_subdir_ne_pair (dir := "one-time-kyber-pre-keys") (by decide) (by decide))
    · rw [List.mem_flatten] at hf_klr
      rcases hf_klr with ⟨_, hsub, hf_in⟩
      rw [List.mem_map] at hsub
      rcases hsub with ⟨⟨id', k, _⟩, _, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
      rcases hf_in with h1 | h2
      · injection h1 with _ hbs; subst hbs
        exact s3a0_kyberRecordBytes_len_le_4900 id' k
      · injection h2 with hp_eq _; subst hp_eq
        exact absurd hnorm (s3a0_baseKeysFile_norm_ne hs_nodot id' "last-resort-kyber-pre-keys")

/-- Per-directory store byte-length caps on `runFiles i` from `CliPqxdhInputs`. -/
private theorem s3a_sub0_store_file_caps (W : CliHooks) (i : Inputs)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i) :
    (∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "identity-key-pair") =
        .ok bs → bs.length ≤ 105) ∧
    (∀ id bs,
      StoresGhost.opened.signed.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 230) ∧
    (∀ id bs,
      StoresGhost.opened.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 125) ∧
    (∀ id bs,
      StoresGhost.opened.kyber.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900) ∧
    (∀ id bs,
      StoresGhost.opened.kyber.lastResort.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900) :=
  ⟨s3a0_ownIkp_le_105 hi,
   s3a0_signed_le_230 hi,
   s3a0_oneTime_le_125 hi,
   s3a0_kyberOneTime_le_4900 hi,
   s3a0_kyberLastResort_le_4900 hi⟩

/-- `PhaseCreditSpec` for `CliSpkDecodeEnv bs` (`bs.length ≤ L ≤ 4900`, covering `L = 230` for
`spkGet` and `L = 4900` for `kpkGet`; `0` live/peak since `9808 ≤ 135167`). -/
private theorem s3a_sub1_cliSpkDecode_credit {bs : List (BitVec 8)} {L : Nat}
    (hbs : bs.length ≤ L) (hL : L ≤ 4900) :
    PhaseCreditSpec fineCostModel (CliSpkDecodeEnv bs) (380 * L + 750000) 0 0 9808 := by
  let smallAlloc_pos_le_94 : ∀ {v : Nat}, 0 < v →
      LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallAllocCost
        fineCostModel v ≤ 94 * (v + 1) := by
    intro v hv
    by_cases h12 : v ≤ 12
    · have h := LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_eq_188_of_le_12 h12; omega
    · by_cases h28 : v ≤ 28
      · have h := LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_le_488_of_le_28 h28; omega
      · by_cases h44 : v ≤ 44
        · have h := LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_le_738_of_le_44 h44; omega
        · by_cases h60 : v ≤ 60
          · have h := LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_le_1126_of_le_60 h60; omega
          · by_cases h108 : v ≤ 108
            · have h := LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_le_1997_of_le_108 h108; omega
            · have h := LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_le_two_mul_add v; omega
  have h_push0 : PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.DecodeErrorPushBoundedEnv 0) 9795 0 0 128 := by
    have hmax : 128 ≤
        LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq
          fineCostModel := by
      rw [LibsignalBinary.Heap.Fine.ClientBounds.fineCostModel_smallMaxReq_eq]; decide
    have h128 : PhaseCreditSpec fineCostModel (· = LibsignalBinary.Heap.rustAllocEvents 128 8) 9795 0 0 128 :=
      (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 8) (req := 128)
        (by decide) hmax).mono
        (Nat.le_trans (LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_le_two_mul_add 128) (by decide))
        (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 128)
    have hnil : PhaseCreditSpec fineCostModel (· = []) 9795 0 0 128 :=
      (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
    exact (hnil.or h128).of_imp fun evs hp => by
      rcases hp with rfl | ⟨_, rfl⟩ | ⟨hlt, _⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · omega
  have h_errTail : PhaseCreditSpec fineCostModel
      LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkErrTailEnv 11792 0 0 128 := by
    have hmax72 : 72 ≤
        LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq
          fineCostModel := by
      rw [LibsignalBinary.Heap.Fine.ClientBounds.fineCostModel_smallMaxReq_eq]; decide
    have h72 : PhaseCreditSpec fineCostModel (· = LibsignalBinary.Heap.rustAllocEvents 72 8) 1997 0 0 72 :=
      (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 8) (req := 72)
        (by decide) hmax72).mono
        (LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_le_1997_of_le_108 (by decide))
        (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 72)
    have hfp : PhaseCreditSpec fineCostModel
        (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv
          (· = LibsignalBinary.Heap.rustAllocEvents 72 8)
          (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.DecodeErrorPushBoundedEnv 0)) 11792 0 0 128 :=
      (h72.concat h_push0).mono (by decide) (by decide) (by decide) (by decide)
    have hnil : PhaseCreditSpec fineCostModel (· = []) 11792 0 0 128 :=
      (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
    have h72' : PhaseCreditSpec fineCostModel (· = LibsignalBinary.Heap.rustAllocEvents 72 8) 11792 0 0 128 :=
      h72.mono (by decide) (by decide) (by decide) (by decide)
    exact ((hnil.or h72').or hfp).of_imp fun evs he => by
      cases he with
      | nil => exact Or.inl (Or.inl rfl)
      | fromOnly => exact Or.inl (Or.inr rfl)
      | fromPush hp => exact Or.inr (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append rfl hp)
  let capsMaxLe (caps : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps) (M : Nat) : Prop :=
    caps.pub ≤ M ∧ caps.priv ≤ M ∧ caps.sig ≤ M
  let spkBytePot (M : Nat) (caps : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps) : Nat :=
    (M - caps.pub) + (M - caps.priv) + (M - caps.sig)
  let spkFuelPot (caps : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps) : Nat :=
    s3a_spkFuel4900 caps.pub + s3a_spkFuel4900 caps.priv + s3a_spkFuel4900 caps.sig
  let spkLoopCum (M rem : Nat) (caps : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps) : Nat :=
    94 * rem + 4 * spkBytePot M caps + 9539 * spkFuelPot caps + 11792
  have h_caps_get_le : ∀ {caps M} (_ : capsMaxLe caps M)
      (f : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkField), caps.get f ≤ M := by
    rintro caps M ⟨h1, h2, h3⟩ f
    cases f <;> simp only [LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.get] <;> omega
  have h_caps_set_le : ∀ {caps M nc} (_ : capsMaxLe caps M) (_ : nc ≤ M)
      (f : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkField), capsMaxLe (caps.set f nc) M := by
    rintro caps M nc ⟨h1, h2, h3⟩ hnc f
    cases f <;> exact
      ⟨by simpa [LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.set],
       by simpa [LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.set],
       by simpa [LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.set]⟩
  have h_caps_set_self : ∀ (caps : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps)
      (f : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkField),
      caps.set f (caps.get f) = caps := by
    intro caps f; cases caps; cases f <;> rfl
  have h_bytePot_step : ∀ {M caps f nc}, capsMaxLe caps M → nc ≤ M → 2 * caps.get f ≤ nc →
      4 * spkBytePot M (caps.set f nc) + 2 * nc ≤ 4 * spkBytePot M caps := by
    rintro M caps f nc ⟨h1, h2, h3⟩ hnc_le h2c
    cases f <;> simp only [spkBytePot,
      LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.get,
      LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.set] at h2c ⊢ <;> omega
  have h_fuelPot_step : ∀ {caps f v nc}, v ≤ 4900 → caps.get f < v →
      nc = max (max v (2 * caps.get f)) 8 → spkFuelPot (caps.set f nc) + 1 ≤ spkFuelPot caps := by
    intro caps f v nc hv hcv hnc
    have hstep := (s3a_spkFuel4900_step_raw hv hcv hnc).1
    cases f <;> simp only [spkFuelPot,
      LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.get,
      LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.set] at hstep ⊢ <;> omega
  have h_res_props : ∀ {c v : Nat}, c < v → v ≤ L →
      let nc := CryptoVerification.LibsignalTripleRatchet.reserveCap c 0 v
      nc = max (max v (2 * c)) 8 ∧ 1 ≤ nc ∧ 2 * c ≤ nc ∧ v ≤ nc ∧ nc ≤ max (2 * L) 128 := by
    intro c v hcv hv; dsimp only [CryptoVerification.LibsignalTripleRatchet.reserveCap]; omega
  have h_noRes : ∀ {wt : CryptoVerification.LibsignalProtoCodec.WireType}
      {bs' v rest : List (BitVec 8)} {c M : Nat},
      CryptoVerification.LibsignalProtoCodec.mergeBytes wt bs' = some (v, rest) →
      v.length ≤ c → c ≤ M → M ≤ 9800 →
      PhaseCreditSpec fineCostModel
        (· = LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeEventsCore
          wt (BitVec.ofNat 64 c) bs') (94 * (v.length + 1)) 0 0 M := by
    intro wt bs' v rest c M hm hle hc hM
    have hmaxM : M ≤
        LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq
          fineCostModel := by
      rw [LibsignalBinary.Heap.Fine.ClientBounds.fineCostModel_smallMaxReq_eq]; omega
    have hc_toNat : (BitVec.ofNat 64 c).toNat = c := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hcore : LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeEventsCore
        wt (BitVec.ofNat 64 c) bs' =
        if v.length = 0 then []
        else LibsignalBinary.Heap.rustAllocEvents v.length 1 ++
          LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.doReserveClearEvents c v.length ++
          LibsignalBinary.Heap.rustDeallocEvents v.length 1 := by
      simp [LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeEventsCore, hm, hc_toNat]
    rw [show (· = LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeEventsCore
        wt (BitVec.ofNat 64 c) bs') =
        (· = if v.length = 0 then []
          else LibsignalBinary.Heap.rustAllocEvents v.length 1 ++
            LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.doReserveClearEvents c v.length ++
            LibsignalBinary.Heap.rustDeallocEvents v.length 1) by rw [hcore]]
    split_ifs with hv0
    · exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
    · have hv_pos : 0 < v.length := Nat.pos_of_ne_zero hv0
      have hv_le_M : v.length ≤ M := Nat.le_trans hle hc
      have halloc : PhaseCreditSpec fineCostModel
          (· = LibsignalBinary.Heap.rustAllocEvents v.length 1) (94 * (v.length + 1)) 0 0 M :=
        (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 1) (req := v.length)
          (by decide) (Nat.le_trans hv_le_M hmaxM)).mono
          (smallAlloc_pos_le_94 hv_pos) (Nat.le_refl 0) (Nat.le_refl 0) hv_le_M
      have hres : LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.doReserveClearEvents
          c v.length = [] := by
        simp [LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.doReserveClearEvents, hle]
      rw [hres, List.append_nil]
      have hfree : PhaseCreditSpec fineCostModel
          (· = LibsignalBinary.Heap.rustDeallocEvents v.length 1) 0 0 0 0 :=
        PhaseCreditSpec.rustDealloc_align16 fineCostModel (by decide)
      exact ((halloc.concat hfree).mono
        (Nat.le_of_eq (Nat.add_zero _)) (Nat.le_refl 0) (Nat.le_refl 0)
        (Nat.max_le.mpr ⟨Nat.le_refl M, Nat.zero_le M⟩)).of_imp fun evs he => by
          subst he
          exact LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append rfl rfl
  have h_res : ∀ {wt : CryptoVerification.LibsignalProtoCodec.WireType}
      {bs' v rest : List (BitVec 8)} {c M : Nat},
      CryptoVerification.LibsignalProtoCodec.mergeBytes wt bs' = some (v, rest) →
      c < v.length → v.length ≤ M →
      1 ≤ CryptoVerification.LibsignalTripleRatchet.reserveCap c 0 v.length →
      CryptoVerification.LibsignalTripleRatchet.reserveCap c 0 v.length ≤ M → M ≤ 9800 →
      PhaseCreditSpec fineCostModel
        (· = LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeEventsCore
          wt (BitVec.ofNat 64 c) bs')
        (94 * (v.length + 1) + (2 * CryptoVerification.LibsignalTripleRatchet.reserveCap c 0 v.length + 9539))
        0 0 M := by
    intro wt bs' v rest c M hm hcv hv_le_M hnc_pos hnc_le hM
    have hmaxM : M ≤
        LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit.HasFineReallocCredit.smallMaxReq
          fineCostModel := by
      rw [LibsignalBinary.Heap.Fine.ClientBounds.fineCostModel_smallMaxReq_eq]; omega
    have hc_lt_M : c ≤ M := Nat.le_trans (Nat.le_of_lt hcv) hv_le_M
    have hc_toNat : (BitVec.ofNat 64 c).toNat = c := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hv_pos : 0 < v.length := Nat.lt_of_le_of_lt (Nat.zero_le c) hcv
    have hv0 : v.length ≠ 0 := Nat.ne_of_gt hv_pos
    have hcore : LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeEventsCore
        wt (BitVec.ofNat 64 c) bs' =
        LibsignalBinary.Heap.rustAllocEvents v.length 1 ++
          LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.doReserveClearEvents c v.length ++
          LibsignalBinary.Heap.rustDeallocEvents v.length 1 := by
      simp [LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeEventsCore, hm, hc_toNat, hv0]
    rw [show (· = LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.bytesMergeEventsCore
        wt (BitVec.ofNat 64 c) bs') =
        (· = LibsignalBinary.Heap.rustAllocEvents v.length 1 ++
          LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.doReserveClearEvents c v.length ++
          LibsignalBinary.Heap.rustDeallocEvents v.length 1) by rw [hcore]]
    have halloc : PhaseCreditSpec fineCostModel
        (· = LibsignalBinary.Heap.rustAllocEvents v.length 1) (94 * (v.length + 1)) 0 0 M :=
      (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 1) (req := v.length)
        (by decide) (Nat.le_trans hv_le_M hmaxM)).mono
        (smallAlloc_pos_le_94 hv_pos) (Nat.le_refl 0) (Nat.le_refl 0) hv_le_M
    have hres_ev : PhaseCreditSpec fineCostModel
        (· = LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.doReserveClearEvents c v.length)
        (2 * CryptoVerification.LibsignalTripleRatchet.reserveCap c 0 v.length + 9539) 0 0 M := by
      unfold LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget.doReserveClearEvents
      have hnle : ¬ v.length ≤ c := Nat.not_le.mpr hcv
      simp only [hnle, ↓reduceIte]
      split_ifs with hc0
      · exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 1)
          (req := CryptoVerification.LibsignalTripleRatchet.reserveCap c 0 v.length)
          (by decide) (Nat.le_trans hnc_le hmaxM)).mono
          (LibsignalBinary.Heap.Fine.ClientBounds.smallAllocCost_le_two_mul_add _)
          (Nat.le_refl 0) (Nat.le_refl 0) hnc_le
      · have hc_pos : 1 ≤ c := Nat.pos_of_ne_zero hc0
        exact (PhaseCreditSpec.rustRealloc_small_small fineCostModel (old := c)
          (new := CryptoVerification.LibsignalTripleRatchet.reserveCap c 0 v.length)
          (al := 1) (by decide) hnc_pos hc_pos
          (Nat.le_trans hc_lt_M hmaxM) hnc_pos (Nat.le_trans hnc_le hmaxM)).mono
          (LibsignalBinary.Heap.Fine.ClientBounds.smallReallocCost_le_two_mul_add _)
          (Nat.le_refl 0) (Nat.le_refl 0) hnc_le
    have hfree : PhaseCreditSpec fineCostModel
        (· = LibsignalBinary.Heap.rustDeallocEvents v.length 1) 0 0 0 0 :=
      PhaseCreditSpec.rustDealloc_align16 fineCostModel (by decide)
    exact (((halloc.concat hres_ev).concat hfree).mono
      (Nat.le_of_eq (Nat.add_zero _)) (Nat.le_refl 0) (Nat.le_refl 0)
      (Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨Nat.le_refl M, Nat.le_refl M⟩, Nat.zero_le M⟩)).of_imp
      fun evs he => by
        subst he
        exact LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append
          (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append rfl rfl) rfl
  have h_cum_skip : ∀ {M rem' rem caps}, rem' < rem →
      spkLoopCum M rem' caps ≤ spkLoopCum M rem caps := by
    intro M rem' rem caps hlt
    dsimp only [spkLoopCum]
    exact Nat.add_le_add_right
      (Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.mul_le_mul_left 94 (Nat.le_of_lt hlt)) _) _) _
  have h_cum_noRes : ∀ {M rem rem' v caps}, rem' + v + 1 ≤ rem →
      94 * (v + 1) + spkLoopCum M rem' caps ≤ spkLoopCum M rem caps := by
    intro M rem rem' v caps hprog
    dsimp only [spkLoopCum]
    generalize 4 * spkBytePot M caps + 9539 * spkFuelPot caps + 11792 = restPot
    have hmul : 94 * (v + 1) + 94 * rem' ≤ 94 * rem := by
      have h := Nat.mul_le_mul_left 94 (show v + 1 + rem' ≤ rem by omega)
      rwa [Nat.mul_add] at h
    generalize 94 * (v + 1) = a1 at hmul ⊢
    generalize 94 * rem' = a2 at hmul ⊢
    generalize 94 * rem = a3 at hmul ⊢
    omega
  have h_cum_res : ∀ {M rem rem' v nc caps caps'}, rem' + v + 1 ≤ rem →
      4 * spkBytePot M caps' + 2 * nc ≤ 4 * spkBytePot M caps →
      spkFuelPot caps' + 1 ≤ spkFuelPot caps →
      (94 * (v + 1) + (2 * nc + 9539)) + spkLoopCum M rem' caps' ≤ spkLoopCum M rem caps := by
    intro M rem rem' v nc caps caps' hprog hb hk
    have hmul94 : 94 * (v + 1) + 94 * rem' ≤ 94 * rem := by
      have h := Nat.mul_le_mul_left 94 (show v + 1 + rem' ≤ rem by omega)
      rwa [Nat.mul_add] at h
    have hmulK : 9539 * spkFuelPot caps' + 9539 ≤ 9539 * spkFuelPot caps := by
      have h := Nat.mul_le_mul_left 9539 hk
      rwa [Nat.mul_add, Nat.mul_one] at h
    dsimp only [spkLoopCum]
    generalize 94 * (v + 1) = a1 at hmul94 ⊢
    generalize 94 * rem' = a2 at hmul94 ⊢
    generalize 94 * rem = a3 at hmul94 ⊢
    generalize 4 * spkBytePot M caps' = b1 at hb ⊢
    generalize 4 * spkBytePot M caps = b2 at hb ⊢
    generalize 2 * nc = n2 at hb ⊢
    generalize 9539 * spkFuelPot caps' = k1 at hmulK ⊢
    generalize 9539 * spkFuelPot caps = k2 at hmulK ⊢
    generalize (9539 : Nat) = c1 at hmulK ⊢
    generalize (11792 : Nat) = c2
    omega
  have hM : max (2 * L) 128 ≤ 9800 := by omega
  have h_loopBounded : ∀ (rem : Nat) {caps : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps},
      rem ≤ L → capsMaxLe caps (max (2 * L) 128) →
      PhaseCreditSpec fineCostModel
        (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkLoopBoundedEnv rem caps)
        (spkLoopCum (max (2 * L) 128) rem caps) 0 0 (max (2 * L) 128) := by
    intro rem
    induction rem using Nat.strongRecOn with
    | ind rem ih =>
      intro caps hrem hcaps
      refine {
        req_align := fun evs he => ?_
        credit_le := fun st0 {_} he => ?_
      }
      · cases he with
        | done herr =>
          exact (h_errTail.mono (Nat.le_refl 11792)
            (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_max_right (2 * L) 128)).req_align evs herr
        | @skipStep _ rem' _ _ hlt hnext =>
          exact (ih rem' hlt (Nat.le_trans (Nat.le_of_lt hlt) hrem) hcaps).req_align evs hnext
        | @bytesStep f _ rem' _ wt bs' v rest evs₂ hm hbs_le hprog _ hnext =>
          have hc : caps.get f ≤ max (2 * L) 128 := h_caps_get_le hcaps f
          have hv : v.length ≤ L := by omega
          by_cases hle : v.length ≤ caps.get f
          · simp only [hle, ↓reduceIte, h_caps_set_self] at hnext
            have h1 := h_noRes hm hle hc hM
            have h2 := ih rem' (by omega) (by omega) hcaps
            exact ((h1.concat h2).mono (h_cum_noRes hprog)
              (Nat.le_refl 0) (Nat.le_refl 0) (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)).req_align
              _ (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append rfl hnext)
          · have hcv : caps.get f < v.length := Nat.lt_of_not_ge hle
            simp only [hle, ↓reduceIte] at hnext
            obtain ⟨hnc_eq, hnc_pos, h2c, _, hnc_le⟩ := h_res_props hcv hv
            have hv_le_M : v.length ≤ max (2 * L) 128 := by omega
            have h1 := h_res hm hcv hv_le_M hnc_pos hnc_le hM
            have h2 := ih rem' (by omega) (by omega) (h_caps_set_le hcaps hnc_le f)
            exact ((h1.concat h2).mono
              (h_cum_res hprog (h_bytePot_step hcaps hnc_le h2c)
                (h_fuelPot_step (Nat.le_trans hv hL) hcv hnc_eq))
              (Nat.le_refl 0) (Nat.le_refl 0) (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)).req_align
              _ (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append rfl hnext)
      · cases he with
        | done herr =>
          have hle11792 : 11792 ≤ spkLoopCum (max (2 * L) 128) rem caps :=
            Nat.le_add_left 11792 _
          exact (h_errTail.mono hle11792
            (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_max_right (2 * L) 128)).credit_le st0 herr
        | @skipStep _ rem' _ _ hlt hnext =>
          exact ((ih rem' hlt (Nat.le_trans (Nat.le_of_lt hlt) hrem) hcaps).mono
            (h_cum_skip hlt) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl _)).credit_le st0 hnext
        | @bytesStep f _ rem' _ wt bs' v rest evs₂ hm hbs_le hprog _ hnext =>
          have hc : caps.get f ≤ max (2 * L) 128 := h_caps_get_le hcaps f
          have hv : v.length ≤ L := by omega
          by_cases hle : v.length ≤ caps.get f
          · simp only [hle, ↓reduceIte, h_caps_set_self] at hnext
            have h1 := h_noRes hm hle hc hM
            have h2 := ih rem' (by omega) (by omega) hcaps
            exact ((h1.concat h2).mono (h_cum_noRes hprog)
              (Nat.le_refl 0) (Nat.le_refl 0) (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)).credit_le
              st0 (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append rfl hnext)
          · have hcv : caps.get f < v.length := Nat.lt_of_not_ge hle
            simp only [hle, ↓reduceIte] at hnext
            obtain ⟨hnc_eq, hnc_pos, h2c, _, hnc_le⟩ := h_res_props hcv hv
            have hv_le_M : v.length ≤ max (2 * L) 128 := by omega
            have h1 := h_res hm hcv hv_le_M hnc_pos hnc_le hM
            have h2 := ih rem' (by omega) (by omega) (h_caps_set_le hcaps hnc_le f)
            exact ((h1.concat h2).mono
              (h_cum_res hprog (h_bytePot_step hcaps hnc_le h2c)
                (h_fuelPot_step (Nat.le_trans hv hL) hcv hnc_eq))
              (Nat.le_refl 0) (Nat.le_refl 0) (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)).credit_le
              st0 (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append rfl hnext)
  have h_cum_zero : spkLoopCum (max (2 * L) 128) bs.length
      LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.zero ≤
        94 * L + 12 * max (2 * L) 128 + 326579 := by
    have hbp : spkBytePot (max (2 * L) 128)
        LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.zero = 3 * max (2 * L) 128 := by
      simp only [spkBytePot, LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.zero, Nat.sub_zero]
      omega
    have hfp : spkFuelPot LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkCaps.zero = 33 := by
      decide
    dsimp only [spkLoopCum]
    rw [hbp, hfp]
    have h1 : 94 * bs.length ≤ 94 * L := Nat.mul_le_mul_left 94 hbs
    have h2 : 4 * (3 * max (2 * L) 128) = 12 * max (2 * L) 128 := (Nat.mul_assoc 4 3 _).symm
    have h3 : 9539 * 33 + 11792 = 326579 := by decide
    rw [h2, Nat.add_assoc, h3]
    omega
  have h_loop : ∀ {fuel : Nat}, PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkLoopEnv fuel bs.length)
      (380 * L + 750000) 0 0 9808 := fun {_} =>
    (h_loopBounded bs.length hbs
      ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩).mono
      (Nat.le_trans h_cum_zero (by omega)) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
  have h_or_free : ∀ {E F : List AllocEvent → Prop} {c r : Nat},
      PhaseCreditSpec fineCostModel E c 0 0 r →
      (∀ evs, F evs → FreeOnlyEvs evs) →
      PhaseCreditSpec fineCostModel
        (fun evs => E evs ∨ ∃ e1 e2, E e1 ∧ F e2 ∧ evs = e1 ++ e2) c 0 0 r := by
    intro E F c r hE hF
    have hfree : PhaseCreditSpec fineCostModel F 0 0 0 0 :=
      (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).of_imp hF
    have hcat : PhaseCreditSpec fineCostModel
        (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv E F) c 0 0 r :=
      (hE.concat hfree).mono (Nat.le_of_eq (Nat.add_zero c)) (Nat.le_refl 0) (Nat.le_refl 0)
        (Nat.max_le.mpr ⟨Nat.le_refl r, Nat.zero_le r⟩)
    exact ((hE.or hcat).mono (Nat.max_le.mpr ⟨Nat.le_refl c, Nat.le_refl c⟩)
      (Nat.le_refl 0) (Nat.le_refl 0)
      (Nat.max_le.mpr ⟨Nat.le_refl r, Nat.le_refl r⟩)).of_imp fun evs h => by
        rcases h with h1 | ⟨e1, e2, h1, h2, rfl⟩
        · exact Or.inl h1
        · exact Or.inr (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append h1 h2)
  have h_spkDec : PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkDecodeEnv bs.length)
      (380 * L + 750000) 0 0 9808 :=
    h_or_free h_loop fun _ h => s3a_spkEpilogue_freeOnly h
  have h_kyberDec : PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.KyberDecodeEnv bs.length)
      (380 * L + 750000) 0 0 9808 :=
    h_or_free h_spkDec fun _ h => s3a_dropDecodeError_freeOnly h
  exact (h_loop.or h_kyberDec).mono
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩) (Nat.le_refl 0) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)

section S3aW1cSub2Helpers

open CryptoVerification.LibsignalProtoCodec (WireType mergeBytes)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open LibsignalBinary.Heap (rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineCostModel_smallMaxReq_eq smallAllocCost_eq_188_of_le_12
   smallAllocCost_le_488_of_le_28 smallAllocCost_le_738_of_le_44
   smallAllocCost_le_1126_of_le_60 smallAllocCost_le_1997_of_le_108
   smallAllocCost_le_two_mul_add smallReallocCost_le_two_mul_add)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (PreKeyDeserializeEnv RecordCodecErrStep RecordCodecLoopEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)

/-- Exact `sc = 8` (`coarseAlt 8 = 9`) small-alloc cost at `128` B: `9528 + 261 = 9789`,
so `253` `RecordCodecLoopEnv.step` (`push0`) steps cost `2,476,526 > 1,700,000` and
`213` steps cost `2,084,980 > 1,450,000`. -/
private theorem s3a_w1c_alloc128_cost_eq :
    LibsignalBinary.Heap.Fine.fineSmallAllocCost (4 * 32) = 9789 := by
  decide

private theorem s3a_w1c_smallAllocCost_pos_le_94 {v : Nat} (hv : 0 < v) :
    HasFineReallocCredit.smallAllocCost fineCostModel v ≤ 94 * (v + 1) := by
  by_cases h12 : v ≤ 12
  · have h := smallAllocCost_eq_188_of_le_12 h12; omega
  · by_cases h28 : v ≤ 28
    · have h := smallAllocCost_le_488_of_le_28 h28; omega
    · by_cases h44 : v ≤ 44
      · have h := smallAllocCost_le_738_of_le_44 h44; omega
      · by_cases h60 : v ≤ 60
        · have h := smallAllocCost_le_1126_of_le_60 h60; omega
        · by_cases h108 : v ≤ 108
          · have h := smallAllocCost_le_1997_of_le_108 h108; omega
          · have h := smallAllocCost_le_two_mul_add v; omega

private theorem s3a_w1c_recordCodecErrStep_credit :
    PhaseCreditSpec fineCostModel RecordCodecErrStep 9789 0 0 128 := by
  have hmax : 128 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have h72 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 72 8) 9789 0 0 128 :=
    (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 8) (req := 72)
      (by decide) (by omega)).mono
      (Nat.le_trans (smallAllocCost_le_1997_of_le_108 (by decide)) (by decide))
      (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  have h128_cost : HasFineReallocCredit.smallAllocCost fineCostModel (4 * 32) ≤ 9789 := by
    change LibsignalBinary.Heap.Fine.fineSmallAllocCost (4 * 32) ≤ 9789
    rw [s3a_w1c_alloc128_cost_eq]
  have h128 : PhaseCreditSpec fineCostModel (· = rustAllocEvents (4 * 32) 8) 9789 0 0 128 :=
    (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 8) (req := 4 * 32)
      (by decide) hmax).mono h128_cost (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  have hnil : PhaseCreditSpec fineCostModel (· = []) 9789 0 0 128 :=
    (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
  exact ((hnil.or h72).or h128).of_imp fun evs hs => by
    cases hs with
    | nil => exact Or.inl (Or.inl rfl)
    | fromErr => exact Or.inl (Or.inr rfl)
    | push0 hp =>
      rcases hp with rfl | ⟨_, rfl⟩ | ⟨hpos, _⟩
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr rfl
      · omega

private theorem s3a_w1c_pkBytesMerge_125_credit {wt : WireType} {valCap : BitVec 64}
    {bs v rest : List (BitVec 8)}
    (hm : mergeBytes wt bs = some (v, rest)) (hv : v.length ≤ 125) :
    PhaseCreditSpec fineCostModel (· = bytesMergeEventsCore wt valCap bs)
      (9789 * (2 * v.length + 1)) 0 0 256 := by
  have hmax256 : 256 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hcore : bytesMergeEventsCore wt valCap bs =
      if v.length = 0 then []
      else rustAllocEvents v.length 1 ++ doReserveClearEvents valCap.toNat v.length ++
        rustDeallocEvents v.length 1 := by
    simp [bytesMergeEventsCore, hm]
  rw [show (· = bytesMergeEventsCore wt valCap bs) =
      (· = if v.length = 0 then []
        else rustAllocEvents v.length 1 ++ doReserveClearEvents valCap.toNat v.length ++
          rustDeallocEvents v.length 1) by rw [hcore]]
  split_ifs with hv0
  · exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  · have hv_pos : 0 < v.length := Nat.pos_of_ne_zero hv0
    have halloc : PhaseCreditSpec fineCostModel
        (· = rustAllocEvents v.length 1) (94 * (v.length + 1)) 0 0 256 :=
      (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 1) (req := v.length)
        (by decide) (by omega)).mono
        (s3a_w1c_smallAllocCost_pos_le_94 hv_pos) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
    have hres : PhaseCreditSpec fineCostModel
        (· = doReserveClearEvents valCap.toNat v.length) 10051 0 0 256 := by
      unfold doReserveClearEvents
      split_ifs with hle hc0
      · exact (PhaseCreditSpec.nil fineCostModel).mono (by decide) (by decide) (by decide) (by decide)
      · have hnc_le : reserveCap valCap.toNat 0 v.length ≤ 256 := by
          dsimp only [reserveCap]; omega
        exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps (al := 1)
          (req := reserveCap valCap.toNat 0 v.length) (by decide) (by omega)).mono
          (Nat.le_trans (smallAllocCost_le_two_mul_add _) (by omega))
          (Nat.le_refl 0) (Nat.le_refl 0) hnc_le
      · have hnc_le : reserveCap valCap.toNat 0 v.length ≤ 256 := by
          dsimp only [reserveCap]; omega
        have hnc_pos : 1 ≤ reserveCap valCap.toNat 0 v.length := by
          dsimp only [reserveCap]; omega
        have hc_pos : 1 ≤ valCap.toNat := Nat.pos_of_ne_zero hc0
        have hc_le : valCap.toNat ≤ 256 := by omega
        exact (PhaseCreditSpec.rustRealloc_small_small fineCostModel (old := valCap.toNat)
          (new := reserveCap valCap.toNat 0 v.length) (al := 1) (by decide) hnc_pos hc_pos
          (Nat.le_trans hc_le hmax256) hnc_pos (Nat.le_trans hnc_le hmax256)).mono
          (Nat.le_trans (smallReallocCost_le_two_mul_add _) (by omega))
          (Nat.le_refl 0) (Nat.le_refl 0) hnc_le
    have hfree : PhaseCreditSpec fineCostModel (· = rustDeallocEvents v.length 1) 0 0 0 0 :=
      PhaseCreditSpec.rustDealloc_align16 fineCostModel (by decide)
    have hsum : (94 * (v.length + 1) + 10051) + 0 ≤ 9789 * (2 * v.length + 1) := by omega
    exact (((halloc.concat hres).concat hfree).mono
      hsum (Nat.le_refl 0) (Nat.le_refl 0) (by decide)).of_imp fun evs he => by
        subst he
        exact ConcatEnv.append (ConcatEnv.append rfl rfl) rfl

private theorem s3a_w1c_recordCodecLoop_125_ev_credit {maxLen : Nat} (hmax : maxLen ≤ 125)
    {budget : Nat} {evs : List AllocEvent} (he : RecordCodecLoopEnv budget maxLen evs) :
    PhaseCreditSpec fineCostModel (· = evs) (9789 * budget) 0 0 256 := by
  induction he with
  | nil =>
    exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
  | @step b _ evs₁ evs₂ h1 _ ih =>
    have hs1 : PhaseCreditSpec fineCostModel (· = evs₁) 9789 0 0 256 :=
      (s3a_w1c_recordCodecErrStep_credit.mono (Nat.le_refl 9789) (Nat.le_refl 0) (Nat.le_refl 0)
        (by decide : 128 ≤ 256)).of_imp fun _ h => by subst h; exact h1
    have hsum : 9789 + 9789 * b ≤ 9789 * (b + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
    exact ((hs1.concat (ih hmax)).mono hsum (Nat.le_refl 0) (Nat.le_refl 0) (by decide)).of_imp
      fun _ h => by subst h; exact ConcatEnv.append rfl rfl
  | @bytesStep b _ wt valCap bs v rest evs₁ evs₂ hm hbs heq _ ih =>
    subst heq
    have hprog := LibsignalBinary.Proofs.RecordCodecs.DepsBudget.mergeBytes_len_bound hm
    have hv : v.length ≤ 125 := by omega
    have hs1 := s3a_w1c_pkBytesMerge_125_credit (valCap := valCap) hm hv
    have hsum : 9789 * (2 * v.length + 1) + 9789 * b ≤ 9789 * (b + 2 * v.length + 1) := by
      have h : (2 * v.length + 1) + b = b + 2 * v.length + 1 := by omega
      rw [← Nat.mul_add, h]
    exact ((hs1.concat (ih hmax)).mono hsum (Nat.le_refl 0) (Nat.le_refl 0) (by decide)).of_imp
      fun _ h => by subst h; exact ConcatEnv.append rfl rfl

private theorem s3a_w1c_recordCodecLoop_125_credit {maxLen : Nat} (hmax : maxLen ≤ 125)
    (budget : Nat) :
    PhaseCreditSpec fineCostModel (RecordCodecLoopEnv budget maxLen) (9789 * budget) 0 0 256 where
  req_align evs he := (s3a_w1c_recordCodecLoop_125_ev_credit hmax he).req_align evs rfl
  credit_le st0 {_} he := (s3a_w1c_recordCodecLoop_125_ev_credit hmax he).credit_le st0 rfl

private theorem s3a_w1c_preKeyDeserialize_125_credit {len : Nat} (hlen : len ≤ 125) :
    PhaseCreditSpec fineCostModel (PreKeyDeserializeEnv len)
      (9789 * (2 * len + 3)) 0 0 256 := by
  have hE := s3a_w1c_recordCodecLoop_125_credit hlen (2 * len + 3)
  have hfree : PhaseCreditSpec fineCostModel
      LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecErrCleanupEnv 0 0 0 0 :=
    (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).of_imp fun _ h => s3a_errCleanup_freeOnly h
  have hcat : PhaseCreditSpec fineCostModel
      (ConcatEnv (RecordCodecLoopEnv (2 * len + 3) len)
        LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecErrCleanupEnv)
      (9789 * (2 * len + 3)) 0 0 256 :=
    (hE.concat hfree).mono (Nat.le_of_eq (Nat.add_zero _)) (Nat.le_refl 0) (Nat.le_refl 0)
      (by decide)
  exact ((hE.or hcat).mono (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (Nat.le_refl 0) (Nat.le_refl 0) (by decide)).of_imp fun evs h => by
      rcases h with h1 | ⟨e1, e2, h1, h2, rfl⟩
      · exact Or.inl h1
      · exact Or.inr (ConcatEnv.append h1 h2)

/-- Tight `CliPkDecodeEnv bs` (`bs.length ≤ 125`) bound: `9789 * 253 = 2,476,617`
(`253` `push0` 128 B steps realize `fineCumSmall = 2,476,526`). -/
private theorem s3a_w1c_cliPkDecode_credit {bs : List (BitVec 8)}
    (hbs : bs.length ≤ 125) :
    PhaseCreditSpec fineCostModel (CliPkDecodeEnv bs) 2476617 0 0 256 := by
  have hmul : 9789 * (2 * bs.length + 3) ≤ 2476617 := by omega
  exact (((s3a_w1c_recordCodecLoop_125_credit hbs (2 * bs.length + 3)).or
    (s3a_w1c_preKeyDeserialize_125_credit hbs)).mono
    (Nat.max_le.mpr ⟨hmul, hmul⟩) (Nat.le_refl 0) (Nat.le_refl 0) (by decide))

/-- Tight `OptIkpTryFromEnv gr` (`bs.length ≤ 105`) bound: `9789 * 213 = 2,085,057`
(`213` `push0` 128 B steps realize `fineCumSmall = 2,084,980`). -/
private theorem s3a_w1c_optIkpTryFrom_credit {gr : Except Unit (List (BitVec 8))}
    (hikp : ∀ bs, gr = .ok bs → bs.length ≤ 105) :
    PhaseCreditSpec fineCostModel (OptIkpTryFromEnv gr) 2085057 0 0 256 := by
  unfold OptIkpTryFromEnv
  cases hgr : gr with
  | error u =>
    exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | ok bs =>
    have hbs : bs.length ≤ 105 := hikp bs hgr
    have hloop := s3a_w1c_recordCodecLoop_125_credit
      (Nat.le_trans hbs (by decide)) (2 * bs.length + 3)
    have hfree : PhaseCreditSpec fineCostModel
        LibsignalBinary.Proofs.RecordCodecs.DepsBudget.IkpPostCleanupEnv 0 0 0 0 :=
      (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).of_imp fun _ h =>
        s3a_ikpPostCleanup_freeOnly h
    have hmul : 9789 * (2 * bs.length + 3) + 0 ≤ 2085057 := by omega
    exact ((hloop.concat hfree).mono hmul (Nat.le_refl 0) (Nat.le_refl 0) (by decide)).of_imp
      fun evs ⟨e1, e2, h1, h2, heq⟩ => by
        subst heq
        exact LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.ConcatEnv.append h1 h2

end S3aW1cSub2Helpers

section S3a5Sub5Helpers

open CryptoGames.LibsignalSession
  (IdentityKey MessageKeyGenerator PublicKey ReceiverChain SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (encodeRecordPrev1Mem)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalSessionRepr (ChainGhost MessageKeyGhost VecPin)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost)
open CryptoVerification.SignalSession.Cli (addressText decimalText)
open CryptoVerification.SignalSession.Cli.Decimal.Helpers (decimalText_length_le)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget
  (KemKeyPairFromPubPrivEnv kemKeyPairFromPubPrivEvents)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (dirDomainCaps_opened_own dirDomainCaps_opened_peers dirDomainCaps_opened_sess keyName_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W4BinaryAcceptWideEnv W4BinaryArchiveDirectEnv W4BinaryIdSaveStepEnv W4BinaryIdTrustStepEnv
   W4BinaryInitBobWideEnv W4BinaryKpkGetStepEnv W4BinaryPkGetStepEnv W4BinaryPkRemoveStepEnv
   W4BinaryPromoteArchiveEnv W4BinarySelfKpStepEnv W4BinarySelfRegIdStepEnv
   W4BinarySessLoadStepEnv W4BinarySessStorePrev1StepEnv W4BinarySessStoreStepEnv
   W4BinarySpkGetStepEnv W4BinaryStageP1OkEnv W4BinaryStageP2PathAWideEnv
   W4BinaryStageP2PathCWideEnv W4CloneACDomEnv W4TrialRunWideEnv mkW4RecvPrekeyWideSlotParams)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W4BinaryStageP4PathAWideEnvFixed W4BinaryStageP4PathCWideEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (DeallocCreditSpec FreeOnlyAlign16Evs IterSeqEnv)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec (dropClonedSessionEvents)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (PhaseCreditSpec.rustAlloc_optLarge fineSmallReallocCost_le_9789_of_le_256 optLargeCost)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (PhaseCreditSpec.recordSerialize_seqFree_tight PhaseCreditSpec.serializePrev1_seqFree_tight
   RecordSerializeSeqFreeEnv SerializePrev1SeqFreeEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit
  (w2TryDecryptFail_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (FreshBobCloneDom SessionCloneDom recordSerializeMaxReq_le_of_dom
   recordSerializePeak_fine_le_of_dom recordSerializeTightCum_fine_le_of_dom
   sessionClone_freshBob16K_fine_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec (w2TryDecryptMaxReq)
open LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738
  (w2TryDecryptGenSeeds738Cum w2TryDecryptSeeds738Cum w2TryDecrypt_genSeeds_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
  (ArchivedTrialIterEnv phaseCredit_archivedTrialLoop_le4 phaseCredit_promoteStateArchive)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
  (W4BobSessionBuildEnv W4BoundedEvs W4PqxdhAcceptEnv phaseCredit_w4BobSessionBuild_small
   phaseCredit_w4BoundedEvs_small phaseCredit_w4PqxdhAccept_small)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4ErrTailWideEnv W4StageP3WideEnv W4TryDecryptCloneFailWideEnv
   phaseCredit_optStageEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
  (addressText_peer_length_le_64 opened_all_dirDomainCaps phaseCreditSpec_seq_freeOnly_exact)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec
  (w4ErrTailWide_fine_phaseCredit_tight w4StageP3Wide_zeroLive_fine_phaseCredit_tight
   w4TryDecryptCloneFailWide_dom_fine_cancel_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
  (fineOptLarge fineOptLarge_mono optLargeCost_fine_eq w4BoxedStoreStep_fine_le_28
   w4BoxedStoreStep_fine_le_44 w4SpqrInit32_fine_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
  (W4ArchivedTrial W4FailedTdCancelEnv W4FailedTryDecryptCall W4RecvPrekeyTryDecACEnv
   W4TrialDecEnv W4TryDecryptCall W4TryDecryptFailLinkedEnv W4TryDecryptPathACEnv
   spqrRecvLinked_zeroSkip_c09a_phaseCreditSpec w4RealFailTdCum w4RealTdACCum)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (W4ArchivedTrialDomOf W4FailedTdDomOf W4TryDecryptPathACDomOf
   w4FailTdPeakOf w4TdACLiveOf w4TdACPeakOf w4TdMaxReqOf w4TrialMaxReqOf w4TrialPeakOf)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.DropSsLocal1Budget
  (SessionDropCapsOk chainPairFreeEvents dropSessionStructureLocal1Events
   dropVecChainEvents dropVecMessageKeyEvents mkFreeEvents optCkCapVal optTailCapVal
   pinFreeEvents senderFreeEvents sgnCapFreeEvents ssFirst3FreeEvents
   ssTail3FreeEvents stepEvents_dropSessionStructureLocal1_bounds vec104FreeEvents)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (ssStateLargeLive)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
  (sessDeserLargeLive)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (deserCancelFineCum deserCancelFineLive deserCancelFineMaxReq deserCancelFinePeak
   recordDeserializeCancelEnv_fine_phaseCreditSpec
   sessDeserializeCancelEnv_fine_phaseCreditSpec sessDeserializeCancelEnv_phaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
  (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
  (DecimalEnv decimalEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (cliRd_ok_le_fileCap)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSavePollEnv cliIdentityKitSaveTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitLoadPollEnv cliSessionKitStorePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
  (OptRegIdMalformedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget
  (CliKpkGetPollEnv KpkPassEnv OptKpkDecodeEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget (OptLoadDeserEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
  (addrTextValEnv_decimal_fine_phaseCredit_tight dirGetEnv_path_readFile_fine_phaseCredit_tight
   seq_freeOnly_phaseCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget
  (CliPkGetPollEnv OptPkDecodeEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
  (CliPkRemovePollEnv OptPkRemoveTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
  (CliSpkGetPollEnv OptSpkDecodeEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (pushBytesEvents)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)

private theorem s3a5_pushBytesEvents_zero_cases {m : Nat} (hm : m ≤ 10) :
    pushBytesEvents m 0 0 = [] ∨
    pushBytesEvents m 0 0 = rustAllocEvents 8 1 ∨
    pushBytesEvents m 0 0 = rustAllocEvents 8 1 ++ rustReallocEvents 8 16 1 := by
  match m with
  | 0 => exact Or.inl (by decide)
  | 1 => exact Or.inr (Or.inl (by decide))
  | 2 => exact Or.inr (Or.inl (by decide))
  | 3 => exact Or.inr (Or.inl (by decide))
  | 4 => exact Or.inr (Or.inl (by decide))
  | 5 => exact Or.inr (Or.inl (by decide))
  | 6 => exact Or.inr (Or.inl (by decide))
  | 7 => exact Or.inr (Or.inl (by decide))
  | 8 => exact Or.inr (Or.inl (by decide))
  | 9 => exact Or.inr (Or.inr (by decide))
  | 10 => exact Or.inr (Or.inr (by decide))
  | _ + 11 => omega

private theorem s3a5_decimal_credit (id : BitVec 32) :
    PhaseCreditSpec fineCostModel (DecimalEnv id) 19578 0 0 16 := by
  have hlen : (decimalText id.toNat).length ≤ 10 :=
    decimalText_length_le 10 id.toNat (by decide) (Nat.lt_trans id.isLt (by decide))
  have ha8 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 8 1) 9789 0 0 8 :=
    s3_rustAlloc_small_credit (req := 8) (al := 1) (by decide) (by decide)
  have hr16 : PhaseCreditSpec fineCostModel (· = rustReallocEvents 8 16 1) 9789 0 0 16 :=
    (PhaseCreditSpec.rustRealloc_small_small fineCostModel (old := 8) (new := 16) (al := 1)
      (by decide) (by decide) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)
      (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
      (fineSmallReallocCost_le_9789_of_le_256 (by decide))
      (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 16)
  have hcat : PhaseCreditSpec fineCostModel
      (· = rustAllocEvents 8 1 ++ rustReallocEvents 8 16 1) 19578 0 0 16 :=
    ((ha8.concat hr16).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  have hall : PhaseCreditSpec fineCostModel _ 19578 0 0 16 :=
    ((PhaseCreditSpec.nil fineCostModel).or (ha8.or hcat)).mono
      (by decide) (by decide) (by decide) (by decide)
  exact hall.of_imp fun evs h => by
    unfold DecimalEnv decimalEvents at h
    rw [h]
    exact s3a5_pushBytesEvents_zero_cases hlen


private theorem s3a5_w4CloneACDom_credit :
    PhaseCreditSpec fineCostModel W4CloneACDomEnv 36295 0 0 208000 where
  req_align evs := fun ⟨_, _, hbob, hE⟩ =>
    (sessionClone_freshBob16K_fine_phaseCredit hbob (Nat.le_refl 16384)).req_align evs hE
  credit_le st0 := fun ⟨_, _, hbob, hE⟩ =>
    (sessionClone_freshBob16K_fine_phaseCredit hbob (Nat.le_refl 16384)).credit_le st0 hE

private theorem s3a5_sessLoadStep_credit (F0 : FsFiles) (peer : AddrGhost)
    (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec fineCostModel (W4BinarySessLoadStepEnv cliIo.rd F0 peer)
      17517856 5316629 8478747 2097152 := by
  unfold W4BinarySessLoadStepEnv cliSessionKitLoadPollEnv
  have hpeerVal : peer.val.name.length ≤ 40 := hpeer
  have haddrLen : (addressText peer.val).length ≤ 64 := addressText_peer_length_le_64 hpeer
  have hdcSess := s3_dirDomainCaps_64 dirDomainCaps_opened_sess (by decide)
  have hAddr := addrTextValEnv_decimal_fine_phaseCredit_tight peer.val hpeerVal
  have hGetSess : PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0
        StoresGhost.opened.sessions (addressText peer.val))
      595741 2105347 3162118 2097152 :=
    (dirGetEnv_path_readFile_fine_phaseCredit_tight
      cliIo.rd F0 StoresGhost.opened.sessions (addressText peer.val) hdcSess haddrLen
      (fun _ h => cliRd_ok_le_fileCap h)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hOptDeser : PhaseCreditSpec fineCostModel
      (OptLoadDeserEnv scopeKit (ofBytesEnv RecordDeserializeCancelEnv)
        (StoresGhost.opened.sessions.get cliIo.rd F0 (addressText peer.val)))
      deserCancelFineCum deserCancelFineLive deserCancelFinePeak deserCancelFineMaxReq := by
    unfold OptLoadDeserEnv
    cases hget : StoresGhost.opened.sessions.get cliIo.rd F0 (addressText peer.val) with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil =>
        exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      | cons b0 bsRest =>
        have hlen : (b0 :: bsRest).length ≤ 2097152 := by
          change cliIo.rd F0 _ = .ok (b0 :: bsRest) at hget
          exact cliRd_ok_le_fileCap hget
        exact s3_phaseCreditSpec_exists fun r henc => by
          unfold ofBytesEnv
          have hlen' : (encodeRecord r).length ≤ 2097152 := by rw [henc]; exact hlen
          exact (recordDeserializeCancelEnv_fine_phaseCreditSpec hlen').of_imp fun _ h => h.2
  have hPoll := hAddr.seq
    (hGetSess.seq (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hOptDeser))
  exact (w4BoxedStoreStep_fine_le_28 (by decide) hPoll).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem s3a5_idTrustStep_credit (F0 : FsFiles) (peer : AddrGhost)
    (remoteIdKey : IdentityKey) (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec fineCostModel (W4BinaryIdTrustStepEnv cliIo.rd F0 peer remoteIdKey)
      596479 2105347 3162118 2097152 := by
  unfold W4BinaryIdTrustStepEnv
  have hdcPeers := s3_dirDomainCaps_64 dirDomainCaps_opened_peers (by decide)
  have hGet : PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0
        StoresGhost.opened.identity.peers peer.val.name)
      595741 2105347 3162118 2097152 :=
    (dirGetEnv_path_readFile_fine_phaseCredit_tight
      cliIo.rd F0 StoresGhost.opened.identity.peers peer.val.name hdcPeers
      (Nat.le_trans hpeer (by decide))
      (fun _ h => cliRd_ok_le_fileCap h)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hPoll := seq_freeOnly_phaseCredit fineCostModel_freeNonInc hGet
  exact (w4BoxedStoreStep_fine_le_44 (by decide) hPoll).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem s3a5_idSaveStep_credit (F0 : FsFiles) (peer : AddrGhost)
    (remoteIdKey : IdentityKey) (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec fineCostModel (W4BinaryIdSaveStepEnv cliIo.rd F0 peer remoteIdKey)
      625846 2105347 3162118 2097152 := by
  unfold W4BinaryIdSaveStepEnv cliIdentityKitSavePollEnv
  have hdcPeers := s3_dirDomainCaps_64 dirDomainCaps_opened_peers (by decide)
  have hGet : PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0
        StoresGhost.opened.identity.peers peer.val.name)
      595741 2105347 3162118 2097152 :=
    (dirGetEnv_path_readFile_fine_phaseCredit_tight
      cliIo.rd F0 StoresGhost.opened.identity.peers peer.val.name hdcPeers
      (Nat.le_trans hpeer (by decide))
      (fun _ h => cliRd_ok_le_fileCap h)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hTail : PhaseCreditSpec fineCostModel
      (cliIdentityKitSaveTailEnv DirPutStrEnv StoresGhost.opened.identity peer.val remoteIdKey
        (StoresGhost.opened.identity.peers.get cliIo.rd F0 peer.val.name))
      29367 0 0 192 := by
    unfold cliIdentityKitSaveTailEnv
    cases StoresGhost.opened.identity.peers.get cliIo.rd F0 peer.val.name with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok _ =>
      have hpks : PhaseCreditSpec fineCostModel PublicKeySerializeEnv 9789 0 0 33 := by
        unfold PublicKeySerializeEnv publicKeySerializeEvents
        exact s3_rustAlloc_small_credit (req := 33) (al := 1) (by decide) (by decide)
      have hput := s3_dirPutStr_opened_credit (dir := StoresGhost.opened.identity.peers) rfl
        (Nat.le_trans hpeer (by decide)) remoteIdKey.serialize
      have hf := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
      exact (hf.seq (hpks.seq hput)).mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  exact (w4BoxedStoreStep_fine_le_44 (by decide) (hGet.seq hTail)).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem s3a5_recordSerializeSeqFree_credit
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (hEnc : (encodeRecord r).length ≤ 2097152) :
    PhaseCreditSpec fineCostModel (RecordSerializeSeqFreeEnv g r)
      8420940 3480713 3480713 2097152 := by
  have hp : 1080975 + optLargeCost fineCostModel 286196 + optLargeCost fineCostModel 2097152 ≤
      3480713 := by
    rw [optLargeCost_fine_eq 286196, optLargeCost_fine_eq 2097152]; decide
  have hr : max (max 208000 286196) 2097152 ≤ 2097152 := by decide
  exact (PhaseCreditSpec.recordSerialize_seqFree_tight fineCostModel_modelHyps g r).mono
    (recordSerializeTightCum_fine_le_of_dom hValid)
    (Nat.le_trans (recordSerializePeak_fine_le_of_dom hValid hEnc) hp)
    (Nat.le_trans (recordSerializePeak_fine_le_of_dom hValid hEnc) hp)
    (Nat.le_trans (recordSerializeMaxReq_le_of_dom hValid hEnc) hr)

private theorem s3a5_sessStoreStep_credit (peer : AddrGhost)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    (hpeer : peer.name.bytes.length ≤ 40)
    (hValid : ∀ G ses, g_rec.cur = some G → r_rec.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (hEnc : (encodeRecord r_rec).length ≤ 2097152) :
    PhaseCreditSpec fineCostModel (W4BinarySessStoreStepEnv peer g_rec r_rec)
      8442732 3480713 3480713 2097152 := by
  unfold W4BinarySessStoreStepEnv cliSessionKitStorePollEnv
  have hAddr := addrTextValEnv_decimal_fine_phaseCredit_tight peer.val hpeer
  have hSer := s3a5_recordSerializeSeqFree_credit hValid hEnc
  have hPut := s2b_dirPutTail_opened_credit (dir := StoresGhost.opened.sessions) rfl
    (addressText peer.val)
  exact (w4BoxedStoreStep_fine_le_44 (by decide) (hAddr.seq (hSer.seq hPut))).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem s3a5_sessStorePrev1Step_credit (peer : AddrGhost)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (enc : List (BitVec 8))
    (hpeer : peer.name.bytes.length ≤ 40)
    (hbob : PostBobPrev1Dom w4PostBobPqCap 2097152 postBobTotalPrev1Cap286K G sess enc) :
    PhaseCreditSpec fineCostModel (W4BinarySessStorePrev1StepEnv peer G sess enc)
      2682704
      ((w4PostBobOneChainLarge + fineOptLarge w4PostBobPqCap) +
        fineOptLarge 2097152 + fineOptLarge postBobTotalPrev1Cap286K)
      ((w4PostBobOneChainLarge + fineOptLarge w4PostBobPqCap) +
        fineOptLarge 2097152 + fineOptLarge postBobTotalPrev1Cap286K)
      postBobTotalPrev1Cap286K := by
  unfold W4BinarySessStorePrev1StepEnv
  have hAddr := addrTextValEnv_decimal_fine_phaseCredit_tight peer.val hpeer
  have hSer := (PhaseCreditSpec.serializePrev1_seqFree_tight fineCostModel_modelHyps G sess enc).mono
    (serializePrev1TightCum_fine_postBob_le hbob)
    (serializePrev1Peak_fine_postBob_le hbob)
    (serializePrev1Peak_fine_postBob_le hbob)
    (serializePrev1MaxReq_postBob_le hbob (by decide) (by decide) (by decide))
  have hPut := s3_dirPut_opened_credit (dir := StoresGhost.opened.sessions) rfl
    (addressText peer.val) (encodeRecordPrev1Mem G sess enc)
  exact (w4BoxedStoreStep_fine_le_44 (by decide) (hAddr.seq (hSer.seq hPut))).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem s3a5_archiveDirect_credit {maxEncLen : Nat} (hEnc : maxEncLen ≤ 2097152) :
    PhaseCreditSpec fineCostModel (W4BinaryArchiveDirectEnv maxEncLen)
      4213766 2105347 2105347 2097152 := by
  unfold W4BinaryArchiveDirectEnv
  have hf := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hAlloc : PhaseCreditSpec fineCostModel
      (fun e => ∃ n ≤ maxEncLen, e = rustAllocEvents n 1)
      4203843 2105347 2105347 2097152 :=
    s3_phaseCreditSpec_exists fun n hn => by
      have hnCap : n ≤ 2097152 := Nat.le_trans hn hEnc
      have hc : 2 * n + 9539 ≤ 4203843 :=
        Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hnCap) 9539) (by decide)
      have hl : optLargeCost fineCostModel n ≤ 2105347 := by
        rw [optLargeCost_fine_eq n]
        exact Nat.le_trans (fineOptLarge_mono hnCap) (by decide)
      exact (PhaseCreditSpec.rustAlloc_optLarge fineCostModel_modelHyps
        (req := n) (al := 1) (by decide)).mono hc hl hl hnCap
  have hVec : PhaseCreditSpec fineCostModel (W4BoundedEvs 1 192) 9923 0 0 192 :=
    (phaseCredit_w4BoundedEvs_small fineCostModel_modelHyps 1 192
      (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
  exact (hf.seq (hAlloc.seq (hVec.seq hf))).mono
    (by decide) (by decide) (by decide) (by decide)

private theorem s3a5_promoteArchive_credit
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    (hValid : ∀ G ses, g_arch.cur = some G → r_arch.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom 286196 ses)
    (hEnc : (encodeRecord r_arch).length ≤ 2097152) :
    PhaseCreditSpec fineCostModel (W4BinaryPromoteArchiveEnv g_arch r_arch)
      8430863 3480713 3480713 2097152 := by
  unfold W4BinaryPromoteArchiveEnv
  have hPush : PhaseCreditSpec fineCostModel (W4BoundedEvs 1 192) 9923 0 0 192 :=
    (phaseCredit_w4BoundedEvs_small fineCostModel_modelHyps 1 192
      (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
  have hProm := phaseCredit_promoteStateArchive fineCostModel_modelHyps
    (s3a5_recordSerializeSeqFree_credit hValid hEnc) hPush
  have hDir := s3a5_archiveDirect_credit hEnc
  exact (hProm.or hDir).mono (by decide) (by decide) (by decide) (by decide)

private theorem s3a5_kemKpFromPubPriv_credit :
    PhaseCreditSpec fineCostModel (SeqEnv KemKeyPairFromPubPrivEnv FreeOnlyEvs)
      19578 0 0 3168 := by
  have ha1 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 1568 1) 9789 0 0 1568 :=
    s3_rustAlloc_small_credit (req := 1568) (al := 1) (by decide) (by decide)
  have ha2 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 3168 1) 9789 0 0 3168 :=
    s3_rustAlloc_small_credit (req := 3168) (al := 1) (by decide) (by decide)
  have hkp : PhaseCreditSpec fineCostModel KemKeyPairFromPubPrivEnv 19578 0 0 3168 :=
    ((ha1.concat ha2).of_imp fun _ h => by
      unfold KemKeyPairFromPubPrivEnv kemKeyPairFromPubPrivEvents at h
      exact ⟨_, _, h, rfl, rfl⟩).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  exact phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hkp

private theorem s3a5_kpkPass_credit (F0 : FsFiles) (dir : DirGhost) (kpkId : BitVec 32)
    (hdc : DirDomainCaps 64 0 0 dir)
    (hcapRd : ∀ bs, cliIo.rd F0 (pathOf dir.path (keyName kpkId)) = .ok bs → bs.length ≤ 4900)
    (hcapGet : ∀ bs, dir.get cliIo.rd F0 (keyName kpkId) = .ok bs → bs.length ≤ 4900)
    (hSpkDec : ∀ {bs : List (BitVec 8)} {L : Nat}, bs.length ≤ L → L ≤ 4900 →
      PhaseCreditSpec fineCostModel (CliSpkDecodeEnv bs) (380 * L + 750000) 0 0 9808) :
    PhaseCreditSpec fineCostModel
      (KpkPassEnv DecimalEnv
        (fun d k => DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0 d (keyName k))
        CliSpkDecodeEnv cliIo.rd F0 dir kpkId)
      (19578 + ((21185 + fineReadFileCum (max 0 4900)) + (380 * 4900 + 750000)))
      (0 + (fineReadFileLive (max 0 4900) + 0))
      (max 0 (0 + max (fineReadFilePeak (max 0 4900)) (fineReadFileLive (max 0 4900) + 0)))
      (max 16 (max (max 256 (fineReadFileMaxReq (max 0 4900))) 9808)) := by
  unfold KpkPassEnv
  have hDec := s3a5_decimal_credit kpkId
  have hGet := dirGetEnv_path_readFile_fine_phaseCredit_tight
    cliIo.rd F0 dir (keyName kpkId) hdc
    (Nat.le_trans (keyName_length_le kpkId) (by decide)) hcapRd
  have hOpt : PhaseCreditSpec fineCostModel
      (OptKpkDecodeEnv CliSpkDecodeEnv (dir.get cliIo.rd F0 (keyName kpkId)))
      (380 * 4900 + 750000) 0 0 9808 := by
    unfold OptKpkDecodeEnv
    cases hgr : dir.get cliIo.rd F0 (keyName kpkId) with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil =>
        exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      | cons b0 bsRest =>
        exact hSpkDec (hcapGet (b0 :: bsRest) hgr) (Nat.le_refl 4900)
  exact hDec.seq (hGet.seq (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hOpt))

private theorem s3a5_subst_rd_files
    {P : ReadRule → FsFiles → List AllocEvent → Prop} {rd1 rd2 : ReadRule} {f1 f2 : FsFiles}
    {c l p r : Nat}
    (hrd : rd1 = rd2) (hf : f1 = f2)
    (h : PhaseCreditSpec fineCostModel (P rd2 f2) c l p r) :
    PhaseCreditSpec fineCostModel (P rd1 f1) c l p r := by
  subst hrd; subst hf; exact h

private theorem s3a5_ite_or_nil (b : Bool) {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec fineCostModel E c l p r) :
    PhaseCreditSpec fineCostModel (if b then E else (· = [])) c l p r := by
  cases b
  · exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le c) (Nat.zero_le l) (Nat.zero_le p) (Nat.zero_le r)
  · exact h

private theorem s3a5_kpkPass_empty_credit (F0 : FsFiles) (kpkId : BitVec 32)
    (hdc : DirDomainCaps 64 0 0 StoresGhost.opened.kyber.oneTime)
    (hempty : StoresGhost.opened.kyber.oneTime.get cliIo.rd F0 (keyName kpkId) = .ok []) :
    PhaseCreditSpec fineCostModel
      (KpkPassEnv DecimalEnv
        (fun d k => DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0 d (keyName k))
        CliSpkDecodeEnv cliIo.rd F0 StoresGhost.opened.kyber.oneTime kpkId)
      (19578 + ((21185 + max 738 (fineReadFileCum 0)) + 0))
      (0 + (fineReadFileLive 0 + 0))
      (max 0 (0 + max (fineReadFilePeak 0) (fineReadFileLive 0 + 0)))
      (max 16 (max (max 256 (fineReadFileMaxReq 0)) 0)) := by
  unfold KpkPassEnv
  have hDec := s3a5_decimal_credit kpkId
  have hcap0 : ∀ bs,
      cliIo.rd F0 (pathOf StoresGhost.opened.kyber.oneTime.path (keyName kpkId)) = .ok bs →
        bs.length ≤ 0 := by
    intro bs h
    change StoresGhost.opened.kyber.oneTime.get cliIo.rd F0 (keyName kpkId) = .ok bs at h
    rw [hempty] at h
    injection h with h
    subst h
    decide
  have hGet := dirGetEnv_path_readFile_fine_phaseCredit_tight
    cliIo.rd F0 StoresGhost.opened.kyber.oneTime (keyName kpkId) hdc
    (Nat.le_trans (keyName_length_le kpkId) (by decide)) hcap0
  have hOpt : PhaseCreditSpec fineCostModel
      (OptKpkDecodeEnv CliSpkDecodeEnv
        (StoresGhost.opened.kyber.oneTime.get cliIo.rd F0 (keyName kpkId)))
      0 0 0 0 := by
    rw [hempty]
    exact PhaseCreditSpec.nil fineCostModel
  exact hDec.seq (hGet.seq (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hOpt))

private theorem s3a5_kpkPoll_credit (F0 : FsFiles) (kpkId : BitVec 32)
    (hdcKot : DirDomainCaps 64 0 0 StoresGhost.opened.kyber.oneTime)
    {c l p r : Nat}
    (hOt : PhaseCreditSpec fineCostModel
      (KpkPassEnv DecimalEnv
        (fun d k => DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0 d (keyName k))
        CliSpkDecodeEnv cliIo.rd F0 StoresGhost.opened.kyber.oneTime kpkId) c l p r)
    (hLr : PhaseCreditSpec fineCostModel
      (KpkPassEnv DecimalEnv
        (fun d k => DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0 d (keyName k))
        CliSpkDecodeEnv cliIo.rd F0 StoresGhost.opened.kyber.lastResort kpkId) c l p r) :
    let c0 := 19578 + ((21185 + max 738 (fineReadFileCum 0)) + 0)
    let l0 := 0 + (fineReadFileLive 0 + 0)
    let p0 := max 0 (0 + max (fineReadFilePeak 0) (fineReadFileLive 0 + 0))
    let r0 := max 16 (max (max 256 (fineReadFileMaxReq 0)) 0)
    PhaseCreditSpec fineCostModel
      (CliKpkGetPollEnv DecimalEnv
        (fun d k => DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd F0 d (keyName k))
        CliSpkDecodeEnv cliIo.rd F0
        ⟨0#64, 0#64, 0#64, kpkId, StoresGhost.opened.kyber⟩)
      (c0 + c) (l0 + l) (max p0 (l0 + p)) (max r0 r) := by
  dsimp only
  unfold CliKpkGetPollEnv
  dsimp only
  cases hgr : StoresGhost.opened.kyber.oneTime.get cliIo.rd F0 (keyName kpkId) with
  | error u =>
    simp only [CryptoVerification.SignalSession.Cli.pkAnsOf]
    exact hOt.mono
      (Nat.le_add_left _ _) (Nat.le_add_left _ _)
      (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_right _ _))
      (Nat.le_max_right _ _)
  | ok bs =>
    cases bs with
    | nil =>
      simp only [CryptoVerification.SignalSession.Cli.pkAnsOf]
      exact (s3a5_kpkPass_empty_credit F0 kpkId hdcKot hgr).seq hLr
    | cons b0 bsRest =>
      simp only [CryptoVerification.SignalSession.Cli.pkAnsOf]
      cases CryptoVerification.RecordCodecs.KyberPreKeyRecord.deserialize (b0 :: bsRest) with
      | error _ =>
        dsimp only
        exact hOt.mono
          (Nat.le_add_left _ _) (Nat.le_add_left _ _)
          (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_right _ _))
          (Nat.le_max_right _ _)
      | ok _ =>
        dsimp only
        exact hOt.mono
          (Nat.le_add_left _ _) (Nat.le_add_left _ _)
          (Nat.le_trans (Nat.le_add_left _ _) (Nat.le_max_right _ _))
          (Nat.le_max_right _ _)


end S3a5Sub5Helpers

section S3a3Sub3Helpers

open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.SignalSession.Cli
  (KpkMarkPollGhost baseKeyEntry baseKeysName decimalText hasChunk)
open CryptoVerification.SignalSession.Cli.Decimal.Helpers (decimalText_length_le)
open LibsignalBinary.Heap (rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineCostModel_largeCost_eq fineCostModel_smallMaxReq_eq smallReallocCost_le_two_mul_add)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (baseKeysName_length_le dirDomainCaps_opened_kpkLr dirDomainCaps_opened_kpkOt keyName_length_le)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (fineSmallReallocCost_le_9789_of_le_256 optLargeCost_of_gt optLargeCost_of_le)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
  (W4BoxedStoreStepEnv phaseCreditSpec_seq_freeOnly_exact w4BoxedStepCum w4BoxedStepMaxReq
   w4BoxedStoreStep_small_phaseCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
  (DecimalEnv decimalEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetMissEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (cliRd_ok_le_fileCap)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.EpiloguePlacedBudget
  (freeOnlyEvs_optDeallocBufEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudgetAux
  (kpkAfterLrGetPreEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortPlacedBudget
  (KpkBaseKeysReserveEnv KpkLastResortPreAfterGetEnv kpkBaseKeysReserveEventsAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux
  (CliKpkMarkPollEnv KpkAfterLrGetCapFreeBranchEnv KpkOneTimeConsTailEnv KpkOneTimePreAfterGetEnv
   KpkSeenAppendReserveMidEnv OptKpkMarkLastResortTailEnv OptKpkMarkOneTimeTailEnv
   kpkSeenAppendReserveEventsAt)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
  (dirGetEnv_path_readFile_fine_phaseCredit_tight)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (optDeallocBufEvents)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (doReserveEvents publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (pushBytesEvents)

private theorem s3a3_seqEnv_assoc_left {A B C : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : SeqEnv A (SeqEnv B C) evs) : SeqEnv (SeqEnv A B) C evs := by
  rcases h with ha | ⟨e1, e23, rfl, ha, hbc⟩
  · exact Or.inl (Or.inl ha)
  · rcases hbc with hb | ⟨e2, e3, rfl, hb, hc⟩
    · exact Or.inl (Or.inr ⟨e1, e23, rfl, ha, hb⟩)
    · exact Or.inr ⟨e1 ++ e2, e3, (List.append_assoc e1 e2 e3).symm,
        Or.inr ⟨e1, e2, rfl, ha, hb⟩, hc⟩

private theorem s3a3_pushBytesEvents_zero_cases {m : Nat} (hm : m ≤ 10) :
    pushBytesEvents m 0 0 = [] ∨
    pushBytesEvents m 0 0 = rustAllocEvents 8 1 ∨
    pushBytesEvents m 0 0 = rustAllocEvents 8 1 ++ rustReallocEvents 8 16 1 := by
  match m with
  | 0 => exact Or.inl (by decide)
  | 1 => exact Or.inr (Or.inl (by decide))
  | 2 => exact Or.inr (Or.inl (by decide))
  | 3 => exact Or.inr (Or.inl (by decide))
  | 4 => exact Or.inr (Or.inl (by decide))
  | 5 => exact Or.inr (Or.inl (by decide))
  | 6 => exact Or.inr (Or.inl (by decide))
  | 7 => exact Or.inr (Or.inl (by decide))
  | 8 => exact Or.inr (Or.inl (by decide))
  | 9 => exact Or.inr (Or.inr (by decide))
  | 10 => exact Or.inr (Or.inr (by decide))
  | _ + 11 => omega

private theorem s3a3_decimal_credit (id : BitVec 32) :
    PhaseCreditSpec fineCostModel (DecimalEnv id) 19578 0 0 16 := by
  have hlen : (decimalText id.toNat).length ≤ 10 :=
    decimalText_length_le 10 id.toNat (by decide) (Nat.lt_trans id.isLt (by decide))
  have ha8 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 8 1) 9789 0 0 8 :=
    s3_rustAlloc_small_credit (req := 8) (al := 1) (by decide) (by decide)
  have hr16 : PhaseCreditSpec fineCostModel (· = rustReallocEvents 8 16 1) 9789 0 0 16 :=
    (PhaseCreditSpec.rustRealloc_small_small fineCostModel (old := 8) (new := 16) (al := 1)
      (by decide) (by decide) (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)
      (by decide) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
      (fineSmallReallocCost_le_9789_of_le_256 (by decide))
      (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 16)
  have hcat : PhaseCreditSpec fineCostModel
      (· = rustAllocEvents 8 1 ++ rustReallocEvents 8 16 1) 19578 0 0 16 :=
    ((ha8.concat hr16).of_imp fun _ h => ⟨_, _, h, rfl, rfl⟩).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  have hall : PhaseCreditSpec fineCostModel _ 19578 0 0 16 :=
    ((PhaseCreditSpec.nil fineCostModel).or (ha8.or hcat)).mono
      (by decide) (by decide) (by decide) (by decide)
  exact hall.of_imp fun evs h => by
    unfold DecimalEnv decimalEvents at h
    rw [h]
    exact s3a3_pushBytesEvents_zero_cases hlen

private theorem s3a3_baseKeysReserveAt_credit (id : BitVec 32) {spare : Nat} (hsp : spare ≤ 9) :
    PhaseCreditSpec fineCostModel (· = kpkBaseKeysReserveEventsAt id spare) 9789 0 0 38 := by
  have hk : (keyName id).length ≤ 10 := keyName_length_le id
  let old := (keyName id).length + spare
  let newCap := reserveCap old (keyName id).length 10
  have hold_le : old ≤ 19 := by dsimp only [old]; omega
  have hrc : 8 ≤ newCap ∧ newCap ≤ 38 := by dsimp only [newCap, old, reserveCap]; omega
  have htoNat : (BitVec.ofNat 64 old).toNat = old := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hold_le (by decide))]
  by_cases hz : old = 0
  · have hb0 : BitVec.ofNat 64 old = 0#64 := by rw [hz]
    have hd : kpkBaseKeysReserveEventsAt id spare = rustAllocEvents newCap 1 := by
      change doReserveEvents ⟨0#64, BitVec.ofNat 64 old, 0#64, keyName id, 10⟩ =
        rustAllocEvents newCap 1
      unfold doReserveEvents
      dsimp only
      rw [htoNat]
      simp only [hb0, ↓reduceIte]
      exact rfl
    exact ((s3_rustAlloc_small_credit (req := newCap) (al := 1)
      (by decide) (Nat.le_trans hrc.2 (by decide))).of_imp
      (fun _ heq => by rw [heq, hd])).mono
      (Nat.le_refl 9789) (Nat.le_refl 0) (Nat.le_refl 0) hrc.2
  · have hpos : 0 < old := Nat.pos_of_ne_zero hz
    have hne0 : BitVec.ofNat 64 old ≠ 0#64 := by
      intro heq
      have ht := congrArg BitVec.toNat heq
      rw [htoNat] at ht
      exact hz ht
    have hd : kpkBaseKeysReserveEventsAt id spare = rustReallocEvents old newCap 1 := by
      change doReserveEvents ⟨0#64, BitVec.ofNat 64 old, 0#64, keyName id, 10⟩ =
        rustReallocEvents old newCap 1
      unfold doReserveEvents
      dsimp only
      rw [htoNat]
      simp only [hne0, ↓reduceIte]
      exact rfl
    exact ((PhaseCreditSpec.rustRealloc_small_small fineCostModel
      (old := old) (new := newCap) (al := 1) (by decide)
      (Nat.le_trans (by decide : 1 ≤ 8) hrc.1) hpos
      (by rw [fineCostModel_smallMaxReq_eq]; exact Nat.le_trans hold_le (by decide))
      (Nat.lt_of_lt_of_le (by decide : 0 < 8) hrc.1)
      (by rw [fineCostModel_smallMaxReq_eq]; exact Nat.le_trans hrc.2 (by decide))).of_imp
      (fun _ heq => by rw [heq, hd])).mono
      (fineSmallReallocCost_le_9789_of_le_256 (Nat.le_trans hrc.2 (by decide)))
      (Nat.le_refl 0) (Nat.le_refl 0) hrc.2

private theorem s3a3_baseKeysReserve_credit (id : BitVec 32) :
    PhaseCreditSpec fineCostModel (KpkBaseKeysReserveEnv id) 9789 0 0 38 := by
  have hex : PhaseCreditSpec fineCostModel
      (fun evs => ∃ spare, spare ≤ 9 ∧ evs = kpkBaseKeysReserveEventsAt id spare)
      9789 0 0 38 :=
    s3_phaseCreditSpec_exists fun _ hsp => s3a3_baseKeysReserveAt_credit id hsp
  exact (((PhaseCreditSpec.nil fineCostModel).or hex).mono
    (by decide) (by decide) (by decide) (by decide)).of_imp fun evs h => by
    unfold KpkBaseKeysReserveEnv at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨0, by decide, rfl⟩
    · exact Or.inr ⟨1, by decide, rfl⟩
    · exact Or.inr ⟨2, by decide, rfl⟩
    · exact Or.inr ⟨3, by decide, rfl⟩
    · exact Or.inr ⟨4, by decide, rfl⟩
    · exact Or.inr ⟨5, by decide, rfl⟩
    · exact Or.inr ⟨6, by decide, rfl⟩
    · exact Or.inr ⟨7, by decide, rfl⟩
    · exact Or.inr ⟨8, by decide, rfl⟩
    · exact Or.inr ⟨9, by decide, rfl⟩

private theorem s3a3_dirGetFixed_ok_credit
    (F0 : FsFiles) (dir : DirGhost) (name : List (BitVec 8))
    {bs : List (BitVec 8)} {fileCap : Nat}
    (hdc : DirDomainCaps 64 0 0 dir)
    (hch : dir.changed = [])
    (hname : name.length ≤ 64)
    (hrd : cliIo.rd F0 (pathOf dir.path name) = .ok bs)
    (hbs : bs.length ≤ fileCap) :
    PhaseCreditSpec fineCostModel
      (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd F0 dir name)
      (21185 + max 738 (fineReadFileCum fileCap))
      (fineReadFileLive fileCap)
      (fineReadFilePeak fileCap)
      (max 256 (fineReadFileMaxReq fileCap)) := by
  have hcap : ∀ bs', cliIo.rd F0 (pathOf dir.path name) = .ok bs' → bs'.length ≤ fileCap := by
    intro bs' h
    rw [hrd] at h
    injection h with heq
    subst heq
    exact hbs
  have hbase := dirGetEnv_path_readFile_fine_phaseCredit_tight cliIo.rd F0 dir name hdc hname hcap
  dsimp only at hbase
  have h0 : max 0 fileCap = fileCap := by omega
  rw [h0] at hbase
  exact hbase.of_imp fun evs hm => by
    unfold DirGetEnv at hm ⊢
    simp only [hch, List.find?_nil] at hm ⊢
    unfold DirGetMissEnv at hm ⊢
    exact s3_seqEnv_mono (fun _ h => h)
      (fun _ hr => s3_seqEnv_mono
        (fun _ hrf => hrf.elim id fun ⟨herr, _, _⟩ => by rw [hrd] at herr; cases herr)
        (fun _ h => h) hr) hm

private theorem s3a3_afterLrGetPre_credit :
    PhaseCreditSpec fineCostModel (· = kpkAfterLrGetPreEvents) 19578 0 0 37 := by
  have h33 : PhaseCreditSpec fineCostModel (· = publicKeySerializeEvents) 9789 0 0 33 :=
    s3_rustAlloc_small_credit (req := 33) (al := 1) (by decide) (by decide)
  have h37 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 37 1) 9789 0 0 37 :=
    s3_rustAlloc_small_credit (req := 37) (al := 1) (by decide) (by decide)
  have hf33 : PhaseCreditSpec fineCostModel (· = rustDeallocEvents 33 1) 0 0 0 0 :=
    PhaseCreditSpec.rustDealloc_align16 fineCostModel (by decide)
  exact (((h33.concat h37).concat hf33).of_imp fun _ h => by
    rw [h]
    unfold kpkAfterLrGetPreEvents
    exact ⟨_, _, rfl, ⟨_, _, rfl, rfl, rfl⟩, rfl⟩).mono
    (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

private theorem s3a3_reserveCap37_eq_two_mul {len spare : Nat} (hge : 37 ≤ len + spare) :
    reserveCap (len + spare) len 37 = 2 * (len + spare) := by
  unfold reserveCap
  omega

private theorem s3a3_reserveCap37_small {len spare : Nat} (hlt : len + spare < 37) :
    37 ≤ reserveCap (len + spare) len 37 ∧ reserveCap (len + spare) len 37 ≤ 73 := by
  unfold reserveCap
  omega

private theorem s3a3_ll_keep_bound (m w old : Nat) :
    m + w ≤ (m - old) + (old + w) := by
  omega

private theorem s3a3_ll_live_bound {m w old : Nat} (hold : old ≤ m + 7) :
    (m - old) + (2 * old + w) ≤ m + m + w + 14 := by
  omega

private theorem s3a3_ll_peak_bound {m w old : Nat} (hold : old ≤ m + 7) :
    (m - old) + (old + w) + (2 * old + w) ≤ 3 * m + 2 * w + 21 := by
  omega

private theorem s3a3_concat_seenReserveAt_credit
    {E₁ : List AllocEvent → Prop} {c₁ : Nat}
    (h₁ : PhaseCreditSpec fineCostModel E₁ c₁ 2105347 3162118 2097152)
    {seenBs : List (BitVec 8)} (hseen : seenBs.length ≤ 2097123)
    {spare : Nat} (hsp : spare < 37) :
    PhaseCreditSpec fineCostModel
      (ConcatEnv E₁ (· = kpkSeenAppendReserveEventsAt seenBs spare))
      (c₁ + 279873) 4202513 6307867 4194318 := by
  let old := seenBs.length + spare
  let newCap := reserveCap old seenBs.length 37
  have hsp36 : spare ≤ 36 := Nat.le_of_lt_succ hsp
  have hold_max : old ≤ 2097159 :=
    Nat.le_trans (Nat.add_le_add hseen hsp36) (by decide)
  have htoNat : (BitVec.ofNat 64 old).toNat = old := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hold_max (by decide))]
  by_cases hz : old = 0
  · have hb0 : BitVec.ofNat 64 old = 0#64 := by rw [hz]
    have hlt37 : seenBs.length + spare < 37 := by change old < 37; rw [hz]; decide
    have hrc := s3a3_reserveCap37_small hlt37
    have hd : kpkSeenAppendReserveEventsAt seenBs spare = rustAllocEvents newCap 1 := by
      change doReserveEvents ⟨0#64, BitVec.ofNat 64 old, 0#64, seenBs, 37⟩ =
        rustAllocEvents newCap 1
      unfold doReserveEvents
      dsimp only
      rw [htoNat]
      simp only [hb0, ↓reduceIte]
      exact rfl
    have ha : PhaseCreditSpec fineCostModel
        (· = kpkSeenAppendReserveEventsAt seenBs spare) 9789 0 0 73 :=
      ((s3_rustAlloc_small_credit (req := newCap) (al := 1)
        (by decide) (Nat.le_trans hrc.2 (by decide))).of_imp
        (fun _ heq => by rw [heq, hd])).mono
        (Nat.le_refl 9789) (Nat.le_refl 0) (Nat.le_refl 0) hrc.2
    exact (h₁.concat ha).mono
      (Nat.add_le_add_left (by decide : 9789 ≤ 279873) c₁)
      (by decide) (by decide) (by decide)
  · have hpos : 0 < old := Nat.pos_of_ne_zero hz
    have hne0 : BitVec.ofNat 64 old ≠ 0#64 := by
      intro heq
      have ht := congrArg BitVec.toNat heq
      rw [htoNat] at ht
      exact hz ht
    have hd : kpkSeenAppendReserveEventsAt seenBs spare = rustReallocEvents old newCap 1 := by
      change doReserveEvents ⟨0#64, BitVec.ofNat 64 old, 0#64, seenBs, 37⟩ =
        rustReallocEvents old newCap 1
      unfold doReserveEvents
      dsimp only
      rw [htoNat]
      simp only [hne0, ↓reduceIte]
      exact rfl
    by_cases hlt37 : old < 37
    · have hrc := s3a3_reserveCap37_small hlt37
      have hss : PhaseCreditSpec fineCostModel
          (· = kpkSeenAppendReserveEventsAt seenBs spare) 279873 0 0 73 :=
        ((PhaseCreditSpec.rustRealloc_small_small fineCostModel
          (old := old) (new := newCap) (al := 1) (by decide)
          (Nat.le_trans (by decide : 1 ≤ 37) hrc.1) hpos
          (by rw [fineCostModel_smallMaxReq_eq]; exact Nat.le_trans (Nat.le_of_lt hlt37) (by decide))
          (Nat.lt_of_lt_of_le (by decide : 0 < 37) hrc.1)
          (by rw [fineCostModel_smallMaxReq_eq]; exact Nat.le_trans hrc.2 (by decide))).of_imp
          (fun _ heq => by rw [heq, hd])).mono
          (Nat.le_trans (fineSmallReallocCost_le_9789_of_le_256 (Nat.le_trans hrc.2 (by decide)))
            (by decide))
          (Nat.le_refl 0) (Nat.le_refl 0) hrc.2
      exact (h₁.concat hss).mono
        (Nat.le_refl _) (by decide) (by decide) (by decide)
    · have hge37 : 37 ≤ old := Nat.le_of_not_lt hlt37
      have hnew_eq : newCap = 2 * old := s3a3_reserveCap37_eq_two_mul hge37
      have hnew_ge74 : 74 ≤ newCap := by
        rw [hnew_eq]
        exact Nat.mul_le_mul_left 2 hge37
      by_cases hold_sm : old ≤ 135167
      · have hnew270 : newCap ≤ 270334 := by
          rw [hnew_eq]
          exact Nat.le_trans (Nat.mul_le_mul_left 2 hold_sm) (by decide)
        by_cases hnew_sm : newCap ≤ 135167
        · have hsr : HasFineReallocCredit.smallReallocCost fineCostModel newCap ≤ 279873 :=
            Nat.le_trans (smallReallocCost_le_two_mul_add newCap)
              (Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hnew_sm) 9539) (by decide))
          have hss : PhaseCreditSpec fineCostModel
              (· = kpkSeenAppendReserveEventsAt seenBs spare) 279873 0 0 135167 :=
            ((PhaseCreditSpec.rustRealloc_small_small fineCostModel
              (old := old) (new := newCap) (al := 1) (by decide)
              (Nat.le_trans (by decide : 1 ≤ 74) hnew_ge74) hpos
              (by rw [fineCostModel_smallMaxReq_eq]; exact hold_sm)
              (Nat.lt_of_lt_of_le (by decide : 0 < 74) hnew_ge74)
              (by rw [fineCostModel_smallMaxReq_eq]; exact hnew_sm)).of_imp
              (fun _ heq => by rw [heq, hd])).mono
              hsr (Nat.le_refl 0) (Nat.le_refl 0) hnew_sm
          exact (h₁.concat hss).mono
            (Nat.le_refl _) (by decide) (by decide) (by decide)
        · have hnew_gt : 135167 < newCap := Nat.lt_of_not_ge hnew_sm
          have hsl : PhaseCreditSpec fineCostModel
              (· = kpkSeenAppendReserveEventsAt seenBs spare) 122 278529 278529 270334 :=
            ((PhaseCreditSpec.rustRealloc_small_large fineCostModel
              (old := old) (new := newCap) (al := 1) (by decide)
              (Nat.le_trans (by decide : 1 ≤ 74) hnew_ge74) hpos
              (by rw [fineCostModel_smallMaxReq_eq]; exact hold_sm)
              (by rw [fineCostModel_smallMaxReq_eq]; exact hnew_gt)).of_imp
              (fun _ heq => by rw [heq, hd])).mono
              (by decide)
              (by rw [fineCostModel_largeCost_eq]
                  exact Nat.le_trans (Nat.add_le_add_right hnew270 8195) (by decide))
              (by rw [fineCostModel_largeCost_eq]
                  exact Nat.le_trans (Nat.add_le_add_right hnew270 8195) (by decide))
              hnew270
          exact (h₁.concat hsl).mono
            (Nat.add_le_add_left (by decide : 122 ≤ 279873) c₁)
            (by decide) (by decide) (by decide)
      · have hold_gt : 135167 < old := Nat.lt_of_not_ge hold_sm
        have hnew_gt : 135167 < newCap := by
          rw [hnew_eq]
          exact Nat.lt_of_lt_of_le hold_gt (Nat.le_mul_of_pos_left old (by decide : 0 < 2))
        have hnew_max : newCap ≤ 4194318 := by
          rw [hnew_eq]
          exact Nat.le_trans (Nat.mul_le_mul_left 2 hold_max) (by decide)
        let l_keep := 2097152 - old
        have hlive_w : 2105347 ≤ l_keep + HasFineReallocCredit.largeCost fineCostModel old := by
          rw [fineCostModel_largeCost_eq]
          exact Nat.le_trans (by decide : 2105347 ≤ 2097152 + 8195)
            (s3a3_ll_keep_bound 2097152 8195 old)
        have h₁' := h₁.mono (Nat.le_refl c₁) hlive_w (Nat.le_refl 3162118) (Nat.le_refl 2097152)
        have hll := h₁'.concat_rustRealloc_large_large (al := 1) (new := newCap)
          (by decide) (Nat.le_trans (by decide : 1 ≤ 74) hnew_ge74)
          (by rw [fineCostModel_smallMaxReq_eq]; exact hold_gt)
          (by rw [fineCostModel_smallMaxReq_eq]; exact hnew_gt)
        have hold_m7 : old ≤ 2097152 + 7 := Nat.le_trans hold_max (by decide)
        refine (hll.of_imp fun _ ⟨e1, e2, heq, he1, he2⟩ =>
          ⟨e1, e2, heq, he1, by rw [he2, hd]⟩).mono
          (Nat.add_le_add_left (by decide : HasFineReallocCredit.largeMetaCost fineCostModel ≤ 279873) c₁)
          ?_ ?_ (Nat.max_le.mpr ⟨by decide, hnew_max⟩)
        · dsimp only [l_keep]
          rw [fineCostModel_largeCost_eq, hnew_eq]
          exact Nat.le_trans (s3a3_ll_live_bound hold_m7) (by decide)
        · dsimp only [l_keep]
          rw [fineCostModel_largeCost_eq, fineCostModel_largeCost_eq, hnew_eq]
          exact Nat.max_le.mpr ⟨by decide, Nat.le_trans (s3a3_ll_peak_bound hold_m7) (by decide)⟩

private theorem s3a3_concat_seenAppendReserveMid_credit
    {E₁ : List AllocEvent → Prop} {c₁ : Nat}
    (h₁ : PhaseCreditSpec fineCostModel E₁ c₁ 2105347 3162118 2097152)
    {seenBs : List (BitVec 8)} (hseen : seenBs.length ≤ 2097123) :
    PhaseCreditSpec fineCostModel
      (ConcatEnv E₁ (KpkSeenAppendReserveMidEnv seenBs))
      (c₁ + 279873) 4202513 6307867 4194318 := by
  have hfast : PhaseCreditSpec fineCostModel (ConcatEnv E₁ FreeOnlyEvs)
      (c₁ + 279873) 4202513 6307867 4194318 :=
    (h₁.concat (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc)).mono
      (Nat.add_le_add_left (Nat.zero_le _) c₁) (by decide) (by decide) (by decide)
  have hfree37 : PhaseCreditSpec fineCostModel (· = optDeallocBufEvents 37#64) 0 0 0 0 :=
    (PhaseCreditSpec.freeOnly fineCostModel_freeNonInc).of_imp fun _ h => by
      rw [h]
      exact freeOnlyEvs_optDeallocBufEvents 37#64
  have hgrow1 : ∀ spare, spare < 37 →
      PhaseCreditSpec fineCostModel
        (ConcatEnv E₁
          (· = kpkSeenAppendReserveEventsAt seenBs spare ++ optDeallocBufEvents 37#64))
        (c₁ + 279873) 4202513 6307867 4194318 := fun spare hsp =>
    (((s3a3_concat_seenReserveAt_credit h₁ hseen hsp).concat hfree37).of_imp
      fun _ ⟨e1, _, heq, he1, he2⟩ => by
        rw [heq, he2, ← List.append_assoc]
        exact ⟨e1 ++ kpkSeenAppendReserveEventsAt seenBs spare, optDeallocBufEvents 37#64,
          rfl, ⟨e1, _, rfl, he1, rfl⟩, rfl⟩).mono
      (Nat.le_of_eq (Nat.add_zero _)) (by decide) (by decide) (by decide)
  have hgrow : PhaseCreditSpec fineCostModel
      (fun evs => ∃ spare, spare < 37 ∧
        ConcatEnv E₁
          (· = kpkSeenAppendReserveEventsAt seenBs spare ++ optDeallocBufEvents 37#64) evs)
      (c₁ + 279873) 4202513 6307867 4194318 :=
    s3_phaseCreditSpec_exists hgrow1
  exact ((hfast.or hgrow).mono
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩) (by decide) (by decide) (by decide)).of_imp
    fun _ ⟨e1, e2, heq, he1, hmid⟩ => by
      cases hmid with
      | fast e2 hf => exact Or.inl ⟨e1, e2, heq, he1, hf⟩
      | grow spare hsp => exact Or.inr ⟨spare, hsp, e1, _, heq, he1, rfl⟩

private theorem s3a3_fineReadFile_0 :
    fineReadFileCum 0 = 0 ∧ fineReadFileLive 0 = 0 ∧
    fineReadFilePeak 0 = 0 ∧ fineReadFileMaxReq 0 = 0 := by
  unfold fineReadFileCum fineReadFileLive fineReadFilePeak fineReadFileMaxReq
  decide

private theorem s3a3_fineReadFile_4900 :
    fineReadFileCum 4900 = 573818 ∧ fineReadFileLive 4900 = 2105347 ∧
    fineReadFilePeak 4900 = 3162118 ∧ fineReadFileMaxReq 4900 = 2097152 := by
  unfold fineReadFileCum fineReadFileLive fineReadFilePeak fineReadFileMaxReq
  rw [optLargeCost_of_le fineCostModel (by rw [fineCostModel_smallMaxReq_eq]; decide)]
  decide

private theorem s3a3_fineReadFile_2M :
    fineReadFileCum 2097152 = 573818 ∧ fineReadFileLive 2097152 = 2105347 ∧
    fineReadFilePeak 2097152 = 3162118 ∧ fineReadFileMaxReq 2097152 = 2097152 := by
  unfold fineReadFileCum fineReadFileLive fineReadFilePeak fineReadFileMaxReq
  rw [optLargeCost_of_gt fineCostModel (by rw [fineCostModel_smallMaxReq_eq]; decide),
    fineCostModel_largeCost_eq]
  decide

private theorem s3a3_kpkMarkPoll_credit (i : Inputs)
    (hkpkOt : ∀ id bs,
      StoresGhost.opened.kyber.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900)
    (kpkId spkId : BitVec 32) (baseKey : CryptoGames.LibsignalSession.PublicKey) :
    PhaseCreditSpec fineCostModel
      (CliKpkMarkPollEnv cliIo.rd DecimalEnv
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd) DirPutEnv (runFiles i)
        ⟨0#64, 0#64, 0#64, 0#64, kpkId, spkId, baseKey, StoresGhost.opened.kyber⟩)
      975111 4202513 6307867 4194318 := by
  let F0 := runFiles i
  let GetFixed := DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd
  let x : KpkMarkPollGhost :=
    ⟨0#64, 0#64, 0#64, 0#64, kpkId, spkId, baseKey, StoresGhost.opened.kyber⟩
  have hdcOt : DirDomainCaps 64 0 0 StoresGhost.opened.kyber.oneTime :=
    s3_dirDomainCaps_64 dirDomainCaps_opened_kpkOt (by decide)
  have hdcLr : DirDomainCaps 64 0 0 StoresGhost.opened.kyber.lastResort :=
    s3_dirDomainCaps_64 dirDomainCaps_opened_kpkLr (by decide)
  have hkn64 : (keyName kpkId).length ≤ 64 :=
    Nat.le_trans (keyName_length_le kpkId) (by decide)
  have hbkn64 : (baseKeysName kpkId).length ≤ 64 :=
    Nat.le_trans (baseKeysName_length_le kpkId) (by decide)
  have hdec := s3a3_decimal_credit kpkId
  obtain ⟨hfc0_c, hfc0_l, hfc0_p, hfc0_r⟩ := s3a3_fineReadFile_0
  obtain ⟨hfc49_c, hfc49_l, hfc49_p, hfc49_r⟩ := s3a3_fineReadFile_4900
  obtain ⟨hfc2M_c, hfc2M_l, hfc2M_p, hfc2M_r⟩ := s3a3_fineReadFile_2M
  unfold CliKpkMarkPollEnv KpkOneTimePreAfterGetEnv
  dsimp only
  cases hOt : StoresGhost.opened.kyber.oneTime.get cliIo.rd F0 (keyName kpkId) with
  | error u =>
    cases u
    dsimp only [OptKpkMarkOneTimeTailEnv]
    have hOtRd :
        cliIo.rd F0 (pathOf StoresGhost.opened.kyber.oneTime.path (keyName kpkId)) = .error () :=
      hOt
    have hg0 : PhaseCreditSpec fineCostModel
        (GetFixed F0 StoresGhost.opened.kyber.oneTime (keyName kpkId))
        595741 0 3162118 2097152 := by
      have hraw := s3_dirGetFixed_credit cliIo.rd F0 StoresGhost.opened.kyber.oneTime
        (keyName kpkId) (fileCap := 0) hdcOt hkn64
        (fun _ h => by rw [hOtRd] at h; cases h)
      dsimp only at hraw
      rw [show max 0 0 = 0 from rfl, hfc0_c, hfc0_l, hfc0_p, hfc0_r] at hraw
      exact hraw.mono (by decide) (by decide) (by decide) (by decide)
    exact (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps (hdec.seq hg0)).mono
      (by decide) (by decide) (by decide) (by decide)
  | ok otBs =>
    cases otBs with
    | cons b bs =>
      dsimp only [OptKpkMarkOneTimeTailEnv, KpkOneTimeConsTailEnv]
      have hg49 : PhaseCreditSpec fineCostModel
          (GetFixed F0 StoresGhost.opened.kyber.oneTime (keyName kpkId))
          595741 2105347 3162118 2097152 := by
        have hraw := s3_dirGetFixed_credit cliIo.rd F0 StoresGhost.opened.kyber.oneTime
          (keyName kpkId) (fileCap := 4900) hdcOt hkn64
          (fun bs' h => hkpkOt kpkId bs' h)
        dsimp only at hraw
        rw [show max 0 4900 = 4900 from rfl, hfc49_c, hfc49_l, hfc49_p, hfc49_r] at hraw
        exact hraw.mono (by decide) (by decide) (by decide) (by decide)
      have hputOt : PhaseCreditSpec fineCostModel
          (DirPutEnv StoresGhost.opened.kyber.oneTime (keyName kpkId) []) 9789 0 0 192 :=
        s3_dirPut_opened_credit rfl (keyName kpkId) []
      have hfree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
        PhaseCreditSpec.freeOnly fineCostModel_freeNonInc
      exact ((hdec.seq hg49).seq (hfree.seq (hdec.seq hputOt))).mono
        (by decide) (by decide) (by decide) (by decide)
    | nil =>
      dsimp only [OptKpkMarkOneTimeTailEnv]
      have hOtRd :
          cliIo.rd F0 (pathOf StoresGhost.opened.kyber.oneTime.path (keyName kpkId)) = .ok [] :=
        hOt
      have hgOtNil : PhaseCreditSpec fineCostModel
          (GetFixed F0 StoresGhost.opened.kyber.oneTime (keyName kpkId))
          21923 0 0 256 := by
        have hraw := s3a3_dirGetFixed_ok_credit F0 StoresGhost.opened.kyber.oneTime
          (keyName kpkId) (fileCap := 0) hdcOt rfl hkn64 hOtRd (Nat.le_refl 0)
        rw [hfc0_c, hfc0_l, hfc0_p, hfc0_r] at hraw
        exact hraw.mono (by decide) (by decide) (by decide) (by decide)
      have hOtPre : PhaseCreditSpec fineCostModel
          (SeqEnv (DecimalEnv kpkId)
            (GetFixed F0 StoresGhost.opened.kyber.oneTime (keyName kpkId)))
          41501 0 0 256 :=
        (hdec.seq hgOtNil).mono (by decide) (by decide) (by decide) (by decide)
      have hres := s3a3_baseKeysReserve_credit kpkId
      cases hLr : StoresGhost.opened.kyber.lastResort.get cliIo.rd F0 (baseKeysName kpkId) with
      | error u =>
        cases u
        dsimp only [OptKpkMarkLastResortTailEnv, KpkLastResortPreAfterGetEnv]
        have hLrRd :
            cliIo.rd F0 (pathOf StoresGhost.opened.kyber.lastResort.path (baseKeysName kpkId)) =
              .error () :=
          hLr
        have hgLrErr : PhaseCreditSpec fineCostModel
            (GetFixed F0 StoresGhost.opened.kyber.lastResort (baseKeysName kpkId))
            595741 0 3162118 2097152 := by
          have hraw := s3_dirGetFixed_credit cliIo.rd F0 StoresGhost.opened.kyber.lastResort
            (baseKeysName kpkId) (fileCap := 0) hdcLr hbkn64
            (fun _ h => by rw [hLrRd] at h; cases h)
          dsimp only at hraw
          rw [show max 0 0 = 0 from rfl, hfc0_c, hfc0_l, hfc0_p, hfc0_r] at hraw
          exact hraw.mono (by decide) (by decide) (by decide) (by decide)
        have hLrPre : PhaseCreditSpec fineCostModel _ 625108 0 3162118 2097152 :=
          (hdec.seq (hres.seq hgLrErr)).mono
            (by decide) (by decide) (by decide) (by decide)
        have hLrAll := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hLrPre
        have hfree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
          PhaseCreditSpec.freeOnly fineCostModel_freeNonInc
        exact (hOtPre.seq (hfree.seq hLrAll)).mono
          (by decide) (by decide) (by decide) (by decide)
      | ok seenBs =>
        dsimp only [OptKpkMarkLastResortTailEnv, KpkLastResortPreAfterGetEnv,
          KpkAfterLrGetCapFreeBranchEnv]
        have hLrRd :
            cliIo.rd F0 (pathOf StoresGhost.opened.kyber.lastResort.path (baseKeysName kpkId)) =
              .ok seenBs :=
          hLr
        have hseen2M : seenBs.length ≤ 2097152 := cliRd_ok_le_fileCap hLrRd
        have hgLrOk : PhaseCreditSpec fineCostModel
            (GetFixed F0 StoresGhost.opened.kyber.lastResort (baseKeysName kpkId))
            595003 2105347 3162118 2097152 := by
          have hraw := s3a3_dirGetFixed_ok_credit F0 StoresGhost.opened.kyber.lastResort
            (baseKeysName kpkId) (fileCap := 2097152) hdcLr rfl hbkn64 hLrRd hseen2M
          rw [hfc2M_c, hfc2M_l, hfc2M_p, hfc2M_r] at hraw
          exact hraw.mono (by decide) (by decide) (by decide) (by decide)
        have hLrPre : PhaseCreditSpec fineCostModel
            (SeqEnv (DecimalEnv kpkId)
              (SeqEnv (KpkBaseKeysReserveEnv kpkId)
                (GetFixed F0 StoresGhost.opened.kyber.lastResort (baseKeysName kpkId))))
            624370 2105347 3162118 2097152 :=
          (hdec.seq (hres.seq hgLrOk)).mono (by decide) (by decide) (by decide) (by decide)
        have hAfterPre := s3a3_afterLrGetPre_credit
        by_cases hmod : seenBs.length % 37 = 0
        · simp only [hmod, ↓reduceIte]
          by_cases hchk : hasChunk seenBs (baseKeyEntry spkId baseKey)
          · simp only [hchk, ↓reduceIte]
            have h15 : PhaseCreditSpec fineCostModel
                (SeqEnv (· = rustAllocEvents 15 1) FreeOnlyEvs) 9789 0 0 15 :=
              phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
                (s3_rustAlloc_small_credit (req := 15) (al := 1) (by decide) (by decide))
            have hfree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
              PhaseCreditSpec.freeOnly fineCostModel_freeNonInc
            exact (hOtPre.seq (hfree.seq (hLrPre.seq (hAfterPre.seq h15)))).mono
              (by decide) (by decide) (by decide) (by decide)
          · simp only [hchk, Bool.false_eq_true, ↓reduceIte]
            have hdiv : seenBs.length / 37 ≤ 2097152 / 37 := Nat.div_le_div_right hseen2M
            have hmul37 : seenBs.length = 37 * (seenBs.length / 37) := by
              have hdm := Nat.div_add_mod seenBs.length 37
              rw [hmod, Nat.add_zero] at hdm
              exact hdm.symm
            have hseen123 : seenBs.length ≤ 2097123 := by
              rw [hmul37]
              exact Nat.le_trans (Nat.mul_le_mul_left 37 hdiv) (by decide)
            have hAB := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hOtPre
            have hABC : PhaseCreditSpec fineCostModel _ 665871 2105347 3162118 2097152 :=
              (hAB.seq hLrPre).mono (by decide) (by decide) (by decide) (by decide)
            have hBefore : PhaseCreditSpec fineCostModel _ 685449 2105347 3162118 2097152 :=
              (hABC.seq hAfterPre).mono (by decide) (by decide) (by decide) (by decide)
            have hCatMid := s3a3_concat_seenAppendReserveMid_credit hBefore hseen123
            have hSeqMid : PhaseCreditSpec fineCostModel
                (SeqEnv _ (KpkSeenAppendReserveMidEnv seenBs))
                965322 4202513 6307867 4194318 :=
              ((hBefore.or hCatMid).mono (by decide) (by decide) (by decide) (by decide)).of_imp
                fun _ hd => hd.elim Or.inl fun ⟨e1, e2, heq, h1, h2⟩ => Or.inr ⟨e1, e2, heq, h1, h2⟩
            have hPutLr : PhaseCreditSpec fineCostModel
                (DirPutEnv StoresGhost.opened.kyber.lastResort (baseKeysName kpkId)
                  (seenBs ++ baseKeyEntry spkId baseKey))
                9789 0 0 192 :=
              s3_dirPut_opened_credit rfl _ _
            exact ((hSeqMid.seq hPutLr).mono
              (by decide) (by decide) (by decide) (by decide)).of_imp fun _ h0 =>
              s3a3_seqEnv_assoc_left (s3a3_seqEnv_assoc_left
                (s3a3_seqEnv_assoc_left (s3a3_seqEnv_assoc_left h0)))
        · simp only [hmod, ↓reduceIte]
          have h14 : PhaseCreditSpec fineCostModel
              (SeqEnv (· = rustAllocEvents 14 1) FreeOnlyEvs) 9789 0 0 14 :=
            phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
              (s3_rustAlloc_small_credit (req := 14) (al := 1) (by decide) (by decide))
          have hfree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
            PhaseCreditSpec.freeOnly fineCostModel_freeNonInc
          exact (hOtPre.seq (hfree.seq (hLrPre.seq (hAfterPre.seq h14)))).mono
            (by decide) (by decide) (by decide) (by decide)

end S3a3Sub3Helpers

/-- `PhaseCreditSpec` for `W4BinaryKpkMarkStepEnvFixed` under `oneTime ≤ 4900` and
`cliRd_ok_le_fileCap` (`baseKeysFile ≤ 2097152`, `seenBs.length % 37 = 0` grow `≤ 4194368`). -/
private theorem s3a_sub3_kpkMarkFixed_credit (i : Inputs)
    (hkpkOt : ∀ id bs,
      StoresGhost.opened.kyber.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900)
    (kpkId spkId : BitVec 32) (baseKey : CryptoGames.LibsignalSession.PublicKey) :
    PhaseCreditSpec fineCostModel
      (W4BinaryKpkMarkStepEnvFixed cliIo.rd (runFiles i) kpkId spkId baseKey)
      1300000 4250000 6400000 4194368 := by
  unfold W4BinaryKpkMarkStepEnvFixed
  have hpoll := s3a3_kpkMarkPoll_credit i hkpkOt kpkId spkId baseKey
  have hbox :=
    LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers.w4BoxedStoreStep_small_phaseCredit
      fineCostModel_modelHyps 32
      (by rw [LibsignalBinary.Heap.Fine.ClientBounds.fineCostModel_smallMaxReq_eq]; decide) hpoll
  exact hbox.mono (by decide) (by decide) (by decide) (by decide)



private theorem s3a_sub3_kpkMarkFixed_tight_credit (i : Inputs)
    (hkpkOt : ∀ id bs,
      StoresGhost.opened.kyber.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900)
    (kpkId spkId : BitVec 32) (baseKey : CryptoGames.LibsignalSession.PublicKey) :
    PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.W4BinaryKpkMarkStepEnvFixed
        cliIo.rd (runFiles i) kpkId spkId baseKey)
      975849 4202513 6307867 4194368 := by
  unfold LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed.W4BinaryKpkMarkStepEnvFixed
  have hpoll := s3a3_kpkMarkPoll_credit i hkpkOt kpkId spkId baseKey
  exact (LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux.w4BoxedStoreStep_fine_le_44
    (by decide) hpoll).mono (by decide) (by decide) (by decide) (by decide)
section S3aSub4Helpers

open CryptoGames.LibsignalSession
  (IdentityKey MessageKeyGenerator PublicKey ReceiverChain SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalSessionRepr (ChainGhost MessageKeyGhost VecPin)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost)
open CryptoVerification.SignalSession.Cli (addressText)
open LibsignalBinary.Heap (rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (dirDomainCaps_opened_peers dirDomainCaps_opened_sess)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W4BinaryArchiveDirectEnv W4BinaryIdSaveStepEnv W4BinaryIdTrustStepEnv
   W4BinaryPromoteArchiveEnv W4BinarySessLoadStepEnv W4BinarySessStoreStepEnv
   W4BinaryStageP1OkEnv W4BinaryStageP2MatchedWideEnv W4BinaryStageP4MatchedWideEnv
   W4CloneBDomEnv W4TrialRunWideEnv mkW4RecvPrekeyWideSlotParams)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (DeallocCreditSpec FreeOnlyAlign16Evs)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (PhaseCreditSpec.rustAlloc_optLarge optLargeCost)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (PhaseCreditSpec.recordSerialize_seqFree_tight RecordSerializeSeqFreeEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit
  (w2TryDecryptFail_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738
   w2TryDecrypt_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (SessionCloneDom recordSerializeMaxReq_le_of_dom recordSerializePeak_fine_le_of_dom
   recordSerializeTightCum_fine_le_of_dom)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec (w2TryDecryptMaxReq)
open LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738 (w2TryDecryptSeeds738Cum)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
  (phaseCredit_archivedTrialLoop_le4 phaseCredit_promoteStateArchive)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
  (W4BoundedEvs phaseCredit_w4BoundedEvs_small)
open LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers (stringClone_phaseCredit_small)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4StageP3WideEnv phaseCredit_optStageEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
  (addressText_peer_length_le_64 phaseCreditSpec_seq_freeOnly_exact)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec
  (sessionClone_dom_fine_phaseCredit_tight w4StageP2MatchedCheck_fine_phaseCredit
   w4StageP3Wide_fine_phaseCredit_tight w4TryDecryptCloneFailWide_dom_fine_cancel_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
  (fineOptLarge_mono optLargeCost_fine_eq w4BoxedStoreStep_fine_le_28 w4BoxedStoreStep_fine_le_44)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
  (W4ArchivedTrial W4FailedTdCancelEnv W4FailedTryDecryptCall W4TrialDecEnv W4TrialDropEnv
   W4TryDecryptCall W4TryDecryptFailLinkedEnv W4TryDecryptPathBEnv
   w4RealFailTdCum)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (W4ArchivedTrialDomOf W4FailedTdDomOf W4TryDecryptCallDomOf
   w4FailTdPeakOf w4TdBLiveOf w4TdMaxReqOf w4TrialMaxReqOf w4TrialPeakOf)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.DropSsLocal1Budget
  (SessionDropCapsOk chainPairFreeEvents dropSessionStructureLocal1Events
   dropVecChainEvents dropVecMessageKeyEvents mkFreeEvents optCkCapVal optTailCapVal
   pinFreeEvents senderFreeEvents sgnCapFreeEvents ssFirst3FreeEvents
   ssTail3FreeEvents stepEvents_dropSessionStructureLocal1_bounds vec104FreeEvents)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (ssStateLargeLive)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
  (sessDeserLargeLive)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (deserCancelFineCum deserCancelFineLive deserCancelFineMaxReq deserCancelFinePeak
   recordDeserializeCancelEnv_fine_phaseCreditSpec
   sessDeserializeCancelEnv_fine_phaseCreditSpec sessDeserializeCancelEnv_phaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
  (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (cliRd_ok_le_fileCap)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSavePollEnv cliIdentityKitSaveTailEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitLoadPollEnv cliSessionKitStorePollEnv)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget (OptLoadDeserEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
  (addrTextValEnv_decimal_fine_phaseCredit_tight dirGetEnv_path_readFile_fine_phaseCredit_tight
   seq_freeOnly_phaseCredit)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeEvents)


private theorem s3a4_w4CloneBDom_credit :
    PhaseCreditSpec fineCostModel W4CloneBDomEnv
      8277456 1375366 1375366 286196 where
  req_align evs := fun ⟨G, ses, hgv, hdom, hE⟩ => by
    have hm : PhaseCreditSpec fineCostModel
        (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.SegCloneEnv G ses.state)
        8277456 1375366 1375366 286196 :=
      (sessionClone_dom_fine_phaseCredit_tight hgv hdom).mono
        (Nat.le_refl _) (by decide) (by decide) (by decide)
    exact hm.req_align evs hE
  credit_le st0 := fun ⟨G, ses, hgv, hdom, hE⟩ => by
    have hm : PhaseCreditSpec fineCostModel
        (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.SegCloneEnv G ses.state)
        8277456 1375366 1375366 286196 :=
      (sessionClone_dom_fine_phaseCredit_tight hgv hdom).mono
        (Nat.le_refl _) (by decide) (by decide) (by decide)
    exact hm.credit_le st0 hE


end S3aSub4Helpers

end S3aHoleAHelpers

section S3bHoleBHelpers

open CryptoGames.LibsignalSession
  (IdentityKey MessageKeyGenerator PublicKey ReceiverChain SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (encodeRecordPrev1Mem)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open LibsignalBinary.Heap.Fine (MmapThresholdReq)
open CryptoVerification.LibsignalSessionRepr (ChainGhost MessageKeyGhost VecPin)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost)
open CryptoVerification.SignalSession.Cli (addressText decimalText keyName)
open CryptoVerification.SignalSession.Cli.Decimal.Helpers
  (decimalText_digit decimalText_ge10 decimalText_length_le)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap
  (FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget
  (KemKeyPairFromPubPrivEnv kemKeyPairFromPubPrivEvents)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (allocBytes1Events_groupSpec dropClonedSessionEvents_groupSpec
   initialStateEnv_groupSpec optTailCloneEvents_groupSpec recordSerializeDomFineGrpS
   segCloneDomFineGrpS segCloneEnv_dom_fine_groupSpec
   senderChainCloneDomFineGrpS senderChainCloneEnv_dom_fine_groupSpec
   serializePrev1DomFineGrpS serializeSomeSeqFreeEnv_groupSpec vecCloneEvents_groupSpec
   vecVecClone1Events_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (CliPkDecodeEnv CliSpkDecodeEnv W4BinaryAcceptWideEnv W4BinaryArchiveDirectEnv
   W4BinaryIdSaveStepEnv W4BinaryIdTrustStepEnv W4BinaryInitBobWideEnv
   W4BinaryKpkGetStepEnv W4BinaryPkGetStepEnv W4BinaryPkRemoveStepEnv
   W4BinaryPromoteArchiveEnv W4BinaryRecvPrekeyDom W4BinaryRecvPrekeyParams
   W4BinaryRecvPrekeyPathBWideEnv W4BinarySelfKpStepEnv W4BinarySelfRegIdStepEnv
   W4BinarySessLoadStepEnv W4BinarySessStorePrev1StepEnv W4BinarySessStoreStepEnv
   W4BinarySpkGetStepEnv W4BinaryStageP1OkEnv W4BinaryStageP1UntrustedEnv
   W4BinaryStageP2MatchedWideEnv W4BinaryStageP2PathAWideEnv W4BinaryStageP2PathCWideEnv
   W4BinaryStageP4MatchedWideEnv W4CloneACDomEnv W4CloneBDomEnv W4TrialRunWideEnv
   mkW4RecvPrekeyWideSlotParams)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (NonFreeBound fineSmallAllocGroupS nonFreeCount nonFreeCount_append nonFreeCount_nil
   nonFreeCount_rustAllocEvents nonFreeCount_rustDeallocEvents nonFreeCount_rustReallocEvents
   smallAllocGroupS_fineCostModel_eq smallAllocGroupS_le_4737_of_le_12
   smallAllocGroupS_le_11056_of_le_28 smallAllocGroupS_le_16659_of_le_44
   smallAllocGroupS_le_24623_of_le_60)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W4BinaryKpkMarkStepEnvFixed W4BinaryRecvPrekeyPathAWideEnvFixed
   W4BinaryRecvPrekeyPathCWideEnvFixed W4BinaryRecvPrekeyWideSlotEnvFixed
   W4BinaryStageP4PathAWideEnvFixed W4BinaryStageP4PathCWideEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (FreeOnlyAlign16Evs IterSeqEnv)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (dropClonedSessionEvents)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (RecordSerializeSeqFreeEnv SerializePrev1SeqFreeEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit
  (w2TryDecryptFailTightEnv_linked_fine_groupSpec_split_12 w2TryDecryptFailTightGroupS_split_12)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds (FreshBobCloneDom SessionCloneDom)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak (optDeallocListEvs)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
  (ArchivedTrialIterEnv PromoteStateArchiveEnv)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
  (W4BobSessionBuildEnv W4BoundedEvs W4PqxdhAcceptEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4ErrTailWideEnv W4StageP2MatchedCheckEnv W4StageP3WideEnv
   W4TryDecryptCloneFailWideEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers (W4BoxedStoreStepEnv)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
  (W4ArchivedTrial W4FailedTdCancelEnv W4FailedTryDecryptCall W4RecvPrekeyRealParams
   W4RecvPrekeyTryDecACEnv mkW4RecvPrekeySlotParams
   w4RealTrialFineGrpS w4RecvPrekeyRealGrpS)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (W4FailedTdDomOf W4RecvPrekeyRealDomOf)
open LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec
  (archivedTrialLoop_le4_groupSpec phaseGroupSpec_ite_nil phaseGroupSpec_optStage
   promoteStateArchive_groupSpec segCloneEnv_freshBobCloneDom_fine_groupSpec
   segCloneFreshBobFineGrpS w4BobSessionBuild_groupSpec w4BoundedEvs_groupSpec
   w4BoxedStoreStep_le_28_fine_groupSpec w4BoxedStoreStep_le_44_fine_groupSpec
   w4ErrTailWide_fine_groupSpec w4ErrTailWideFineGrpS w4InitBobSpqrFineGrpS
   w4PqxdhAccept_fine_groupSpec w4StageP2MatchedCheck_fine_groupSpec
   w4StageP2MatchedCheckFineGrpS w4StageP3Wide_fine_groupSpec w4StageP3WideFineGrpS
   w4TryDecryptCloneFailWide_fine_groupSpec)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget (PreKeyDeserializeEnv RecordCodecLoopEnv)
open LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget
  (KyberDecodeEnv SpkCaps SpkDecodeEnv SpkErrTailEnv SpkField SpkLoopBoundedEnv SpkLoopEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.DropSsLocal1Budget
  (chainPairFreeEvents dropSessionStructureLocal1Events dropVecChainEvents
   dropVecMessageKeyEvents mkFreeEvents optCkCapVal optTailCapVal pinFreeEvents senderFreeEvents
   sgnCapFreeEvents ssFirst3FreeEvents ssTail3FreeEvents vec104FreeEvents)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (deserCancelFineGrpS recordDeserializeCancelEnv_fine_groupSpec
   sessDeserializeCancelEnv_fine_groupSpec)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSavePollEnv cliIdentityKitSaveTailEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitLoadPollEnv cliSessionKitStorePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
  (OptIkpTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
  (OptRegIdMalformedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget (CliKpkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux
  (CliKpkMarkPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget (CliPkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
  (CliPkRemovePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (CliSpkGetPollEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (PublicKeySerializeEnv publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget (pushByteStep pushBytesEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv segCloneEvents)

private theorem dirGet_readPlain_groups_s3b
    (rd : ReadRule) (F0 : FsFiles) (dir : DirGhost) (name : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (DirGetEnv PathEnv (ReadFileRuleEnv rd) rd F0 dir name)
      (42 * FineScale) := by
  refine (s3_dirGetFixed_groups fineCostModel rd F0 dir name).of_imp fun evs h => ?_
  unfold DirGetEnv
  unfold DirGetEnv at h
  cases hfind : dir.changed.find? (fun e => e.1 == name) with
  | some _ => rw [hfind] at h; exact h
  | none =>
    rw [hfind] at h
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a.DirGetMissEnv at h ⊢
    exact s3_seqEnv_mono (fun _ hp => hp)
      (fun _ hr => s3_seqEnv_mono (fun _ hrf => Or.inl hrf) (fun _ ha => ha) hr) h

private theorem pushBytesEvents_nonFree_le_s3b :
    ∀ (m cap len : Nat), nonFreeCount (pushBytesEvents m cap len) ≤ m
  | 0, _, _ => by simp [pushBytesEvents, nonFreeCount_nil]
  | m + 1, cap, len => by
    unfold pushBytesEvents
    rw [nonFreeCount_append]
    have hstep : nonFreeCount (pushByteStep cap len).2 ≤ 1 := by
      unfold pushByteStep
      split
      · dsimp only; simp [nonFreeCount_nil]
      · dsimp only; split <;> simp [nonFreeCount_rustAllocEvents, nonFreeCount_rustReallocEvents]
    have ih := pushBytesEvents_nonFree_le_s3b m (pushByteStep cap len).1 (len + 1)
    omega

private theorem decimal_groups_s3b (n : BitVec 32) :
    PhaseGroupSpec fineCostModel (DecimalEnv n) (30 * FineScale) := by
  have hnf : NonFreeBound (DecimalEnv n) 10 := by
    intro evs h
    unfold DecimalEnv LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget.decimalEvents at h
    subst h
    have hlen : (decimalText n.toNat).length ≤ 10 :=
      decimalText_length_le 10 n.toNat (by omega) (Nat.lt_trans n.isLt (by omega))
    exact Nat.le_trans (pushBytesEvents_nonFree_le_s3b _ 0 0) hlen
  exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by omega)

private def spkIndLe_s3b (k x : Nat) : Nat :=
  if x ≤ k then 1 else 0

private theorem spkIndLe_mono_s3b (k : Nat) {x y : Nat} (h : x ≤ y) :
    spkIndLe_s3b k y ≤ spkIndLe_s3b k x := by
  unfold spkIndLe_s3b
  split_ifs <;> omega

private theorem spkIndLe_lt_s3b (k x y : Nat) (hx : x ≤ k) (hy : k < y) :
    spkIndLe_s3b k y + 1 ≤ spkIndLe_s3b k x := by
  unfold spkIndLe_s3b
  simp [hx, Nat.not_le.mpr hy]

/-- 14-tier doubling rank on `Vec<u8>` capacity `c` for `SpkLoopBoundedEnv` at `rem ≤ 4900`:
each `reserveCap c 0 v.length` with `c < v.length ≤ 4900` strictly decreases `spkCapRank_s3b`. -/
private def spkCapRank_s3b (c : Nat) : Nat :=
  spkIndLe_s3b 0 c + spkIndLe_s3b 4 c + spkIndLe_s3b 8 c + spkIndLe_s3b 16 c +
  spkIndLe_s3b 32 c + spkIndLe_s3b 64 c + spkIndLe_s3b 128 c + spkIndLe_s3b 256 c +
  spkIndLe_s3b 512 c + spkIndLe_s3b 1024 c + spkIndLe_s3b 2048 c + spkIndLe_s3b 4096 c +
  spkIndLe_s3b 4899 c + spkIndLe_s3b 4899 c

private def spkCapsRank_s3b (caps : SpkCaps) : Nat :=
  spkCapRank_s3b caps.pub + spkCapRank_s3b caps.priv + spkCapRank_s3b caps.sig

private theorem spkCapRank_step_lt_s3b {c vlen : Nat} (hlt : c < vlen) (hle : vlen ≤ 4900) :
    spkCapRank_s3b (reserveCap c 0 vlen) + 1 ≤ spkCapRank_s3b c := by
  have hres : max 8 (max vlen (2 * c)) ≤ reserveCap c 0 vlen := by
    unfold reserveCap; omega
  generalize reserveCap c 0 vlen = r at hres ⊢
  have hr8 : 8 ≤ r := by omega
  have hrv : vlen ≤ r := by omega
  have hr2 : 2 * c ≤ r := by omega
  have hcr : c ≤ r := by omega
  have m0 := spkIndLe_mono_s3b 0 hcr
  have m4 := spkIndLe_mono_s3b 4 hcr
  have m8 := spkIndLe_mono_s3b 8 hcr
  have m16 := spkIndLe_mono_s3b 16 hcr
  have m32 := spkIndLe_mono_s3b 32 hcr
  have m64 := spkIndLe_mono_s3b 64 hcr
  have m128 := spkIndLe_mono_s3b 128 hcr
  have m256 := spkIndLe_mono_s3b 256 hcr
  have m512 := spkIndLe_mono_s3b 512 hcr
  have m1024 := spkIndLe_mono_s3b 1024 hcr
  have m2048 := spkIndLe_mono_s3b 2048 hcr
  have m4096 := spkIndLe_mono_s3b 4096 hcr
  have m4899 := spkIndLe_mono_s3b 4899 hcr
  unfold spkCapRank_s3b
  by_cases hc4 : c ≤ 4
  · have s := spkIndLe_lt_s3b 4 c r hc4 (by omega); omega
  · by_cases hc8 : c ≤ 8
    · have s := spkIndLe_lt_s3b 8 c r hc8 (by omega); omega
    · by_cases hc16 : c ≤ 16
      · have s := spkIndLe_lt_s3b 16 c r hc16 (by omega); omega
      · by_cases hc32 : c ≤ 32
        · have s := spkIndLe_lt_s3b 32 c r hc32 (by omega); omega
        · by_cases hc64 : c ≤ 64
          · have s := spkIndLe_lt_s3b 64 c r hc64 (by omega); omega
          · by_cases hc128 : c ≤ 128
            · have s := spkIndLe_lt_s3b 128 c r hc128 (by omega); omega
            · by_cases hc256 : c ≤ 256
              · have s := spkIndLe_lt_s3b 256 c r hc256 (by omega); omega
              · by_cases hc512 : c ≤ 512
                · have s := spkIndLe_lt_s3b 512 c r hc512 (by omega); omega
                · by_cases hc1024 : c ≤ 1024
                  · have s := spkIndLe_lt_s3b 1024 c r hc1024 (by omega); omega
                  · by_cases hc2048 : c ≤ 2048
                    · have s := spkIndLe_lt_s3b 2048 c r hc2048 (by omega); omega
                    · by_cases hc4096 : c ≤ 4096
                      · have s := spkIndLe_lt_s3b 4096 c r hc4096 (by omega); omega
                      · have s := spkIndLe_lt_s3b 4899 c r (by omega) (by omega); omega

private theorem rustAlloc_linear_groups_s3b (n : Nat) (hn : 0 < n) :
    PhaseGroupSpec fineCostModel (· = rustAllocEvents n 1) (3172 * (n + 1)) := by
  by_cases h60 : n ≤ 60
  · have hm : n ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
    have hsm := PhaseGroupSpec.rustAlloc_small fineCostModel (size := n) (align := 1) (by decide) hm
    rw [smallAllocGroupS_fineCostModel_eq] at hsm
    by_cases h12 : n ≤ 12
    · have hb := smallAllocGroupS_le_4737_of_le_12 h12
      exact hsm.mono (by omega)
    · by_cases h28 : n ≤ 28
      · have hb := smallAllocGroupS_le_11056_of_le_28 h28
        exact hsm.mono (by omega)
      · have hb := smallAllocGroupS_le_24623_of_le_60 h60
        exact hsm.mono (by omega)
  · exact (PhaseGroupSpec.rustAlloc_any fineCostModel n 1).mono (by unfold FineScale; omega)

private theorem optByteFree_spk_freeOnly_s3b {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.OptByteFreeEnv evs) :
    FreeOnlyEvs evs := by
  rcases h with rfl | ⟨cap, _, _, rfl⟩
  · exact FreeOnlyEvs.nil
  · exact FreeOnlyEvs.singleton 1 cap

private theorem spkEpilogueFree_freeOnly_s3b {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.SpkEpilogueFreeEnv evs) :
    FreeOnlyEvs evs := by
  rcases h with ⟨e1, e2, e3, h1, h2, h3, rfl⟩
  exact FreeOnlyEvs.append
    (FreeOnlyEvs.append (optByteFree_spk_freeOnly_s3b h1) (optByteFree_spk_freeOnly_s3b h2))
    (optByteFree_spk_freeOnly_s3b h3)

private theorem dropDecodeError_freeOnly_s3b {evs : List AllocEvent}
    (h : LibsignalBinary.Proofs.RecordCodecs.SignedDepsBudget.DropDecodeErrorEnv evs) :
    FreeOnlyEvs evs := by
  rcases h with rfl | ⟨c, _, _, rfl⟩
  · exact FreeOnlyEvs.singleton 8 72
  · exact FreeOnlyEvs.append (FreeOnlyEvs.singleton 8 (c * 32)) (FreeOnlyEvs.singleton 8 72)

private theorem spkErrTail_groups_s3b :
    PhaseGroupSpec fineCostModel SpkErrTailEnv (6 * FineScale) := by
  have hnf : NonFreeBound SpkErrTailEnv 2 := by
    intro evs h
    cases h with
    | nil => simp [nonFreeCount_nil]
    | fromOnly => simp [nonFreeCount_rustAllocEvents]
    | fromPush hp =>
      rw [nonFreeCount_append]
      have h72 : nonFreeCount (rustAllocEvents 72 8) = 1 := nonFreeCount_rustAllocEvents 72 8
      rcases hp with rfl | ⟨_, rfl⟩ | ⟨hpos, _⟩
      · simp [h72, nonFreeCount_nil]
      · simp [h72, nonFreeCount_rustAllocEvents]
      · omega
  exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by omega)

private theorem doReserveClear_groups_s3b (cap vlen : Nat) :
    PhaseGroupSpec fineCostModel (· = doReserveClearEvents cap vlen) (3 * FineScale) := by
  have hnf : NonFreeBound (· = doReserveClearEvents cap vlen) 1 := by
    intro evs h
    subst h
    unfold doReserveClearEvents
    split
    · simp [nonFreeCount_nil]
    · split <;> simp [nonFreeCount_rustAllocEvents, nonFreeCount_rustReallocEvents]
  exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by omega)

private theorem spkCaps_set_get_s3b (f : SpkField) (caps : SpkCaps) :
    caps.set f (caps.get f) = caps := by
  cases f <;> rfl

private theorem spkCapsRank_set_lt_s3b (f : SpkField) (caps : SpkCaps) {vlen : Nat}
    (hlt : caps.get f < vlen) (hle : vlen ≤ 4900) :
    spkCapsRank_s3b (caps.set f (reserveCap (caps.get f) 0 vlen)) + 1 ≤ spkCapsRank_s3b caps := by
  cases f <;>
  · dsimp only [SpkCaps.get, SpkCaps.set, spkCapsRank_s3b] at hlt ⊢
    have h := spkCapRank_step_lt_s3b hlt hle
    omega

private theorem spkLoopBounded_eq_groups_s3b {rem : Nat} {caps : SpkCaps} {evs : List AllocEvent}
    (h : SpkLoopBoundedEnv rem caps evs) :
    rem ≤ 4900 →
      PhaseGroupSpec fineCostModel (· = evs)
        (3172 * rem + (3 * spkCapsRank_s3b caps + 6) * FineScale) := by
  induction h with
  | done htail =>
    intro _
    exact (spkErrTail_groups_s3b.of_imp fun _ he => by subst he; exact htail).mono
      (by unfold FineScale; omega)
  | skipStep hlt _ ih =>
    intro hrem
    exact (ih (by omega)).mono (by unfold FineScale; omega)
  | @bytesStep f rem rem' caps wt bs v rest evs₂ hm _ hprog hcap_lt _ ih =>
    intro hrem
    have ih' := ih (by omega)
    have hbv : (BitVec.ofNat 64 (caps.get f)).toNat = caps.get f := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    by_cases hv0 : v.length = 0
    · have hbm : bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs = [] := by
        simp [bytesMergeEventsCore, hm, hv0]
      have hle_cap : v.length ≤ caps.get f := by omega
      simp only [hle_cap, ↓reduceIte, spkCaps_set_get_s3b] at ih'
      rw [hbm, List.nil_append]
      exact ih'.mono (by unfold FineScale; omega)
    · have hv_pos : 0 < v.length := Nat.pos_of_ne_zero hv0
      have hbm : bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs =
          rustAllocEvents v.length 1 ++
            doReserveClearEvents (caps.get f) v.length ++
            rustDeallocEvents v.length 1 := by
        simp [bytesMergeEventsCore, hm, hv0, hbv, List.append_assoc]
      have halloc := rustAlloc_linear_groups_s3b v.length hv_pos
      have hfree : PhaseGroupSpec fineCostModel (· = rustDeallocEvents v.length 1) 0 :=
        (PhaseGroupSpec.freeOnly fineCostModel).of_imp fun _ he => by
          subst he; exact FreeOnlyEvs.singleton 1 v.length
      by_cases hle_cap : v.length ≤ caps.get f
      · have hdrc : doReserveClearEvents (caps.get f) v.length = [] := by
          simp [doReserveClearEvents, hle_cap]
        simp only [hle_cap, ↓reduceIte, spkCaps_set_get_s3b] at ih'
        rw [hbm, hdrc, List.append_nil]
        have h1 := (s3_phaseGroupSpec_append_eq fineCostModel halloc hfree).mono
          (Nat.le_of_eq (Nat.add_zero _))
        exact (s3_phaseGroupSpec_append_eq fineCostModel h1 ih').mono (by unfold FineScale; omega)
      · have hlt_cap : caps.get f < v.length := by omega
        have hv_4900 : v.length ≤ 4900 := by omega
        simp only [hle_cap, ↓reduceIte] at ih'
        have hrank := spkCapsRank_set_lt_s3b f caps hlt_cap hv_4900
        rw [hbm]
        have h12 := s3_phaseGroupSpec_append_eq fineCostModel
          halloc (doReserveClear_groups_s3b (caps.get f) v.length)
        have h123 := (s3_phaseGroupSpec_append_eq fineCostModel h12 hfree).mono
          (Nat.le_of_eq (Nat.add_zero _))
        exact (s3_phaseGroupSpec_append_eq fineCostModel h123 ih').mono (by unfold FineScale; omega)

/-- Tight `PhaseGroupSpec` for `CliSpkDecodeEnv bs` when `bs.length ≤ L ≤ 4900`:
each `bytesMerge` step consumes `≥ v.length + 1` input bytes (`rustAllocEvents v.length 1` costs
`≤ 3172 * (v.length + 1)`) and at most `42` `doReserveClearEvents` capacity doublings occur across
`(pub, priv, sig)` (`≤ 42 * 3 * FineScale` + `6 * FineScale` `SpkErrTailEnv`). -/
private theorem cliSpkDecode_groups_s3b {bs : List (BitVec 8)} {L : Nat}
    (hbs : bs.length ≤ L) (hL : L ≤ 4900) :
    PhaseGroupSpec fineCostModel (CliSpkDecodeEnv bs) (3172 * L + 132 * FineScale) := by
  have hbs_4900 : bs.length ≤ 4900 := Nat.le_trans hbs hL
  have hloop : PhaseGroupSpec fineCostModel (SpkLoopBoundedEnv bs.length SpkCaps.zero)
      (3172 * bs.length + 132 * FineScale) := by
    have hex : PhaseGroupSpec fineCostModel
        (fun evs => ∃ e, SpkLoopBoundedEnv bs.length SpkCaps.zero e ∧ evs = e)
        (3172 * bs.length + (3 * spkCapsRank_s3b SpkCaps.zero + 6) * FineScale) :=
      s3_phaseGroupSpec_exists (P := SpkLoopBoundedEnv bs.length SpkCaps.zero)
        (E := fun e evs => evs = e) fun e he => spkLoopBounded_eq_groups_s3b he hbs_4900
    have hrank0 : spkCapsRank_s3b SpkCaps.zero = 42 := by decide
    rw [hrank0] at hex
    exact (hex.of_imp fun evs h => ⟨evs, h, rfl⟩).mono (by unfold FineScale; omega)
  have hseq : PhaseGroupSpec fineCostModel
      (SeqEnv (SpkLoopBoundedEnv bs.length SpkCaps.zero) FreeOnlyEvs)
      (3172 * L + 132 * FineScale) :=
    (hloop.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (by unfold FineScale; omega)
  refine hseq.of_imp fun evs h => ?_
  rcases h with hL0 | hK
  · exact Or.inl hL0
  · rcases hK with hS | ⟨evs₁, evs₂, hS, hD, rfl⟩
    · rcases hS with hL0 | ⟨evsL, evsF, hL0, hF, rfl⟩
      · exact Or.inl hL0
      · exact Or.inr ⟨evsL, evsF, rfl, hL0, spkEpilogueFree_freeOnly_s3b hF⟩
    · rcases hS with hL0 | ⟨evsL, evsF, hL0, hF, rfl⟩
      · exact Or.inr ⟨evs₁, evs₂, rfl, hL0, dropDecodeError_freeOnly_s3b hD⟩
      · exact Or.inr ⟨evsL, evsF ++ evs₂, List.append_assoc _ _ _, hL0,
          FreeOnlyEvs.append (spkEpilogueFree_freeOnly_s3b hF) (dropDecodeError_freeOnly_s3b hD)⟩

/-- Tight `PhaseGroupSpec` for `CliPkDecodeEnv bs` when `bs.length ≤ 125`:
`s3_recordCodecLoop_nonFree` bounds `nonFreeCount ≤ 2 * 125 + 3 = 253` (`RecordCodecErrCleanupEnv`
is `FreeOnlyEvs`), giving `253 * 3 * FineScale = 759 * FineScale`. -/
private theorem cliPkDecode_groups_s3b {bs : List (BitVec 8)} (hbs : bs.length ≤ 125) :
    PhaseGroupSpec fineCostModel (CliPkDecodeEnv bs) (759 * FineScale) := by
  have hnf : NonFreeBound (CliPkDecodeEnv bs) 253 := by
    intro evs h
    have hclean : ∀ {e},
        LibsignalBinary.Proofs.RecordCodecs.DepsBudget.RecordCodecErrCleanupEnv e →
          nonFreeCount e = 0 := by
      rintro e ⟨_, eD, ⟨e1, e2, h1, h2, rfl⟩, hD, rfl⟩
      have f1 : nonFreeCount e1 = 0 := by rcases h1 with rfl | ⟨_, _, _, rfl⟩ <;> rfl
      have f2 : nonFreeCount e2 = 0 := by rcases h2 with rfl | ⟨_, _, _, rfl⟩ <;> rfl
      have fD : nonFreeCount eD = 0 := by
        rcases hD with rfl | ⟨_, _, _, rfl⟩ <;>
          simp [nonFreeCount_append, nonFreeCount_rustDeallocEvents]
      simp [nonFreeCount_append, f1, f2, fD]
    rcases h with hL | (hL | ⟨evsL, evsC, hL, hC, rfl⟩)
    · have hc := s3_recordCodecLoop_nonFree hL; omega
    · have hc := s3_recordCodecLoop_nonFree hL; omega
    · rw [nonFreeCount_append, hclean hC]
      have hc := s3_recordCodecLoop_nonFree hL; omega
  exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by omega)


private theorem freeOnly_nonFree_zero_s3b {evs : List AllocEvent} (h : FreeOnlyEvs evs) :
    nonFreeCount evs = 0 := by
  induction evs with
  | nil => rfl
  | cons ev tl ih =>
    obtain ⟨al, sz, hev⟩ := h ev (List.mem_cons_self ..)
    subst hev
    rw [show AllocEvent.free al sz :: tl = rustDeallocEvents sz al ++ tl from rfl,
      nonFreeCount_append, nonFreeCount_rustDeallocEvents, Nat.zero_add]
    exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)

private theorem kpkMarkStepFixed_groups_s3b (rd : ReadRule) (files : FsFiles)
    (kpkId spkId : BitVec 32) (baseKey : PublicKey) :
    PhaseGroupSpec fineCostModel (W4BinaryKpkMarkStepEnvFixed rd files kpkId spkId baseKey)
      (16659 + 159 * FineScale) := by
  unfold W4BinaryKpkMarkStepEnvFixed CliKpkMarkPollEnv
  have hf := PhaseGroupSpec.freeOnly fineCostModel
  have hdec := decimal_groups_s3b kpkId
  have hgetOt := s3_dirGetFixed_groups fineCostModel rd files
    StoresGhost.opened.kyber.oneTime (keyName kpkId)
  have hpre : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.KpkOneTimePreAfterGetEnv
        DecimalEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd) files
        ⟨0#64, 0#64, 0#64, 0#64, kpkId, spkId, baseKey, StoresGhost.opened.kyber⟩)
      (72 * FineScale) :=
    (hdec.seq hgetOt).mono (by omega)
  have htail : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.OptKpkMarkOneTimeTailEnv
        rd DecimalEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed rd) rd) DirPutEnv files
        ⟨0#64, 0#64, 0#64, 0#64, kpkId, spkId, baseKey, StoresGhost.opened.kyber⟩
        (StoresGhost.opened.kyber.oneTime.get rd files (keyName kpkId)))
      (87 * FineScale) := by
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.OptKpkMarkOneTimeTailEnv
    cases StoresGhost.opened.kyber.oneTime.get rd files (keyName kpkId) with
    | error _ => exact hf.mono (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | cons b rest =>
        unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.KpkOneTimeConsTailEnv
        have hput := s3_dirPut_opened_groups fineCostModel
          (dir := StoresGhost.opened.kyber.oneTime) rfl (keyName kpkId) []
        exact (hf.seq (hdec.seq hput)).mono (by omega)
      | nil =>
        unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortPlacedBudget.KpkLastResortPreAfterGetEnv
        have hres : PhaseGroupSpec fineCostModel
            (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortPlacedBudget.KpkBaseKeysReserveEnv kpkId)
            (3 * FineScale) := by
          have hnf : NonFreeBound
              (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortPlacedBudget.KpkBaseKeysReserveEnv kpkId)
              1 := by
            intro evs hr
            have hdr : ∀ (x : DoReserveCall),
                nonFreeCount (LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveEvents x) ≤ 1 := by
              intro x; unfold LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveEvents
              split <;> simp [nonFreeCount_rustAllocEvents, nonFreeCount_rustReallocEvents]
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
            · simp [nonFreeCount_nil]
            all_goals exact hdr _
          exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by omega)
        have hgetLr := s3_dirGetFixed_groups fineCostModel rd files
          StoresGhost.opened.kyber.lastResort (CryptoVerification.SignalSession.Cli.baseKeysName kpkId)
        have hlrPre := (hdec.seq (hres.seq hgetLr)).mono (show 30 * FineScale + (3 * FineScale + 42 * FineScale) ≤ 75 * FineScale by omega)
        have hlrTail : PhaseGroupSpec fineCostModel
            (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.OptKpkMarkLastResortTailEnv
              DirPutEnv ⟨0#64, 0#64, 0#64, 0#64, kpkId, spkId, baseKey, StoresGhost.opened.kyber⟩
              (StoresGhost.opened.kyber.lastResort.get rd files
                (CryptoVerification.SignalSession.Cli.baseKeysName kpkId)))
            (12 * FineScale) := by
          unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.OptKpkMarkLastResortTailEnv
          cases StoresGhost.opened.kyber.lastResort.get rd files
            (CryptoVerification.SignalSession.Cli.baseKeysName kpkId) with
          | error _ => exact hf.mono (Nat.zero_le _)
          | ok seenBs =>
            have hpreEv : PhaseGroupSpec fineCostModel
                (· = LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudgetAux.kpkAfterLrGetPreEvents)
                (6 * FineScale) := by
              have hnf : NonFreeBound
                  (· = LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGetPlacedBudgetAux.kpkAfterLrGetPreEvents)
                  2 := by
                intro evs he; subst he; decide
              exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by omega)
            have hbr : PhaseGroupSpec fineCostModel
                (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.KpkAfterLrGetCapFreeBranchEnv
                  DirPutEnv ⟨0#64, 0#64, 0#64, 0#64, kpkId, spkId, baseKey, StoresGhost.opened.kyber⟩ seenBs)
                (6 * FineScale) := by
              unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.KpkAfterLrGetCapFreeBranchEnv
              split_ifs
              · exact ((PhaseGroupSpec.rustAlloc_any fineCostModel 15 1).seq hf).mono (by omega)
              · have hmid : PhaseGroupSpec fineCostModel
                    (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.KpkSeenAppendReserveMidEnv seenBs)
                    (3 * FineScale) := by
                  have hnf : NonFreeBound
                      (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.KpkSeenAppendReserveMidEnv seenBs)
                      1 := by
                    intro evs hm
                    cases hm with
                    | fast _ hfo => exact Nat.le_trans (freeOnly_nonFree_zero_s3b hfo).le (by decide)
                    | grow spare _ =>
                      rw [nonFreeCount_append]
                      have h1 : nonFreeCount
                          (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.kpkSeenAppendReserveEventsAt seenBs spare) ≤ 1 := by
                        unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.SymPlacedBudgetAux.kpkSeenAppendReserveEventsAt
                          LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.doReserveEvents
                        split <;> simp [nonFreeCount_rustAllocEvents, nonFreeCount_rustReallocEvents]
                      have h2 : nonFreeCount
                          (LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget.optDeallocBufEvents 37#64) = 0 := by
                        decide
                      omega
                  exact (PhaseGroupSpec.of_nonFreeBound fineCostModel hnf).mono (by omega)
                have hputLr := s3_dirPut_opened_groups fineCostModel
                  (dir := StoresGhost.opened.kyber.lastResort) rfl
                  (CryptoVerification.SignalSession.Cli.baseKeysName kpkId)
                  (seenBs ++ CryptoVerification.SignalSession.Cli.baseKeyEntry spkId baseKey)
                exact (hmid.seq hputLr).mono (by omega)
              · exact ((PhaseGroupSpec.rustAlloc_any fineCostModel 14 1).seq hf).mono (by omega)
            exact (hpreEv.seq hbr).mono (by omega)
        exact (hf.seq (hlrPre.seq hlrTail)).mono (by omega)
  exact (w4BoxedStoreStep_le_44_fine_groupSpec (by decide) (hpre.seq htail)).mono (by omega)


private theorem recordSerializeSeqFreeEnv_of_valid_fine_groupSpec_s3b {pqCap : Nat}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget.SessionGhostValid G ses ∧
        SessionCloneDom pqCap ses) :
    PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit.RecordSerializeSeqFreeEnv g r)
      LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.recordSerializeDomFineGrpS := by
  unfold LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit.RecordSerializeSeqFreeEnv
    LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.recordSerializeDomFineGrpS
  cases hg : g.cur <;> cases hr : r.currentSession
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · rename_i G ses
    obtain ⟨hgv, hdom⟩ := hValid G ses hg hr
    exact LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.serializeSomeSeqFreeEnv_groupSpec
      fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.segCloneEnv_dom_fine_groupSpec hgv hdom)


end S3bHoleBHelpers



/-! ## `rfl` Wrappers Over `GateM2rGStatesRecvTwins.m2rg_*` -/

/-- Re-export of the `<States>::recv` inclusion into `StatesRecvProtoEnv'`. -/
theorem w4c_statesRecvExactTightEnv_sub_statesRecvProtoEnv' {F : ShaCompress} (K : MlKem)
    {pb : V1State} (x : StatesRecvGhost F) {evs : List AllocEvent}
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok x.self)
    (h : LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired.StatesRecvExactTightEnv
      K x evs) :
    @StatesRecvProtoEnv' F K x.self x.msg evs :=
  statesRecvExactTightEnv_sub_statesRecvProtoEnv' K x hfrom h

/-- `(SR, LoopAdvEnv, maxOps)`-parametric Path B `try_decrypt` envelope (`rfl` with `m2rg_`). -/
abbrev W4TryDecryptPathBCmkSrEnvOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem)
    (td : LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot.W4TryDecryptCallCmk) :
    List AllocEvent → Prop :=
  m2rg_TryDecryptCliLinkedEnvOf' LoopAdvEnv maxOps C K (SR C.F K) td.a

/-- `(SR, LoopAdvEnv, maxOps)`-parametric archived-trial run envelope (`rfl` with `m2rg_`). -/
abbrev W4TrialRunWideCmkSrEnvOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem) (x : W4ArchivedTrialCmk) (evs : List AllocEvent) : Prop :=
  m2rg_W4TrialRunWideCmkEnvOf' LoopAdvEnv maxOps C K (SR C.F K) x evs

/-- `(SR, LoopAdvEnv, maxOps)`-parametric Path A/C Stage-P3 `try_decrypt` envelope (`rfl` with `m2rg_`). -/
abbrev W4RecvPrekeyTryDecACCmkSrEnvOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (R : W4RecvPrekeyRealParamsCmk) (evs : List AllocEvent) : Prop :=
  m2rg_W4RecvPrekeyTryDecACCmkEnvOf' LoopAdvEnv maxOps SR R evs

/-- `(SR, LoopAdvEnv, maxOps)`-parametric `W4DecryptPrekeySlotParams` bundle (`rfl` with `m2rg_`). -/
abbrev mkW4RecvPrekeyWideCmkSrSlotParamsOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (R : W4RecvPrekeyRealParamsCmk) : W4DecryptPrekeySlotParams W4ArchivedTrialCmk :=
  m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf' LoopAdvEnv maxOps SR R

/-- `(SR, LoopAdvEnv, maxOps)`-parametric Path B envelope (`rfl` with `m2rg_`). -/
abbrev W4BinaryRecvPrekeyPathBWideCmkSrEnvOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  m2rg_W4BinaryRecvPrekeyPathBWideCmkEnvOf' LoopAdvEnv maxOps SR w evs

/-- `(SR, LoopAdvEnv, maxOps)`-parametric Path A (`Fixed`) envelope (`rfl` with `m2rg_`). -/
abbrev W4BinaryRecvPrekeyPathAWideCmkSrEnvFixedOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  m2rg_W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf' LoopAdvEnv maxOps SR w evs

/-- `(SR, LoopAdvEnv, maxOps)`-parametric Path C (`Fixed`, with `VerNe-prev1` `W4StageP3Prev1WideEnv`
on Stage P3) envelope (`rfl` with `m2rg_`). -/
abbrev W4BinaryRecvPrekeyPathCWideCmkVerNeSrEnvFixedOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  m2rg_W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed'
    LoopAdvEnv maxOps SR (m2rg_verNePrev1P3PathCEnv' LoopAdvEnv maxOps SR) w evs

/-- Complete 4-arm `(SR, LoopAdvEnv, maxOps)`-parametric W4 slot envelope (`Fixed`, with
`VerNe-prev1` on Path C Stage P3; `rfl` with `m2rg_`). -/
abbrev W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf'
    LoopAdvEnv maxOps SR (m2rg_verNePrev1P3PathCEnv' LoopAdvEnv maxOps SR) w evs

/-- Complete 4-arm `(SR, LoopAdvEnv, maxOps)`-parametric W4 slot envelope (`AllFixed`, with
`VerNe-prev1` on Path C Stage P3; `rfl` with `m2rg_`). -/
abbrev W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf'
    LoopAdvEnv maxOps SR (m2rg_verNePrev1P3PathCEnv' LoopAdvEnv maxOps SR) w evs

theorem w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {w : W4BinaryRecvPrekeyParamsCmk}
    (hfiles : w.base.files = runFiles i) (hrd : w.base.rd = cliIo.rd) :
    W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf SR LoopAdvEnv maxOps w =
      W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf SR LoopAdvEnv maxOps w :=
  m2rg_wideSlotEnvCmkWithP3CAllFixed'_eq_fixed hi hfiles hrd

theorem w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed_of_cliPqOrD3RecvDom {P : PEParams} {i : Inputs}
    (hi : CliPqOrD3RecvDom P i) {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {w : W4BinaryRecvPrekeyParamsCmk}
    (hfiles : w.base.files = runFiles i) (hrd : w.base.rd = cliIo.rd) :
    W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf SR LoopAdvEnv maxOps w =
      W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf SR LoopAdvEnv maxOps w := by
  rcases hi with hPq | ⟨_, _, rc, hwf, rfl⟩
  · exact w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed hPq hfiles hrd
  · exact w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed (cliPqxdhInputs_pqRecvInputs_nil hwf rc) hfiles hrd

/-! ## Local Slot-Params Projection from `W4PostBobPrev1Dom.W4BinaryRecvPrekeyDomCmk0'` -/

private structure Dom0pLocalRealDom (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps smallFileCap maxCt : Nat)
    (R : W4RecvPrekeyRealParamsCmk) : Prop where
  kpk_dir : R.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            R.kpkDir = StoresGhost.opened.kyber.lastResort
  outer_dom : W4DecryptPrekeyTightDom' (mkW4RecvPrekeyWideCmkSrSlotParamsOf SR LoopAdvEnv maxOps R)
    2097152 smallFileCap 286196 286196 2097152 286196 2097152
    w4PostBobPqCap 2097152 postBobTotalPrev1Cap286K 4096
  cur_fail_dom : R.hasCurSession = true → W4FailedTdDomCmkOf R.C.F R.K maxCt R.fc_cur
  trials_dom : ∀ x ∈ R.archivedTrials, W4ArchivedTrialDomCmkOf R.C.F R.K maxCt x
  tdB_dom : R.isPathB = true → W4TryDecryptCallDomCmkOf R.C.F R.K maxCt R.td_B
  tdAC_dom : R.isPathAC = true → W4TryDecryptPathACDomCmkOf R.C.F R.K maxCt R.td_AC

private def Dom0pLocalDom (SR : W4StatesRecvEnv) (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (c : CallV) (i : Inputs) (w : W4BinaryRecvPrekeyParamsCmk) : Prop :=
  ∀ peerAddr, c = .recv peerAddr →
    w.base.peer.val = addrValOf peerAddr ∧
    w.base.peer.name.bytes.length ≤ 40 ∧
    w.base.files = runFiles i ∧
    w.base.rd = cliIo.rd ∧
    (Dom0pLocalRealDom SR LoopAdvEnv maxOps sessionCapBytes msgCapBytes w.base ∧
      w.base.archivedTrials = [])

private theorem dom0p_toLocalDom {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv}
    {maxOps : Nat} {c : CallV} {i : Inputs} {w : W4BinaryRecvPrekeyParamsCmk}
    (hw4 : W4BinaryRecvPrekeyDomCmk0' SR LoopAdvEnv maxOps c i w) :
    Dom0pLocalDom SR LoopAdvEnv maxOps c i w := by
  intro peerAddr hc
  obtain ⟨hpv, hp40, hfiles, hrd, hd, htr⟩ := hw4 peerAddr hc
  refine ⟨hpv, hp40, hfiles, hrd, ⟨⟨hd.kpk_dir, ?_, hd.cur_fail_dom, hd.trials_dom,
    hd.tdB_dom, hd.tdAC_dom⟩, htr⟩⟩
  exact
    { peer_len := hd.outer_dom.peer_len
      ownKey_len := hd.outer_dom.ownKey_len
      ownReg_len := hd.outer_dom.ownReg_len
      kpkMark_len := hd.outer_dom.kpkMark_len
      res_old := hd.outer_dom.res_old
      res_new := hd.outer_dom.res_new
      ikm_small := hd.outer_dom.ikm_small
      spqr_key := hd.outer_dom.spqr_key
      sess_cap := hd.outer_dom.sess_cap
      small_cap := hd.outer_dom.small_cap
      cur_dom := hd.outer_dom.cur_dom
      arch_valid := hd.outer_dom.arch_valid
      arch_enc := hd.outer_dom.arch_enc
      out0_valid := hd.outer_dom.out0_valid
      out0_enc := hd.outer_dom.out0_enc
      out1_postBob := hd.outer_dom.out1_postBob
      trials_len4 := hd.outer_dom.trials_len4 }

/-! ## Closed-`Nat` Post-Bob `Dom0'` Stage & Slot Bounds -/

section StageSpecs

open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.SignalSession.Cli (addressText)
open LibsignalBinary.Heap (FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (keyName_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (CliPkDecodeEnv CliSpkDecodeEnv W4BinaryAcceptWideEnv W4BinaryIdSaveStepEnv
   W4BinaryIdTrustStepEnv W4BinaryInitBobWideEnv W4BinaryKpkGetStepEnv W4BinaryPkGetStepEnv
   W4BinaryPkRemoveStepEnv W4BinaryPromoteArchiveEnv W4BinarySelfKpStepEnv W4BinarySelfRegIdStepEnv
   W4BinarySessLoadStepEnv W4BinarySessStorePrev1StepEnv W4BinarySessStoreStepEnv
   W4BinarySpkGetStepEnv W4BinaryStageP1OkEnv W4BinaryStageP1UntrustedEnv
   W4CloneACDomEnv W4CloneBDomEnv)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed (W4BinaryKpkMarkStepEnvFixed)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_freeNonInc fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
  (W4BoundedEvs phaseCredit_w4BoundedEvs_small phaseCredit_w4PqxdhAccept_small w4PqxdhAcceptCum)
open LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers (stringClone_phaseCredit_small)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (phaseCredit_optStageEnv phaseCredit_w4BobSessionBuild9_small)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
  (opened_all_dirDomainCaps phaseCreditSpec_seq_freeOnly_exact w4SpqrInitCum)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec
  (w4ErrTailWide_fine_phaseCredit_tight w4StageP2MatchedCheck_fine_phaseCredit
   w4StageP3Wide_fine_phaseCredit_tight w4StageP3Wide_zeroLive_fine_phaseCredit_tight
   w4TryDecryptCloneFailWide_dom_fine_cancel_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
  (boxAllocEnv_fine_le_28 fineOptLarge w4BoxedStoreStep_fine_le_28 w4SpqrInit32_fine_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec
  (boxAllocEnv_le_28_fine_groupSpec phaseGroupSpec_ite_nil phaseGroupSpec_optStage
   w4BobSessionBuild9FineGrpS w4BobSessionBuild9_groupSpec w4BoxedStoreStep_le_28_fine_groupSpec
   w4BoxedStoreStep_le_44_fine_groupSpec w4ErrTailWideFineGrpS w4ErrTailWide_fine_groupSpec
   w4PqxdhAcceptFineGrpS w4PqxdhAccept_fine_groupSpec w4StageP2MatchedCheck_fine_groupSpec
   w4StageP3Wide_fine_groupSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget (deserCancelFineGrpS)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (cliRd_ok_le_fileCap)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
  (OptIkpTryFromEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
  (OptRegIdMalformedEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget (OptPkDecodeEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
  (OptPkRemoveTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (OptSpkDecodeEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
  (dirGetEnv_path_readFile_fine_phaseCredit_tight)

/-- Tight `PhaseCreditSpec` for `VerNeTightTopEnv enc` (`(16,910,031, 3,211,282, 5,316,629, 2,097,152)`). -/
theorem verNeTightTopEnv_fine_phaseCreditSpec (enc : List (BitVec 8)) :
    PhaseCreditSpec fineCostModel (VerNeTightTopEnv enc)
      16910031 3211282 5316629 2097152 := by
  unfold VerNeTightTopEnv VerNeTightTopEnvOf VerNeS1Env VerNeTailEnv
  have hS1 : PhaseCreditSpec fineCostModel
      (SeqEnv (· = rustAllocEvents 192 8) FreeOnlyEvs) 9789 0 0 192 :=
    phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
      (s3_rustAlloc_small_credit (req := 192) (al := 8) (by decide) (by decide))
  have hTail : PhaseCreditSpec fineCostModel
      (SeqEnv (· = rustAllocEvents 17 1) FreeOnlyEvs) 9789 0 0 17 :=
    phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
      (s3_rustAlloc_small_credit (req := 17) (al := 1) (by decide) (by decide))
  have hMid := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (verNeSessionCancelEnv_fine_phaseCreditSpec enc)
  exact (hS1.seq (hMid.seq hTail)).mono (by decide) (by decide) (by decide) (by decide)

/-- Tight `PhaseGroupSpec` for `VerNeTightTopEnv enc` (`deserCancelFineGrpS + 6 * FineScale`). -/
theorem verNeTightTopEnv_fine_groupSpec (enc : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (VerNeTightTopEnv enc)
      (deserCancelFineGrpS + 6 * FineScale) := by
  unfold VerNeTightTopEnv VerNeTightTopEnvOf VerNeS1Env VerNeTailEnv
  have hf := PhaseGroupSpec.freeOnly fineCostModel
  have hS1 := (PhaseGroupSpec.rustAlloc_any fineCostModel 192 8).seq hf
  have hTail := (PhaseGroupSpec.rustAlloc_any fineCostModel 17 1).seq hf
  have hMid := (verNeSessionCancelEnv_fine_groupSpec enc).seq hf
  exact (hS1.seq (hMid.seq hTail)).mono (by unfold FineScale; omega)

/-! ### Closed `Nat` `Dom0'` 5-Tuple (`w4CmkDom0'*` & `fits2_zbDom0'*`) -/

/-- Post-Bob (`rc_len1 ≤ 1`) scaled group bound for `SerializePrev1SeqFreeEnv` (`35,952,015`),
built directly from `W4PostBobPrev1Dom.segClonePostBob1FineGrpS`. -/
def serializePrev1PostBob1FineGrpS : Nat :=
  segClonePostBob1FineGrpS + (11056 + 3 * FineScale) + 3 * FineScale

/-- Exact closed decimal-literal cumulative small-pool credit (`140,230,427` B) for `Dom0'`
(`W4RecvPrekeyCmkDom0'`). -/
abbrev w4CmkDom0'Cum : Nat := 140230427

/-- Exact closed decimal-literal post-slot live large-pool credit (`29,726,017` B) for `Dom0'`. -/
abbrev w4CmkDom0'Live : Nat := 29726017

/-- Exact closed decimal-literal transient peak large-pool credit (`29,726,017` B) for `Dom0'`. -/
abbrev w4CmkDom0'Peak : Nat := 29726017

/-- Exact closed decimal-literal maximum single allocation request (`4,194,368` B = `2 * (2,097,152 + 32)`
from `W4BinaryKpkMarkStepEnvFixed` on Paths A & C, dominating `postBobTotalPrev1Cap286K = 2,469,364` B). -/
abbrev w4CmkDom0'MaxReq : Nat := 4194368

/-- Exact `maxOps`-parametric `FineScale`-scaled small-group expression `grpS` (`83`/`109`/`128`)
for `Dom0'` (`serializePrev1PostBob1FineGrpS` on `gStore1`). -/
def w4CmkDom0'GrpSExprOf (maxOps : Nat) : Nat :=
  let gLoad := 11056 + 51 * FineScale + deserCancelFineGrpS
  let gTrust := 16659 + 42 * FineScale
  let gP1Ok := gLoad + gTrust
  let gUntr := gP1Ok + 3 * FineScale
  let gSave := 16659 + 51 * FineScale
  let gStore0 := 16659 + 12 * FineScale +
    LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.recordSerializeDomFineGrpS
  let gStore1 := 16659 + 12 * FineScale + serializePrev1PostBob1FineGrpS
  let gProm := LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.recordSerializeDomFineGrpS +
    3 * FineScale
  let gCloneB := LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.segCloneDomFineGrpS
  let gCloneAC := LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.segCloneFreshBobFineGrpS
  let gTd := w4cTdGrpSOf maxOps
  let gTdFail := w4cTdFailGrpSOf maxOps
  let gCurCloneFail := gCloneB + gTdFail + w4ErrTailWideFineGrpS
  let gSpk := 11056 + 216 * FineScale
  let gKpk := 11056 + 894 * FineScale
  let gPkGet := 11056 + 831 * FineScale
  let gSelfKp := 11056 + 681 * FineScale
  let gSelfReg := 11056 + 45 * FineScale
  let gInitBob := max w4PqxdhAcceptFineGrpS (18 * FineScale) +
    ((3 * FineScale * 128) + w4BobSessionBuild9FineGrpS)
  let gMark := 16659 + 159 * FineScale
  let gPkRm := 11056 + 105 * FineScale
  let gP2B := LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4StageP2MatchedCheckFineGrpS + gProm
  let gP3B := gCloneB + gTd + w4ErrTailWideFineGrpS
  let gP4B := gSave + gStore0
  let gPathB := gP1Ok + (gP2B + (gP3B + gP4B))
  let gP2A := 3 * FineScale + (gSpk + (gKpk + (6 * FineScale + (3 * FineScale +
    (gPkGet + (gSelfKp + (gInitBob + (gSelfReg + w4ErrTailWideFineGrpS))))))))
  let gP3A := gCloneAC + gTd + w4ErrTailWideFineGrpS
  let gP4A := gSave + (gMark + (gPkRm + gStore0))
  let gPathA := gP1Ok + (gP2A + (gP3A + gP4A))
  let gP2C := gCurCloneFail + (0 + (3 * FineScale + (gSpk + (gKpk + (6 * FineScale +
    (3 * FineScale + (gPkGet + (gSelfKp + (gInitBob + (gSelfReg +
      (gProm + w4ErrTailWideFineGrpS)))))))))))
  let gP3C := max (gCloneAC + gTd + w4ErrTailWideFineGrpS)
    (gCloneAC + (deserCancelFineGrpS + 6 * FineScale))
  let gP4C := gSave + (gMark + (gPkRm + gStore1))
  let gPathC := gP1Ok + (gP2C + (gP3C + gP4C))
  max gUntr (max gPathB (max gPathA gPathC))

/-- Parametric `Dom0'` `grpS` function specialized at `maxOps = 83`, `109`, `128`. -/
abbrev w4CmkDom0'GrpSOf (maxOps : Nat) : Nat := w4CmkDom0'GrpSExprOf maxOps

/-- Exact closed decimal-literal `Dom0'` `grpS` at `maxOps = 83` (`2,730,214,888`). -/
abbrev w4CmkDom0'GrpS83 : Nat := 2730214888

/-- Exact closed decimal-literal `Dom0'` `grpS` at `maxOps = 109 = w4c_defaultDecodeMaxOps` (`2,737,495,460`). -/
abbrev w4CmkDom0'GrpS109 : Nat := 2737495460

/-- Exact closed decimal-literal `Dom0'` `grpS` at `maxOps = 128` (`2,742,815,878`). -/
abbrev w4CmkDom0'GrpS128 : Nat := 2742815878

/-- Definitional cap aliases (`rfl`-equal to `w4CmkDom0'*`). -/
abbrev fits2_zbDom0'Cum : Nat := w4CmkDom0'Cum
abbrev fits2_zbDom0'Live : Nat := w4CmkDom0'Live
abbrev fits2_zbDom0'Peak : Nat := w4CmkDom0'Peak
abbrev fits2_zbDom0'MaxReq : Nat := w4CmkDom0'MaxReq
abbrev fits2_zbDom0'GrpS83 : Nat := w4CmkDom0'GrpS83
abbrev fits2_zbDom0'GrpS109 : Nat := w4CmkDom0'GrpS109
abbrev fits2_zbDom0'GrpS128 : Nat := w4CmkDom0'GrpS128

theorem w4CmkDom0'_live_le_peak : w4CmkDom0'Live ≤ w4CmkDom0'Peak := by decide
theorem fits2_zbDom0'_live_le_peak : fits2_zbDom0'Live ≤ fits2_zbDom0'Peak := by decide
theorem w4CmkDom0'GrpSOf_83_eq : w4CmkDom0'GrpSOf 83 = w4CmkDom0'GrpS83 := by decide
theorem w4CmkDom0'GrpSOf_109_eq :
    w4CmkDom0'GrpSOf w4c_defaultDecodeMaxOps = w4CmkDom0'GrpS109 := by decide
theorem w4CmkDom0'GrpSOf_128_eq : w4CmkDom0'GrpSOf 128 = w4CmkDom0'GrpS128 := by decide

/-- Kernel-`decide` check tying `w4CmkDom0'Cum` to `W4PostBobPrev1Dom.w4PostBobSerializePrev1TightCum`. -/
theorem w4CmkDom0'Cum_eq_postBobDelta :
    w4CmkDom0'Cum = 138754427 + (w4PostBobSerializePrev1TightCum - 1184912) := by decide

/-- Equality check tying `w4CmkDom0'Peak` to `W4PostBobPrev1Dom` constants. -/
theorem w4CmkDom0'Peak_eq_postBobDelta :
    w4CmkDom0'Peak =
      29203219 +
        (((w4PostBobOneChainLarge + fineOptLarge w4PostBobPqCap) +
            fineOptLarge 2097152 + fineOptLarge postBobTotalPrev1Cap286K) -
          4570694) := by decide

private theorem s3c_tdCum_eq : w4cTdCumOf msgCapBytes = 44530601 := by decide
private theorem s3c_tdLive_eq : w4cTdLiveOf msgCapBytes = 2086032 := by decide
private theorem s3c_tdPeak_eq : w4cTdPeakOf msgCapBytes = 2086032 := by decide
private theorem s3c_tdMaxReq_eq : w4cTdMaxReqOf msgCapBytes = 1048576 := by decide
private theorem s3c_tdFailCum_eq : w4cTdFailCumOf msgCapBytes = 44526173 := by decide
private theorem s3c_tdFailPeak_eq : w4cTdFailPeakOf msgCapBytes = 2086032 := by decide
private theorem s3c_store1_live_eq :
    (w4PostBobOneChainLarge + fineOptLarge w4PostBobPqCap) +
      fineOptLarge 2097152 + fineOptLarge postBobTotalPrev1Cap286K = 5093492 := by decide

/-- `PhaseCreditSpec` for the Untrusted and Path B (`Matched`) arms of `recv-prekey`. -/
private theorem s3a_sub4_cmkDom0_untrusted_and_pathB_credit
    {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    (hLoopSub : W4LoopAdvSub LoopAdvEnv CmkLoopAdvanceEvs)
    (hSr : ∀ F K, StatesRecvTightCreditSpec F (SR F K) 1647247 93776)
    (i : Inputs) (peerAddr : AddrV) (w4 : W4BinaryRecvPrekeyParamsCmk)
    (hw4 : Dom0pLocalDom SR LoopAdvEnv maxOps (.recv peerAddr) i w4) :
    PhaseCreditSpec fineCostModel
      (fun e =>
        W4BinaryStageP1UntrustedEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey e ∨
        W4BinaryRecvPrekeyPathBWideCmkSrEnvOf SR LoopAdvEnv maxOps w4 e)
      w4CmkDom0'Cum w4CmkDom0'Live w4CmkDom0'Peak w4CmkDom0'MaxReq := by
  obtain ⟨_, hpeer, hfiles, hrd, hDom, hTrialsNil⟩ := hw4 peerAddr rfl
  have hf := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hLoad : PhaseCreditSpec fineCostModel
      (W4BinarySessLoadStepEnv w4.base.rd w4.base.files w4.base.peer)
      17517856 5316629 8478747 2097152 := by
    rw [hrd, hfiles]; exact s3a5_sessLoadStep_credit (runFiles i) w4.base.peer hpeer
  have hTrust : PhaseCreditSpec fineCostModel
      (W4BinaryIdTrustStepEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey)
      596479 2105347 3162118 2097152 := by
    rw [hrd, hfiles]
    exact s3a5_idTrustStep_credit (runFiles i) w4.base.peer w4.remoteIdKey hpeer
  have hStr : PhaseCreditSpec fineCostModel
      (LibsignalBinary.Heap.RustStdAllocBudgetBridge.StringCloneEnv w4.base.peer.name)
      9619 0 0 40 :=
    stringClone_phaseCredit_small fineCostModel_modelHyps hpeer
      (by rw [fineCostModel_smallMaxReq_eq]; decide)
  have hStrF : PhaseCreditSpec fineCostModel _ 9619 0 0 40 :=
    phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hStr
  have hTrStr : PhaseCreditSpec fineCostModel _ 606098 2105347 3162118 2097152 :=
    (hTrust.seq hStrF).mono (by decide) (by decide) (by decide) (by decide)
  have hUntr : PhaseCreditSpec fineCostModel
      (W4BinaryStageP1UntrustedEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey)
      18123954 7421976 10584094 2097152 := by
    unfold W4BinaryStageP1UntrustedEnv
    exact (hLoad.seq hTrStr).mono (by decide) (by decide) (by decide) (by decide)
  have hP1Ok : PhaseCreditSpec fineCostModel
      (W4BinaryStageP1OkEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey)
      18114335 7421976 10584094 2097152 := by
    unfold W4BinaryStageP1OkEnv
    exact (hLoad.seq (phaseCredit_optStageEnv fineCostModel_modelHyps hTrust)).mono
      (by decide) (by decide) (by decide) (by decide)
  let P := mkW4RecvPrekeyWideCmkSrSlotParamsOf SR LoopAdvEnv maxOps w4.base
  have hLoop : PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.IterSeqEnv
        (LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak.ArchivedTrialIterEnv
          P.DecEnv P.TrialEnv P.DropEnv) P.archivedTrials)
      0 0 0 0 := by
    have hnil : P.archivedTrials = [] := hTrialsNil
    rw [hnil]
    exact PhaseCreditSpec.nil fineCostModel
  have hProm := s3a5_promoteArchive_credit w4.base.g_arch w4.base.r_arch
    hDom.outer_dom.arch_valid hDom.outer_dom.arch_enc
  have hPromOr : PhaseCreditSpec fineCostModel _ 8430863 3480713 3480713 2097152 :=
    (hf.or (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hProm)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hLoopProm : PhaseCreditSpec fineCostModel _ 8430863 3480713 3480713 2097152 :=
    (hLoop.seq hPromOr).mono (by decide) (by decide) (by decide) (by decide)
  have hP2BRight : PhaseCreditSpec fineCostModel _ 8430863 3480713 3480713 2097152 :=
    phaseCredit_optStageEnv fineCostModel_modelHyps
      ((hf.or hLoopProm).mono (by decide) (by decide) (by decide) (by decide))
  have hP2B : PhaseCreditSpec fineCostModel _ 8433208 3480713 3480713 2097152 :=
    (w4StageP2MatchedCheck_fine_phaseCredit.seq hP2BRight).mono
      (by decide) (by decide) (by decide) (by decide)
  have hTdB0 : PhaseCreditSpec fineCostModel P.TryDecEnv
      (w4cTdCumOf msgCapBytes) (w4cTdLiveOf msgCapBytes)
      (w4cTdPeakOf msgCapBytes) (w4cTdMaxReqOf msgCapBytes) := by
    change PhaseCreditSpec fineCostModel
      (if w4.base.isPathB then
        m2rg_TryDecryptCliLinkedEnvOf' LoopAdvEnv maxOps w4.base.C w4.base.K
          (SR w4.base.C.F w4.base.K) w4.base.td_B.a
       else fun _ => False) _ _ _ _
    cases hpb : w4.base.isPathB
    · exact (PhaseCreditSpec.empty fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact (w4c_tryDecryptCliLinkedSrEnvOf_cmk_phaseCreditSpec (maxOps := maxOps)
        (hSr w4.base.C.F w4.base.K) (hDom.tdB_dom hpb)).of_imp fun _ h =>
        m2rg_tryDecryptCliLinkedEnvOf'_mono hLoopSub (Nat.le_refl maxOps) (fun _ _ _ hr => hr) h
  have hTdB : PhaseCreditSpec fineCostModel P.TryDecEnv 44530601 2086032 2086032 1048576 := by
    rwa [s3c_tdCum_eq, s3c_tdLive_eq, s3c_tdPeak_eq, s3c_tdMaxReq_eq] at hTdB0
  have hP3B : PhaseCreditSpec fineCostModel _ 52816731 3461398 3461398 1048576 :=
    (w4StageP3Wide_fine_phaseCredit_tight s3a4_w4CloneBDom_credit hTdB).mono
      (by decide) (by decide) (by decide) (by decide)
  have hSave : PhaseCreditSpec fineCostModel
      (W4BinaryIdSaveStepEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey)
      625846 2105347 3162118 2097152 := by
    rw [hrd, hfiles]
    exact s3a5_idSaveStep_credit (runFiles i) w4.base.peer w4.remoteIdKey hpeer
  have hStore := s3a5_sessStoreStep_credit w4.base.peer w4.base.g_out0 w4.base.r_out0 hpeer
    hDom.outer_dom.out0_valid hDom.outer_dom.out0_enc
  have hP4B : PhaseCreditSpec fineCostModel _ 9068578 5586060 5586060 2097152 :=
    ((phaseCredit_optStageEnv fineCostModel_modelHyps hSave).seq
      (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
        (phaseCredit_optStageEnv fineCostModel_modelHyps hStore))).mono
      (by decide) (by decide) (by decide) (by decide)
  have hOptP2B := phaseCredit_optStageEnv fineCostModel_modelHyps hP2B
  have hOptP3B := phaseCredit_optStageEnv fineCostModel_modelHyps hP3B
  have hOptP4B := phaseCredit_optStageEnv fineCostModel_modelHyps hP4B
  have hP34B : PhaseCreditSpec fineCostModel _ 61885309 9047458 9047458 2097152 :=
    (hOptP3B.seq hOptP4B).mono (by decide) (by decide) (by decide) (by decide)
  have hP234B : PhaseCreditSpec fineCostModel _ 70318517 12528171 12528171 2097152 :=
    (hOptP2B.seq hP34B).mono (by decide) (by decide) (by decide) (by decide)
  have hPathB : PhaseCreditSpec fineCostModel
      (W4BinaryRecvPrekeyPathBWideCmkSrEnvOf SR LoopAdvEnv maxOps w4)
      w4CmkDom0'Cum w4CmkDom0'Live w4CmkDom0'Peak w4CmkDom0'MaxReq := by
    unfold W4BinaryRecvPrekeyPathBWideCmkSrEnvOf m2rg_W4BinaryRecvPrekeyPathBWideCmkEnvOf'
    exact (hP1Ok.seq hP234B).mono (by decide) (by decide) (by decide) (by decide)
  exact (hUntr.or hPathB).mono (by decide) (by decide) (by decide) (by decide)

/-- `PhaseCreditSpec` for the Path A and Path C arms of `recv-prekey`. -/
private theorem s3a_sub5_cmkDom0_pathAC_credit
    {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    (hLoopSub : W4LoopAdvSub LoopAdvEnv CmkLoopAdvanceEvs)
    (hSr : ∀ F K, StatesRecvTightCreditSpec F (SR F K) 1647247 93776)
    (i : Inputs) (peerAddr : AddrV) (w4 : W4BinaryRecvPrekeyParamsCmk)
    (hw4 : Dom0pLocalDom SR LoopAdvEnv maxOps (.recv peerAddr) i w4)
    (hikp : ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "identity-key-pair") =
        .ok bs → bs.length ≤ 105)
    (hspk : ∀ id bs,
      StoresGhost.opened.signed.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 230)
    (hopk : ∀ id bs,
      StoresGhost.opened.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 125)
    (hkpkOt : ∀ id bs,
      StoresGhost.opened.kyber.oneTime.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900)
    (hkpkLr : ∀ id bs,
      StoresGhost.opened.kyber.lastResort.get cliIo.rd (runFiles i) (keyName id) = .ok bs →
        bs.length ≤ 4900) :
    PhaseCreditSpec fineCostModel
      (fun e =>
        W4BinaryRecvPrekeyPathAWideCmkSrEnvFixedOf SR LoopAdvEnv maxOps w4 e ∨
        W4BinaryRecvPrekeyPathCWideCmkVerNeSrEnvFixedOf SR LoopAdvEnv maxOps w4 e)
      w4CmkDom0'Cum w4CmkDom0'Live w4CmkDom0'Peak w4CmkDom0'MaxReq := by
  obtain ⟨_, hpeer, hfiles, hrd, hDom, hTrialsNil⟩ := hw4 peerAddr rfl
  obtain ⟨hdcOwn0, _hdcPeers0, hdcSpk0, hdcKot0, hdcKlr0, hdcOpk0, _hdcSess0⟩ :=
    opened_all_dirDomainCaps
  have hdcOwn := s3_dirDomainCaps_64 hdcOwn0 (by decide)
  have hdcSpk := s3_dirDomainCaps_64 hdcSpk0 (by decide)
  have hdcKot := s3_dirDomainCaps_64 hdcKot0 (by decide)
  have hdcKlr := s3_dirDomainCaps_64 hdcKlr0 (by decide)
  have hdcOpk := s3_dirDomainCaps_64 hdcOpk0 (by decide)
  have hf := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hLoad : PhaseCreditSpec fineCostModel
      (W4BinarySessLoadStepEnv w4.base.rd w4.base.files w4.base.peer)
      17517856 5316629 8478747 2097152 := by
    rw [hrd, hfiles]; exact s3a5_sessLoadStep_credit (runFiles i) w4.base.peer hpeer
  have hTrust : PhaseCreditSpec fineCostModel
      (W4BinaryIdTrustStepEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey)
      596479 2105347 3162118 2097152 := by
    rw [hrd, hfiles]
    exact s3a5_idTrustStep_credit (runFiles i) w4.base.peer w4.remoteIdKey hpeer
  have hP1Ok : PhaseCreditSpec fineCostModel
      (W4BinaryStageP1OkEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey)
      18114335 7421976 10584094 2097152 := by
    unfold W4BinaryStageP1OkEnv
    exact (hLoad.seq (phaseCredit_optStageEnv fineCostModel_modelHyps hTrust)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hBnd33 : PhaseCreditSpec fineCostModel _ 9605 0 0 33 :=
    (phaseCredit_optStageEnv fineCostModel_modelHyps
      (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
        (phaseCredit_w4BoundedEvs_small fineCostModel_modelHyps 1 33
          (by rw [fineCostModel_smallMaxReq_eq]; decide)))).mono
      (by decide) (by decide) (by decide) (by decide)
  have hOptSpk : PhaseCreditSpec fineCostModel
      (OptSpkDecodeEnv CliSpkDecodeEnv
        (StoresGhost.opened.signed.get cliIo.rd (runFiles i) (keyName w4.base.spkId)))
      837400 0 0 9808 := by
    unfold OptSpkDecodeEnv
    cases hgr : StoresGhost.opened.signed.get cliIo.rd (runFiles i) (keyName w4.base.spkId) with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil =>
        exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      | cons b0 bsRest =>
        exact s3a_sub1_cliSpkDecode_credit (hspk w4.base.spkId (b0 :: bsRest) hgr) (by decide)
  have hSpkGet : PhaseCreditSpec fineCostModel _ 33595 0 0 4096 :=
    (dirGetEnv_path_readFile_fine_phaseCredit_tight
      cliIo.rd (runFiles i) StoresGhost.opened.signed (keyName w4.base.spkId) hdcSpk
      (Nat.le_trans (keyName_length_le w4.base.spkId) (by decide))
      (fun bs h => hspk w4.base.spkId bs h)).mono (by decide) (by decide) (by decide) (by decide)
  have hSpkTail : PhaseCreditSpec fineCostModel _ 870995 0 0 9808 :=
    (hSpkGet.seq (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hOptSpk)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hSpkBody : PhaseCreditSpec fineCostModel _ 890573 0 0 9808 :=
    ((s3a5_decimal_credit w4.base.spkId).seq hSpkTail).mono
      (by decide) (by decide) (by decide) (by decide)
  have hSpkCli : PhaseCreditSpec fineCostModel _ 891061 0 0 9808 :=
    (w4BoxedStoreStep_fine_le_28 (boxSz := 16) (by decide) hSpkBody).mono
      (by decide) (by decide) (by decide) (by decide)
  have hSpkStep : PhaseCreditSpec fineCostModel _ 891061 0 0 9808 :=
    phaseCredit_optStageEnv fineCostModel_modelHyps
      (s3a5_subst_rd_files (P := fun rd files => W4BinarySpkGetStepEnv rd files w4.base.spkId)
        hrd hfiles hSpkCli)
  have hOtKpk : PhaseCreditSpec fineCostModel _ 3226581 2105347 3162118 2097152 :=
    (s3a5_kpkPass_credit (runFiles i) StoresGhost.opened.kyber.oneTime w4.base.kpkId
      hdcKot (fun bs h => hkpkOt w4.base.kpkId bs h) (fun bs h => hkpkOt w4.base.kpkId bs h)
      (fun hbs hL => s3a_sub1_cliSpkDecode_credit hbs hL)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hLrKpk : PhaseCreditSpec fineCostModel _ 3226581 2105347 3162118 2097152 :=
    (s3a5_kpkPass_credit (runFiles i) StoresGhost.opened.kyber.lastResort w4.base.kpkId
      hdcKlr (fun bs h => hkpkLr w4.base.kpkId bs h) (fun bs h => hkpkLr w4.base.kpkId bs h)
      (fun hbs hL => s3a_sub1_cliSpkDecode_credit hbs hL)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hKpkPoll : PhaseCreditSpec fineCostModel _ 3268082 2105347 3162118 2097152 :=
    (s3a5_kpkPoll_credit (runFiles i) w4.base.kpkId hdcKot hOtKpk hLrKpk).mono
      (by decide) (by decide) (by decide) (by decide)
  have hKpkCli : PhaseCreditSpec fineCostModel _ 3268570 2105347 3162118 2097152 :=
    (w4BoxedStoreStep_fine_le_28 (boxSz := 16) (by decide) hKpkPoll).mono
      (by decide) (by decide) (by decide) (by decide)
  have hKpkStep : PhaseCreditSpec fineCostModel _ 3268570 2105347 3162118 2097152 :=
    phaseCredit_optStageEnv fineCostModel_modelHyps
      (s3a5_subst_rd_files (P := fun rd files => W4BinaryKpkGetStepEnv rd files w4.base.kpkId)
        hrd hfiles hKpkCli)
  have hKemStep : PhaseCreditSpec fineCostModel _ 19578 0 0 3168 :=
    phaseCredit_optStageEnv fineCostModel_modelHyps s3a5_kemKpFromPubPriv_credit
  have hBnd21 : PhaseCreditSpec fineCostModel _ 9581 0 0 21 :=
    (phaseCredit_optStageEnv fineCostModel_modelHyps
      (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
        (phaseCredit_w4BoundedEvs_small fineCostModel_modelHyps 1 21
          (by rw [fineCostModel_smallMaxReq_eq]; decide)))).mono
      (by decide) (by decide) (by decide) (by decide)
  have hOptPk : PhaseCreditSpec fineCostModel
      (OptPkDecodeEnv CliPkDecodeEnv
        (StoresGhost.opened.oneTime.get cliIo.rd (runFiles i) (keyName w4.base.opkId)))
      2476617 0 0 256 := by
    unfold OptPkDecodeEnv
    cases hgr : StoresGhost.opened.oneTime.get cliIo.rd (runFiles i) (keyName w4.base.opkId) with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil =>
        exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      | cons b0 bsRest =>
        exact s3a_w1c_cliPkDecode_credit (hopk w4.base.opkId (b0 :: bsRest) hgr)
  have hPkGetRead : PhaseCreditSpec fineCostModel _ 33595 0 0 4096 :=
    (dirGetEnv_path_readFile_fine_phaseCredit_tight
      cliIo.rd (runFiles i) StoresGhost.opened.oneTime (keyName w4.base.opkId) hdcOpk
      (Nat.le_trans (keyName_length_le w4.base.opkId) (by decide))
      (fun bs h => hopk w4.base.opkId bs h)).mono (by decide) (by decide) (by decide) (by decide)
  have hPkGetTail : PhaseCreditSpec fineCostModel _ 2510212 0 0 4096 :=
    (hPkGetRead.seq (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hOptPk)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hPkGetBody : PhaseCreditSpec fineCostModel _ 2529790 0 0 4096 :=
    ((s3a5_decimal_credit w4.base.opkId).seq hPkGetTail).mono
      (by decide) (by decide) (by decide) (by decide)
  have hPkGetCli : PhaseCreditSpec fineCostModel _ 2530278 0 0 4096 :=
    (w4BoxedStoreStep_fine_le_28 (boxSz := 16) (by decide) hPkGetBody).mono
      (by decide) (by decide) (by decide) (by decide)
  have hPkGetStep : PhaseCreditSpec fineCostModel _ 2530278 0 0 4096 :=
    phaseCredit_optStageEnv fineCostModel_modelHyps
      (s3a5_ite_or_nil w4.base.hasOpk
        (s3a5_subst_rd_files (P := fun rd files => W4BinaryPkGetStepEnv rd files w4.base.opkId)
          hrd hfiles hPkGetCli))
  have hkpName : (utf8 "identity-key-pair").length ≤ 64 := by
    rw [s3_utf8_length]; decide
  have hSelfKpRead : PhaseCreditSpec fineCostModel _ 33595 0 0 4096 :=
    (dirGetEnv_path_readFile_fine_phaseCredit_tight
      cliIo.rd (runFiles i) StoresGhost.opened.identity.own (utf8 "identity-key-pair") hdcOwn
      hkpName (fun bs h => hikp bs h)).mono (by decide) (by decide) (by decide) (by decide)
  have hSelfKpCli : PhaseCreditSpec fineCostModel
      (W4BinarySelfKpStepEnv cliIo.rd (runFiles i)) 2119140 0 0 4096 := by
    unfold W4BinarySelfKpStepEnv LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4OptBoxedStoreStepEnv
    have hBox := phaseCredit_optStageEnv fineCostModel_modelHyps
      (boxAllocEnv_fine_le_28 (boxSz := 16) (by decide))
    have hTail : PhaseCreditSpec fineCostModel _ 2118652 0 0 4096 :=
      (hSelfKpRead.seq
        (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps (s3a_w1c_optIkpTryFrom_credit hikp))).mono
        (by decide) (by decide) (by decide) (by decide)
    exact (hBox.seq hTail).mono (by decide) (by decide) (by decide) (by decide)
  have hSelfKpStep : PhaseCreditSpec fineCostModel _ 2119140 0 0 4096 :=
    phaseCredit_optStageEnv fineCostModel_modelHyps
      (s3a5_subst_rd_files (P := fun rd files => W4BinarySelfKpStepEnv rd files)
        hrd hfiles hSelfKpCli)
  have hSmallIkm : max 4096 1569 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; exact hDom.outer_dom.ikm_small
  have hSm68 : 68 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hAccWide : PhaseCreditSpec fineCostModel
      (W4BinaryAcceptWideEnv w4.base.x_res w4.base.hasOpk) 78751 0 0 4096 :=
    ((phaseCredit_w4PqxdhAccept_small fineCostModel_modelHyps
        (hasOpk := w4.base.hasOpk) hDom.outer_dom.res_old hDom.outer_dom.res_new hSmallIkm).or
      (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
        (phaseCredit_w4BoundedEvs_small fineCostModel_modelHyps 6 192
          (by rw [fineCostModel_smallMaxReq_eq]; decide)))).mono
      (by decide) (by decide) (by decide) (by decide)
  have hSpqrBob : PhaseCreditSpec fineCostModel _ 2389411 0 0 4224 :=
    (phaseCredit_optStageEnv fineCostModel_modelHyps
      ((w4SpqrInit32_fine_phaseCredit w4.base.C.F w4.base.x_spqr hDom.outer_dom.spqr_key).seq
        (phaseCredit_optStageEnv fineCostModel_modelHyps
          (phaseCredit_w4BobSessionBuild9_small fineCostModel_modelHyps hSm68)))).mono
      (by decide) (by decide) (by decide) (by decide)
  have hInitBob0 : PhaseCreditSpec fineCostModel
      (W4BinaryInitBobWideEnv w4.base.C.F w4.base.x_res w4.base.hasOpk w4.base.x_spqr)
      2468162 0 0 4224 :=
    (hAccWide.seq hSpqrBob).mono (by decide) (by decide) (by decide) (by decide)
  have hInitBobStep : PhaseCreditSpec fineCostModel _ 2468162 0 0 4224 :=
    phaseCredit_optStageEnv fineCostModel_modelHyps hInitBob0
  have hregName : (utf8 "registration-id").length ≤ 64 := by
    rw [s3_utf8_length]; decide
  have hRegMal : PhaseCreditSpec fineCostModel
      (OptRegIdMalformedEnv
        (StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "registration-id")))
      9789 0 0 14 := by
    unfold OptRegIdMalformedEnv
    cases StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "registration-id") with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok bs =>
      dsimp only
      split_ifs
      · exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      · exact s3_rustAlloc_small_credit (req := 14) (al := 1) (by decide) (by decide)
  have hRegRead : PhaseCreditSpec fineCostModel _ 595003 2105347 3162118 2097152 :=
    (dirGetEnv_path_readFile_fine_phaseCredit_tight
      cliIo.rd (runFiles i) StoresGhost.opened.identity.own (utf8 "registration-id") hdcOwn
      hregName (fun _ h => cliRd_ok_le_fileCap h)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hRegBody : PhaseCreditSpec fineCostModel _ 604792 2105347 3162118 2097152 :=
    (hRegRead.seq (phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps hRegMal)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hSelfRegCli : PhaseCreditSpec fineCostModel _ 605280 2105347 3162118 2097152 :=
    (w4BoxedStoreStep_fine_le_28 (boxSz := 16) (by decide) hRegBody).mono
      (by decide) (by decide) (by decide) (by decide)
  have hSelfRegStep : PhaseCreditSpec fineCostModel _ 605280 2105347 3162118 2097152 :=
    phaseCredit_optStageEnv fineCostModel_modelHyps
      (s3a5_subst_rd_files (P := fun rd files => W4BinarySelfRegIdStepEnv rd files)
        hrd hfiles hSelfRegCli)
  -- Pairwise stage P2A collapses (pure decimal arithmetic at each step)
  have hA9 : PhaseCreditSpec fineCostModel _ 613954 2105347 3162118 2097152 :=
    (hSelfRegStep.seq w4ErrTailWide_fine_phaseCredit_tight).mono
      (by decide) (by decide) (by decide) (by decide)
  have hA8 : PhaseCreditSpec fineCostModel _ 3082116 2105347 3162118 2097152 :=
    (hInitBobStep.seq hA9).mono (by decide) (by decide) (by decide) (by decide)
  have hA7 : PhaseCreditSpec fineCostModel _ 5201256 2105347 3162118 2097152 :=
    (hSelfKpStep.seq hA8).mono (by decide) (by decide) (by decide) (by decide)
  have hA6 : PhaseCreditSpec fineCostModel _ 7731534 2105347 3162118 2097152 :=
    (hPkGetStep.seq hA7).mono (by decide) (by decide) (by decide) (by decide)
  have hA5 : PhaseCreditSpec fineCostModel _ 7741115 2105347 3162118 2097152 :=
    (hBnd21.seq hA6).mono (by decide) (by decide) (by decide) (by decide)
  have hA4 : PhaseCreditSpec fineCostModel _ 7760693 2105347 3162118 2097152 :=
    (hKemStep.seq hA5).mono (by decide) (by decide) (by decide) (by decide)
  have hA3 : PhaseCreditSpec fineCostModel _ 11029263 4210694 5267465 2097152 :=
    (hKpkStep.seq hA4).mono (by decide) (by decide) (by decide) (by decide)
  have hA2 : PhaseCreditSpec fineCostModel _ 11920324 4210694 5267465 2097152 :=
    (hSpkStep.seq hA3).mono (by decide) (by decide) (by decide) (by decide)
  have hP2ATail : PhaseCreditSpec fineCostModel _ 11929929 4210694 5267465 2097152 :=
    (hBnd33.seq hA2).mono (by decide) (by decide) (by decide) (by decide)
  have hOptP2A := phaseCredit_optStageEnv fineCostModel_modelHyps hP2ATail
  let P := mkW4RecvPrekeyWideCmkSrSlotParamsOf SR LoopAdvEnv maxOps w4.base
  have hCurTrial0 : PhaseCreditSpec fineCostModel P.CurTrialFailEnv
      (w4cTdFailCumOf msgCapBytes) 0 (w4cTdFailPeakOf msgCapBytes) (w4cTdMaxReqOf msgCapBytes) := by
    change PhaseCreditSpec fineCostModel
      (if w4.base.hasCurSession then
        m2rg_W4FailedTdCancelCmkEnvOf' LoopAdvEnv maxOps w4.base.C w4.base.K
          (SR w4.base.C.F w4.base.K) w4.base.fc_cur
       else fun _ => False) _ _ _ _
    cases hcs : w4.base.hasCurSession
    · exact (PhaseCreditSpec.empty fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact (w4FailedTdCancelCmkSrEnvOf_phaseCreditSpec (maxOps := maxOps)
        (hSr w4.base.C.F w4.base.K) (hDom.cur_fail_dom hcs)).of_imp fun _ h => by
        rcases h with hf0 | ⟨e1, e2, rfl, h1, h2⟩
        · exact Or.inl hf0
        · exact Or.inr ⟨e1, e2, rfl,
            LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins.m2rg_tryDecryptCliLinkedFailEnvOf'_mono
              hLoopSub (Nat.le_refl maxOps) (fun _ _ _ hr => hr) h1, h2⟩
  have hCurTrial : PhaseCreditSpec fineCostModel P.CurTrialFailEnv 44526173 0 2086032 1048576 := by
    rwa [s3c_tdFailCum_eq, s3c_tdFailPeak_eq, s3c_tdMaxReq_eq] at hCurTrial0
  have hCurStep : PhaseCreditSpec fineCostModel _ 52812303 0 3461398 1048576 :=
    (phaseCredit_optStageEnv fineCostModel_modelHyps
      (w4TryDecryptCloneFailWide_dom_fine_cancel_phaseCredit hDom.outer_dom.cur_dom hCurTrial)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hLoop0 : PhaseCreditSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.IterSeqEnv
        (LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak.ArchivedTrialIterEnv
          P.DecEnv P.TrialEnv P.DropEnv) P.archivedTrials)
      0 0 0 0 := by
    have hnil : P.archivedTrials = [] := hTrialsNil
    rw [hnil]
    exact PhaseCreditSpec.nil fineCostModel
  have hLoopStep := phaseCredit_optStageEnv fineCostModel_modelHyps hLoop0
  have hPromStep : PhaseCreditSpec fineCostModel _ 8430863 3480713 3480713 2097152 :=
    phaseCredit_optStageEnv fineCostModel_modelHyps
      (s3a5_promoteArchive_credit w4.base.g_arch w4.base.r_arch
        hDom.outer_dom.arch_valid hDom.outer_dom.arch_enc)
  -- Pairwise stage P2C collapses (pure decimal arithmetic at each step)
  have hC11 : PhaseCreditSpec fineCostModel _ 8439537 3480713 3480713 2097152 :=
    (hPromStep.seq w4ErrTailWide_fine_phaseCredit_tight).mono
      (by decide) (by decide) (by decide) (by decide)
  have hC10 : PhaseCreditSpec fineCostModel _ 9044817 5586060 5586060 2097152 :=
    (hSelfRegStep.seq hC11).mono (by decide) (by decide) (by decide) (by decide)
  have hC9 : PhaseCreditSpec fineCostModel _ 11512979 5586060 5586060 2097152 :=
    (hInitBobStep.seq hC10).mono (by decide) (by decide) (by decide) (by decide)
  have hC8 : PhaseCreditSpec fineCostModel _ 13632119 5586060 5586060 2097152 :=
    (hSelfKpStep.seq hC9).mono (by decide) (by decide) (by decide) (by decide)
  have hC7 : PhaseCreditSpec fineCostModel _ 16162397 5586060 5586060 2097152 :=
    (hPkGetStep.seq hC8).mono (by decide) (by decide) (by decide) (by decide)
  have hC6 : PhaseCreditSpec fineCostModel _ 16171978 5586060 5586060 2097152 :=
    (hBnd21.seq hC7).mono (by decide) (by decide) (by decide) (by decide)
  have hC5 : PhaseCreditSpec fineCostModel _ 16191556 5586060 5586060 2097152 :=
    (hKemStep.seq hC6).mono (by decide) (by decide) (by decide) (by decide)
  have hC4 : PhaseCreditSpec fineCostModel _ 19460126 7691407 7691407 2097152 :=
    (hKpkStep.seq hC5).mono (by decide) (by decide) (by decide) (by decide)
  have hC3 : PhaseCreditSpec fineCostModel _ 20351187 7691407 7691407 2097152 :=
    (hSpkStep.seq hC4).mono (by decide) (by decide) (by decide) (by decide)
  have hC2 : PhaseCreditSpec fineCostModel _ 20360792 7691407 7691407 2097152 :=
    (hBnd33.seq hC3).mono (by decide) (by decide) (by decide) (by decide)
  have hC1 : PhaseCreditSpec fineCostModel _ 20360792 7691407 7691407 2097152 :=
    (hLoopStep.seq hC2).mono (by decide) (by decide) (by decide) (by decide)
  have hP2CTail : PhaseCreditSpec fineCostModel _ 73173095 7691407 7691407 2097152 :=
    (hCurStep.seq hC1).mono (by decide) (by decide) (by decide) (by decide)
  have hOptP2C := phaseCredit_optStageEnv fineCostModel_modelHyps hP2CTail
  have hTdAC0 : PhaseCreditSpec fineCostModel
      (W4RecvPrekeyTryDecACCmkSrEnvOf SR LoopAdvEnv maxOps w4.base)
      (w4cTdCumOf msgCapBytes) (w4cTdLiveOf msgCapBytes)
      (w4cTdPeakOf msgCapBytes) (w4cTdMaxReqOf msgCapBytes) := by
    unfold W4RecvPrekeyTryDecACCmkSrEnvOf m2rg_W4RecvPrekeyTryDecACCmkEnvOf'
    cases hpac : w4.base.isPathAC
    · exact (PhaseCreditSpec.empty fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact (w4c_tryDecryptCliLinkedSrEnvOf_cmk_phaseCreditSpec (maxOps := maxOps)
        (hSr w4.base.C.F w4.base.K) (hDom.tdAC_dom hpac).base).of_imp fun _ h =>
        m2rg_tryDecryptCliLinkedEnvOf'_mono hLoopSub (Nat.le_refl maxOps) (fun _ _ _ hr => hr) h
  have hTdAC : PhaseCreditSpec fineCostModel
      (W4RecvPrekeyTryDecACCmkSrEnvOf SR LoopAdvEnv maxOps w4.base)
      44530601 2086032 2086032 1048576 := by
    rwa [s3c_tdCum_eq, s3c_tdLive_eq, s3c_tdPeak_eq, s3c_tdMaxReq_eq] at hTdAC0
  have hTdACWide : PhaseCreditSpec fineCostModel _ 44575570 2086032 2086032 1048576 :=
    (w4StageP3Wide_zeroLive_fine_phaseCredit_tight s3a5_w4CloneACDom_credit hTdAC).mono
      (by decide) (by decide) (by decide) (by decide)
  have hOptP3A := phaseCredit_optStageEnv fineCostModel_modelHyps hTdACWide
  have hVerNeSeq : PhaseCreditSpec fineCostModel _ 16946326 3211282 5316629 2097152 :=
    (s3a5_w4CloneACDom_credit.seq (verNeTightTopEnv_fine_phaseCreditSpec w4.base.enc_prev1)).mono
      (by decide) (by decide) (by decide) (by decide)
  have hOptP3C : PhaseCreditSpec fineCostModel
      (m2rg_verNePrev1P3PathCEnv' LoopAdvEnv maxOps SR w4)
      44575570 3211282 5316629 2097152 := by
    unfold m2rg_verNePrev1P3PathCEnv' m2rg_verNePrev1P3PathCEnvOf' W4StageP3Prev1WideEnvOf
    exact phaseCredit_optStageEnv fineCostModel_modelHyps
      ((hTdACWide.or hVerNeSeq).mono (by decide) (by decide) (by decide) (by decide))
  have hSaveStep0 : PhaseCreditSpec fineCostModel
      (W4BinaryIdSaveStepEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey)
      625846 2105347 3162118 2097152 := by
    rw [hrd, hfiles]
    exact s3a5_idSaveStep_credit (runFiles i) w4.base.peer w4.remoteIdKey hpeer
  have hSaveStep := phaseCredit_optStageEnv fineCostModel_modelHyps hSaveStep0
  have hMarkStep0 : PhaseCreditSpec fineCostModel
      (W4BinaryKpkMarkStepEnvFixed w4.base.rd w4.base.files w4.base.kpkId w4.base.spkId w4.baseKey)
      975849 4202513 6307867 4194368 := by
    rw [hrd, hfiles]
    exact s3a_sub3_kpkMarkFixed_tight_credit i hkpkOt w4.base.kpkId w4.base.spkId w4.baseKey
  have hMarkStep := phaseCredit_optStageEnv fineCostModel_modelHyps hMarkStep0
  have hTailRem : PhaseCreditSpec fineCostModel
      (OptPkRemoveTailEnv DecimalEnv DirPutEnv
        ⟨0#64, 0#64, 0#64, w4.base.opkId, StoresGhost.opened.oneTime⟩
        (StoresGhost.opened.oneTime.get cliIo.rd (runFiles i) (keyName w4.base.opkId)))
      29367 0 0 192 := by
    unfold OptPkRemoveTailEnv
    cases StoresGhost.opened.oneTime.get cliIo.rd (runFiles i) (keyName w4.base.opkId) with
    | error _ =>
      exact hf.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil =>
        exact hf.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      | cons _ _ =>
        have hDec2 := s3a5_decimal_credit w4.base.opkId
        have hPut := s3_dirPut_opened_credit (dir := StoresGhost.opened.oneTime) rfl
          (keyName w4.base.opkId) []
        exact (hf.seq (hDec2.seq hPut)).mono
          (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  have hPkRemTail : PhaseCreditSpec fineCostModel _ 62962 0 0 4096 :=
    (hPkGetRead.seq hTailRem).mono (by decide) (by decide) (by decide) (by decide)
  have hPkRemBody : PhaseCreditSpec fineCostModel _ 82540 0 0 4096 :=
    ((s3a5_decimal_credit w4.base.opkId).seq hPkRemTail).mono
      (by decide) (by decide) (by decide) (by decide)
  have hPkRemCli : PhaseCreditSpec fineCostModel _ 83028 0 0 4096 :=
    (w4BoxedStoreStep_fine_le_28 (boxSz := 16) (by decide) hPkRemBody).mono
      (by decide) (by decide) (by decide) (by decide)
  have hPkRemStep : PhaseCreditSpec fineCostModel _ 83028 0 0 4096 :=
    phaseCredit_optStageEnv fineCostModel_modelHyps
      (s3a5_ite_or_nil w4.base.hasOpk
        (s3a5_subst_rd_files (P := fun rd files => W4BinaryPkRemoveStepEnv rd files w4.base.opkId)
          hrd hfiles hPkRemCli))
  have hStore0 : PhaseCreditSpec fineCostModel _ 8442732 3480713 3480713 2097152 :=
    phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
      (phaseCredit_optStageEnv fineCostModel_modelHyps
        (s3a5_sessStoreStep_credit w4.base.peer w4.base.g_out0 w4.base.r_out0 hpeer
          hDom.outer_dom.out0_valid hDom.outer_dom.out0_enc))
  have hStore1Raw := s3a5_sessStorePrev1Step_credit w4.base.peer w4.base.G_out1 w4.base.sess_out1
    w4.base.enc_prev1 hpeer hDom.outer_dom.out1_postBob
  have hStore10 : PhaseCreditSpec fineCostModel
      (W4BinarySessStorePrev1StepEnv w4.base.peer w4.base.G_out1 w4.base.sess_out1 w4.base.enc_prev1)
      2682704 5093492 5093492 postBobTotalPrev1Cap286K := by
    rwa [s3c_store1_live_eq] at hStore1Raw
  have hStore1 := phaseCreditSpec_seq_freeOnly_exact fineCostModel_modelHyps
    (phaseCredit_optStageEnv fineCostModel_modelHyps hStore10)
  -- Pairwise stage P4A / P4C / PathA / PathC collapses
  have hP4A2 : PhaseCreditSpec fineCostModel _ 8525760 3480713 3480713 2097152 :=
    (hPkRemStep.seq hStore0).mono (by decide) (by decide) (by decide) (by decide)
  have hP4A1 : PhaseCreditSpec fineCostModel _ 9501609 7683226 7683226 4194368 :=
    (hMarkStep.seq hP4A2).mono (by decide) (by decide) (by decide) (by decide)
  have hOptP4A : PhaseCreditSpec fineCostModel _ 10127455 9788573 9788573 4194368 :=
    phaseCredit_optStageEnv fineCostModel_modelHyps
      ((hSaveStep.seq hP4A1).mono (by decide) (by decide) (by decide) (by decide))
  have hP4C2 : PhaseCreditSpec fineCostModel _ 2765732 5093492 5093492 2469364 :=
    (hPkRemStep.seq hStore1).mono (by decide) (by decide) (by decide) (by decide)
  have hP4C1 : PhaseCreditSpec fineCostModel _ 3741581 9296005 9296005 4194368 :=
    (hMarkStep.seq hP4C2).mono (by decide) (by decide) (by decide) (by decide)
  have hOptP4C : PhaseCreditSpec fineCostModel _ 4367427 11401352 11401352 4194368 :=
    phaseCredit_optStageEnv fineCostModel_modelHyps
      ((hSaveStep.seq hP4C1).mono (by decide) (by decide) (by decide) (by decide))
  have hPA34 : PhaseCreditSpec fineCostModel _ 54703025 11874605 11874605 4194368 :=
    (hOptP3A.seq hOptP4A).mono (by decide) (by decide) (by decide) (by decide)
  have hPA234 : PhaseCreditSpec fineCostModel _ 66632954 16085299 16085299 4194368 :=
    (hOptP2A.seq hPA34).mono (by decide) (by decide) (by decide) (by decide)
  have hPathA : PhaseCreditSpec fineCostModel
      (W4BinaryRecvPrekeyPathAWideCmkSrEnvFixedOf SR LoopAdvEnv maxOps w4)
      w4CmkDom0'Cum w4CmkDom0'Live w4CmkDom0'Peak w4CmkDom0'MaxReq := by
    unfold W4BinaryRecvPrekeyPathAWideCmkSrEnvFixedOf m2rg_W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf'
    exact (hP1Ok.seq hPA234).mono (by decide) (by decide) (by decide) (by decide)
  have hPC34 : PhaseCreditSpec fineCostModel _ 48942997 14612634 14612634 4194368 :=
    (hOptP3C.seq hOptP4C).mono (by decide) (by decide) (by decide) (by decide)
  have hPC234 : PhaseCreditSpec fineCostModel _ 122116092 22304041 22304041 4194368 :=
    (hOptP2C.seq hPC34).mono (by decide) (by decide) (by decide) (by decide)
  have hPathC : PhaseCreditSpec fineCostModel
      (W4BinaryRecvPrekeyPathCWideCmkVerNeSrEnvFixedOf SR LoopAdvEnv maxOps w4)
      w4CmkDom0'Cum w4CmkDom0'Live w4CmkDom0'Peak w4CmkDom0'MaxReq := by
    unfold W4BinaryRecvPrekeyPathCWideCmkVerNeSrEnvFixedOf m2rg_W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed'
    exact (hP1Ok.seq hPC234).mono (by decide) (by decide) (by decide) (by decide)
  exact (hPathA.or hPathC).mono (by decide) (by decide) (by decide) (by decide)

/-- Stage-level `PhaseCreditSpec` on `W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf` under
`CliPqxdhInputs` + `W4BinaryRecvPrekeyDomCmk0'` (without `parseArgs` premise). -/
theorem w4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf_phaseCreditSpec'_of_dom
    {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    (hLoopSub : W4LoopAdvSub LoopAdvEnv CmkLoopAdvanceEvs)
    (hSr : ∀ F K, StatesRecvTightCreditSpec F (SR F K) 1647247 93776)
    (W : CliHooks) (i : Inputs) (peerAddr : AddrV)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (w4 : W4BinaryRecvPrekeyParamsCmk)
    (hw4 : W4BinaryRecvPrekeyDomCmk0' SR LoopAdvEnv maxOps (.recv peerAddr) i w4) :
    PhaseCreditSpec fineCostModel
      (W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf SR LoopAdvEnv maxOps w4)
      w4CmkDom0'Cum w4CmkDom0'Live w4CmkDom0'Peak w4CmkDom0'MaxReq := by
  have hw4 := dom0p_toLocalDom hw4
  obtain ⟨hikp, hspk, hopk, hkpkOt, hkpkLr⟩ := s3a_sub0_store_file_caps W i hi
  have hUB := s3a_sub4_cmkDom0_untrusted_and_pathB_credit hLoopSub hSr i peerAddr w4 hw4
  have hAC := s3a_sub5_cmkDom0_pathAC_credit hLoopSub hSr i peerAddr w4 hw4
    hikp hspk hopk hkpkOt hkpkLr
  have h4arms : PhaseCreditSpec fineCostModel
      (fun e =>
        W4BinaryStageP1UntrustedEnv w4.base.rd w4.base.files w4.base.peer w4.remoteIdKey e ∨
        W4BinaryRecvPrekeyPathBWideCmkSrEnvOf SR LoopAdvEnv maxOps w4 e ∨
        W4BinaryRecvPrekeyPathAWideCmkSrEnvFixedOf SR LoopAdvEnv maxOps w4 e ∨
        W4BinaryRecvPrekeyPathCWideCmkVerNeSrEnvFixedOf SR LoopAdvEnv maxOps w4 e)
      w4CmkDom0'Cum w4CmkDom0'Live w4CmkDom0'Peak w4CmkDom0'MaxReq := by
    refine (hUB.or hAC).of_imp ?_ |>.mono
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
    rintro e (hU | hB | hA | hC)
    · exact Or.inl (Or.inl hU)
    · exact Or.inl (Or.inr hB)
    · exact Or.inr (Or.inl hA)
    · exact Or.inr (Or.inr hC)
  have hFree : PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
    PhaseCreditSpec.freeOnly fineCostModel_freeNonInc
  have hSeq : PhaseCreditSpec fineCostModel _
      w4CmkDom0'Cum w4CmkDom0'Live w4CmkDom0'Peak w4CmkDom0'MaxReq :=
    (h4arms.seq hFree).mono
      (Nat.le_of_eq (Nat.add_zero _))
      (Nat.le_of_eq (Nat.add_zero _))
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_trans (Nat.le_of_eq (Nat.add_zero _)) w4CmkDom0'_live_le_peak⟩)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩)
  unfold W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
    m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf'
  exact (hFree.or hSeq).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

/-- Stage-level `PhaseCreditSpec` on `W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf` under
`CliPqxdhInputs` + `W4BinaryRecvPrekeyDomCmk0'`. -/
theorem w4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf_phaseCreditSpec'
    {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    (hLoopSub : W4LoopAdvSub LoopAdvEnv CmkLoopAdvanceEvs)
    (hSr : ∀ F K, StatesRecvTightCreditSpec F (SR F K) 1647247 93776)
    (W : CliHooks) (i : Inputs) (peerAddr : AddrV)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (_hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (w4 : W4BinaryRecvPrekeyParamsCmk)
    (hw4 : W4BinaryRecvPrekeyDomCmk0' SR LoopAdvEnv maxOps (.recv peerAddr) i w4) :
    PhaseCreditSpec fineCostModel
      (W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf SR LoopAdvEnv maxOps w4)
      w4CmkDom0'Cum w4CmkDom0'Live w4CmkDom0'Peak w4CmkDom0'MaxReq :=
  w4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf_phaseCreditSpec'_of_dom
    hLoopSub hSr W i peerAddr hi w4 hw4

private theorem s3g_p1untr_le (a b c : Nat) : a + (b + (c + 0)) ≤ a + b + c := by omega
private theorem s3g_p2b_le (a b : Nat) : a + max 0 (0 + max 0 (b + 0)) ≤ a + b := by omega
private theorem s3g_add2_zero (a b : Nat) : a + (b + 0) ≤ a + b := by omega
private theorem s3g_add4_zero (a b c d : Nat) :
    a + (b + (c + (d + 0))) ≤ a + (b + (c + d)) := by omega
private theorem s3g_outer_zero (x : Nat) : max 0 (x + 0) ≤ x := by omega

/-- Stage-level `PhaseGroupSpec` on `W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf` under
`CliPqxdhInputs` + `W4BinaryRecvPrekeyDomCmk0'` (`maxOps`-parametric, without `parseArgs` premise). -/
theorem w4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf_phaseGroupSpec'_of_dom
    {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    (hLoopSub : W4LoopAdvSub LoopAdvEnv CmkLoopAdvanceEvs)
    (hSrG : ∀ F K, StatesRecvTightGroupSpec F (SR F K) statesRecvTightGroupS_split)
    (W : CliHooks) (i : Inputs) (peerAddr : AddrV)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (w4 : W4BinaryRecvPrekeyParamsCmk)
    (hw4 : W4BinaryRecvPrekeyDomCmk0' SR LoopAdvEnv maxOps (.recv peerAddr) i w4) :
    PhaseGroupSpec fineCostModel
      (W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf SR LoopAdvEnv maxOps w4)
      (w4CmkDom0'GrpSOf maxOps) := by
  have hw4 := dom0p_toLocalDom hw4
  obtain ⟨_, hpeer40, hfiles, hrd, hDom, hTrialsNil⟩ := hw4 peerAddr rfl
  obtain ⟨hikp, hspkCap, hopkCap, hkpkOtCap, hkpkLrCap⟩ := s3a_sub0_store_file_caps W i hi
  have hf := PhaseGroupSpec.freeOnly fineCostModel
  let R := w4.base
  let P := mkW4RecvPrekeyWideCmkSrSlotParamsOf SR LoopAdvEnv maxOps R
  have hpeerValLen : R.peer.val.name.length ≤ 40 := hpeer40
  have hAddrG := LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux.addrTextValEnv_decimal_groupSpec
    fineCostModel R.peer.val hpeerValLen
  have hGetSess := dirGet_readPlain_groups_s3b R.rd R.files
    StoresGhost.opened.sessions (CryptoVerification.SignalSession.Cli.addressText R.peer.val)
  have hGetPeers := dirGet_readPlain_groups_s3b R.rd R.files
    StoresGhost.opened.identity.peers R.peer.val.name
  have hOptDeser : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget.OptLoadDeserEnv
        CryptoVerification.SignalSession.Cli.Slots.scopeKit
        (LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.ofBytesEnv
          LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux.RecordDeserializeCancelEnv)
        (StoresGhost.opened.sessions.get R.rd R.files
          (CryptoVerification.SignalSession.Cli.addressText R.peer.val)))
      deserCancelFineGrpS := by
    unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget.OptLoadDeserEnv
    cases StoresGhost.opened.sessions.get R.rd R.files
      (CryptoVerification.SignalSession.Cli.addressText R.peer.val) with
    | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | cons b0 bsRest =>
        exact s3_phaseGroupSpec_exists fun r _ => by
          unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser.ofBytesEnv
          exact (LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget.recordDeserializeCancelEnv_fine_groupSpec
            (CryptoVerification.E2E.Record.encodeRecord r)).of_imp fun _ h => h.2
  have hLoadStep : PhaseGroupSpec fineCostModel
      (W4BinarySessLoadStepEnv R.rd R.files R.peer)
      (11056 + 51 * FineScale + deserCancelFineGrpS) :=
    (w4BoxedStoreStep_le_28_fine_groupSpec
      (by decide) (hAddrG.seq (hGetSess.seq (hOptDeser.seq hf)))).mono (by omega)
  have hTrustStep : PhaseGroupSpec fineCostModel
      (W4BinaryIdTrustStepEnv R.rd R.files R.peer w4.remoteIdKey)
      (16659 + 42 * FineScale) :=
    (w4BoxedStoreStep_le_44_fine_groupSpec (by decide) (hGetPeers.seq hf)).mono (by omega)
  have hStrClone : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Heap.RustStdAllocBudgetBridge.StringCloneEnv R.peer.name)
      (3 * FineScale) := by
    unfold LibsignalBinary.Heap.RustStdAllocBudgetBridge.StringCloneEnv
    exact (((PhaseGroupSpec.nil fineCostModel).of_imp fun _ h => h.2).or
      ((PhaseGroupSpec.rustAlloc_any fineCostModel R.peer.name.bytes.length 1).of_imp
        fun _ h => h.2)).mono (by omega)
  have hP1Ok : PhaseGroupSpec fineCostModel
      (W4BinaryStageP1OkEnv R.rd R.files R.peer w4.remoteIdKey)
      ((11056 + 51 * FineScale + deserCancelFineGrpS) + (16659 + 42 * FineScale)) :=
    hLoadStep.seq (phaseGroupSpec_optStage hTrustStep)
  have hP1Untrusted : PhaseGroupSpec fineCostModel
      (W4BinaryStageP1UntrustedEnv R.rd R.files R.peer w4.remoteIdKey)
      ((11056 + 51 * FineScale + deserCancelFineGrpS) + (16659 + 42 * FineScale) + 3 * FineScale) :=
    (hLoadStep.seq (hTrustStep.seq (hStrClone.seq hf))).mono (s3g_p1untr_le _ _ _)
  have hSaveStep : PhaseGroupSpec fineCostModel
      (W4BinaryIdSaveStepEnv R.rd R.files R.peer w4.remoteIdKey)
      (16659 + 51 * FineScale) := by
    have hSaveTail : PhaseGroupSpec fineCostModel
        (LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSaveTailEnv
          DirPutStrEnv StoresGhost.opened.identity R.peer.val w4.remoteIdKey
          (StoresGhost.opened.identity.peers.get R.rd R.files R.peer.val.name))
        (9 * FineScale) := by
      unfold LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget.cliIdentityKitSaveTailEnv
      cases StoresGhost.opened.identity.peers.get R.rd R.files R.peer.val.name with
      | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | ok _ =>
        have hpks : PhaseGroupSpec fineCostModel
            LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.PublicKeySerializeEnv
            (3 * FineScale) := PhaseGroupSpec.rustAlloc_any fineCostModel 33 1
        have hput := s3_dirPutStr_opened_groups fineCostModel
          (dir := StoresGhost.opened.identity.peers) rfl R.peer.val.name w4.remoteIdKey.serialize
        exact (hf.seq (hpks.seq hput)).mono (by omega)
    exact (w4BoxedStoreStep_le_44_fine_groupSpec (by decide) (hGetPeers.seq hSaveTail)).mono (by omega)
  have hArchSer := recordSerializeSeqFreeEnv_of_valid_fine_groupSpec_s3b hDom.outer_dom.arch_valid
  have hOut0Ser := recordSerializeSeqFreeEnv_of_valid_fine_groupSpec_s3b hDom.outer_dom.out0_valid
  have hOut1Ser : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit.SerializePrev1SeqFreeEnv
        R.G_out1 R.sess_out1 R.enc_prev1)
      serializePrev1PostBob1FineGrpS := by
    unfold LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit.SerializePrev1SeqFreeEnv
    have hcl := segCloneEnv_postBobPrev1Dom_fine_groupSpec hDom.outer_dom.out1_postBob
    have hvv := LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.vecVecClone1Events_fine_groupSpec R.enc_prev1
    have hout := PhaseGroupSpec.rustAlloc_any fineCostModel
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.encodeRecordPrev1Mem
        R.G_out1 R.sess_out1 R.enc_prev1).length 1
    exact (hcl.seq (hvv.seq (hout.seq hf))).mono (by decide)
  have hSessStore0 : PhaseGroupSpec fineCostModel
      (W4BinarySessStoreStepEnv R.peer R.g_out0 R.r_out0)
      (16659 + 12 * FineScale +
        LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.recordSerializeDomFineGrpS) := by
    have hput := s3_dirPut_opened_groups fineCostModel (dir := StoresGhost.opened.sessions) rfl
      (CryptoVerification.SignalSession.Cli.addressText R.peer.val)
      (CryptoVerification.E2E.Record.encodeRecord R.r_out0)
    exact (w4BoxedStoreStep_le_44_fine_groupSpec
      (by decide) (hAddrG.seq (hOut0Ser.seq hput))).mono (by omega)
  have hSessStore1 : PhaseGroupSpec fineCostModel
      (W4BinarySessStorePrev1StepEnv R.peer R.G_out1 R.sess_out1 R.enc_prev1)
      (16659 + 12 * FineScale + serializePrev1PostBob1FineGrpS) := by
    have hput := s3_dirPut_opened_groups fineCostModel (dir := StoresGhost.opened.sessions) rfl
      (CryptoVerification.SignalSession.Cli.addressText R.peer.val)
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.encodeRecordPrev1Mem
        R.G_out1 R.sess_out1 R.enc_prev1)
    exact (w4BoxedStoreStep_le_44_fine_groupSpec
      (by decide) (hAddrG.seq (hOut1Ser.seq hput))).mono (by omega)
  have hPromArch : PhaseGroupSpec fineCostModel
      (W4BinaryPromoteArchiveEnv R.g_arch R.r_arch)
      (LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.recordSerializeDomFineGrpS + 3 * FineScale) := by
    have h1 := LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.promoteStateArchive_groupSpec
      fineCostModel hArchSer
      (LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoundedEvs_groupSpec fineCostModel 1 192)
    have h2 : PhaseGroupSpec fineCostModel
        (LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryArchiveDirectEnv
          (CryptoVerification.E2E.Record.encodeRecord R.r_arch).length)
        (6 * FineScale) := by
      have ha : PhaseGroupSpec fineCostModel
          (fun e => ∃ n ≤ (CryptoVerification.E2E.Record.encodeRecord R.r_arch).length,
            e = LibsignalBinary.Heap.rustAllocEvents n 1)
          (3 * FineScale) :=
        s3_phaseGroupSpec_exists (P := fun n => n ≤ (CryptoVerification.E2E.Record.encodeRecord R.r_arch).length)
          (E := fun n e => e = LibsignalBinary.Heap.rustAllocEvents n 1) fun n _ =>
          PhaseGroupSpec.rustAlloc_any fineCostModel n 1
      have hb := LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoundedEvs_groupSpec fineCostModel 1 192
      exact (hf.seq (ha.seq (hb.seq hf))).mono (by unfold FineScale; omega)
    exact (h1.or h2).mono (by decide)
  have hTrials : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.IterSeqEnv
        (LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak.ArchivedTrialIterEnv
          P.DecEnv P.TrialEnv P.DropEnv) P.archivedTrials)
      0 := by
    have hnil : P.archivedTrials = [] := hTrialsNil
    rw [hnil]
    exact PhaseGroupSpec.nil fineCostModel
  have hCloneB : PhaseGroupSpec fineCostModel
      W4CloneBDomEnv LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.segCloneDomFineGrpS :=
    (s3_phaseGroupSpec_exists fun (gs : SessionGhost × Session (List (BitVec 8)))
        (hp : LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget.SessionGhostValid gs.1 gs.2 ∧
          LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.SessionCloneDom 286196 gs.2) =>
      LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.segCloneEnv_dom_fine_groupSpec hp.1 hp.2).of_imp
      fun _ ⟨G, ses, hgv, hdom, hs⟩ => ⟨(G, ses), ⟨hgv, hdom⟩, hs⟩
  have hCloneAC : PhaseGroupSpec fineCostModel
      W4CloneACDomEnv LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.segCloneFreshBobFineGrpS :=
    (s3_phaseGroupSpec_exists fun (gs : SessionGhost × Session (List (BitVec 8)))
        (hp : LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds.FreshBobCloneDom 16384 gs.1 gs.2) =>
      LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.segCloneEnv_freshBobCloneDom_fine_groupSpec hp).of_imp
      fun _ ⟨G, ses, hfb, hs⟩ => ⟨(G, ses), hfb, hs⟩
  have hTdB : PhaseGroupSpec fineCostModel P.TryDecEnv (w4cTdGrpSOf maxOps) := by
    change PhaseGroupSpec fineCostModel
      (if R.isPathB then
        m2rg_TryDecryptCliLinkedEnvOf' LoopAdvEnv maxOps R.C R.K (SR R.C.F R.K) R.td_B.a
      else fun _ => False) _
    cases hpb : R.isPathB
    · exact { groups_le := fun _ {_} h => False.elim h }
    · exact (w4c_tryDecryptCliLinkedSrEnvOf_cmk_phaseGroupSpec (maxOps := maxOps)
        (hSrG R.C.F R.K) (hDom.tdB_dom hpb)).of_imp fun _ h =>
        m2rg_tryDecryptCliLinkedEnvOf'_mono hLoopSub (Nat.le_refl maxOps) (fun _ _ _ hr => hr) h
  have hTdAC : PhaseGroupSpec fineCostModel
      (W4RecvPrekeyTryDecACCmkSrEnvOf SR LoopAdvEnv maxOps R)
      (w4cTdGrpSOf maxOps) := by
    unfold W4RecvPrekeyTryDecACCmkSrEnvOf m2rg_W4RecvPrekeyTryDecACCmkEnvOf'
    cases hpac : R.isPathAC
    · exact { groups_le := fun _ {_} h => False.elim h }
    · exact (w4c_tryDecryptCliLinkedSrEnvOf_cmk_phaseGroupSpec (maxOps := maxOps)
        (hSrG R.C.F R.K) (hDom.tdAC_dom hpac).base).of_imp fun _ h =>
        m2rg_tryDecryptCliLinkedEnvOf'_mono hLoopSub (Nat.le_refl maxOps) (fun _ _ _ hr => hr) h
  have hCurFail : PhaseGroupSpec fineCostModel P.CurTrialFailEnv (w4cTdFailGrpSOf maxOps) := by
    change PhaseGroupSpec fineCostModel
      (if R.hasCurSession then
        m2rg_W4FailedTdCancelCmkEnvOf' LoopAdvEnv maxOps R.C R.K (SR R.C.F R.K) R.fc_cur
      else fun _ => False) _
    cases hcs : R.hasCurSession
    · exact { groups_le := fun _ {_} h => False.elim h }
    · exact (w4FailedTdCancelCmkSrEnvOf_phaseGroupSpec (maxOps := maxOps)
        (hSrG R.C.F R.K) (hDom.cur_fail_dom hcs)).of_imp fun _ h => by
        rcases h with hf0 | ⟨e1, e2, rfl, h1, h2⟩
        · exact Or.inl hf0
        · exact Or.inr ⟨e1, e2, rfl,
            LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins.m2rg_tryDecryptCliLinkedFailEnvOf'_mono
              hLoopSub (Nat.le_refl maxOps) (fun _ _ _ hr => hr) h1, h2⟩
  have hCurCloneFail : PhaseGroupSpec fineCostModel
      (LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec.W4TryDecryptCloneFailWideEnv
        (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.SegCloneEnv R.G_cur R.st_cur)
        P.CurTrialFailEnv
        (· = LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit.dropClonedSessionEvents R.G_cur R.st_cur))
      (LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.segCloneDomFineGrpS +
        w4cTdFailGrpSOf maxOps + w4ErrTailWideFineGrpS) := by
    rcases hDom.outer_dom.cur_dom with hNo | ⟨ses_cur, hst_eq, hgv, hdom⟩
    · have hEmpty : PhaseGroupSpec fineCostModel
          (LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec.W4TryDecryptCloneFailWideEnv
            (LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget.SegCloneEnv R.G_cur R.st_cur)
            P.CurTrialFailEnv
            (· = LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit.dropClonedSessionEvents R.G_cur R.st_cur))
          0 :=
        { groups_le := fun _ {_} hE => by
            rcases hE with h1 | ⟨_, _, _, h1, _⟩
            · obtain ⟨_, _, _, ⟨_, e2, _, _, htf⟩, _⟩ := h1
              exact False.elim (hNo e2 htf)
            · obtain ⟨_, _, _, ⟨_, e2, _, _, htf⟩, _⟩ := h1
              exact False.elim (hNo e2 htf) }
      exact hEmpty.mono (Nat.zero_le _)
    · have hst_eq' : ses_cur.state = R.st_cur := hst_eq
      rw [← hst_eq']
      exact LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4TryDecryptCloneFailWide_fine_groupSpec
        (LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.segCloneEnv_dom_fine_groupSpec hgv hdom)
        hCurFail
        (LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.dropClonedSessionEvents_groupSpec
          fineCostModel R.G_cur ses_cur.state)
  have hSpkGetStep : PhaseGroupSpec fineCostModel
      (W4BinarySpkGetStepEnv R.rd R.files R.spkId)
      (11056 + 216 * FineScale) := by
    have hopt : PhaseGroupSpec fineCostModel
        (OptSpkDecodeEnv CliSpkDecodeEnv
          (StoresGhost.opened.signed.get R.rd R.files (keyName R.spkId)))
        (144 * FineScale) := by
      unfold OptSpkDecodeEnv
      cases hget : StoresGhost.opened.signed.get R.rd R.files (keyName R.spkId) with
      | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | ok bs =>
        cases bs with
        | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
        | cons b rest =>
          have hbs : (b :: rest).length ≤ 230 := by
            rw [hfiles, hrd] at hget; exact hspkCap R.spkId (b :: rest) hget
          exact (cliSpkDecode_groups_s3b hbs (by decide)).mono (by decide)
    exact (w4BoxedStoreStep_le_28_fine_groupSpec
      (by decide) ((decimal_groups_s3b R.spkId).seq
        ((dirGet_readPlain_groups_s3b R.rd R.files StoresGhost.opened.signed (keyName R.spkId)).seq
          (hopt.seq hf)))).mono (by omega)
  have hKpkGetStep : PhaseGroupSpec fineCostModel
      (W4BinaryKpkGetStepEnv R.rd R.files R.kpkId)
      (11056 + 894 * FineScale) := by
    have hpassOt : PhaseGroupSpec fineCostModel
        (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.KpkPassEnv
          DecimalEnv
          (fun d k => DirGetEnv PathEnv (ReadFileRuleEnv R.rd) R.rd R.files d (keyName k))
          CliSpkDecodeEnv R.rd R.files StoresGhost.opened.kyber.oneTime R.kpkId)
        (447 * FineScale) := by
      have hopt : PhaseGroupSpec fineCostModel
          (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.OptKpkDecodeEnv
            CliSpkDecodeEnv (StoresGhost.opened.kyber.oneTime.get R.rd R.files (keyName R.kpkId)))
          (375 * FineScale) := by
        unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.OptKpkDecodeEnv
        cases hget : StoresGhost.opened.kyber.oneTime.get R.rd R.files (keyName R.kpkId) with
        | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
        | ok bs =>
          cases bs with
          | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
          | cons b rest =>
            have hbs : (b :: rest).length ≤ 4900 := by
              rw [hfiles, hrd] at hget; exact hkpkOtCap R.kpkId (b :: rest) hget
            exact (cliSpkDecode_groups_s3b hbs (by decide)).mono (by decide)
      exact ((decimal_groups_s3b R.kpkId).seq
        ((dirGet_readPlain_groups_s3b R.rd R.files StoresGhost.opened.kyber.oneTime (keyName R.kpkId)).seq
          (hopt.seq hf))).mono (by omega)
    have hpassLr : PhaseGroupSpec fineCostModel
        (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.KpkPassEnv
          DecimalEnv
          (fun d k => DirGetEnv PathEnv (ReadFileRuleEnv R.rd) R.rd R.files d (keyName k))
          CliSpkDecodeEnv R.rd R.files StoresGhost.opened.kyber.lastResort R.kpkId)
        (447 * FineScale) := by
      have hopt : PhaseGroupSpec fineCostModel
          (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.OptKpkDecodeEnv
            CliSpkDecodeEnv (StoresGhost.opened.kyber.lastResort.get R.rd R.files (keyName R.kpkId)))
          (375 * FineScale) := by
        unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.OptKpkDecodeEnv
        cases hget : StoresGhost.opened.kyber.lastResort.get R.rd R.files (keyName R.kpkId) with
        | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
        | ok bs =>
          cases bs with
          | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
          | cons b rest =>
            have hbs : (b :: rest).length ≤ 4900 := by
              rw [hfiles, hrd] at hget; exact hkpkLrCap R.kpkId (b :: rest) hget
            exact (cliSpkDecode_groups_s3b hbs (by decide)).mono (by decide)
      exact ((decimal_groups_s3b R.kpkId).seq
        ((dirGet_readPlain_groups_s3b R.rd R.files StoresGhost.opened.kyber.lastResort (keyName R.kpkId)).seq
          (hopt.seq hf))).mono (by omega)
    have hpoll : PhaseGroupSpec fineCostModel
        (LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.CliKpkGetPollEnv
          DecimalEnv
          (fun d k => DirGetEnv PathEnv (ReadFileRuleEnv R.rd) R.rd R.files d (keyName k))
          CliSpkDecodeEnv R.rd R.files ⟨0#64, 0#64, 0#64, R.kpkId, StoresGhost.opened.kyber⟩)
        (894 * FineScale) := by
      unfold LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.CliKpkGetPollEnv
      dsimp only
      split
      · exact (hpassOt.seq hpassLr).mono (by omega)
      · exact hpassOt.mono (by omega)
    exact (w4BoxedStoreStep_le_28_fine_groupSpec (by decide) hpoll).mono (by omega)
  have hPkGetStep : PhaseGroupSpec fineCostModel
      (W4BinaryPkGetStepEnv R.rd R.files R.opkId)
      (11056 + 831 * FineScale) := by
    have hopt : PhaseGroupSpec fineCostModel
        (OptPkDecodeEnv CliPkDecodeEnv (StoresGhost.opened.oneTime.get R.rd R.files (keyName R.opkId)))
        (759 * FineScale) := by
      unfold OptPkDecodeEnv
      cases hget : StoresGhost.opened.oneTime.get R.rd R.files (keyName R.opkId) with
      | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | ok bs =>
        cases bs with
        | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
        | cons b rest =>
          have hbs : (b :: rest).length ≤ 125 := by
            rw [hfiles, hrd] at hget; exact hopkCap R.opkId (b :: rest) hget
          exact cliPkDecode_groups_s3b hbs
    exact (w4BoxedStoreStep_le_28_fine_groupSpec
      (by decide) ((decimal_groups_s3b R.opkId).seq
        ((dirGet_readPlain_groups_s3b R.rd R.files StoresGhost.opened.oneTime (keyName R.opkId)).seq
          (hopt.seq hf)))).mono (by omega)
  have hPkGetOpt := phaseGroupSpec_ite_nil R.hasOpk (fun _ => hPkGetStep)
  have hSelfKpStep : PhaseGroupSpec fineCostModel
      (W4BinarySelfKpStepEnv R.rd R.files)
      (11056 + 681 * FineScale) := by
    unfold W4BinarySelfKpStepEnv LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4OptBoxedStoreStepEnv
    have hikp_r : ∀ bs,
        StoresGhost.opened.identity.own.get R.rd R.files (utf8 "identity-key-pair") = .ok bs →
          bs.length ≤ 105 := by
      rw [hfiles, hrd]; exact hikp
    exact ((phaseGroupSpec_optStage (boxAllocEnv_le_28_fine_groupSpec (boxSz := 16) (by decide))).seq
      ((dirGet_readPlain_groups_s3b R.rd R.files StoresGhost.opened.identity.own
          (utf8 "identity-key-pair")).seq
        ((s3_ikpTryFrom_groups fineCostModel hikp_r).seq hf))).mono (by omega)
  have hSelfRegStep : PhaseGroupSpec fineCostModel
      (W4BinarySelfRegIdStepEnv R.rd R.files)
      (11056 + 45 * FineScale) := by
    have hmal : PhaseGroupSpec fineCostModel
        (OptRegIdMalformedEnv
          (StoresGhost.opened.identity.own.get R.rd R.files (utf8 "registration-id")))
        (3 * FineScale) := by
      unfold OptRegIdMalformedEnv
      cases StoresGhost.opened.identity.own.get R.rd R.files (utf8 "registration-id") with
      | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | ok bs =>
        dsimp only; split_ifs
        · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
        · exact PhaseGroupSpec.rustAlloc_any fineCostModel 14 1
    exact (w4BoxedStoreStep_le_28_fine_groupSpec
      (by decide) ((dirGet_readPlain_groups_s3b R.rd R.files StoresGhost.opened.identity.own
          (utf8 "registration-id")).seq (hmal.seq hf))).mono (by omega)
  have hPk33 : PhaseGroupSpec fineCostModel
      (SeqEnv (W4BoundedEvs 1 33) FreeOnlyEvs) (3 * FineScale) :=
    ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoundedEvs_groupSpec fineCostModel 1 33).seq hf).mono
      (by omega)
  have hKemKp : PhaseGroupSpec fineCostModel
      (SeqEnv LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget.KemKeyPairFromPubPrivEnv
        FreeOnlyEvs)
      (6 * FineScale) := by
    have hk : PhaseGroupSpec fineCostModel
        LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.KeyPairCalleesAuxBudget.KemKeyPairFromPubPrivEnv
        (6 * FineScale) :=
      (s3_phaseGroupSpec_append_eq fineCostModel
        (PhaseGroupSpec.rustAlloc_any fineCostModel 1568 1)
        (PhaseGroupSpec.rustAlloc_any fineCostModel 3168 1)).mono (by decide)
    exact (hk.seq hf).mono (by omega)
  have hTail21 : PhaseGroupSpec fineCostModel
      (SeqEnv (W4BoundedEvs 1 21) FreeOnlyEvs) (3 * FineScale) :=
    ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoundedEvs_groupSpec fineCostModel 1 21).seq hf).mono
      (by omega)
  have hInitBob : PhaseGroupSpec fineCostModel
      (W4BinaryInitBobWideEnv R.C.F R.x_res R.hasOpk R.x_spqr)
      (max w4PqxdhAcceptFineGrpS (18 * FineScale) +
        ((3 * FineScale * 128) + w4BobSessionBuild9FineGrpS)) := by
    have hacc1 := w4PqxdhAccept_fine_groupSpec R.x_res R.hasOpk
    have hacc2 := ((LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec.w4BoundedEvs_groupSpec
      fineCostModel 6 192).seq hf).mono (show 6 * (3 * FineScale) + 0 ≤ 18 * FineScale by omega)
    have hacc := hacc1.or hacc2
    have hspqr := LibsignalBinary.Proofs.PeakBudget.CliGroupBounds.initialStateEnv_groupSpec fineCostModel R.C.F R.x_spqr
    have hbob := phaseGroupSpec_optStage (w4BobSessionBuild9_groupSpec fineCostModel)
    exact (hacc.seq (phaseGroupSpec_optStage (hspqr.seq hbob))).mono (by decide)
  have hKpkMarkStep := kpkMarkStepFixed_groups_s3b R.rd R.files R.kpkId R.spkId w4.baseKey
  have hPkRmStep : PhaseGroupSpec fineCostModel
      (W4BinaryPkRemoveStepEnv R.rd R.files R.opkId)
      (11056 + 105 * FineScale) := by
    have htail : PhaseGroupSpec fineCostModel
        (OptPkRemoveTailEnv DecimalEnv DirPutEnv
          ⟨0#64, 0#64, 0#64, R.opkId, StoresGhost.opened.oneTime⟩
          (StoresGhost.opened.oneTime.get R.rd R.files (keyName R.opkId)))
        (33 * FineScale) := by
      unfold OptPkRemoveTailEnv
      cases StoresGhost.opened.oneTime.get R.rd R.files (keyName R.opkId) with
      | error _ => exact hf.mono (Nat.zero_le _)
      | ok bs =>
        cases bs with
        | nil => exact hf.mono (Nat.zero_le _)
        | cons _ _ =>
          exact (hf.seq ((decimal_groups_s3b R.opkId).seq
            (s3_dirPut_opened_groups fineCostModel (dir := StoresGhost.opened.oneTime) rfl
              (keyName R.opkId) []))).mono (by omega)
    exact (w4BoxedStoreStep_le_28_fine_groupSpec
      (by decide) ((decimal_groups_s3b R.opkId).seq
        ((dirGet_readPlain_groups_s3b R.rd R.files StoresGhost.opened.oneTime
            (keyName R.opkId)).seq htail))).mono (by omega)
  have hPkRmOpt := phaseGroupSpec_ite_nil R.hasOpk (fun _ => hPkRmStep)
  -- Zero-`omega` definitional stage/path group assembly
  have hP2B := (w4StageP2MatchedCheck_fine_groupSpec.seq
    (phaseGroupSpec_optStage (hf.or (hTrials.seq (hf.or (hPromArch.seq hf)))))).mono
    (s3g_p2b_le _ _)
  have hP3B := w4StageP3Wide_fine_groupSpec hCloneB hTdB
  have hP4B := ((phaseGroupSpec_optStage hSaveStep).seq
    ((phaseGroupSpec_optStage hSessStore0).seq hf)).mono (s3g_add2_zero _ _)
  have hPathB :=
    (hP1Ok.seq ((phaseGroupSpec_optStage hP2B).seq
      ((phaseGroupSpec_optStage hP3B).seq (phaseGroupSpec_optStage hP4B)))).of_imp
      fun _ (h : W4BinaryRecvPrekeyPathBWideCmkSrEnvOf SR LoopAdvEnv maxOps w4 _) => h
  have hP2A :=
    (phaseGroupSpec_optStage hPk33).seq
      ((phaseGroupSpec_optStage hSpkGetStep).seq
        ((phaseGroupSpec_optStage hKpkGetStep).seq
          ((phaseGroupSpec_optStage hKemKp).seq
            ((phaseGroupSpec_optStage hTail21).seq
              ((phaseGroupSpec_optStage hPkGetOpt).seq
                ((phaseGroupSpec_optStage hSelfKpStep).seq
                  ((phaseGroupSpec_optStage hInitBob).seq
                     ((phaseGroupSpec_optStage hSelfRegStep).seq
                      w4ErrTailWide_fine_groupSpec))))))))
  have hP3A := w4StageP3Wide_fine_groupSpec hCloneAC hTdAC
  have hP4A :=
    ((phaseGroupSpec_optStage hSaveStep).seq
      ((phaseGroupSpec_optStage hKpkMarkStep).seq
        ((phaseGroupSpec_optStage hPkRmOpt).seq
          ((phaseGroupSpec_optStage hSessStore0).seq hf)))).mono (s3g_add4_zero _ _ _ _)
  have hPathA :=
    (hP1Ok.seq ((phaseGroupSpec_optStage hP2A).seq
      ((phaseGroupSpec_optStage hP3A).seq (phaseGroupSpec_optStage hP4A)))).of_imp
      fun _ (h : W4BinaryRecvPrekeyPathAWideCmkSrEnvFixedOf SR LoopAdvEnv maxOps w4 _) => h
  have hP2C :=
    (phaseGroupSpec_optStage hCurCloneFail).seq
      ((phaseGroupSpec_optStage hTrials).seq
        ((phaseGroupSpec_optStage hPk33).seq
          ((phaseGroupSpec_optStage hSpkGetStep).seq
            ((phaseGroupSpec_optStage hKpkGetStep).seq
              ((phaseGroupSpec_optStage hKemKp).seq
                ((phaseGroupSpec_optStage hTail21).seq
                  ((phaseGroupSpec_optStage hPkGetOpt).seq
                    ((phaseGroupSpec_optStage hSelfKpStep).seq
                      ((phaseGroupSpec_optStage hInitBob).seq
                        ((phaseGroupSpec_optStage hSelfRegStep).seq
                          ((phaseGroupSpec_optStage hPromArch).seq
                            w4ErrTailWide_fine_groupSpec)))))))))))
  have hP3C :=
    (phaseGroupSpec_optStage
      (hP3A.or (hCloneAC.seq (verNeTightTopEnv_fine_groupSpec R.enc_prev1)))).of_imp
      fun _ (h : m2rg_verNePrev1P3PathCEnv' LoopAdvEnv maxOps SR w4 _) => h
  have hP4C :=
    ((phaseGroupSpec_optStage hSaveStep).seq
      ((phaseGroupSpec_optStage hKpkMarkStep).seq
        ((phaseGroupSpec_optStage hPkRmOpt).seq
          ((phaseGroupSpec_optStage hSessStore1).seq hf)))).mono (s3g_add4_zero _ _ _ _)
  have hPathC :=
    (hP1Ok.seq ((phaseGroupSpec_optStage hP2C).seq (hP3C.seq (phaseGroupSpec_optStage hP4C)))).of_imp
      fun _ (h : W4BinaryRecvPrekeyPathCWideCmkVerNeSrEnvFixedOf SR LoopAdvEnv maxOps w4 _) => h
  unfold W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
    m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf' w4CmkDom0'GrpSOf w4CmkDom0'GrpSExprOf
  exact (hf.or ((hP1Untrusted.or (hPathB.or (hPathA.or hPathC))).seq hf)).mono (s3g_outer_zero _)

/-- Stage-level `PhaseGroupSpec` on `W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf` under
`CliPqxdhInputs` + `W4BinaryRecvPrekeyDomCmk0'` (`maxOps`-parametric). -/
theorem w4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf_phaseGroupSpec'
    {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    (hLoopSub : W4LoopAdvSub LoopAdvEnv CmkLoopAdvanceEvs)
    (hSrG : ∀ F K, StatesRecvTightGroupSpec F (SR F K) statesRecvTightGroupS_split)
    (W : CliHooks) (i : Inputs) (peerAddr : AddrV)
    (hi : CliPqxdhInputs ⟨W.C, W.Q⟩ i)
    (_hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (w4 : W4BinaryRecvPrekeyParamsCmk)
    (hw4 : W4BinaryRecvPrekeyDomCmk0' SR LoopAdvEnv maxOps (.recv peerAddr) i w4) :
    PhaseGroupSpec fineCostModel
      (W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf SR LoopAdvEnv maxOps w4)
      (w4CmkDom0'GrpSOf maxOps) :=
  w4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf_phaseGroupSpec'_of_dom
    hLoopSub hSrG W i peerAddr hi w4 hw4

end StageSpecs

/-! ## `SingleSlotFineSpec` Instances, `cliDecPkCanonSlotEnvExact'` Dischargers, & `1 GiB` Checks -/

private theorem dom0p_exists_cliPqxdhInputs_same_argv_runFiles {P : PEParams} {i : Inputs}
    (hi : CliPqOrD3RecvDom P i) :
    ∃ i₀ : Inputs, CliPqxdhInputs P i₀ ∧ i₀.argv = i.argv ∧ runFiles i₀ = runFiles i := by
  rcases hi with hPq | ⟨st, ct, rc, hwf, rfl⟩
  · exact ⟨i, hPq, rfl, rfl⟩
  · exact ⟨pqRecvInputs P st [] rc, cliPqxdhInputs_pqRecvInputs_nil hwf rc,
      rfl, (runFiles_pqRecvInputs_eq_nil P st ct rc).symm⟩

private theorem dom0p_peerSpqrStateTight640_of_cliPqOrD3RecvDom {P : PEParams}
    {i : Inputs} {peerV : AddrV}
    (hi : CliPqOrD3RecvDom P i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV)) :
    PeerSpqrStateTight640 P.C.F P.Q.K (runFiles i) (addrValOf peerV) := by
  obtain ⟨i₀, hi₀, hargv, hfiles⟩ := dom0p_exists_cliPqxdhInputs_same_argv_runFiles hi
  have hparse₀ : parseArgs uuidTryParse (i₀.argv.map bytesOfString) = some (.recv peerV) := by
    rwa [hargv]
  rw [← hfiles]
  exact peerSpqrStateTight640_of_cliPqInputs_recv hi₀ hparse₀

private theorem dom0p_allFixed_eq_localFixed {P : PEParams} {i : Inputs}
    (hi : CliPqOrD3RecvDom P i)
    {SR : W4StatesRecvEnv} {maxOps : Nat} {w : W4BinaryRecvPrekeyParamsCmk}
    (hfiles : w.base.files = runFiles i) (hrd : w.base.rd = cliIo.rd)
    (htr : w.base.archivedTrials = []) :
    W4RecvPrekeyCmkDom0.W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
        SR CmkLoopAdvanceEvs maxOps w =
      W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf SR CmkLoopAdvanceEvs maxOps w := by
  rw [W4RecvPrekeyCmkDom0.w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed_of_cliPqOrD3RecvDom
    hi hfiles hrd]
  have hP2M : ∀ (T₁ T₂ : W4ArchivedTrialCmk → List AllocEvent → Prop),
      LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryStageP2MatchedWideEnv
        W4TrialDecCmkEnv T₁ W4TrialDropCmkEnv
        w.base.archivedTrials w.base.g_arch w.base.r_arch =
      LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryStageP2MatchedWideEnv
        W4TrialDecCmkEnv T₂ W4TrialDropCmkEnv
        w.base.archivedTrials w.base.g_arch w.base.r_arch := by
    intro T₁ T₂; rw [htr]; rfl
  have hP2C : ∀ Ccur (T₁ T₂ : W4ArchivedTrialCmk → List AllocEvent → Prop),
      LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryStageP2PathCWideEnv
        w.base.G_cur w.base.st_cur Ccur W4TrialDecCmkEnv T₁
        W4TrialDropCmkEnv w.base.archivedTrials w.base.g_arch w.base.r_arch w.base.hasOpk
        w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId w.base.C.F
        w.base.x_res w.base.x_spqr =
      LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs.W4BinaryStageP2PathCWideEnv
        w.base.G_cur w.base.st_cur Ccur W4TrialDecCmkEnv T₂
        W4TrialDropCmkEnv w.base.archivedTrials w.base.g_arch w.base.r_arch w.base.hasOpk
        w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId w.base.C.F
        w.base.x_res w.base.x_spqr := by
    intro Ccur T₁ T₂; rw [htr]; rfl
  unfold W4RecvPrekeyCmkDom0.W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
    W4RecvPrekeyCmkDom0.W4BinaryRecvPrekeyPathBWideCmkSrEnvOf
    W4RecvPrekeyCmkDom0.W4BinaryRecvPrekeyPathAWideCmkSrEnvFixedOf
    W4RecvPrekeyCmkDom0.W4BinaryRecvPrekeyPathCWideCmkVerNeSrEnvFixedOf
    W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
    m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf'
    m2rg_W4BinaryRecvPrekeyPathBWideCmkEnvOf'
    m2rg_W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf'
    m2rg_W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed'
    m2rg_verNePrev1P3PathCEnv'
    m2rg_verNePrev1P3PathCEnvOf'
    W4RecvPrekeyCmkDom0.mkW4RecvPrekeyWideCmkSrSlotParamsOf
    m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf'
  dsimp only
  rw [hP2M _ _, hP2C _ _ _]
  rfl

private def dom0p_dummyCliHooks (P : PEParams) : CliHooks where
  C := P.C
  Q := P.Q
  bcmp := fun a b => if a = b then 0#64 else 1#64
  bcmp_ok := fun a b _ => by
    split
    · next h => exact ⟨fun _ => h, fun _ => by decide⟩
    · next h =>
      exact ⟨fun hz => False.elim ((by decide : (1#64).setWidth 32 ≠ 0#32) hz),
        fun heq => False.elim (h heq)⟩
  utf8Err := fun _ => (0#64, 0#16)

/-- `SR`-parametric `maxOps`-parametric `SingleSlotFineSpec` for `Dom0'` (`W4BinaryRecvPrekeyDomCmk0'`). -/
def w4BinaryRecvPrekeyCmkDom0'Of_singleSlotFineSpec {P : PEParams} {c : CallV} {i : Inputs}
    (SR : W4StatesRecvEnv) (maxOps : Nat)
    (hSrCred : ∀ F K, StatesRecvTightCreditSpec F (SR F K) 1647247 93776)
    (hSrGrp : ∀ F K, StatesRecvTightGroupSpec F (SR F K) statesRecvTightGroupS_split)
    (hi : CliPqOrD3RecvDom P i) :
    SingleSlotFineSpec
      (fun evs =>
        match c with
        | .recv _ =>
          ∃ w : W4BinaryRecvPrekeyParamsCmk,
            W4BinaryRecvPrekeyDomCmk0' SR CmkLoopAdvanceEvs maxOps c i w ∧
              W4RecvPrekeyCmkDom0.W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
                SR CmkLoopAdvanceEvs maxOps w evs
        | _ => False) where
  cum := w4CmkDom0'Cum
  live := w4CmkDom0'Live
  peak := w4CmkDom0'Peak
  maxReq := w4CmkDom0'MaxReq
  grpS := w4CmkDom0'GrpSOf maxOps
  credit := by
    cases c with
    | recv peerAddr =>
      obtain ⟨i₀, hi₀, _, hfilesEq⟩ := dom0p_exists_cliPqxdhInputs_same_argv_runFiles hi
      let W := dom0p_dummyCliHooks P
      refine ⟨fun evs ⟨w, hw4, henv⟩ => ?_, fun st0 {evs} ⟨w, hw4, henv⟩ => ?_⟩
      · obtain ⟨hpv, hp40, hfiles, hrd, hd, htr⟩ := hw4 peerAddr rfl
        rw [dom0p_allFixed_eq_localFixed hi hfiles hrd htr] at henv
        have hw4₀ : W4BinaryRecvPrekeyDomCmk0'
            SR CmkLoopAdvanceEvs maxOps (.recv peerAddr) i₀ w := by
          intro p hp; cases hp
          exact ⟨hpv, hp40, hfiles.trans hfilesEq.symm, hrd, hd, htr⟩
        exact (w4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf_phaseCreditSpec'_of_dom
          (fun _ _ _ _ _ hp => hp) hSrCred W i₀ peerAddr hi₀ w hw4₀).req_align evs henv
      · obtain ⟨hpv, hp40, hfiles, hrd, hd, htr⟩ := hw4 peerAddr rfl
        rw [dom0p_allFixed_eq_localFixed hi hfiles hrd htr] at henv
        have hw4₀ : W4BinaryRecvPrekeyDomCmk0'
            SR CmkLoopAdvanceEvs maxOps (.recv peerAddr) i₀ w := by
          intro p hp; cases hp
          exact ⟨hpv, hp40, hfiles.trans hfilesEq.symm, hrd, hd, htr⟩
        exact (w4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf_phaseCreditSpec'_of_dom
          (fun _ _ _ _ _ hp => hp) hSrCred W i₀ peerAddr hi₀ w hw4₀).credit_le st0 henv
    | keygen _ _ => exact ⟨fun _ h => False.elim h, fun _ {_} h => False.elim h⟩
    | init _ _ => exact ⟨fun _ h => False.elim h, fun _ {_} h => False.elim h⟩
    | send _ => exact ⟨fun _ h => False.elim h, fun _ {_} h => False.elim h⟩
  live_le_peak := w4CmkDom0'_live_le_peak
  groups := by
    cases c with
    | recv peerAddr =>
      obtain ⟨i₀, hi₀, _, hfilesEq⟩ := dom0p_exists_cliPqxdhInputs_same_argv_runFiles hi
      let W := dom0p_dummyCliHooks P
      refine ⟨fun st0 {evs} ⟨w, hw4, henv⟩ => ?_⟩
      obtain ⟨hpv, hp40, hfiles, hrd, hd, htr⟩ := hw4 peerAddr rfl
      rw [dom0p_allFixed_eq_localFixed hi hfiles hrd htr] at henv
      have hw4₀ : W4BinaryRecvPrekeyDomCmk0'
          SR CmkLoopAdvanceEvs maxOps (.recv peerAddr) i₀ w := by
        intro p hp; cases hp
        exact ⟨hpv, hp40, hfiles.trans hfilesEq.symm, hrd, hd, htr⟩
      exact (w4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf_phaseGroupSpec'_of_dom
        (fun _ _ _ _ _ hp => hp) hSrGrp W i₀ peerAddr hi₀ w hw4₀).groups_le st0 henv
    | keygen _ _ => exact ⟨fun _ {_} h => False.elim h⟩
    | init _ _ => exact ⟨fun _ {_} h => False.elim h⟩
    | send _ => exact ⟨fun _ {_} h => False.elim h⟩

/-- Default `maxOps = 109` `SR`-parametric `SingleSlotFineSpec` for `Dom0'`. -/
def w4BinaryRecvPrekeyCmkDom0'_singleSlotFineSpec {P : PEParams} {c : CallV} {i : Inputs}
    (SR : W4StatesRecvEnv)
    (hSrCred : ∀ F K, StatesRecvTightCreditSpec F (SR F K) 1647247 93776)
    (hSrGrp : ∀ F K, StatesRecvTightGroupSpec F (SR F K) statesRecvTightGroupS_split)
    (hi : CliPqOrD3RecvDom P i) :
    SingleSlotFineSpec
      (fun evs =>
        match c with
        | .recv _ =>
          ∃ w : W4BinaryRecvPrekeyParamsCmk,
            W4BinaryRecvPrekeyDomCmk0'
              SR CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps c i w ∧
              W4RecvPrekeyCmkDom0.W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
                SR CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps w evs
        | _ => False) :=
  { w4BinaryRecvPrekeyCmkDom0'Of_singleSlotFineSpec SR w4c_defaultDecodeMaxOps hSrCred hSrGrp hi with
    grpS := w4CmkDom0'GrpS109
    groups := by
      rw [← w4CmkDom0'GrpSOf_109_eq]
      exact (w4BinaryRecvPrekeyCmkDom0'Of_singleSlotFineSpec
        SR w4c_defaultDecodeMaxOps hSrCred hSrGrp hi).groups }

theorem w4BinaryRecvPrekeyCmkDom0'_singleSlotFineSpec_caps
    {P : PEParams} {c : CallV} {i : Inputs}
    (SR : W4StatesRecvEnv)
    (hSrCred : ∀ F K, StatesRecvTightCreditSpec F (SR F K) 1647247 93776)
    (hSrGrp : ∀ F K, StatesRecvTightGroupSpec F (SR F K) statesRecvTightGroupS_split)
    (hi : CliPqOrD3RecvDom P i) :
    let S := w4BinaryRecvPrekeyCmkDom0'_singleSlotFineSpec (c := c) SR hSrCred hSrGrp hi
    S.cum = w4CmkDom0'Cum ∧
      S.live = w4CmkDom0'Live ∧
      S.peak = w4CmkDom0'Peak ∧
      S.maxReq = w4CmkDom0'MaxReq ∧
      S.grpS = w4CmkDom0'GrpS109 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Sealed `@StatesRecvProtoEnv'` `maxOps`-parametric `SingleSlotFineSpec` (`0` `SR` hypotheses). -/
def w4BinaryRecvPrekeyCmkDom0'Of_singleSlotFineSpec' {P : PEParams} {c : CallV} {i : Inputs}
    (maxOps : Nat) (hi : CliPqOrD3RecvDom P i) :
    SingleSlotFineSpec
      (fun evs =>
        match c with
        | .recv _ =>
          ∃ w : W4BinaryRecvPrekeyParamsCmk,
            W4BinaryRecvPrekeyDomCmk0'
              w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs maxOps c i w ∧
              W4RecvPrekeyCmkDom0.W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
                w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs maxOps w evs
        | _ => False) :=
  w4BinaryRecvPrekeyCmkDom0'Of_singleSlotFineSpec
    w4c_repairedStatesRecvEnvFam maxOps
    w4c_repairedStatesRecv_creditSpec w4c_repairedStatesRecv_split_groupSpec hi

/-- Sealed `@StatesRecvProtoEnv'` default `maxOps = 109` `SingleSlotFineSpec` (`0` `SR` hypotheses). -/
def w4BinaryRecvPrekeyCmkDom0'_singleSlotFineSpec' {P : PEParams} {c : CallV} {i : Inputs}
    (hi : CliPqOrD3RecvDom P i) :
    SingleSlotFineSpec
      (fun evs =>
        match c with
        | .recv _ =>
          ∃ w : W4BinaryRecvPrekeyParamsCmk,
            W4BinaryRecvPrekeyDomCmk0'
              w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps c i w ∧
              W4RecvPrekeyCmkDom0.W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
                w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps w evs
        | _ => False) :=
  w4BinaryRecvPrekeyCmkDom0'_singleSlotFineSpec
    w4c_repairedStatesRecvEnvFam
    w4c_repairedStatesRecv_creditSpec w4c_repairedStatesRecv_split_groupSpec hi

theorem w4BinaryRecvPrekeyCmkDom0'_singleSlotFineSpec'_caps
    {P : PEParams} {c : CallV} {i : Inputs} (hi : CliPqOrD3RecvDom P i) :
    let S := w4BinaryRecvPrekeyCmkDom0'_singleSlotFineSpec' (c := c) hi
    S.cum = w4CmkDom0'Cum ∧
      S.live = w4CmkDom0'Live ∧
      S.peak = w4CmkDom0'Peak ∧
      S.maxReq = w4CmkDom0'MaxReq ∧
      S.grpS = w4CmkDom0'GrpS109 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Call-Site `DecPkGhost` & `cliDecPkCanonSlotEnvExact'` Dischargers -/

/-- Direct `PhaseCreditSpec` for unguarded `realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf` on
`CliPqOrD3RecvDom`. -/
theorem realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf_phaseCreditSpec [LibsignalPlacement]
    {SR : W4StatesRecvEnv} {maxOps : Nat}
    (hSrCred : ∀ F K, StatesRecvTightCreditSpec F (SR F K) 1647247 93776)
    (hSrGrp : ∀ F K, StatesRecvTightGroupSpec F (SR F K) statesRecvTightGroupS_split)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {i : Inputs} {peerV : AddrV} {x : DecPkGhost}
    (hi : CliPqOrD3RecvDom ⟨W.C, W.Q⟩ i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV))
    (hx_peer : x.peer.val = addrValOf peerV)
    (hx_files : x.F = runFiles i)
    (hct : x.msg.message.ciphertext.length ≤ msgCapBytes) :
    PhaseCreditSpec fineCostModel
      (realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf SR CmkLoopAdvanceEvs maxOps X W x)
      w4CmkDom0'Cum w4CmkDom0'Live w4CmkDom0'Peak w4CmkDom0'MaxReq := by
  refine (w4BinaryRecvPrekeyCmkDom0'Of_singleSlotFineSpec (c := .recv peerV)
    SR maxOps hSrCred hSrGrp hi).credit.of_imp ?_
  rintro evs ⟨w4, hcs0, _, _, henv⟩
  have hcs0' : W4BinaryCallSiteDomCmk0' W.C W.Q.K x.msg.message.ciphertext.length
      (addrValOf peerV) (runFiles i) w4.base := by
    rwa [← hx_peer, ← hx_files]
  have hd := W4BinaryCallSiteDomCmk0'.toCmkDom0Of' SR CmkLoopAdvanceEvs maxOps hcs0' hparse hct
  refine ⟨w4, ?_, henv⟩
  intro p hp; cases hp
  exact ⟨hcs0'.1.eq_peerVal, hd.1.outer_dom.peer_len, hcs0'.1.eq_files, hcs0'.1.eq_rd, hd⟩

/-- Direct `PhaseGroupSpec` for unguarded `realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf` on
`CliPqOrD3RecvDom`. -/
theorem realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf_phaseGroupSpec [LibsignalPlacement]
    {SR : W4StatesRecvEnv} {maxOps : Nat}
    (hSrCred : ∀ F K, StatesRecvTightCreditSpec F (SR F K) 1647247 93776)
    (hSrGrp : ∀ F K, StatesRecvTightGroupSpec F (SR F K) statesRecvTightGroupS_split)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {i : Inputs} {peerV : AddrV} {x : DecPkGhost}
    (hi : CliPqOrD3RecvDom ⟨W.C, W.Q⟩ i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV))
    (hx_peer : x.peer.val = addrValOf peerV)
    (hx_files : x.F = runFiles i)
    (hct : x.msg.message.ciphertext.length ≤ msgCapBytes) :
    PhaseGroupSpec fineCostModel
      (realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf SR CmkLoopAdvanceEvs maxOps X W x)
      (w4CmkDom0'GrpSOf maxOps) := by
  refine (w4BinaryRecvPrekeyCmkDom0'Of_singleSlotFineSpec (c := .recv peerV)
    SR maxOps hSrCred hSrGrp hi).groups.of_imp ?_
  rintro evs ⟨w4, hcs0, _, _, henv⟩
  have hcs0' : W4BinaryCallSiteDomCmk0' W.C W.Q.K x.msg.message.ciphertext.length
      (addrValOf peerV) (runFiles i) w4.base := by
    rwa [← hx_peer, ← hx_files]
  have hd := W4BinaryCallSiteDomCmk0'.toCmkDom0Of' SR CmkLoopAdvanceEvs maxOps hcs0' hparse hct
  refine ⟨w4, ?_, henv⟩
  intro p hp; cases hp
  exact ⟨hcs0'.1.eq_peerVal, hd.1.outer_dom.peer_len, hcs0'.1.eq_files, hcs0'.1.eq_rd, hd⟩

/-- `PhaseCreditSpec` for `cliDecPkCanonSlotEnvExact'` on `CliPqOrD3RecvDom`, discharging both
`PeerSpqrStateTight640` and `SessionGetPrev0Guard`. -/
theorem cliDecPkCanonSlotEnvExact'_phaseCredit_of_cliPqOrD3RecvDom [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {i : Inputs} {peerV : AddrV} {x : DecPkGhost}
    (hi : CliPqOrD3RecvDom ⟨W.C, W.Q⟩ i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV))
    (hx_peer : x.peer.val = addrValOf peerV)
    (hx_files : x.F = runFiles i)
    (hct : x.msg.message.ciphertext.length ≤ msgCapBytes) :
    PhaseCreditSpec fineCostModel
      (cliDecPkCanonSlotEnvExact' X W x)
      fits2_zbDom0'Cum fits2_zbDom0'Live fits2_zbDom0'Peak fits2_zbDom0'MaxReq := by
  have hp640 : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val := by
    rw [hx_files, hx_peer]
    exact dom0p_peerSpqrStateTight640_of_cliPqOrD3RecvDom hi hparse
  have hprev0 : SessionGetPrev0Guard x.F x.peer.val := by
    rw [hx_files, hx_peer]
    exact sessionGetPrev0Guard_of_cliPqOrD3RecvDom hi hparse
  refine (realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf_phaseCreditSpec
    (maxOps := w4c_defaultDecodeMaxOps)
    w4c_repairedStatesRecv_creditSpec w4c_repairedStatesRecv_split_groupSpec
    X W hi hparse hx_peer hx_files hct).of_imp ?_
  intro evs hevs
  exact hevs hp640 hprev0

/-- `PhaseGroupSpec` for `cliDecPkCanonSlotEnvExact'` on `CliPqOrD3RecvDom` at
`fits2_zbDom0'GrpS109`. -/
theorem cliDecPkCanonSlotEnvExact'_groupSpec_of_cliPqOrD3RecvDom [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {i : Inputs} {peerV : AddrV} {x : DecPkGhost}
    (hi : CliPqOrD3RecvDom ⟨W.C, W.Q⟩ i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV))
    (hx_peer : x.peer.val = addrValOf peerV)
    (hx_files : x.F = runFiles i)
    (hct : x.msg.message.ciphertext.length ≤ msgCapBytes) :
    PhaseGroupSpec fineCostModel
      (cliDecPkCanonSlotEnvExact' X W x)
      fits2_zbDom0'GrpS109 := by
  have hp640 : PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val := by
    rw [hx_files, hx_peer]
    exact dom0p_peerSpqrStateTight640_of_cliPqOrD3RecvDom hi hparse
  have hprev0 : SessionGetPrev0Guard x.F x.peer.val := by
    rw [hx_files, hx_peer]
    exact sessionGetPrev0Guard_of_cliPqOrD3RecvDom hi hparse
  dsimp only [fits2_zbDom0'GrpS109]
  rw [← w4CmkDom0'GrpSOf_109_eq]
  refine (realCliDecPkBinaryWideSlotEnvCmkDom0'FixedOf_phaseGroupSpec
    (maxOps := w4c_defaultDecodeMaxOps)
    w4c_repairedStatesRecv_creditSpec w4c_repairedStatesRecv_split_groupSpec
    X W hi hparse hx_peer hx_files hct).of_imp ?_
  intro evs hevs
  exact hevs hp640 hprev0

/-- Curried `PhaseCreditSpec` discharger inhabiting `fits2_w4DecPk_phaseCredit_Stmt W
(cliDecPkCanonSlotEnvExact' X W) fits2_zbDom0'Cum fits2_zbDom0'Live fits2_zbDom0'Peak
fits2_zbDom0'MaxReq`. -/
theorem fits2_cliDecPkCanonSlotEnvExact'_phaseCredit [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
    (pm : PreKeySignalMessage)
    (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV))
    (_hin : g.i.stdin.length ≤ msgCapBytes)
    (_hc : g.c = .recv peerV)
    (_hstdin : g.i.stdin = 3#8 :: rest)
    (_hpk : pksmParse rest = some pm)
    (hct : pm.message.ciphertext.length ≤ msgCapBytes) :
    PhaseCreditSpec fineCostModel
      (cliDecPkCanonSlotEnvExact' X W (r3bDecPkGhost g meV peerV pm))
      fits2_zbDom0'Cum fits2_zbDom0'Live fits2_zbDom0'Peak fits2_zbDom0'MaxReq :=
  cliDecPkCanonSlotEnvExact'_phaseCredit_of_cliPqOrD3RecvDom
    X W (Or.inl hi_g) hp rfl rfl hct

/-- Curried `PhaseGroupSpec` discharger inhabiting `fits2_w4DecPk_groupSpec_Stmt W
(cliDecPkCanonSlotEnvExact' X W) fits2_zbDom0'GrpS109`. -/
theorem fits2_cliDecPkCanonSlotEnvExact'_groupSpec [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
    (pm : PreKeySignalMessage)
    (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
    (hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV))
    (_hin : g.i.stdin.length ≤ msgCapBytes)
    (_hc : g.c = .recv peerV)
    (_hstdin : g.i.stdin = 3#8 :: rest)
    (_hpk : pksmParse rest = some pm)
    (hct : pm.message.ciphertext.length ≤ msgCapBytes) :
    PhaseGroupSpec fineCostModel
      (cliDecPkCanonSlotEnvExact' X W (r3bDecPkGhost g meV peerV pm))
      fits2_zbDom0'GrpS109 :=
  cliDecPkCanonSlotEnvExact'_groupSpec_of_cliPqOrD3RecvDom
    X W (Or.inl hi_g) hp rfl rfl hct

/-! ### Whole-`main` `1 GiB` (`cliOneGiB`) & `2 ^ 48` VA `decide` Closures -/

/-- Definitional (`rfl`) Exact-kit `W3` (`init`), `W1` (`send`), and `W2` (`recv` whisper) slot
constants matching `CliKitEnvFitsExact.{w3InitExact*,w1EncExact*,w2DecSigExact*}`. -/
abbrev dom0p_w3InitExactCum : Nat := w3InitRealCum + 4500000
abbrev dom0p_w3InitExactLive : Nat := w3InitRealLive + 65536
abbrev dom0p_w3InitExactPeak : Nat := w3InitRealPeak + 65536
abbrev dom0p_w3InitExactMaxReq : Nat := w3InitRealMaxReq + 65536
abbrev dom0p_w3InitExactGrpS : Nat := w3InitRealGrpS + 1500 * FineScale

abbrev dom0p_w1EncExactCum : Nat := w1SendRealDcanCum + 45 * 738
abbrev dom0p_w1EncExactLive : Nat := w1SendRealDcanPeak
abbrev dom0p_w1EncExactPeak : Nat := w1SendRealDcanPeak
abbrev dom0p_w1EncExactMaxReq : Nat := w1SendRealDcanMaxReq
abbrev dom0p_w1EncExactGrpS : Nat := w1SendRealDcanGrpS + 45 * (3 * FineScale)

abbrev dom0p_w2DecSigExactCum : Nat :=
  w2RecvWhisperRealDcanCum + ((25000 + 2) * 738 + 11 * 143484) + 45 * 738
abbrev dom0p_w2DecSigExactLive : Nat := w2RecvWhisperRealDcanPeak
abbrev dom0p_w2DecSigExactPeak : Nat := w2RecvWhisperRealDcanPeak
abbrev dom0p_w2DecSigExactMaxReq : Nat := w2RecvWhisperRealDcanMaxReq
abbrev dom0p_w2DecSigExactGrpS : Nat :=
  w2RecvWhisperRealDcanGrpS + ((25000 + 2) * 16659 + 11 * (3 * FineScale)) + 45 * (3 * FineScale)

/-- Definitional (`rfl`) mirror of `ElfSlicesPqOomMainFitsReduce.mfr_slotMainFitsOneGiBOf`
(`PksmCanonSliceEnv` + `w3InitExact*`, `cliOneGiB = 1,073,741,824` B & `2 ^ 48` VA). -/
abbrev dom0p_slotMainFitsOneGiBOf
    (encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
     decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS : Nat) : Prop :=
  let runCum := cliRunBinary1MiBCustomPksmCum
    (pksmCanonSliceCum msgCapBytes) dom0p_w3InitExactCum encCum decSigCum decPkCum
  let mCum := 123250 + m3PhaseDeltaCum_tight + runCum +
    cliMaxDirtyEntries *
      (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
    m6DeltaCum
  let mPeak := cliMainTightPeakOf
    (cliRun1MiBCustomPksmLive
      (pksmCanonSliceLive msgCapBytes) dom0p_w3InitExactLive encLive decSigLive decPkLive)
    (cliRun1MiBCustomPksmPeak
      (pksmCanonSliceLive msgCapBytes) (pksmCanonSlicePeak msgCapBytes)
      dom0p_w3InitExactPeak encLive encPeak decSigPeak decPkPeak)
  let mReq := max (max (16 * 2048) 16384)
    (cliMainTightReqOf
      (cliRunBinary1MiBCustomPksmMaxReq
        (pksmCanonSliceMaxReq msgCapBytes)
        dom0p_w3InitExactMaxReq encMaxReq decSigMaxReq decPkMaxReq))
  let rGrpS := cliRunOpenedCustomPksmGrpS msgCapBytes
    (pksmCanonSliceGrpS msgCapBytes) dom0p_w3InitExactGrpS encGrpS decSigGrpS decPkGrpS
  let mGrpS := cliMainWidenedSetupFineGrpS + (rGrpS + 27 * FineScale) +
    cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale
  234 * FineScale + dom0p_w3InitExactGrpS ≤ rGrpS - 15 * FineScale ∧
  cliDecoupledRamNeed cliDefaultStaticBytes mCum mPeak mReq
    ((mGrpS + FineScale - 1) / FineScale) ≤ cliOneGiB ∧
  cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount mCum mPeak mReq
    ((mGrpS + FineScale - 1) / FineScale) ≤ 2 ^ 48

/-- Definitional (`rfl`) mirror of `D3MainEntryBudgetFitsCapDom0.d3SlotMainFitsOneGiBOf`
(`PksmTryFromWireSliceEnv` + `w3InitExact*`, `cliOneGiB = 1,073,741,824` B & `2 ^ 48` VA). -/
abbrev dom0p_d3SlotMainFitsOneGiBOf
    (encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
     decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS : Nat) : Prop :=
  let rGrpS := cliRunOpenedCustomPksmGrpS msgCapBytes
    (pksmTryFromCapDeltaGrpS msgCapBytes) dom0p_w3InitExactGrpS encGrpS decSigGrpS decPkGrpS
  let runCum := cliRunBinary1MiBCustomPksmCum
    (pksmSliceCum msgCapBytes) dom0p_w3InitExactCum encCum decSigCum decPkCum
  let mCum := 123250 + m3PhaseDeltaCum_tight + runCum +
    cliMaxDirtyEntries *
      (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
    m6DeltaCum
  let mPeak := cliMainTightPeakOf
    (cliRun1MiBCustomPksmLive
      (pksmSliceLive msgCapBytes) dom0p_w3InitExactLive encLive decSigLive decPkLive)
    (cliRun1MiBCustomPksmPeak
      (pksmSliceLive msgCapBytes) (pksmSlicePeak msgCapBytes)
      dom0p_w3InitExactPeak encLive encPeak decSigPeak decPkPeak)
  let mReq := max (max (16 * 2048) 16384)
    (cliMainTightReqOf
      (cliRunBinary1MiBCustomPksmMaxReq
        (pksmSliceMaxReq msgCapBytes)
        dom0p_w3InitExactMaxReq encMaxReq decSigMaxReq decPkMaxReq))
  let mGrpS := cliMainWidenedSetupFineGrpS + (rGrpS + 27 * FineScale) +
    cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale
  15 * FineScale ≤ rGrpS ∧
  234 * FineScale + dom0p_w3InitExactGrpS ≤ rGrpS - 15 * FineScale ∧
  cliDecoupledRamNeed cliDefaultStaticBytes mCum mPeak mReq
    ((mGrpS + FineScale - 1) / FineScale) ≤ cliOneGiB ∧
  cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount mCum mPeak mReq
    ((mGrpS + FineScale - 1) / FineScale) ≤ 2 ^ 48

/-- `Dom0'` `@83` (`PksmCanonSliceEnv`) fits within `1 GiB` RAM
(`681,919,628 B ≤ 1,073,741,824 B`) and `2 ^ 48` VA. -/
theorem fits2_zbDom0'_fits_oneGiB_83 :
    dom0p_slotMainFitsOneGiBOf
      dom0p_w1EncExactCum dom0p_w1EncExactLive dom0p_w1EncExactPeak
      dom0p_w1EncExactMaxReq dom0p_w1EncExactGrpS
      dom0p_w2DecSigExactCum dom0p_w2DecSigExactLive dom0p_w2DecSigExactPeak
      dom0p_w2DecSigExactMaxReq dom0p_w2DecSigExactGrpS
      fits2_zbDom0'Cum fits2_zbDom0'Live fits2_zbDom0'Peak
      fits2_zbDom0'MaxReq fits2_zbDom0'GrpS83 := by
  decide

/-- `Dom0'` `@109` (`PksmCanonSliceEnv`) fits within `1 GiB` RAM
(`682,181,772 B ≤ 1,073,741,824 B`, `391,560,052 B` headroom) and `2 ^ 48` VA. -/
theorem fits2_zbDom0'_fits_oneGiB_109 :
    dom0p_slotMainFitsOneGiBOf
      dom0p_w1EncExactCum dom0p_w1EncExactLive dom0p_w1EncExactPeak
      dom0p_w1EncExactMaxReq dom0p_w1EncExactGrpS
      dom0p_w2DecSigExactCum dom0p_w2DecSigExactLive dom0p_w2DecSigExactPeak
      dom0p_w2DecSigExactMaxReq dom0p_w2DecSigExactGrpS
      fits2_zbDom0'Cum fits2_zbDom0'Live fits2_zbDom0'Peak
      fits2_zbDom0'MaxReq fits2_zbDom0'GrpS109 := by
  decide

/-- `Dom0'` `@128` (`PksmCanonSliceEnv`) fits within `1 GiB` RAM
(`682,443,916 B ≤ 1,073,741,824 B`) and `2 ^ 48` VA. -/
theorem fits2_zbDom0'_fits_oneGiB_128 :
    dom0p_slotMainFitsOneGiBOf
      dom0p_w1EncExactCum dom0p_w1EncExactLive dom0p_w1EncExactPeak
      dom0p_w1EncExactMaxReq dom0p_w1EncExactGrpS
      dom0p_w2DecSigExactCum dom0p_w2DecSigExactLive dom0p_w2DecSigExactPeak
      dom0p_w2DecSigExactMaxReq dom0p_w2DecSigExactGrpS
      fits2_zbDom0'Cum fits2_zbDom0'Live fits2_zbDom0'Peak
      fits2_zbDom0'MaxReq fits2_zbDom0'GrpS128 := by
  decide

/-- `Dom0'` `@83` (`PksmTryFromWireSliceEnv`) fits within `1 GiB` RAM
(`789,021,814 B ≤ 1,073,741,824 B`) and `2 ^ 48` VA. -/
theorem d3_zbDom0'_fits_oneGiB_83 :
    dom0p_d3SlotMainFitsOneGiBOf
      dom0p_w1EncExactCum dom0p_w1EncExactLive dom0p_w1EncExactPeak
      dom0p_w1EncExactMaxReq dom0p_w1EncExactGrpS
      dom0p_w2DecSigExactCum dom0p_w2DecSigExactLive dom0p_w2DecSigExactPeak
      dom0p_w2DecSigExactMaxReq dom0p_w2DecSigExactGrpS
      fits2_zbDom0'Cum fits2_zbDom0'Live fits2_zbDom0'Peak
      fits2_zbDom0'MaxReq fits2_zbDom0'GrpS83 := by
  decide

/-- `Dom0'` `@109` (`PksmTryFromWireSliceEnv`) fits within `1 GiB` RAM
(`789,283,958 B ≤ 1,073,741,824 B`, `284,457,866 B` headroom) and `2 ^ 48` VA. -/
theorem d3_zbDom0'_fits_oneGiB_109 :
    dom0p_d3SlotMainFitsOneGiBOf
      dom0p_w1EncExactCum dom0p_w1EncExactLive dom0p_w1EncExactPeak
      dom0p_w1EncExactMaxReq dom0p_w1EncExactGrpS
      dom0p_w2DecSigExactCum dom0p_w2DecSigExactLive dom0p_w2DecSigExactPeak
      dom0p_w2DecSigExactMaxReq dom0p_w2DecSigExactGrpS
      fits2_zbDom0'Cum fits2_zbDom0'Live fits2_zbDom0'Peak
      fits2_zbDom0'MaxReq fits2_zbDom0'GrpS109 := by
  decide

/-- `Dom0'` `@128` (`PksmTryFromWireSliceEnv`) fits within `1 GiB` RAM
(`789,546,102 B ≤ 1,073,741,824 B`) and `2 ^ 48` VA. -/
theorem d3_zbDom0'_fits_oneGiB_128 :
    dom0p_d3SlotMainFitsOneGiBOf
      dom0p_w1EncExactCum dom0p_w1EncExactLive dom0p_w1EncExactPeak
      dom0p_w1EncExactMaxReq dom0p_w1EncExactGrpS
      dom0p_w2DecSigExactCum dom0p_w2DecSigExactLive dom0p_w2DecSigExactPeak
      dom0p_w2DecSigExactMaxReq dom0p_w2DecSigExactGrpS
      fits2_zbDom0'Cum fits2_zbDom0'Live fits2_zbDom0'Peak
      fits2_zbDom0'MaxReq fits2_zbDom0'GrpS128 := by
  decide

end LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0PostBob
