/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak
public import LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738
public import LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
public import LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec
public import LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# Zero-Archived-Trial (`archivedTrials = []`) `recv-prekey` Real-Slot Instance

Zero-archived-trial (`R.archivedTrials = []`) domain narrowing and closed-`Nat` `SingleSlotFineSpec`
instances for `W4RecvPrekeyRealEnv` at both baseline `(4096, 65536)` and `1 MiB` Variant (i)
`(sessionCapBytes, msgCapBytes)`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlotDom0

open CryptoGames.LibsignalSession (SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (encodeRecordPrev1Mem)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule StoresGhost keyName)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FreeOnlyEvs rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (dropClonedSessionEvents_groupSpec dropVecVecClone1Events_groupSpec
   optTailCloneEvents_groupSpec phaseGroupSpec_append_eq recordSerializeDomFineGrpS
   segCloneDomFineGrpS segCloneEnv_dom_fine_groupSpec senderChainCloneDomFineGrpS
   senderChainCloneEnv_dom_fine_groupSpec serializeSomeCancelEnv_groupSpec vecCloneEvents_groupSpec
   vecVecClone1Events_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
  (cliRecvPrekeySlotCumCap cliRecvPrekeySlotGrpSCap cliRecvPrekeySlotLiveCap
   cliRecvPrekeySlotPeakCap cliRecvPrekeySlotReqCap)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (HasFineGroupCredit PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
  (d3RecvW4ExtCum d3RecvW4ExtGrpS d3RecvW4ExtLive d3RecvW4ExtMaxReq d3RecvW4ExtPeak)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (DeallocCreditSpec PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (RecordSerializeCancelEnv dropClonedSessionEvents)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit (SerializePrev1CancelEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit
  (w2TryDecryptFailTightEnv_linked_fine_groupSpec_split_12 w2TryDecryptFailTightGroupS_split_12
   w2TryDecryptFail_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738
   w2TryDecryptSeeds12GroupS_split_12 w2TryDecryptSeedsEnv_12_linked_fine_groupSpec_split_12
   w2TryDecryptTightEnv_linked_fine_groupSpec_split_12
   w2TryDecrypt_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit (w2TryDecryptTightGroupS_split_12)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (SessionCloneDom ghostCloneValid_of_sessionGhostValid)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec (w2TryDecryptMaxReq)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak (optDeallocListEvs)
open LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738
  (w2TryDecryptGenSeeds738Cum w2TryDecryptSeeds738Cum w2TryDecrypt_genSeeds_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
  (W4BoundedEvs phaseCredit_w4BoundedEvs_small)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (W4DecryptPrekeyPathAEnv W4DecryptPrekeyPathBEnv W4DecryptPrekeyPathCEnv W4StageP2PathCCliEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers (W4StageP1UntrustedCliEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec
  (w4DecryptPrekeySplitSlot_opened_fine_phaseCredit w4DecryptPrekeySplitTightCum
   w4DecryptPrekeySplitTightLive w4DecryptPrekeySplitTightMaxReq w4DecryptPrekeySplitTightPeak)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux (FreshBobPrev1Dom)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
  (W4FailedTdCancelEnv W4FailedTdDom W4FailedTryDecryptCall W4RecvPrekeyRealDom
   W4RecvPrekeyRealEnv W4RecvPrekeyRealParams W4RecvPrekeyTryDecACEnv W4TryDecryptCall
   W4TryDecryptCallDom W4TryDecryptFailLinkedEnv W4TryDecryptPathACDom W4TryDecryptPathACEnv
   W4TryDecryptPathBEnv mkW4RecvPrekeySlotParams segCloneFreshBobFineGrpS
   serializePrev1FreshBobFineGrpS spqrRecvLinked_zeroSkip_c09a_phaseCreditSpec w4RealFailTdCum
   w4RealFailTdPeak w4RealTdACCum w4RealTdACLive w4RealTdACPeak w4RealTdBLive w4RealTdMaxReq
   w4RecvPrekeyRealCum w4RecvPrekeyRealGrpS w4RecvPrekeyRealLive w4RecvPrekeyRealMaxReq
   w4RecvPrekeyRealPeak)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot1MiB
  (W4FailedTdDomOf W4RecvPrekeyRealDomOf W4TryDecryptCallDomOf W4TryDecryptPathACDomOf
   w4FailTdPeakOf w4RecvPrekeyReal1MiB_i_Cum w4RecvPrekeyReal1MiB_i_Live
   w4RecvPrekeyReal1MiB_i_MaxReq w4RecvPrekeyReal1MiB_i_Peak w4TdACLiveOf w4TdACPeakOf
   w4TdBLiveOf w4TdMaxReqOf)
open LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec
  (archivedTrialLoop_le4_groupSpec phaseGroupSpec_ite_nil w4BoundedEvs_groupSpec
   w4ErrTailFineGrpS w4ErrTail_fine_groupSpec w4InitBobSpqrFineGrpS
   w4SmallStoreStep16FineGrpS w4SmallStoreStep16_fine_groupSpec w4SmallStoreStep32FineGrpS
   w4StageP1OkBaseFineGrpS w4StageP1OkCli_fine_groupSpec w4StageP1UntrustedBaseFineGrpS
   w4StageP1UntrustedCli_fine_groupSpec w4StageP2Matched_groupSpec w4StageP2OverBob_fine_groupSpec
   w4StageP2PathACliFineGrpS w4StageP2PathACli_fine_groupSpec w4StageP3FineGrpS
   w4StageP3_fine_groupSpec w4StageP4MatchedCli_fine_groupSpec w4StageP4PathACli_fine_groupSpec
   w4StageP4PathCCli_fine_groupSpec w4TryDecryptCloneFail_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak (W4TryDecryptCloneFailEnv)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (deserCancelFineCum deserCancelFineGrpS deserCancelFineLive deserCancelFineMaxReq
   deserCancelFinePeak recordDeserializeCancelEnv_fine_groupSpec
   recordDeserializeCancelEnv_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
  (chainCloneEvents senderChainCloneEvents)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv segCloneEvents)

/-! ## `W4RecvPrekeyRealDom0` & `W4RecvPrekeyRealDom0Of` Definitions -/

/-- `W4RecvPrekeyRealDom R ∧ R.archivedTrials = []`.
Citations:
- `LibsignalBinary/Specifications/SignalSession/PqDir.lean` l.60–72 (`DEV-C-PREV`,
  "`encodeRecordUnderExtras` writes none")
- `LibsignalBinary/Specifications/LibsignalE2E/StateXModel.lean` l.124–125 ("(no previous sessions)"). -/
def W4RecvPrekeyRealDom0 (R : W4RecvPrekeyRealParams) : Prop :=
  W4RecvPrekeyRealDom R ∧ R.archivedTrials = []

/-- Parametric `(smallFileCap, maxCt)` counterpart of `W4RecvPrekeyRealDom0` over
`W4RecvPrekeyRealDomOf`.
Citations:
- `LibsignalBinary/Specifications/SignalSession/PqDir.lean` l.60–72 (`DEV-C-PREV`,
  "`encodeRecordUnderExtras` writes none")
- `LibsignalBinary/Specifications/LibsignalE2E/StateXModel.lean` l.124–125 ("(no previous sessions)"). -/
def W4RecvPrekeyRealDom0Of (smallFileCap maxCt : Nat) (R : W4RecvPrekeyRealParams) : Prop :=
  W4RecvPrekeyRealDomOf smallFileCap maxCt R ∧ R.archivedTrials = []

abbrev W4RecvPrekeyRealDomOf0 := W4RecvPrekeyRealDom0Of

/-! ## Closed `Nat` `Dom0` Constants & Kernel `by decide` Cap Checks -/

/-- Closed-`Nat` W4 (`recv-prekey`) `Δcum` bound at `0` archived trials (`R.archivedTrials = []`). -/
def w4RecvPrekeyRealDom0Cum : Nat :=
  w4DecryptPrekeySplitTightCum 2097152 4096 0 deserCancelFineCum
    w4RealFailTdCum 0 0 9923
    w4RealFailTdCum w4RealTdACCum 4096

/-- Closed-`Nat` W4 (`recv-prekey`) `Δlive` bound at `0` archived trials (`R.archivedTrials = []`). -/
def w4RecvPrekeyRealDom0Live : Nat :=
  w4DecryptPrekeySplitTightLive 2097152 4096 0 deserCancelFineLive
    2097152 2097152 2457152 w4RealTdBLive w4RealTdACLive

/-- Closed-`Nat` W4 (`recv-prekey`) `Δpeak` bound at `0` archived trials (`R.archivedTrials = []`). -/
def w4RecvPrekeyRealDom0Peak : Nat :=
  w4DecryptPrekeySplitTightPeak 2097152 4096 0 deserCancelFineLive deserCancelFinePeak
    286196 286196 2097152 286196 2097152 16384 2097152 2457152
    w4RealFailTdPeak 0 0
    w4RealTdBLive w4RealFailTdPeak w4RealTdACLive w4RealTdACPeak

/-- Closed-`Nat` W4 (`recv-prekey`) `maxReq` bound at `0` archived trials (`R.archivedTrials = []`). -/
def w4RecvPrekeyRealDom0MaxReq : Nat :=
  w4DecryptPrekeySplitTightMaxReq 2097152 4096 0 deserCancelFineMaxReq
    286196 286196 2097152 286196 2097152 16384 2097152 2457152
    w4RealTdMaxReq 0 0 192
    w4RealTdMaxReq w4RealTdMaxReq 4096

/-- Closed-`Nat` W4 (`recv-prekey`) `grpS` bound at `0` archived trials (`R.archivedTrials = []`,
replacing `4 * (gDec + gTr)` by `0` in `gB` and `gC`). -/
def w4RecvPrekeyRealDom0GrpS : Nat :=
  let gDeser := deserCancelFineGrpS
  let gCur := w2TryDecryptFailTightGroupS_split_12
  let gPush := 3 * FineScale
  let gArchSer := recordSerializeDomFineGrpS
  let gOut0Ser := recordSerializeDomFineGrpS
  let gOut1Ser := serializePrev1FreshBobFineGrpS
  let gTdB := w2TryDecryptTightGroupS_split_12
  let gTdAC := w2TryDecryptSeeds12GroupS_split_12
  let gU := w4StageP1UntrustedBaseFineGrpS + gDeser
  let gB := (w4StageP1OkBaseFineGrpS + gDeser) +
    (0 + gArchSer + gPush) +
    w4StageP3FineGrpS gTdB +
    (w4SmallStoreStep32FineGrpS + (16659 + (6 * FineScale + gOut0Ser)))
  let gA := (w4StageP1OkBaseFineGrpS + gDeser) +
    w4StageP2PathACliFineGrpS +
    w4StageP3FineGrpS gTdAC +
    (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
      (16659 + (6 * FineScale + gOut0Ser)))
  let gC := (w4StageP1OkBaseFineGrpS + gDeser) +
    ((segCloneDomFineGrpS + w4ErrTailFineGrpS + 5 * w4SmallStoreStep16FineGrpS +
        gArchSer + w4InitBobSpqrFineGrpS + w4ErrTailFineGrpS) +
      gCur + 0 + gPush) +
    w4StageP3FineGrpS gTdAC +
    (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
      (16659 + (6 * FineScale + gOut1Ser)))
  max (max gU gB) (max gA gC)

/-- All 5 `cliRecvPrekeySlot*Cap` inequalities and `live ≤ peak` hold for `w4RecvPrekeyRealDom0*`
on closed `Nat`s by `decide`. -/
theorem w4RecvPrekeyRealDom0_caps_le :
    w4RecvPrekeyRealDom0Live ≤ w4RecvPrekeyRealDom0Peak ∧
    w4RecvPrekeyRealDom0Cum ≤ cliRecvPrekeySlotCumCap ∧
    w4RecvPrekeyRealDom0Live ≤ cliRecvPrekeySlotLiveCap ∧
    w4RecvPrekeyRealDom0Peak ≤ cliRecvPrekeySlotPeakCap ∧
    w4RecvPrekeyRealDom0MaxReq ≤ cliRecvPrekeySlotReqCap ∧
    w4RecvPrekeyRealDom0GrpS ≤ cliRecvPrekeySlotGrpSCap :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Monotonicity check (`Dom0 ≤ Real` across all 5 coordinates) by plain kernel `decide`. -/
theorem w4RecvPrekeyRealDom0_le_real :
    w4RecvPrekeyRealDom0Cum ≤ w4RecvPrekeyRealCum ∧
    w4RecvPrekeyRealDom0Live ≤ w4RecvPrekeyRealLive ∧
    w4RecvPrekeyRealDom0Peak ≤ w4RecvPrekeyRealPeak ∧
    w4RecvPrekeyRealDom0MaxReq ≤ w4RecvPrekeyRealMaxReq ∧
    w4RecvPrekeyRealDom0GrpS ≤ w4RecvPrekeyRealGrpS :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- Parametric uniform-`smallFileCap` `Δcum` at `0` archived trials. -/
def w4RecvPrekeyRealDom0CumOf (smallFileCap : Nat) : Nat :=
  w4DecryptPrekeySplitTightCum 2097152 smallFileCap 0 deserCancelFineCum
    w4RealFailTdCum 0 0 9923
    w4RealFailTdCum w4RealTdACCum 4096

/-- Parametric uniform-`smallFileCap` `Δlive` at `0` archived trials. -/
def w4RecvPrekeyRealDom0LiveOf (smallFileCap maxCt : Nat) : Nat :=
  w4DecryptPrekeySplitTightLive 2097152 smallFileCap 0 deserCancelFineLive
    2097152 2097152 2457152 (w4TdBLiveOf maxCt) (w4TdACLiveOf maxCt)

/-- Parametric uniform-`smallFileCap` `Δpeak` at `0` archived trials. -/
def w4RecvPrekeyRealDom0PeakOf (smallFileCap maxCt : Nat) : Nat :=
  w4DecryptPrekeySplitTightPeak 2097152 smallFileCap 0 deserCancelFineLive deserCancelFinePeak
    286196 286196 2097152 286196 2097152 16384 2097152 2457152
    (w4FailTdPeakOf maxCt) 0 0
    (w4TdBLiveOf maxCt) (w4FailTdPeakOf maxCt) (w4TdACLiveOf maxCt) (w4TdACPeakOf maxCt)

/-- Parametric uniform-`smallFileCap` `maxReq` at `0` archived trials. -/
def w4RecvPrekeyRealDom0MaxReqOf (smallFileCap maxCt : Nat) : Nat :=
  w4DecryptPrekeySplitTightMaxReq 2097152 smallFileCap 0 deserCancelFineMaxReq
    286196 286196 2097152 286196 2097152 16384 2097152 2457152
    (w4TdMaxReqOf maxCt) 0 0 192
    (w4TdMaxReqOf maxCt) (w4TdMaxReqOf maxCt) 4096

/-- Variant (i) `Dom0` closed constants at `(sessionCapBytes, msgCapBytes)`. -/
def w4RecvPrekeyReal1MiB_i_Dom0Cum : Nat := w4RecvPrekeyRealDom0CumOf sessionCapBytes
def w4RecvPrekeyReal1MiB_i_Dom0Live : Nat := w4RecvPrekeyRealDom0LiveOf sessionCapBytes msgCapBytes
def w4RecvPrekeyReal1MiB_i_Dom0Peak : Nat := w4RecvPrekeyRealDom0PeakOf sessionCapBytes msgCapBytes
def w4RecvPrekeyReal1MiB_i_Dom0MaxReq : Nat := w4RecvPrekeyRealDom0MaxReqOf sessionCapBytes msgCapBytes
def w4RecvPrekeyReal1MiB_i_Dom0GrpS : Nat := w4RecvPrekeyRealDom0GrpS

/-- Variant (i) `Dom0` cap check against `w4RecvPrekeyReal1MiB_i_*` and `d3RecvW4Ext*` by `decide`. -/
theorem w4RecvPrekeyReal1MiB_i_Dom0_caps_le :
    w4RecvPrekeyReal1MiB_i_Dom0Live ≤ w4RecvPrekeyReal1MiB_i_Dom0Peak ∧
    w4RecvPrekeyReal1MiB_i_Dom0Cum ≤ w4RecvPrekeyReal1MiB_i_Cum ∧
    w4RecvPrekeyReal1MiB_i_Dom0Live ≤ w4RecvPrekeyReal1MiB_i_Live ∧
    w4RecvPrekeyReal1MiB_i_Dom0Peak ≤ w4RecvPrekeyReal1MiB_i_Peak ∧
    w4RecvPrekeyReal1MiB_i_Dom0MaxReq ≤ w4RecvPrekeyReal1MiB_i_MaxReq ∧
    w4RecvPrekeyReal1MiB_i_Dom0GrpS ≤ w4RecvPrekeyRealGrpS ∧
    w4RecvPrekeyReal1MiB_i_Dom0Cum ≤ d3RecvW4ExtCum ∧
    w4RecvPrekeyReal1MiB_i_Dom0Live ≤ d3RecvW4ExtLive ∧
    w4RecvPrekeyReal1MiB_i_Dom0Peak ≤ d3RecvW4ExtPeak ∧
    w4RecvPrekeyReal1MiB_i_Dom0MaxReq ≤ d3RecvW4ExtMaxReq ∧
    w4RecvPrekeyReal1MiB_i_Dom0GrpS ≤ d3RecvW4ExtGrpS :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, by decide, by decide, by decide⟩

/-! ## Private Monotonicity, Credit, & Group Helpers -/

private theorem z0_dhSmall_of_le_5 {dhCap : Nat} (h : dhCap ≤ 5) :
    104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
  rw [fineCostModel_smallMaxReq_eq]
  match dhCap, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => decide

private theorem z0_w2Seeds738Cum_le_5 {dhCap : Nat} (needGrow : Bool) (h : dhCap ≤ 5) :
    w2TryDecryptSeeds738Cum dhCap needGrow 12 23313687 ≤ w4RealFailTdCum := by
  unfold w4RealFailTdCum
  match dhCap, needGrow, h with
  | 0, false, _ | 0, true, _ | 1, false, _ | 1, true, _
  | 2, false, _ | 2, true, _ | 3, false, _ | 3, true, _
  | 4, false, _ | 4, true, _ | 5, false, _ | 5, true, _ => decide

private theorem z0_w2GenSeeds12Cum_le_5 {dhCap : Nat} (needGrow : Bool) (h : dhCap ≤ 5) :
    w2TryDecryptGenSeeds738Cum 12 dhCap needGrow 12 3897904 ≤ w4RealTdACCum := by
  unfold w4RealTdACCum
  match dhCap, needGrow, h with
  | 0, false, _ | 0, true, _ | 1, false, _ | 1, true, _
  | 2, false, _ | 2, true, _ | 3, false, _ | 3, true, _
  | 4, false, _ | 4, true, _ | 5, false, _ | 5, true, _ => decide

private theorem z0_w2MaxReq_le_5 {dhCap : Nat} (h : dhCap ≤ 5) :
    w2TryDecryptMaxReq dhCap 2000 302480 65536 ≤ w4RealTdMaxReq := by
  unfold w4RealTdMaxReq
  match dhCap, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => decide

private theorem z0_w2MaxReqOf_le_5 {dhCap maxCt : Nat} (h : dhCap ≤ 5) :
    w2TryDecryptMaxReq dhCap 2000 302480 maxCt ≤ w4TdMaxReqOf maxCt := by
  unfold w4TdMaxReqOf w2TryDecryptMaxReq
  have h104 : max 416 (104 * (2 * dhCap)) ≤ max 416 (104 * (2 * 5)) := by
    match dhCap, h with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => decide
  exact Nat.max_le.mpr
    ⟨Nat.le_max_left _ _,
     Nat.le_trans
       (Nat.max_le.mpr
         ⟨Nat.le_trans h104 (Nat.le_max_left _ _),
          Nat.le_max_right _ _⟩)
       (Nat.le_max_right _ _)⟩

private theorem z0_deallocCreditSpec_mono_le {M : AllocCostModel} [HasFineReallocCredit M]
    {E : List AllocEvent → Prop} {d₁ d₂ : Nat}
    (h : DeallocCreditSpec M E d₂) (hd : d₁ ≤ d₂) :
    DeallocCreditSpec M E d₁ where
  req_align := h.req_align
  credit_sub st0 {_} hE := by
    obtain ⟨hc, hl, hp⟩ := h.credit_sub st0 hE
    exact ⟨hc, Nat.le_trans hl (Nat.sub_le_sub_left hd _), hp⟩

private theorem z0_optDeallocListEvs_freeOnly (pairs : List (Nat × Nat)) :
    FreeOnlyEvs (optDeallocListEvs pairs) := by
  induction pairs with
  | nil => exact fun _ h => nomatch h
  | cons p rest ih =>
    rcases p with ⟨req, al⟩
    intro ev hev
    simp only [optDeallocListEvs, List.mem_append] at hev
    rcases hev with he | he
    · split at he
      · nomatch he
      · unfold rustDeallocEvents at he
        rw [List.mem_singleton] at he
        exact ⟨al, req, he⟩
    · exact ih ev he

private theorem z0_w4TryDecryptPathB_phaseCredit
    {F : ShaCompress} {K : MlKem} {td : W4TryDecryptCall F}
    (hDom : W4TryDecryptCallDom F K td) :
    PhaseCreditSpec fineCostModel (W4TryDecryptPathBEnv F K td)
      w4RealFailTdCum w4RealTdBLive w4RealFailTdPeak w4RealTdMaxReq := by
  have hBase := w2TryDecrypt_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738 F K
    (needGrow := td.needGrow) (withAddr := td.withAddr) (errAlloc := td.errAlloc)
    td.stBytes td.w.pre_pb td.w.vn td.w.pb td.w.st0 td.w.sckaMsg td.w.v
    td.w.xInit td.w.xNew td.w.xAdd td.w.xRk td.w.xSInto td.w.xCInto
    (z0_dhSmall_of_le_5 hDom.dh_le) hDom.caps_len hDom.chain_le hDom.top_tight hDom.ct_le
  exact hBase.mono
    (z0_w2Seeds738Cum_le_5 td.needGrow hDom.dh_le)
    (Nat.le_refl _) (Nat.le_refl _) (z0_w2MaxReq_le_5 hDom.dh_le)

private theorem z0_w4TryDecryptPathAC_phaseCredit
    {F : ShaCompress} {K : MlKem} {td : W4TryDecryptCall F}
    (hDom : W4TryDecryptPathACDom F K td) :
    PhaseCreditSpec fineCostModel (W4TryDecryptPathACEnv F K td)
      w4RealTdACCum w4RealTdACLive w4RealTdACPeak w4RealTdMaxReq := by
  have hBase := w2TryDecrypt_genSeeds_fine_phaseCreditSpec (maxSeeds := 12)
    (needGrow := td.needGrow) (withAddr := td.withAddr) (errAlloc := td.errAlloc)
    (z0_dhSmall_of_le_5 hDom.base.dh_le) hDom.base.caps_len hDom.base.chain_le
    (spqrRecvLinked_zeroSkip_c09a_phaseCreditSpec F K td.stBytes td.w
      hDom.base.top_tight hDom.zero_skip)
    hDom.base.ct_le
  exact hBase.mono
    (z0_w2GenSeeds12Cum_le_5 td.needGrow hDom.base.dh_le)
    (Nat.le_refl _) (Nat.le_refl _) (z0_w2MaxReq_le_5 hDom.base.dh_le)

private theorem z0_w4FailedTdCancel_phaseCredit
    {F : ShaCompress} {K : MlKem} {fc : W4FailedTryDecryptCall F}
    (hDom : W4FailedTdDom F K fc) :
    PhaseCreditSpec fineCostModel (W4FailedTdCancelEnv F K fc)
      w4RealFailTdCum 0 w4RealFailTdPeak w4RealTdMaxReq := by
  have hTd0 : PhaseCreditSpec fineCostModel (W4TryDecryptFailLinkedEnv F K fc.td) _ _ _ _ :=
    w2TryDecryptFail_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738 F K
      (needGrow := fc.td.needGrow) (withAddr := fc.td.withAddr) (errAlloc := fc.td.errAlloc)
      fc.td.stBytes fc.td.w.pre_pb fc.td.w.vn fc.td.w.pb fc.td.w.st0 fc.td.w.sckaMsg fc.td.w.v
      fc.td.w.xInit fc.td.w.xNew fc.td.w.xAdd fc.td.w.xRk fc.td.w.xSInto fc.td.w.xCInto
      (z0_dhSmall_of_le_5 hDom.td_dom.dh_le) hDom.td_dom.caps_len hDom.td_dom.chain_le
      hDom.td_dom.top_tight hDom.td_dom.ct_le
  have hTd := hTd0.mono
    (z0_w2Seeds738Cum_le_5 fc.td.needGrow hDom.td_dom.dh_le)
    (Nat.le_of_eq (Nat.zero_add _).symm)
    (Nat.le_refl _) (z0_w2MaxReq_le_5 hDom.td_dom.dh_le)
  have hDrop := z0_deallocCreditSpec_mono_le
    (LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak.DeallocCreditSpec.optDeallocList
      fineCostModel fc.failDropPairs hDom.align_le)
    hDom.cancel_live
  have hCancel := hTd.concat_dealloc_cancel hDrop
  exact ((PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).or hCancel).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem z0_w4TryDecryptPathBOf_phaseCredit {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {td : W4TryDecryptCall F}
    (hDom : W4TryDecryptCallDomOf F K maxCt td) :
    PhaseCreditSpec fineCostModel (W4TryDecryptPathBEnv F K td)
      w4RealFailTdCum (w4TdBLiveOf maxCt) (w4FailTdPeakOf maxCt) (w4TdMaxReqOf maxCt) := by
  have hBase := w2TryDecrypt_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738 F K
    (needGrow := td.needGrow) (withAddr := td.withAddr) (errAlloc := td.errAlloc)
    td.stBytes td.w.pre_pb td.w.vn td.w.pb td.w.st0 td.w.sckaMsg td.w.v
    td.w.xInit td.w.xNew td.w.xAdd td.w.xRk td.w.xSInto td.w.xCInto
    (z0_dhSmall_of_le_5 hDom.dh_le) hDom.caps_len hDom.chain_le hDom.top_tight hDom.ct_le
  exact hBase.mono
    (z0_w2Seeds738Cum_le_5 td.needGrow hDom.dh_le)
    (Nat.le_refl _) (Nat.le_refl _) (z0_w2MaxReqOf_le_5 hDom.dh_le)

private theorem z0_w4TryDecryptPathACOf_phaseCredit {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {td : W4TryDecryptCall F}
    (hDom : W4TryDecryptPathACDomOf F K maxCt td) :
    PhaseCreditSpec fineCostModel (W4TryDecryptPathACEnv F K td)
      w4RealTdACCum (w4TdACLiveOf maxCt) (w4TdACPeakOf maxCt) (w4TdMaxReqOf maxCt) := by
  have hBase := w2TryDecrypt_genSeeds_fine_phaseCreditSpec (maxSeeds := 12)
    (needGrow := td.needGrow) (withAddr := td.withAddr) (errAlloc := td.errAlloc)
    (z0_dhSmall_of_le_5 hDom.base.dh_le) hDom.base.caps_len hDom.base.chain_le
    (spqrRecvLinked_zeroSkip_c09a_phaseCreditSpec F K td.stBytes td.w
      hDom.base.top_tight hDom.zero_skip)
    hDom.base.ct_le
  exact hBase.mono
    (z0_w2GenSeeds12Cum_le_5 td.needGrow hDom.base.dh_le)
    (Nat.le_refl _) (Nat.le_refl _) (z0_w2MaxReqOf_le_5 hDom.base.dh_le)

private theorem z0_w4FailedTdCancelOf_phaseCredit {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {fc : W4FailedTryDecryptCall F}
    (hDom : W4FailedTdDomOf F K maxCt fc) :
    PhaseCreditSpec fineCostModel (W4FailedTdCancelEnv F K fc)
      w4RealFailTdCum 0 (w4FailTdPeakOf maxCt) (w4TdMaxReqOf maxCt) := by
  have hTd0 : PhaseCreditSpec fineCostModel (W4TryDecryptFailLinkedEnv F K fc.td) _ _ _ _ :=
    w2TryDecryptFail_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738 F K
      (needGrow := fc.td.needGrow) (withAddr := fc.td.withAddr) (errAlloc := fc.td.errAlloc)
      fc.td.stBytes fc.td.w.pre_pb fc.td.w.vn fc.td.w.pb fc.td.w.st0 fc.td.w.sckaMsg fc.td.w.v
      fc.td.w.xInit fc.td.w.xNew fc.td.w.xAdd fc.td.w.xRk fc.td.w.xSInto fc.td.w.xCInto
      (z0_dhSmall_of_le_5 hDom.td_dom.dh_le) hDom.td_dom.caps_len hDom.td_dom.chain_le
      hDom.td_dom.top_tight hDom.td_dom.ct_le
  have hTd := hTd0.mono
    (z0_w2Seeds738Cum_le_5 fc.td.needGrow hDom.td_dom.dh_le)
    (Nat.le_of_eq (Nat.zero_add _).symm)
    (Nat.le_refl _) (z0_w2MaxReqOf_le_5 hDom.td_dom.dh_le)
  have hDrop := z0_deallocCreditSpec_mono_le
    (LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak.DeallocCreditSpec.optDeallocList
      fineCostModel fc.failDropPairs hDom.align_le)
    hDom.cancel_live
  have hCancel := hTd.concat_dealloc_cancel hDrop
  exact ((PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).or hCancel).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem z0_segCloneEnv_freshBob_fine_groupSpec
    {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hbob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    PhaseGroupSpec fineCostModel (SegCloneEnv G ses.state) segCloneFreshBobFineGrpS := by
  have hgv := ghostCloneValid_of_sessionGhostValid hbob.gv
  have hloc := vecCloneEvents_groupSpec fineCostModel G.localIk
  have hrem := vecCloneEvents_groupSpec fineCostModel G.remoteIk
  have hroot := PhaseGroupSpec.rustAlloc_any fineCostModel 32 1
  have hsnd : PhaseGroupSpec fineCostModel
      (· = match G.sender, ses.state.senderChain with
           | some gs, some sc => senderChainCloneEvents gs sc
           | _, _ => [])
      senderChainCloneDomFineGrpS := by
    rcases hgv.sender_ok with ⟨hn1, hn2⟩ | ⟨gs, sc, hgs, hsc, _hsrk, _hpriv⟩
    · rw [hn1, hn2]
      exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · rw [hgs, hsc]
      exact senderChainCloneEnv_dom_fine_groupSpec sc (by omega) (by omega)
  have hrc : PhaseGroupSpec fineCostModel
      (· = if ses.state.receiverChains = [] then []
           else rustAllocEvents (104 * ses.state.receiverChains.length) 8 ++
             (G.chains.zip ses.state.receiverChains).flatMap chainCloneEvents)
      0 := by
    rw [hbob.rc_nil]
    simp only [↓reduceIte]
    exact PhaseGroupSpec.nil fineCostModel
  have hpend := optTailCloneEvents_groupSpec fineCostModel G.pending
  have hkyb := optTailCloneEvents_groupSpec fineCostModel G.kyber
  have halice := vecCloneEvents_groupSpec fineCostModel G.alice
  have hpq : PhaseGroupSpec fineCostModel
      (· = if ses.state.pqRatchetState.length = 0 then []
           else rustAllocEvents ses.state.pqRatchetState.length 1)
      (3 * FineScale) := by
    split
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact PhaseGroupSpec.rustAlloc_any fineCostModel ses.state.pqRatchetState.length 1
  have s1 := phaseGroupSpec_append_eq fineCostModel hloc hrem
  have s2 := phaseGroupSpec_append_eq fineCostModel s1 hroot
  have s3 := phaseGroupSpec_append_eq fineCostModel s2 hsnd
  have s4 := phaseGroupSpec_append_eq fineCostModel s3 hrc
  have s5 := phaseGroupSpec_append_eq fineCostModel s4 hpend
  have s6 := phaseGroupSpec_append_eq fineCostModel s5 hkyb
  have s7 := phaseGroupSpec_append_eq fineCostModel s6 halice
  have s8 := phaseGroupSpec_append_eq fineCostModel s7 hpq
  unfold SegCloneEnv segCloneEvents segCloneFreshBobFineGrpS
  exact s8.mono (by decide)

private theorem z0_serializePrev1CancelEnv_freshBob_fine_groupSpec
    {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hbob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    PhaseGroupSpec fineCostModel (SerializePrev1CancelEnv G ses enc)
      serializePrev1FreshBobFineGrpS := by
  unfold SerializePrev1CancelEnv serializePrev1FreshBobFineGrpS
  have hcl := z0_segCloneEnv_freshBob_fine_groupSpec hbob
  have hvv := vecVecClone1Events_fine_groupSpec enc
  have hout := PhaseGroupSpec.rustAlloc_any fineCostModel (encodeRecordPrev1Mem G ses enc).length 1
  have hd1 := dropClonedSessionEvents_groupSpec fineCostModel G ses.state
  have hd2 := dropVecVecClone1Events_groupSpec fineCostModel enc
  exact (((hcl.concat hvv).concat hout).concat (hd1.concat hd2)).mono (by decide)

private theorem z0_recordSerializeCancelEnv_of_valid_fine_groupSpec {pqCap : Nat}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hValid : ∀ G ses, g.cur = some G → r.currentSession = some ses →
      SessionGhostValid G ses ∧ SessionCloneDom pqCap ses) :
    PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv g r) recordSerializeDomFineGrpS := by
  unfold RecordSerializeCancelEnv recordSerializeDomFineGrpS
  cases hg : g.cur <;> cases hr : r.currentSession
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · rename_i G ses
    obtain ⟨hgv, hdom⟩ := hValid G ses hg hr
    exact serializeSomeCancelEnv_groupSpec fineCostModel (segCloneEnv_dom_fine_groupSpec hgv hdom)

private theorem z0_w4FailedTdCancel_fine_groupSpec
    {F : ShaCompress} {K : MlKem} {fc : W4FailedTryDecryptCall F}
    (hDom : W4FailedTdDom F K fc) :
    PhaseGroupSpec fineCostModel (W4FailedTdCancelEnv F K fc)
      w2TryDecryptFailTightGroupS_split_12 := by
  have hFail := w2TryDecryptFailTightEnv_linked_fine_groupSpec_split_12 F K
    fc.td.dhCap fc.td.needGrow fc.td.withAddr fc.td.errAlloc fc.td.ctLen
    fc.td.stBytes fc.td.w.pre_pb fc.td.w.vn fc.td.w.pb fc.td.w.st0 fc.td.w.sckaMsg fc.td.w.v
    fc.td.w.xInit fc.td.w.xNew fc.td.w.xAdd fc.td.w.xRk fc.td.w.xSInto fc.td.w.xCInto
    hDom.td_dom.caps_len hDom.td_dom.top_tight
  have hDrop : PhaseGroupSpec fineCostModel (· = optDeallocListEvs fc.failDropPairs) 0 :=
    (PhaseGroupSpec.freeOnly fineCostModel).of_imp fun _ h => by
      subst h
      exact z0_optDeallocListEvs_freeOnly fc.failDropPairs
  have hCat := (hFail.concat hDrop).mono (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hCat).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem z0_w4FailedTdCancelOf_fine_groupSpec {maxCt : Nat}
    {F : ShaCompress} {K : MlKem} {fc : W4FailedTryDecryptCall F}
    (hDom : W4FailedTdDomOf F K maxCt fc) :
    PhaseGroupSpec fineCostModel (W4FailedTdCancelEnv F K fc)
      w2TryDecryptFailTightGroupS_split_12 := by
  have hFail := w2TryDecryptFailTightEnv_linked_fine_groupSpec_split_12 F K
    fc.td.dhCap fc.td.needGrow fc.td.withAddr fc.td.errAlloc fc.td.ctLen
    fc.td.stBytes fc.td.w.pre_pb fc.td.w.vn fc.td.w.pb fc.td.w.st0 fc.td.w.sckaMsg fc.td.w.v
    fc.td.w.xInit fc.td.w.xNew fc.td.w.xAdd fc.td.w.xRk fc.td.w.xSInto fc.td.w.xCInto
    hDom.td_dom.caps_len hDom.td_dom.top_tight
  have hDrop : PhaseGroupSpec fineCostModel (· = optDeallocListEvs fc.failDropPairs) 0 :=
    (PhaseGroupSpec.freeOnly fineCostModel).of_imp fun _ h => by
      subst h
      exact z0_optDeallocListEvs_freeOnly fc.failDropPairs
  have hCat := (hFail.concat hDrop).mono (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hCat).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem z0_p2c_grp_reassoc (gCl gCur gErr gLoop s16 gSer gPush gBob : Nat) :
    (gCl + gCur + gErr) +
      (gLoop + (s16 + (s16 + (s16 + (s16 + ((gSer + gPush + gBob) + (s16 + gErr))))))) ≤
      (gCl + gErr + 5 * s16 + gSer + gBob + gErr) + gCur + gLoop + gPush := by
  omega

private theorem z0_four_stages_grp_reassoc (a b c d : Nat) :
    a + (b + (c + d)) ≤ a + b + c + d := by
  omega

private theorem z0_w4StageP2PathCCli_curDom_fine_groupSpec {α : Type} {pqCap : Nat}
    {G_cur : SessionGhost} {st_cur : SessionState (List (BitVec 8))}
    {CurTrialFailEnv : List AllocEvent → Prop}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop} {xs : List α}
    {g_arch : RecordGhost} {r_arch : SessionRecord (List (BitVec 8))}
    {VecPushEnv : List AllocEvent → Prop}
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (spkDir kpkDir opkDir ownDir : DirGhost)
    (spkId kpkId opkId : BitVec 32)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    {g_cur g_dec g_tr g_archSer g_push : Nat}
    (hCurDom : (∀ evs, ¬ CurTrialFailEnv evs) ∨
      ∃ ses_cur : Session (List (BitVec 8)),
        ses_cur.state = st_cur ∧ SessionGhostValid G_cur ses_cur ∧
          SessionCloneDom pqCap ses_cur)
    (hCur : PhaseGroupSpec fineCostModel CurTrialFailEnv g_cur)
    (hlen4 : xs.length ≤ 4)
    (hDec : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DecEnv x) g_dec)
    (hTr : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DropEnv x) 0)
    (hArchSer : PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv g_arch r_arch) g_archSer)
    (hPush : PhaseGroupSpec fineCostModel VecPushEnv g_push) :
    PhaseGroupSpec fineCostModel
      (W4StageP2PathCCliEnv G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
        g_arch r_arch VecPushEnv hasOpk rd files spkDir kpkDir opkDir ownDir
        spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr)
      ((segCloneDomFineGrpS + w4ErrTailFineGrpS + 5 * w4SmallStoreStep16FineGrpS +
          g_archSer + w4InitBobSpqrFineGrpS + w4ErrTailFineGrpS) +
        g_cur + 4 * (g_dec + g_tr) + g_push) := by
  have hE1 : PhaseGroupSpec fineCostModel
      (fun e1 => FreeOnlyEvs e1 ∨
        W4TryDecryptCloneFailEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
          (· = dropClonedSessionEvents G_cur st_cur) e1)
      (segCloneDomFineGrpS + g_cur + w4ErrTailFineGrpS) := by
    rcases hCurDom with hNo | ⟨ses_cur, hst_eq, hgv, hdom⟩
    · have hEmpty : PhaseGroupSpec fineCostModel
          (W4TryDecryptCloneFailEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
            (· = dropClonedSessionEvents G_cur st_cur)) 0 :=
        { groups_le := fun _ {_} hE => by
            rcases hE with h1 | ⟨_, _, _, h1, _⟩
            · obtain ⟨_, _, _, ⟨_, e2, _, _, htf⟩, _⟩ := h1
              exact False.elim (hNo e2 htf)
            · obtain ⟨_, _, _, ⟨_, e2, _, _, htf⟩, _⟩ := h1
              exact False.elim (hNo e2 htf) }
      exact ((PhaseGroupSpec.freeOnly fineCostModel).or hEmpty).mono (Nat.zero_le _)
    · subst hst_eq
      exact ((PhaseGroupSpec.freeOnly fineCostModel).or
        (w4TryDecryptCloneFail_fine_groupSpec
          (segCloneEnv_dom_fine_groupSpec hgv hdom) hCur
          (dropClonedSessionEvents_groupSpec fineCostModel G_cur ses_cur.state))).mono
        (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
  have hE2 := ((PhaseGroupSpec.freeOnly fineCostModel).or
    (archivedTrialLoop_le4_groupSpec fineCostModel hlen4 hDec hTr hDrop)).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
  have hSpk := w4SmallStoreStep16_fine_groupSpec rd files spkDir (keyName spkId)
  have hKpk := w4SmallStoreStep16_fine_groupSpec rd files kpkDir (keyName kpkId)
  have hOptPk := phaseGroupSpec_ite_nil hasOpk fun _ =>
    w4SmallStoreStep16_fine_groupSpec rd files opkDir (keyName opkId)
  have hKp := w4SmallStoreStep16_fine_groupSpec rd files ownDir ownKeyName
  have hOver := w4StageP2OverBob_fine_groupSpec x_res hasOpk F x_spqr hArchSer hPush
  have hReg := w4SmallStoreStep16_fine_groupSpec rd files ownDir ownRegName
  have hErr := w4ErrTail_fine_groupSpec
  exact (hE1.seq (hE2.seq (hSpk.seq (hKpk.seq (hOptPk.seq
    (hKp.seq (hOver.seq (hReg.seq hErr)))))))).mono
    (z0_p2c_grp_reassoc segCloneDomFineGrpS g_cur w4ErrTailFineGrpS (4 * (g_dec + g_tr))
      w4SmallStoreStep16FineGrpS g_archSer g_push w4InitBobSpqrFineGrpS)

private theorem z0_phaseCredit_exists_guarded_u {α : Sort _} {M : AllocCostModel}
    [HasFineReallocCredit M] {P : α → Prop} {E : α → List AllocEvent → Prop} {c l p r : Nat}
    (h : ∀ x, P x → PhaseCreditSpec M (E x) c l p r) :
    PhaseCreditSpec M (fun evs => ∃ x, P x ∧ E x evs) c l p r where
  req_align evs := fun ⟨x, hx, he⟩ => (h x hx).req_align evs he
  credit_le st0 := fun ⟨x, hx, he⟩ => (h x hx).credit_le st0 he

private theorem z0_phaseGroup_exists_guarded_u {α : Sort _} {M : AllocCostModel}
    [HasFineGroupCredit M] {P : α → Prop} {E : α → List AllocEvent → Prop} {g : Nat}
    (h : ∀ x, P x → PhaseGroupSpec M (E x) g) :
    PhaseGroupSpec M (fun evs => ∃ x, P x ∧ E x evs) g where
  groups_le st0 := fun ⟨x, hx, he⟩ => (h x hx).groups_le st0 he

/-! ## Baseline `W4RecvPrekeyRealDom0` Credit, Group, & `SingleSlotFineSpec` -/

/-- Witness-free `PhaseCreditSpec fineCostModel` for `W4RecvPrekeyRealEnv R` under
`W4RecvPrekeyRealDom0 R` (`R.archivedTrials = []`). -/
theorem w4RecvPrekeyRealDom0_phaseCreditSpec
    (R : W4RecvPrekeyRealParams) (h : W4RecvPrekeyRealDom0 R) :
    PhaseCreditSpec fineCostModel (W4RecvPrekeyRealEnv R)
      w4RecvPrekeyRealDom0Cum w4RecvPrekeyRealDom0Live
      w4RecvPrekeyRealDom0Peak w4RecvPrekeyRealDom0MaxReq := by
  obtain ⟨hDom, hNil⟩ := h
  let P := mkW4RecvPrekeySlotParams R
  have hPNil : P.archivedTrials = [] := hNil
  have hCur : PhaseCreditSpec fineCostModel P.CurTrialFailEnv
      w4RealFailTdCum 0 w4RealFailTdPeak w4RealTdMaxReq := by
    change PhaseCreditSpec fineCostModel
      (if R.hasCurSession then W4FailedTdCancelEnv R.F R.K R.fc_cur else fun _ => False)
      _ _ _ _
    cases hcs : R.hasCurSession
    · exact (PhaseCreditSpec.empty fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact z0_w4FailedTdCancel_phaseCredit (hDom.cur_fail_dom hcs)
  have hPush : PhaseCreditSpec fineCostModel P.VecPushEnv 9923 0 0 192 := by
    have hsm : 192 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; decide
    have hc9923 : 1 * (2 * 192 + 9539) ≤ 9923 := by decide
    exact PhaseCreditSpec.mono hc9923 (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
      (phaseCredit_w4BoundedEvs_small fineCostModel_modelHyps 1 192 hsm)
  have hTdB : PhaseCreditSpec fineCostModel P.TryDecEnv
      w4RealFailTdCum w4RealTdBLive w4RealFailTdPeak w4RealTdMaxReq := by
    change PhaseCreditSpec fineCostModel
      (if R.isPathB then W4TryDecryptPathBEnv R.F R.K R.td_B else fun _ => False)
      _ _ _ _
    cases hpb : R.isPathB
    · exact (PhaseCreditSpec.empty fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact z0_w4TryDecryptPathB_phaseCredit (hDom.tdB_dom hpb)
  have hTdAC : PhaseCreditSpec fineCostModel (W4RecvPrekeyTryDecACEnv R)
      w4RealTdACCum w4RealTdACLive w4RealTdACPeak w4RealTdMaxReq := by
    unfold W4RecvPrekeyTryDecACEnv
    cases hpac : R.isPathAC
    · exact (PhaseCreditSpec.empty fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact z0_w4TryDecryptPathAC_phaseCredit (hDom.tdAC_dom hpac)
  have hFalse : ∀ x ∈ P.archivedTrials, False := by
    rw [hPNil]; intro _ hx; cases hx
  unfold W4RecvPrekeyRealEnv w4RecvPrekeyRealDom0Cum w4RecvPrekeyRealDom0Live
    w4RecvPrekeyRealDom0Peak w4RecvPrekeyRealDom0MaxReq
  exact w4DecryptPrekeySplitSlot_opened_fine_phaseCredit P
    (c_dec := 0) (p_dec := 0) (r_dec := 0) (c_tr := 0) (p_tr := 0) (r_tr := 0)
    (l_dec := fun _ => 0)
    rfl rfl rfl hDom.kpk_dir rfl rfl hDom.outer_dom
    (fun _ hbs => recordDeserializeCancelEnv_fine_phaseCreditSpec hbs)
    hCur
    (fun x hx => (hFalse x hx).elim)
    (fun x hx => (hFalse x hx).elim)
    (fun x hx => (hFalse x hx).elim)
    (fun x hx => (hFalse x hx).elim)
    hPush hTdB hTdAC

/-- Witness-free `PhaseGroupSpec fineCostModel` for `W4RecvPrekeyRealEnv R` under
`W4RecvPrekeyRealDom0 R` (`R.archivedTrials = []`). -/
theorem w4RecvPrekeyRealDom0_fine_groupSpec
    (R : W4RecvPrekeyRealParams) (h : W4RecvPrekeyRealDom0 R) :
    PhaseGroupSpec fineCostModel (W4RecvPrekeyRealEnv R) w4RecvPrekeyRealDom0GrpS := by
  obtain ⟨hDom, hNil⟩ := h
  let P := mkW4RecvPrekeySlotParams R
  have hPNil : P.archivedTrials = [] := hNil
  let TryDecAC := W4RecvPrekeyTryDecACEnv R
  have hDeser : ∀ bs : List (BitVec 8), bs.length ≤ 2097152 →
      PhaseGroupSpec fineCostModel (P.DeserEnv bs) deserCancelFineGrpS :=
    fun bs _ => recordDeserializeCancelEnv_fine_groupSpec bs
  have hCur : PhaseGroupSpec fineCostModel P.CurTrialFailEnv w2TryDecryptFailTightGroupS_split_12 := by
    change PhaseGroupSpec fineCostModel
      (if R.hasCurSession then W4FailedTdCancelEnv R.F R.K R.fc_cur else fun _ => False) _
    cases hcs : R.hasCurSession
    · exact { groups_le := fun _ {_} he => False.elim he }
    · exact z0_w4FailedTdCancel_fine_groupSpec (hDom.cur_fail_dom hcs)
  have hDec : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DecEnv x) 0 :=
    fun _ hx => nomatch (hPNil ▸ hx : _ ∈ ([] : List _))
  have hTr : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.TrialEnv x) 0 :=
    fun _ hx => nomatch (hPNil ▸ hx : _ ∈ ([] : List _))
  have hDrop : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DropEnv x) 0 :=
    fun _ hx => nomatch (hPNil ▸ hx : _ ∈ ([] : List _))
  have hPush : PhaseGroupSpec fineCostModel P.VecPushEnv (3 * FineScale) := by
    change PhaseGroupSpec fineCostModel (W4BoundedEvs 1 192) (3 * FineScale)
    simpa [Nat.one_mul] using w4BoundedEvs_groupSpec fineCostModel 1 192
  have hArchSer : PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv P.g_arch P.r_arch)
      recordSerializeDomFineGrpS :=
    z0_recordSerializeCancelEnv_of_valid_fine_groupSpec hDom.outer_dom.arch_valid
  have hOut0Ser : PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv P.g_out0 P.r_out0)
      recordSerializeDomFineGrpS :=
    z0_recordSerializeCancelEnv_of_valid_fine_groupSpec hDom.outer_dom.out0_valid
  have hOut1Ser : PhaseGroupSpec fineCostModel
      (SerializePrev1CancelEnv P.G_out1 P.sess_out1 P.enc_prev1)
      serializePrev1FreshBobFineGrpS :=
    z0_serializePrev1CancelEnv_freshBob_fine_groupSpec hDom.outer_dom.out1_freshBob
  have hTdB : PhaseGroupSpec fineCostModel P.TryDecEnv w2TryDecryptTightGroupS_split_12 := by
    change PhaseGroupSpec fineCostModel
      (if R.isPathB then W4TryDecryptPathBEnv R.F R.K R.td_B else fun _ => False) _
    cases hpb : R.isPathB
    · exact { groups_le := fun _ {_} he => False.elim he }
    · have hd := hDom.tdB_dom hpb
      exact w2TryDecryptTightEnv_linked_fine_groupSpec_split_12 R.F R.K
        R.td_B.dhCap R.td_B.needGrow R.td_B.withAddr R.td_B.errAlloc R.td_B.ctLen
        R.td_B.stBytes R.td_B.w.pre_pb R.td_B.w.vn R.td_B.w.pb R.td_B.w.st0
        R.td_B.w.sckaMsg R.td_B.w.v R.td_B.w.xInit R.td_B.w.xNew R.td_B.w.xAdd
        R.td_B.w.xRk R.td_B.w.xSInto R.td_B.w.xCInto hd.caps_len hd.top_tight
  have hTdAC : PhaseGroupSpec fineCostModel TryDecAC w2TryDecryptSeeds12GroupS_split_12 := by
    unfold TryDecAC W4RecvPrekeyTryDecACEnv
    cases hpac : R.isPathAC
    · exact { groups_le := fun _ {_} he => False.elim he }
    · have hd := (hDom.tdAC_dom hpac).base
      exact w2TryDecryptSeedsEnv_12_linked_fine_groupSpec_split_12 R.F R.K
        R.td_AC.dhCap R.td_AC.needGrow R.td_AC.withAddr R.td_AC.errAlloc R.td_AC.ctLen
        R.td_AC.stBytes R.td_AC.w.pre_pb R.td_AC.w.vn R.td_AC.w.pb R.td_AC.w.st0
        R.td_AC.w.sckaMsg R.td_AC.w.v R.td_AC.w.xInit R.td_AC.w.xNew R.td_AC.w.xAdd
        R.td_AC.w.xRk R.td_AC.w.xSInto R.td_AC.w.xCInto hd.caps_len hd.top_tight
  have hP1 := w4StageP1OkCli_fine_groupSpec P.rd P.files P.sessDir P.peersDir P.peer hDeser
  let gU := w4StageP1UntrustedBaseFineGrpS + deserCancelFineGrpS
  let gB := (w4StageP1OkBaseFineGrpS + deserCancelFineGrpS) +
    (4 * (0 + 0) + recordSerializeDomFineGrpS + 3 * FineScale) +
    w4StageP3FineGrpS w2TryDecryptTightGroupS_split_12 +
    (w4SmallStoreStep32FineGrpS + (16659 + (6 * FineScale + recordSerializeDomFineGrpS)))
  let gA := (w4StageP1OkBaseFineGrpS + deserCancelFineGrpS) +
    w4StageP2PathACliFineGrpS +
    w4StageP3FineGrpS w2TryDecryptSeeds12GroupS_split_12 +
    (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
      (16659 + (6 * FineScale + recordSerializeDomFineGrpS)))
  let gC := (w4StageP1OkBaseFineGrpS + deserCancelFineGrpS) +
    ((segCloneDomFineGrpS + w4ErrTailFineGrpS + 5 * w4SmallStoreStep16FineGrpS +
        recordSerializeDomFineGrpS + w4InitBobSpqrFineGrpS + w4ErrTailFineGrpS) +
      w2TryDecryptFailTightGroupS_split_12 +
      4 * (0 + 0) + 3 * FineScale) +
    w4StageP3FineGrpS w2TryDecryptSeeds12GroupS_split_12 +
    (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
      (16659 + (6 * FineScale + serializePrev1FreshBobFineGrpS)))
  have hLeU : gU ≤ w4RecvPrekeyRealDom0GrpS :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hLeB : gB ≤ w4RecvPrekeyRealDom0GrpS :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hLeA : gA ≤ w4RecvPrekeyRealDom0GrpS :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hLeC : gC ≤ w4RecvPrekeyRealDom0GrpS :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hArms : PhaseGroupSpec fineCostModel
      (fun e =>
        W4StageP1UntrustedCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer e ∨
        W4DecryptPrekeyPathBEnv P e ∨
        W4DecryptPrekeyPathAEnv ({ P with TryDecEnv := TryDecAC }) e ∨
        W4DecryptPrekeyPathCEnv ({ P with TryDecEnv := TryDecAC }) e)
      w4RecvPrekeyRealDom0GrpS :=
    { groups_le := fun st0 {e} hArm => by
        rcases hArm with hU | hB | hA | hC
        · exact ((w4StageP1UntrustedCli_fine_groupSpec P.rd P.files P.sessDir P.peersDir P.peer
            hDeser).mono hLeU).groups_le st0 hU
        · have hp2 := w4StageP2Matched_groupSpec fineCostModel hDom.outer_dom.trials_len4
            hDec hTr hDrop hArchSer hPush
          have hp3 := w4StageP3_fine_groupSpec hTdB
          have hp4 := w4StageP4MatchedCli_fine_groupSpec P.rd P.files P.peersDir P.sessDir P.peer
            hOut0Ser
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (z0_four_stages_grp_reassoc _ _ _ _)).mono hLeB).groups_le st0 hB
        · have hp2 := w4StageP2PathACli_fine_groupSpec P.hasOpk P.rd P.files
            P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
            P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr
          have hp3 := w4StageP3_fine_groupSpec hTdAC
          have hp4 := w4StageP4PathACli_fine_groupSpec P.hasOpk P.rd P.files
            P.peersDir P.kpkDir P.opkDir P.sessDir P.peer P.kpkMarkName P.opkId hOut0Ser
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (z0_four_stages_grp_reassoc _ _ _ _)).mono hLeA).groups_le st0 hA
        · have hp2 := z0_w4StageP2PathCCli_curDom_fine_groupSpec P.hasOpk P.rd P.files
            P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
            P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr
            hDom.outer_dom.cur_dom hCur hDom.outer_dom.trials_len4
            hDec hTr hDrop hArchSer hPush
          have hp3 := w4StageP3_fine_groupSpec hTdAC
          have hp4 := w4StageP4PathCCli_fine_groupSpec P.hasOpk P.rd P.files
            P.peersDir P.kpkDir P.opkDir P.sessDir P.peer P.kpkMarkName P.opkId hOut1Ser
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (z0_four_stages_grp_reassoc _ _ _ _)).mono hLeC).groups_le st0 hC }
  have hSeq := (hArms.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hSeq).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

/-- Witness-free `SingleSlotFineSpec` for `W4RecvPrekeyRealEnv R` under
`W4RecvPrekeyRealDom0 R` (`R.archivedTrials = []`). -/
def w4RecvPrekeyRealDom0_singleSlotFineSpec
    (R : W4RecvPrekeyRealParams) (h : W4RecvPrekeyRealDom0 R) :
    SingleSlotFineSpec (W4RecvPrekeyRealEnv R) where
  cum := w4RecvPrekeyRealDom0Cum
  live := w4RecvPrekeyRealDom0Live
  peak := w4RecvPrekeyRealDom0Peak
  maxReq := w4RecvPrekeyRealDom0MaxReq
  grpS := w4RecvPrekeyRealDom0GrpS
  credit := w4RecvPrekeyRealDom0_phaseCreditSpec R h
  live_le_peak := w4RecvPrekeyRealDom0_caps_le.1
  groups := w4RecvPrekeyRealDom0_fine_groupSpec R h

/-! ## Parametric & `1 MiB` Variant (i) `Dom0` `SingleSlotFineSpec` -/

/-- Parametric `PhaseCreditSpec fineCostModel` for `W4RecvPrekeyRealEnv R` under
`W4RecvPrekeyRealDom0Of smallFileCap maxCt R`. -/
theorem w4RecvPrekeyRealDom0Of_phaseCreditSpec {smallFileCap maxCt : Nat}
    (R : W4RecvPrekeyRealParams) (h : W4RecvPrekeyRealDom0Of smallFileCap maxCt R) :
    PhaseCreditSpec fineCostModel (W4RecvPrekeyRealEnv R)
      (w4RecvPrekeyRealDom0CumOf smallFileCap)
      (w4RecvPrekeyRealDom0LiveOf smallFileCap maxCt)
      (w4RecvPrekeyRealDom0PeakOf smallFileCap maxCt)
      (w4RecvPrekeyRealDom0MaxReqOf smallFileCap maxCt) := by
  obtain ⟨hDom, hNil⟩ := h
  let P := mkW4RecvPrekeySlotParams R
  have hPNil : P.archivedTrials = [] := hNil
  have hCur : PhaseCreditSpec fineCostModel P.CurTrialFailEnv
      w4RealFailTdCum 0 (w4FailTdPeakOf maxCt) (w4TdMaxReqOf maxCt) := by
    change PhaseCreditSpec fineCostModel
      (if R.hasCurSession then W4FailedTdCancelEnv R.F R.K R.fc_cur else fun _ => False) _ _ _ _
    cases hcs : R.hasCurSession
    · exact (PhaseCreditSpec.empty fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact z0_w4FailedTdCancelOf_phaseCredit (hDom.cur_fail_dom hcs)
  have hPush : PhaseCreditSpec fineCostModel P.VecPushEnv 9923 0 0 192 := by
    have hsm : 192 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]; decide
    have hc9923 : 1 * (2 * 192 + 9539) ≤ 9923 := by decide
    exact PhaseCreditSpec.mono hc9923 (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
      (phaseCredit_w4BoundedEvs_small fineCostModel_modelHyps 1 192 hsm)
  have hTdB : PhaseCreditSpec fineCostModel P.TryDecEnv
      w4RealFailTdCum (w4TdBLiveOf maxCt) (w4FailTdPeakOf maxCt) (w4TdMaxReqOf maxCt) := by
    change PhaseCreditSpec fineCostModel
      (if R.isPathB then W4TryDecryptPathBEnv R.F R.K R.td_B else fun _ => False) _ _ _ _
    cases hpb : R.isPathB
    · exact (PhaseCreditSpec.empty fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact z0_w4TryDecryptPathBOf_phaseCredit (hDom.tdB_dom hpb)
  have hTdAC : PhaseCreditSpec fineCostModel (W4RecvPrekeyTryDecACEnv R)
      w4RealTdACCum (w4TdACLiveOf maxCt) (w4TdACPeakOf maxCt) (w4TdMaxReqOf maxCt) := by
    unfold W4RecvPrekeyTryDecACEnv
    cases hpac : R.isPathAC
    · exact (PhaseCreditSpec.empty fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact z0_w4TryDecryptPathACOf_phaseCredit (hDom.tdAC_dom hpac)
  have hFalse : ∀ x ∈ P.archivedTrials, False := by
    rw [hPNil]; intro _ hx; cases hx
  unfold W4RecvPrekeyRealEnv w4RecvPrekeyRealDom0CumOf w4RecvPrekeyRealDom0LiveOf
    w4RecvPrekeyRealDom0PeakOf w4RecvPrekeyRealDom0MaxReqOf
  exact w4DecryptPrekeySplitSlot_opened_fine_phaseCredit P
    (c_dec := 0) (p_dec := 0) (r_dec := 0) (c_tr := 0) (p_tr := 0) (r_tr := 0)
    (l_dec := fun _ => 0)
    rfl rfl rfl hDom.kpk_dir rfl rfl hDom.outer_dom
    (fun _ hbs => recordDeserializeCancelEnv_fine_phaseCreditSpec hbs)
    hCur
    (fun x hx => (hFalse x hx).elim)
    (fun x hx => (hFalse x hx).elim)
    (fun x hx => (hFalse x hx).elim)
    (fun x hx => (hFalse x hx).elim)
    hPush hTdB hTdAC

/-- Parametric `PhaseGroupSpec fineCostModel` for `W4RecvPrekeyRealEnv R` under
`W4RecvPrekeyRealDom0Of smallFileCap maxCt R`. -/
theorem w4RecvPrekeyRealDom0Of_fine_groupSpec {smallFileCap maxCt : Nat}
    (R : W4RecvPrekeyRealParams) (h : W4RecvPrekeyRealDom0Of smallFileCap maxCt R) :
    PhaseGroupSpec fineCostModel (W4RecvPrekeyRealEnv R) w4RecvPrekeyRealDom0GrpS := by
  obtain ⟨hDom, hNil⟩ := h
  let P := mkW4RecvPrekeySlotParams R
  have hPNil : P.archivedTrials = [] := hNil
  let TryDecAC := W4RecvPrekeyTryDecACEnv R
  have hDeser : ∀ bs : List (BitVec 8), bs.length ≤ 2097152 →
      PhaseGroupSpec fineCostModel (P.DeserEnv bs) deserCancelFineGrpS :=
    fun bs _ => recordDeserializeCancelEnv_fine_groupSpec bs
  have hCur : PhaseGroupSpec fineCostModel P.CurTrialFailEnv w2TryDecryptFailTightGroupS_split_12 := by
    change PhaseGroupSpec fineCostModel
      (if R.hasCurSession then W4FailedTdCancelEnv R.F R.K R.fc_cur else fun _ => False) _
    cases hcs : R.hasCurSession
    · exact { groups_le := fun _ {_} he => False.elim he }
    · exact z0_w4FailedTdCancelOf_fine_groupSpec (hDom.cur_fail_dom hcs)
  have hDec : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DecEnv x) 0 :=
    fun _ hx => nomatch (hPNil ▸ hx : _ ∈ ([] : List _))
  have hTr : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.TrialEnv x) 0 :=
    fun _ hx => nomatch (hPNil ▸ hx : _ ∈ ([] : List _))
  have hDrop : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DropEnv x) 0 :=
    fun _ hx => nomatch (hPNil ▸ hx : _ ∈ ([] : List _))
  have hPush : PhaseGroupSpec fineCostModel P.VecPushEnv (3 * FineScale) := by
    change PhaseGroupSpec fineCostModel (W4BoundedEvs 1 192) (3 * FineScale)
    simpa [Nat.one_mul] using w4BoundedEvs_groupSpec fineCostModel 1 192
  have hArchSer := z0_recordSerializeCancelEnv_of_valid_fine_groupSpec hDom.outer_dom.arch_valid
  have hOut0Ser := z0_recordSerializeCancelEnv_of_valid_fine_groupSpec hDom.outer_dom.out0_valid
  have hOut1Ser := z0_serializePrev1CancelEnv_freshBob_fine_groupSpec hDom.outer_dom.out1_freshBob
  have hTdB : PhaseGroupSpec fineCostModel P.TryDecEnv w2TryDecryptTightGroupS_split_12 := by
    change PhaseGroupSpec fineCostModel
      (if R.isPathB then W4TryDecryptPathBEnv R.F R.K R.td_B else fun _ => False) _
    cases hpb : R.isPathB
    · exact { groups_le := fun _ {_} he => False.elim he }
    · have hd := hDom.tdB_dom hpb
      exact w2TryDecryptTightEnv_linked_fine_groupSpec_split_12 R.F R.K
        R.td_B.dhCap R.td_B.needGrow R.td_B.withAddr R.td_B.errAlloc R.td_B.ctLen
        R.td_B.stBytes R.td_B.w.pre_pb R.td_B.w.vn R.td_B.w.pb R.td_B.w.st0
        R.td_B.w.sckaMsg R.td_B.w.v R.td_B.w.xInit R.td_B.w.xNew R.td_B.w.xAdd
        R.td_B.w.xRk R.td_B.w.xSInto R.td_B.w.xCInto hd.caps_len hd.top_tight
  have hTdAC : PhaseGroupSpec fineCostModel TryDecAC w2TryDecryptSeeds12GroupS_split_12 := by
    unfold TryDecAC W4RecvPrekeyTryDecACEnv
    cases hpac : R.isPathAC
    · exact { groups_le := fun _ {_} he => False.elim he }
    · have hd := (hDom.tdAC_dom hpac).base
      exact w2TryDecryptSeedsEnv_12_linked_fine_groupSpec_split_12 R.F R.K
        R.td_AC.dhCap R.td_AC.needGrow R.td_AC.withAddr R.td_AC.errAlloc R.td_AC.ctLen
        R.td_AC.stBytes R.td_AC.w.pre_pb R.td_AC.w.vn R.td_AC.w.pb R.td_AC.w.st0
        R.td_AC.w.sckaMsg R.td_AC.w.v R.td_AC.w.xInit R.td_AC.w.xNew R.td_AC.w.xAdd
        R.td_AC.w.xRk R.td_AC.w.xSInto R.td_AC.w.xCInto hd.caps_len hd.top_tight
  have hP1 := w4StageP1OkCli_fine_groupSpec P.rd P.files P.sessDir P.peersDir P.peer hDeser
  let gU := w4StageP1UntrustedBaseFineGrpS + deserCancelFineGrpS
  let gB := (w4StageP1OkBaseFineGrpS + deserCancelFineGrpS) +
    (4 * (0 + 0) + recordSerializeDomFineGrpS + 3 * FineScale) +
    w4StageP3FineGrpS w2TryDecryptTightGroupS_split_12 +
    (w4SmallStoreStep32FineGrpS + (16659 + (6 * FineScale + recordSerializeDomFineGrpS)))
  let gA := (w4StageP1OkBaseFineGrpS + deserCancelFineGrpS) +
    w4StageP2PathACliFineGrpS +
    w4StageP3FineGrpS w2TryDecryptSeeds12GroupS_split_12 +
    (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
      (16659 + (6 * FineScale + recordSerializeDomFineGrpS)))
  let gC := (w4StageP1OkBaseFineGrpS + deserCancelFineGrpS) +
    ((segCloneDomFineGrpS + w4ErrTailFineGrpS + 5 * w4SmallStoreStep16FineGrpS +
        recordSerializeDomFineGrpS + w4InitBobSpqrFineGrpS + w4ErrTailFineGrpS) +
      w2TryDecryptFailTightGroupS_split_12 +
      4 * (0 + 0) + 3 * FineScale) +
    w4StageP3FineGrpS w2TryDecryptSeeds12GroupS_split_12 +
    (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
      (16659 + (6 * FineScale + serializePrev1FreshBobFineGrpS)))
  have hLeU : gU ≤ w4RecvPrekeyRealDom0GrpS :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hLeB : gB ≤ w4RecvPrekeyRealDom0GrpS :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hLeA : gA ≤ w4RecvPrekeyRealDom0GrpS :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hLeC : gC ≤ w4RecvPrekeyRealDom0GrpS :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hArms : PhaseGroupSpec fineCostModel
      (fun e =>
        W4StageP1UntrustedCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer e ∨
        W4DecryptPrekeyPathBEnv P e ∨
        W4DecryptPrekeyPathAEnv ({ P with TryDecEnv := TryDecAC }) e ∨
        W4DecryptPrekeyPathCEnv ({ P with TryDecEnv := TryDecAC }) e)
      w4RecvPrekeyRealDom0GrpS :=
    { groups_le := fun st0 {e} hArm => by
        rcases hArm with hU | hB | hA | hC
        · exact ((w4StageP1UntrustedCli_fine_groupSpec P.rd P.files P.sessDir P.peersDir P.peer
            hDeser).mono hLeU).groups_le st0 hU
        · have hp2 := w4StageP2Matched_groupSpec fineCostModel hDom.outer_dom.trials_len4
            hDec hTr hDrop hArchSer hPush
          have hp3 := w4StageP3_fine_groupSpec hTdB
          have hp4 := w4StageP4MatchedCli_fine_groupSpec P.rd P.files P.peersDir P.sessDir P.peer
            hOut0Ser
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (z0_four_stages_grp_reassoc _ _ _ _)).mono hLeB).groups_le st0 hB
        · have hp2 := w4StageP2PathACli_fine_groupSpec P.hasOpk P.rd P.files
            P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
            P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr
          have hp3 := w4StageP3_fine_groupSpec hTdAC
          have hp4 := w4StageP4PathACli_fine_groupSpec P.hasOpk P.rd P.files
            P.peersDir P.kpkDir P.opkDir P.sessDir P.peer P.kpkMarkName P.opkId hOut0Ser
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (z0_four_stages_grp_reassoc _ _ _ _)).mono hLeA).groups_le st0 hA
        · have hp2 := z0_w4StageP2PathCCli_curDom_fine_groupSpec P.hasOpk P.rd P.files
            P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
            P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr
            hDom.outer_dom.cur_dom hCur hDom.outer_dom.trials_len4
            hDec hTr hDrop hArchSer hPush
          have hp3 := w4StageP3_fine_groupSpec hTdAC
          have hp4 := w4StageP4PathCCli_fine_groupSpec P.hasOpk P.rd P.files
            P.peersDir P.kpkDir P.opkDir P.sessDir P.peer P.kpkMarkName P.opkId hOut1Ser
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (z0_four_stages_grp_reassoc _ _ _ _)).mono hLeC).groups_le st0 hC }
  have hSeq := (hArms.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hSeq).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

/-- Parametric `SingleSlotFineSpec` for `W4RecvPrekeyRealEnv R` under
`W4RecvPrekeyRealDom0Of smallFileCap maxCt R`. -/
def w4RecvPrekeyRealDom0Of_singleSlotFineSpec {smallFileCap maxCt : Nat}
    (R : W4RecvPrekeyRealParams) (h : W4RecvPrekeyRealDom0Of smallFileCap maxCt R) :
    SingleSlotFineSpec (W4RecvPrekeyRealEnv R) where
  cum := w4RecvPrekeyRealDom0CumOf smallFileCap
  live := w4RecvPrekeyRealDom0LiveOf smallFileCap maxCt
  peak := w4RecvPrekeyRealDom0PeakOf smallFileCap maxCt
  maxReq := w4RecvPrekeyRealDom0MaxReqOf smallFileCap maxCt
  grpS := w4RecvPrekeyRealDom0GrpS
  credit := w4RecvPrekeyRealDom0Of_phaseCreditSpec R h
  live_le_peak := Nat.le_max_right _ _
  groups := w4RecvPrekeyRealDom0Of_fine_groupSpec R h

/-- Variant (i) closed `Dom0` `SingleSlotFineSpec` (`W4RecvPrekeyRealDom0Of sessionCapBytes msgCapBytes`). -/
def w4RecvPrekeyReal1MiB_i_Dom0_singleSlotFineSpec
    (R : W4RecvPrekeyRealParams)
    (h : W4RecvPrekeyRealDom0Of sessionCapBytes msgCapBytes R) :
    SingleSlotFineSpec (W4RecvPrekeyRealEnv R) where
  cum := w4RecvPrekeyReal1MiB_i_Dom0Cum
  live := w4RecvPrekeyReal1MiB_i_Dom0Live
  peak := w4RecvPrekeyReal1MiB_i_Dom0Peak
  maxReq := w4RecvPrekeyReal1MiB_i_Dom0MaxReq
  grpS := w4RecvPrekeyReal1MiB_i_Dom0GrpS
  credit := w4RecvPrekeyRealDom0Of_phaseCreditSpec R h
  live_le_peak := w4RecvPrekeyReal1MiB_i_Dom0_caps_le.1
  groups := w4RecvPrekeyRealDom0Of_fine_groupSpec R h

/-- Existential Variant (i) `Dom0` W4 real-slot envelope (`(sessionCapBytes, msgCapBytes)`). -/
def ValidOverRealSlotEnvDom0 (evs : List AllocEvent) : Prop :=
  ∃ w4R : W4RecvPrekeyRealParams,
    W4RecvPrekeyRealDom0Of sessionCapBytes msgCapBytes w4R ∧ W4RecvPrekeyRealEnv w4R evs

theorem validOverRealSlotEnvDom0_phaseCreditSpec :
    PhaseCreditSpec fineCostModel ValidOverRealSlotEnvDom0
      w4RecvPrekeyReal1MiB_i_Dom0Cum w4RecvPrekeyReal1MiB_i_Dom0Live
      w4RecvPrekeyReal1MiB_i_Dom0Peak w4RecvPrekeyReal1MiB_i_Dom0MaxReq :=
  z0_phaseCredit_exists_guarded_u fun w4R hw4 =>
    (w4RecvPrekeyReal1MiB_i_Dom0_singleSlotFineSpec w4R hw4).credit

theorem validOverRealSlotEnvDom0_fine_groupSpec :
    PhaseGroupSpec fineCostModel ValidOverRealSlotEnvDom0 w4RecvPrekeyReal1MiB_i_Dom0GrpS :=
  z0_phaseGroup_exists_guarded_u fun w4R hw4 =>
    (w4RecvPrekeyReal1MiB_i_Dom0_singleSlotFineSpec w4R hw4).groups

/-- Closed `SingleSlotFineSpec` on `ValidOverRealSlotEnvDom0`. -/
def validOverRealSlotEnvDom0_singleSlotFineSpec :
    SingleSlotFineSpec ValidOverRealSlotEnvDom0 where
  cum := w4RecvPrekeyReal1MiB_i_Dom0Cum
  live := w4RecvPrekeyReal1MiB_i_Dom0Live
  peak := w4RecvPrekeyReal1MiB_i_Dom0Peak
  maxReq := w4RecvPrekeyReal1MiB_i_Dom0MaxReq
  grpS := w4RecvPrekeyReal1MiB_i_Dom0GrpS
  credit := validOverRealSlotEnvDom0_phaseCreditSpec
  live_le_peak := w4RecvPrekeyReal1MiB_i_Dom0_caps_le.1
  groups := validOverRealSlotEnvDom0_fine_groupSpec

end LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlotDom0
