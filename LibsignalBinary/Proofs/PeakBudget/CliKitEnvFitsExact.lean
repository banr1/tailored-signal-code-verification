/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit
public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
public import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
public import LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
public import LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
public import LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
public import LibsignalBinary.Proofs.RecordCodecs.DepsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdKeyPairPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.IdRegIdPollPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# Slot-Parametric Exact-Kit Whole-`main` `FitsEnv` Closure

**Checked by Lean.**

Proves whole-`main` `FitsEnv fineCostModel` on
`RealCliRunEnvMemExact.realCliMainBinaryKitEnvOfSlot EncSlot DecSigSlot img S X W i` under
`CliPqxdhInputs ⟨W.C, W.Q⟩ i`: discharges `initEnv` (`W3InitBinaryKitSlotEnvFixed`) and `pksmEnv`
(`PksmCanonSliceEnv`) directly, verifies the `@128` + `25,000`-jump + `6`-trial ceiling against
`1 GiB` RAM and `2 ^ 48` VA, and provides cap-parametric, ceiling-specialized, and curried
whole-`main` `FitsEnv` theorems.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact

open Arm64.Obj (Image)
open Arm64.Process (ProcessInputs bytesOfString initFsState)
open CryptoGames.LibsignalSessionApi (PreKeySignalMessage Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E
  (PEParams PreKeyBundleFields UnreachedPqxdhPrimitives djbKey keyPairOf)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalProtoCodec (encodeBytesField)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost uuidTryParse)
open CryptoVerification.RecordCodecs
  (IdentityKeyPairStructure encodeProto3BytesField)
open CryptoVerification.SignalSession
  (CliHooks CliPqxdhInputs Inputs PqParty PublicBundle baseKeysFile bundleDir encodeDir
   pqInitInputs pqInputs pqRecvInputs pqSendInputs publicBundleOf)
open CryptoVerification.SignalSession.Cli
  (DirGhost ReadRule StoresGhost addressText cliInputs pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV RunCall cliIo cliRd parseArgs pathStr readViewF)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecSigGhost EncGhost RunSem runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.Pksm (pksmParse)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_largeCost_eq fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Heap.SpecBudget (allocBytes1Events)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (DirDomainCaps addressText_length_le argv_length_le_of_cliPqInputs dirDomainCaps_opened_own
   dirDomainCaps_opened_peers dirDomainCaps_opened_sess)
open LibsignalBinary.Proofs.PeakBudget.CliFitsTraceArith
  (cliBudgetLimits cliDecoupledRamNeed cliDecoupledRamNeed_mono cliDecoupledVaNeed
   cliDecoupledVaNeed_mono cliDefaultStaticBytes cliDefaultStaticCount cliMaxAddrTextBytes
   cliMaxDirPathBytes cliMaxDirtyEntries cliOneGiB fitsEnv_fineCostModel_of_group_literal_bounds)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (allocBytes1Events_groupSpec cliIoReadFileEnv_nonFreeBound initialStateEnv_groupSpec
   m5PhaseEnv_groupSpec m6Env_groupSpec optTailCloneEvents_groupSpec readFileRuleEnv_nonFreeBound
   serializeSomeSeqFreeEnv_groupSpec vecCloneEvents_groupSpec w3BoxedStoreStepEnv_groupSpec
   w3InitiateFullEnv_groupSpec w3InitiateFullEnvWide_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliMainIoCredit (specCliIoReadSchedule_events_eq)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (M5PhaseEnv M6Env cliMainDeltaLive_tight cliMainDeltaPeak_tight cliMainMaxReq
   m3PhaseDeltaCum_tight m3PhaseMaxReq m5DirStepDeltaPeak m5DirStepMaxReq m6DeltaCum
   m6_phaseCredit_small1024)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W1BinarySendDom W1BinarySendParams W2BinaryWhisperDom W2BinaryWhisperParams W3BinaryInitDom
   W3BinaryInitParams)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers (phaseCredit_or_freeOnly_left)
open LibsignalBinary.Proofs.PeakBudget.CliSlotEnvelopeBridge
  (CliRunBinaryEnv OptStageEnv RealCliMainBinaryEnvOf cliMainBoundedSetup_fine_groupSpec
   cliMainBoundedSetup_phaseCredit_fine cliRunBinary1MiBCustomPksmCum
   cliRunBinary1MiBCustomPksmMaxReq cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_cliPqInputs
   m5Phase_Bounded_phaseCredit_fine)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
  (CliRealCalleeFineSpecs cliRun1MiBCustomPksmLive cliRun1MiBCustomPksmPeak
   cliRunOpenedCustomPksmGrpS w3InitRealCum w3InitRealGrpS w3InitRealLive w3InitRealMaxReq
   w3InitRealPeak w3InitReal_caps_le)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
  (cliMainTightLiveOf cliMainTightPeakOf cliMainTightReqOf)
open LibsignalBinary.Proofs.PeakBudget.DirPeakHelpers
  (cliIoCapEvents cliIoReadCaps phaseCreditSpec_cliIoReadFile_tight)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (HasFineGroupCredit NonFreeBound PhaseGroupSpec nonFreeCount nonFreeCount_append nonFreeCount_nil
   nonFreeCount_rustAllocEvents nonFreeCount_rustDeallocEvents nonFreeCount_rustReallocEvents)
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs (cliDecPkCanonSlotEnvExact)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemExact
  (mkBinaryKitRealCalleeEnvsSlotOf realCliMainBinaryKitEnvOfSlot
   realCliMainBinaryKitEnvOfSlot_fitsEnv_cliBudgetLimits_Stmt)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W3InitBinaryKitSlotEnvFixed w3InitBinaryKitSlotEnvFixed_eq_plain)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
  (cliRunBinaryEnv_fine_groupSpec_of_cap d3RecvW4ExtCum d3RecvW4ExtGrpS d3RecvW4ExtLive
   d3RecvW4ExtPeak d3RecvW4Ext_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
  (ValidPostSetupWitness cliMainWidenedSetupFineGrpS)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (DeallocCreditSpec ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (allocBytes1_fine_phaseCredit_tight fineReadFileCum fineReadFileLive fineReadFileMaxReq
   fineReadFilePeak optLargeCost_fine_of_le)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
  (rustAllocTightCum rustAllocTightCum_fine_le_738)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (PhaseCreditSpec.recordSerialize_seqFree_tight RecordSerializeSeqFreeEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
  (w1SendRealDcanCum w1SendRealDcanGrpS w1SendRealDcanMaxReq w1SendRealDcanPeak)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
  (w2RecvWhisperRealDcanCum w2RecvWhisperRealDcanGrpS w2RecvWhisperRealDcanMaxReq
   w2RecvWhisperRealDcanPeak)
open LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec
  (w3BoxedStoreStep_phaseCredit w3SpqrInit32_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateStagesPeak
  (phaseCreditSpec_seq_freeOnly phaseCreditSpec_w3InitiateFull_small
   phaseCreditSpec_w3InitiateFullWide_small)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateTightSpec
  (AliceInitiatedAnyCkBounds RecordAliceInitiatedAnyCkBounds fineSmallAllocCost_le_9789_of_le_3820
   recordSerializeMaxReq_aliceInitiatedAnyCk_le_3820
   recordSerializeTightCum_aliceInitiatedAnyCk_le_32485)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTightCredit
  (pksmCanonSliceCum pksmCanonSliceGrpS pksmCanonSliceLive pksmCanonSliceLive_le_peak
   pksmCanonSliceMaxReq pksmCanonSlicePeak pksmCanonSlice_fine_groupSpec
   pksmCanonSlice_fine_phaseCredit)
open LibsignalBinary.Proofs.RecordCodecs.DepsBudget
  (IdentityKeyPairTryFromEnv IkpSubEnv RecordCodecLoopEnv ikpSubEnv_phaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (deserCancelFineCum deserCancelFineGrpS deserCancelFineLive deserCancelFineMaxReq
   deserCancelFinePeak recordDeserializeCancelEnv_fine_groupSpec
   recordDeserializeCancelEnv_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
  (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
  (DirGetAfterReadEnv DirGetEnv DirGetErrAllocEnv DirGetMissEnv DirGetPathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
  (PathEnv pathAppendNameEvents pathEvents pathPushSlashEvents pathToOwnedEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv DirPutTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
  (OverCapFile ReadFileRuleEnvFixed cliRd_ok_le_fileCap readFileOverCapEvents)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSaveTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R3bProofPlacedBudget
  (r3bDecPkGhost)
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

/-! ## W3 (`init`) `W3InitBinaryKitSlotEnvFixed` `SingleSlotFineSpec` -/

private theorem ckx_byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
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

private theorem ckx_utf8_length (s : String) :
    (utf8 s).length = (s.toList.flatMap String.utf8EncodeChar).length := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, List.utf8Encode, ckx_byteArray_toList_eq_data]

private theorem ckx_seqEnv_mono {A₁ A₂ B₁ B₂ : List AllocEvent → Prop}
    (hA : ∀ evs, A₁ evs → A₂ evs) (hB : ∀ evs, B₁ evs → B₂ evs) :
    ∀ {evs}, SeqEnv A₁ B₁ evs → SeqEnv A₂ B₂ evs
  | _, Or.inl ha => Or.inl (hA _ ha)
  | _, Or.inr ⟨e1, e2, rfl, ha, hb⟩ => Or.inr ⟨e1, e2, rfl, hA _ ha, hB _ hb⟩

private theorem ckx_phaseGroupSpec_append_eq (M : AllocCostModel) [HasFineGroupCredit M]
    {e₁ e₂ : List AllocEvent} {g₁ g₂ : Nat}
    (h₁ : PhaseGroupSpec M (· = e₁) g₁) (h₂ : PhaseGroupSpec M (· = e₂) g₂) :
    PhaseGroupSpec M (· = e₁ ++ e₂) (g₁ + g₂) :=
  (h₁.concat h₂).of_imp fun _ h => ⟨e₁, e₂, h, rfl, rfl⟩

private theorem ckx_dirGetFixed_credit
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
        exact ckx_seqEnv_mono (fun _ h => h)
          (fun _ hr => ckx_seqEnv_mono
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

private theorem ckx_dirGetFixed_groups (M : AllocCostModel) [HasFineGroupCredit M]
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
      exact (ckx_phaseGroupSpec_append_eq M p1 (ckx_phaseGroupSpec_append_eq M p2 p3)).mono
        (by omega)
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

private theorem ckx_stepEvents_small_live_peak_nonInc
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
    obtain ⟨hl₂, hp₂⟩ := ckx_stepEvents_small_live_peak_nonInc hM hsmall tl (M.step ev st) htl
    simp only [AllocCostModel.stepEvents_cons]
    exact ⟨Nat.le_trans hl₂ h1.1, Nat.le_trans hp₂ h1.2⟩

private theorem ckx_phaseCreditSpec_zero_live_peak_of_small
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E : List AllocEvent → Prop} {c l p r : Nat}
    (hspec : PhaseCreditSpec M E c l p r)
    (hsmall : r ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M E c 0 0 r where
  req_align := hspec.req_align
  credit_le st0 {evs} hE := by
    obtain ⟨hc, _, _⟩ := hspec.credit_le st0 hE
    obtain ⟨hl, hp⟩ :=
      ckx_stepEvents_small_live_peak_nonInc hM hsmall evs st0 (hspec.req_align evs hE)
    exact ⟨hc, by omega, by omega⟩

private theorem ckx_phaseCreditSpec_exists {α : Sort _}
    {M : AllocCostModel} [HasFineReallocCredit M]
    {P : α → Prop} {E : α → List AllocEvent → Prop} {c l p r : Nat}
    (h : ∀ a, P a → PhaseCreditSpec M (E a) c l p r) :
    PhaseCreditSpec M (fun evs => ∃ a, P a ∧ E a evs) c l p r where
  req_align evs := fun ⟨a, ha, hE⟩ => (h a ha).req_align evs hE
  credit_le st0 := fun ⟨a, ha, hE⟩ => (h a ha).credit_le st0 hE

private theorem ckx_phaseGroupSpec_exists {α : Sort _}
    {M : AllocCostModel} [HasFineGroupCredit M]
    {P : α → Prop} {E : α → List AllocEvent → Prop} {g : Nat}
    (h : ∀ a, P a → PhaseGroupSpec M (E a) g) :
    PhaseGroupSpec M (fun evs => ∃ a, P a ∧ E a evs) g where
  groups_le st0 := fun ⟨a, ha, hE⟩ => (h a ha).groups_le st0 hE

private theorem ckx_dirDomainCaps_64 {maxDir maxEntries maxVal : Nat} {dir : DirGhost}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir) (hle : maxDir ≤ 64) :
    DirDomainCaps 64 maxEntries maxVal dir :=
  ⟨Nat.le_trans hdc.path_len_le hle, hdc.changed_len_le, hdc.changed_val_le⟩

private theorem ckx_rustAlloc_small_credit {req al : Nat}
    (hal : al ≤ 16) (hsmall : req ≤ 3820) :
    PhaseCreditSpec fineCostModel (· = rustAllocEvents req al) 9789 0 0 req := by
  by_cases hpos : 0 < req
  · have ha := PhaseCreditSpec.rustAlloc_small fineCostModel
      (req := req) (al := al) hal hpos
      (by rw [fineCostModel_smallMaxReq_eq]; omega)
    have hc : HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 9789 :=
      fineSmallAllocCost_le_9789_of_le_3820 hsmall
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
        fineSmallAllocCost_le_9789_of_le_3820 (Nat.zero_le _)
      split
      · obtain ⟨hc, hl, hp⟩ := fineCostModel_modelHyps.step_alloc_small_any st0 (Nat.zero_le _)
        simp only [AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
        exact ⟨by omega, by omega, by omega⟩
      · obtain ⟨hc, hl, hp⟩ := fineCostModel_modelHyps.step_aligned_small_any st0
          (by omega : max al 8 ≤ 16) (Nat.zero_le _)
        simp only [AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
        exact ⟨by omega, by omega, by omega⟩

private theorem ckx_dirPut_opened_credit {dir : DirGhost} (hch : dir.changed = [])
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
    (ckx_rustAlloc_small_credit (req := 192) (al := 8) (by decide) (by decide))).of_imp himp
    |>.mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by decide)

private theorem ckx_dirPut_opened_groups (M : AllocCostModel) [HasFineGroupCredit M]
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

private theorem ckx_dirPutStr_opened_credit {dir : DirGhost} (hch : dir.changed = [])
    {name : List (BitVec 8)} (hname : name.length ≤ 64) (bytes : List (BitVec 8)) :
    PhaseCreditSpec fineCostModel (DirPutStrEnv dir name bytes) 19578 0 0 192 := by
  unfold DirPutStrEnv
  split_ifs with hnil
  · exact (ckx_dirPut_opened_credit hch name bytes).mono (by decide)
      (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)
  · have ha := ckx_rustAlloc_small_credit (req := name.length) (al := 1)
      (by decide) (Nat.le_trans hname (by decide))
    exact (ha.seq (ckx_dirPut_opened_credit hch name bytes)).mono
      (by decide : 9789 + 9789 ≤ 19578) (Nat.le_refl 0) (Nat.le_refl 0)
      (Nat.max_le.mpr ⟨Nat.le_trans hname (by decide), Nat.le_refl 192⟩)

private theorem ckx_dirPutStr_opened_groups (M : AllocCostModel) [HasFineGroupCredit M]
    {dir : DirGhost} (hch : dir.changed = []) (name bytes : List (BitVec 8)) :
    PhaseGroupSpec M (DirPutStrEnv dir name bytes) (6 * FineScale) := by
  unfold DirPutStrEnv
  split_ifs
  · exact (ckx_dirPut_opened_groups M hch name bytes).mono (by omega)
  · exact ((PhaseGroupSpec.rustAlloc_any M name.length 1).seq
      (ckx_dirPut_opened_groups M hch name bytes)).mono (by omega)

private theorem ckx_recordCodecLoop_nonFree {budget maxLen : Nat} {evs : List AllocEvent}
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

private theorem ckx_ikpTryFrom_credit {gr : Except Unit (List (BitVec 8))}
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
    have hzero := ckx_phaseCreditSpec_zero_live_peak_of_small fineCostModel_modelHyps hcr
      (by rw [fineCostModel_smallMaxReq_eq]; decide)
    exact hzero.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

private theorem ckx_ikpTryFrom_groups (M : AllocCostModel) [HasFineGroupCredit M]
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
      have hcL : nonFreeCount evsL ≤ 2 * bs.length + 3 := ckx_recordCodecLoop_nonFree hL
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

private theorem ckx_segClone_aliceInitiated_groups
    {G : SessionGhost} {sess : Session (List (BitVec 8))}
    (hb : AliceInitiatedAnyCkBounds G sess) :
    PhaseGroupSpec fineCostModel (SegCloneEnv G sess.state) (42 * FineScale) := by
  have hloc := vecCloneEvents_groupSpec fineCostModel G.localIk
  have hrem := vecCloneEvents_groupSpec fineCostModel G.remoteIk
  have hroot := PhaseGroupSpec.rustAlloc_any fineCostModel 32 1
  have hsnd : PhaseGroupSpec fineCostModel
      (· = match G.sender, sess.state.senderChain with
           | some gs, some sc => senderChainCloneEvents gs sc
           | _, _ => [])
      (9 * FineScale) := by
    cases G.sender <;> cases sess.state.senderChain
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · rename_i gs sc
      unfold senderChainCloneEvents chainCloneEvents senderChainAsProtoGhost
      dsimp only
      have c1 := vecCloneEvents_groupSpec fineCostModel gs.srk
      have c2 := vecCloneEvents_groupSpec fineCostModel gs.priv
      have c3 := PhaseGroupSpec.rustAlloc_any fineCostModel 32 1
      have c4 : PhaseGroupSpec fineCostModel (· = ([] : List AllocEvent)) 0 :=
        PhaseGroupSpec.nil fineCostModel
      exact (ckx_phaseGroupSpec_append_eq fineCostModel
        (ckx_phaseGroupSpec_append_eq fineCostModel
          (ckx_phaseGroupSpec_append_eq fineCostModel c1 c2) c3) c4).mono (by decide)
  have hrc : PhaseGroupSpec fineCostModel
      (· = if sess.state.receiverChains = [] then []
           else rustAllocEvents (104 * sess.state.receiverChains.length) 8 ++
             (G.chains.zip sess.state.receiverChains).flatMap chainCloneEvents)
      (12 * FineScale) := by
    rcases hb.recv_shape with hnil | ⟨rc0, hrc1, hmks⟩
    · simp only [hnil, ↓reduceIte]
      exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · rw [hrc1]
      simp only [List.cons_ne_self, ↓reduceIte, List.length_singleton, Nat.mul_one]
      have hbuf := PhaseGroupSpec.rustAlloc_any fineCostModel 104 8
      cases G.chains with
      | nil =>
        simp only [List.zip_nil_left, List.flatMap_nil, List.append_nil]
        exact hbuf.mono (by decide)
      | cons gc0 gcs =>
        simp only [List.zip_cons_cons, List.zip_nil_right, List.flatMap_cons, List.flatMap_nil,
          List.append_nil]
        unfold chainCloneEvents
        dsimp only
        rw [hmks]
        simp only [↓reduceIte]
        have c1 := vecCloneEvents_groupSpec fineCostModel gc0.srk
        have c2 := vecCloneEvents_groupSpec fineCostModel gc0.priv
        have c3 : PhaseGroupSpec fineCostModel
            (· = match rc0.chainKey with | none => [] | some _ => rustAllocEvents 32 1)
            (3 * FineScale) := by
          cases rc0.chainKey
          · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
          · exact PhaseGroupSpec.rustAlloc_any fineCostModel 32 1
        have c4 : PhaseGroupSpec fineCostModel (· = ([] : List AllocEvent)) 0 :=
          PhaseGroupSpec.nil fineCostModel
        have hch := ckx_phaseGroupSpec_append_eq fineCostModel
          (ckx_phaseGroupSpec_append_eq fineCostModel
            (ckx_phaseGroupSpec_append_eq fineCostModel c1 c2) c3) c4
        exact (ckx_phaseGroupSpec_append_eq fineCostModel hbuf hch).mono (by decide)
  have hpend := optTailCloneEvents_groupSpec fineCostModel G.pending
  have hkyb := optTailCloneEvents_groupSpec fineCostModel G.kyber
  have halice := vecCloneEvents_groupSpec fineCostModel G.alice
  have hpq : PhaseGroupSpec fineCostModel
      (· = if sess.state.pqRatchetState.length = 0 then []
           else rustAllocEvents sess.state.pqRatchetState.length 1)
      (3 * FineScale) := by
    split
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    · exact PhaseGroupSpec.rustAlloc_any fineCostModel sess.state.pqRatchetState.length 1
  have s1 := ckx_phaseGroupSpec_append_eq fineCostModel hloc hrem
  have s2 := ckx_phaseGroupSpec_append_eq fineCostModel s1 hroot
  have s3 := ckx_phaseGroupSpec_append_eq fineCostModel s2 hsnd
  have s4 := ckx_phaseGroupSpec_append_eq fineCostModel s3 hrc
  have s5 := ckx_phaseGroupSpec_append_eq fineCostModel s4 hpend
  have s6 := ckx_phaseGroupSpec_append_eq fineCostModel s5 hkyb
  have s7 := ckx_phaseGroupSpec_append_eq fineCostModel s6 halice
  have s8 := ckx_phaseGroupSpec_append_eq fineCostModel s7 hpq
  unfold SegCloneEnv segCloneEvents
  exact s8.mono (by decide)

private theorem ckx_recordSerializeSeqFree_aliceInitiated_groups
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hb : RecordAliceInitiatedAnyCkBounds g r) :
    PhaseGroupSpec fineCostModel (RecordSerializeSeqFreeEnv g r) (45 * FineScale) := by
  unfold RecordSerializeSeqFreeEnv
  cases hgc : g.cur <;> cases hrc : r.currentSession
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · rename_i G sess
    exact serializeSomeSeqFreeEnv_groupSpec fineCostModel
      (ckx_segClone_aliceInitiated_groups (hb G sess hgc hrc))

private theorem ckx_w3Fixed_credit {peerAddr : AddrV}
    {dir : List (BitVec 8)} {i : Inputs} {w : W3BinaryInitParams}
    (hdom : W3BinaryInitDom (.init peerAddr dir) i w)
    (hikp : ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "identity-key-pair") =
        .ok bs → bs.length ≤ 105) :
    PhaseCreditSpec fineCostModel (W3InitBinaryKitSlotEnvFixed w)
      (w3InitRealCum + 4500000)
      (w3InitRealLive + 65536)
      (w3InitRealPeak + 65536)
      (w3InitRealMaxReq + 65536) := by
  obtain ⟨_, hpeer, hF, hspqr, _, halice⟩ := hdom peerAddr dir rfl
  have hpeerVal : w.x.peer.val.name.length ≤ 40 := hpeer
  have haddrLen : (addressText w.x.peer.val).length ≤ 64 := by
    have h51 := addressText_length_le w.x.peer.val
    omega
  have hdcOwn := ckx_dirDomainCaps_64 dirDomainCaps_opened_own (by decide)
  have hdcPeers := ckx_dirDomainCaps_64 dirDomainCaps_opened_peers (by decide)
  have hdcSess := ckx_dirDomainCaps_64 dirDomainCaps_opened_sess (by decide)
  have hGetPeers := ckx_dirGetFixed_credit
    cliIo.rd w.x.F StoresGhost.opened.identity.peers w.x.peer.val.name hdcPeers
    (Nat.le_trans hpeerVal (by decide)) (fun _ h => cliRd_ok_le_fileCap h)
  have htrust := w3BoxedStoreStep_phaseCredit fineCostModel_modelHyps 32
    (phaseCreditSpec_seq_freeOnly fineCostModel_modelHyps hGetPeers)
  have hAddr := addrTextValEnv_decimal_fine_phaseCredit_tight w.x.peer.val hpeerVal
  have hGetSess := ckx_dirGetFixed_credit
    cliIo.rd w.x.F StoresGhost.opened.sessions (addressText w.x.peer.val) hdcSess
    haddrLen (fun _ h => cliRd_ok_le_fileCap h)
  have hOptDeser : PhaseCreditSpec fineCostModel
      (OptLoadDeserEnv scopeKit (ofBytesEnv RecordDeserializeCancelEnv)
        (StoresGhost.opened.sessions.get cliIo.rd w.x.F (addressText w.x.peer.val)))
      deserCancelFineCum deserCancelFineLive deserCancelFinePeak deserCancelFineMaxReq := by
    unfold OptLoadDeserEnv
    cases hget : StoresGhost.opened.sessions.get cliIo.rd w.x.F (addressText w.x.peer.val) with
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
          change cliIo.rd w.x.F _ = .ok (b0 :: bsRest) at hget
          exact cliRd_ok_le_fileCap hget
        exact ckx_phaseCreditSpec_exists fun r henc => by
          unfold ofBytesEnv
          have hlen' : (encodeRecord r).length ≤ 2097152 := by rw [henc]; exact hlen
          exact (recordDeserializeCancelEnv_fine_phaseCreditSpec hlen').of_imp fun _ h => h.2
  have hload := w3BoxedStoreStep_phaseCredit fineCostModel_modelHyps 24
    (hAddr.seq (hGetSess.seq (phaseCreditSpec_seq_freeOnly fineCostModel_modelHyps hOptDeser)))
  have hikp_w : ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd w.x.F (utf8 "identity-key-pair") = .ok bs →
        bs.length ≤ 105 := by
    rw [hF]; exact hikp
  have hkpName : (utf8 "identity-key-pair").length ≤ 64 := by
    rw [ckx_utf8_length]; decide
  have hGetKp := ckx_dirGetFixed_credit
    cliIo.rd w.x.F StoresGhost.opened.identity.own (utf8 "identity-key-pair") hdcOwn
    hkpName hikp_w
  have hIkp := phaseCreditSpec_seq_freeOnly fineCostModel_modelHyps (ckx_ikpTryFrom_credit hikp_w)
  have hkp := w3BoxedStoreStep_phaseCredit fineCostModel_modelHyps 16 (hGetKp.seq hIkp)
  have hspqrSpec := w3SpqrInit32_phaseCredit fineCostModel_modelHyps w.F w.x_spqr hspqr
  have hregName : (utf8 "registration-id").length ≤ 64 := by
    rw [ckx_utf8_length]; decide
  have hGetReg := ckx_dirGetFixed_credit
    cliIo.rd w.x.F StoresGhost.opened.identity.own (utf8 "registration-id") hdcOwn
    hregName (fun _ h => cliRd_ok_le_fileCap h)
  have hRegMal : PhaseCreditSpec fineCostModel
      (OptRegIdMalformedEnv
        (StoresGhost.opened.identity.own.get cliIo.rd w.x.F (utf8 "registration-id")))
      9789 0 0 14 := by
    unfold OptRegIdMalformedEnv
    cases StoresGhost.opened.identity.own.get cliIo.rd w.x.F (utf8 "registration-id") with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok bs =>
      dsimp only
      split_ifs
      · exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      · exact ckx_rustAlloc_small_credit (req := 14) (al := 1) (by decide) (by decide)
  have hreg := w3BoxedStoreStep_phaseCredit fineCostModel_modelHyps 16
    (hGetReg.seq (phaseCreditSpec_seq_freeOnly fineCostModel_modelHyps hRegMal))
  have hSaveTail : PhaseCreditSpec fineCostModel
      (cliIdentityKitSaveTailEnv DirPutStrEnv StoresGhost.opened.identity w.x.peer.val w.peerKey
        (StoresGhost.opened.identity.peers.get cliIo.rd w.x.F w.x.peer.val.name))
      29367 0 0 192 := by
    unfold cliIdentityKitSaveTailEnv
    cases StoresGhost.opened.identity.peers.get cliIo.rd w.x.F w.x.peer.val.name with
    | error _ =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | ok _ =>
      have hpks : PhaseCreditSpec fineCostModel PublicKeySerializeEnv 9789 0 0 33 := by
        unfold PublicKeySerializeEnv publicKeySerializeEvents
        exact ckx_rustAlloc_small_credit (req := 33) (al := 1) (by decide) (by decide)
      have hput := ckx_dirPutStr_opened_credit (dir := StoresGhost.opened.identity.peers) rfl
        (Nat.le_trans hpeerVal (by decide)) w.peerKey.serialize
      have hbody := hpks.seq hput
      have hf := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
      exact (hf.seq hbody).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
  have hsave := w3BoxedStoreStep_phaseCredit fineCostModel_modelHyps 32 (hGetPeers.seq hSaveTail)
  have hSer0 := PhaseCreditSpec.recordSerialize_seqFree_tight fineCostModel_modelHyps w.g_rec w.r_rec
  have hSerReq := recordSerializeMaxReq_aliceInitiatedAnyCk_le_3820 halice
  have hSerCum := recordSerializeTightCum_aliceInitiatedAnyCk_le_32485 halice
  have hSer := (ckx_phaseCreditSpec_zero_live_peak_of_small fineCostModel_modelHyps hSer0
    (by rw [fineCostModel_smallMaxReq_eq]; omega)).mono
    hSerCum (Nat.le_refl 0) (Nat.le_refl 0) hSerReq
  have hPutSess := ckx_dirPut_opened_credit (dir := StoresGhost.opened.sessions) rfl
    (addressText w.x.peer.val) (encodeRecord w.r_rec)
  have hstore := w3BoxedStoreStep_phaseCredit fineCostModel_modelHyps 32
    (hAddr.seq (hSer.seq hPutSess))
  have hfull := phaseCreditSpec_w3InitiateFullWide_small fineCostModel_modelHyps hpeer
    (by rw [fineCostModel_smallMaxReq_eq]; decide)
    htrust hload hkp hspqrSpec hreg hsave hstore
  exact hfull.mono (by decide) (by decide) (by decide) (by decide)

private theorem ckx_w3Fixed_groups {peerAddr : AddrV}
    {dir : List (BitVec 8)} {i : Inputs} {w : W3BinaryInitParams}
    (hdom : W3BinaryInitDom (.init peerAddr dir) i w)
    (hikp : ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "identity-key-pair") =
        .ok bs → bs.length ≤ 105) :
    PhaseGroupSpec fineCostModel (W3InitBinaryKitSlotEnvFixed w)
      (w3InitRealGrpS + 1500 * FineScale) := by
  obtain ⟨_, hpeer, hF, _, _, halice⟩ := hdom peerAddr dir rfl
  have hpeerVal : w.x.peer.val.name.length ≤ 40 := hpeer
  have hikp_w : ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd w.x.F (utf8 "identity-key-pair") = .ok bs →
        bs.length ≤ 105 := by
    rw [hF]; exact hikp
  have hf := PhaseGroupSpec.freeOnly fineCostModel
  have hGetPeersG := ckx_dirGetFixed_groups fineCostModel
    cliIo.rd w.x.F StoresGhost.opened.identity.peers w.x.peer.val.name
  have hGetSessG := ckx_dirGetFixed_groups fineCostModel
    cliIo.rd w.x.F StoresGhost.opened.sessions (addressText w.x.peer.val)
  have hGetKpG := ckx_dirGetFixed_groups fineCostModel
    cliIo.rd w.x.F StoresGhost.opened.identity.own (utf8 "identity-key-pair")
  have hGetRegG := ckx_dirGetFixed_groups fineCostModel
    cliIo.rd w.x.F StoresGhost.opened.identity.own (utf8 "registration-id")
  have htrust := w3BoxedStoreStepEnv_groupSpec fineCostModel 32
    (hGetPeersG.seq hf)
  have hAddrG := addrTextValEnv_decimal_groupSpec fineCostModel w.x.peer.val hpeerVal
  have hOptDeserG : PhaseGroupSpec fineCostModel
      (OptLoadDeserEnv scopeKit (ofBytesEnv RecordDeserializeCancelEnv)
        (StoresGhost.opened.sessions.get cliIo.rd w.x.F (addressText w.x.peer.val)))
      deserCancelFineGrpS := by
    unfold OptLoadDeserEnv
    cases StoresGhost.opened.sessions.get cliIo.rd w.x.F (addressText w.x.peer.val) with
    | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    | ok bs =>
      cases bs with
      | nil => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      | cons b0 bsRest =>
        exact ckx_phaseGroupSpec_exists fun r _ => by
          unfold ofBytesEnv
          exact (recordDeserializeCancelEnv_fine_groupSpec (encodeRecord r)).of_imp fun _ h => h.2
  have hload := w3BoxedStoreStepEnv_groupSpec fineCostModel 24
    (hAddrG.seq (hGetSessG.seq (hOptDeserG.seq hf)))
  have hkp := w3BoxedStoreStepEnv_groupSpec fineCostModel 16
    (hGetKpG.seq ((ckx_ikpTryFrom_groups fineCostModel hikp_w).seq hf))
  have hspqrG := initialStateEnv_groupSpec fineCostModel w.F w.x_spqr
  have hRegMalG : PhaseGroupSpec fineCostModel
      (OptRegIdMalformedEnv
        (StoresGhost.opened.identity.own.get cliIo.rd w.x.F (utf8 "registration-id")))
      (3 * FineScale) := by
    unfold OptRegIdMalformedEnv
    cases StoresGhost.opened.identity.own.get cliIo.rd w.x.F (utf8 "registration-id") with
    | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    | ok bs =>
      dsimp only
      split_ifs
      · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
      · exact PhaseGroupSpec.rustAlloc_any fineCostModel 14 1
  have hreg := w3BoxedStoreStepEnv_groupSpec fineCostModel 16
    (hGetRegG.seq (hRegMalG.seq hf))
  have hSaveTailG : PhaseGroupSpec fineCostModel
      (cliIdentityKitSaveTailEnv DirPutStrEnv StoresGhost.opened.identity w.x.peer.val w.peerKey
        (StoresGhost.opened.identity.peers.get cliIo.rd w.x.F w.x.peer.val.name))
      (9 * FineScale) := by
    unfold cliIdentityKitSaveTailEnv
    cases StoresGhost.opened.identity.peers.get cliIo.rd w.x.F w.x.peer.val.name with
    | error _ => exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
    | ok _ =>
      have hpks : PhaseGroupSpec fineCostModel PublicKeySerializeEnv (3 * FineScale) := by
        unfold PublicKeySerializeEnv publicKeySerializeEvents
        exact PhaseGroupSpec.rustAlloc_any fineCostModel 33 1
      have hput := ckx_dirPutStr_opened_groups fineCostModel
        (dir := StoresGhost.opened.identity.peers) rfl w.x.peer.val.name w.peerKey.serialize
      exact (hf.seq (hpks.seq hput)).mono (by omega)
  have hsave := w3BoxedStoreStepEnv_groupSpec fineCostModel 32 (hGetPeersG.seq hSaveTailG)
  have hSerG := ckx_recordSerializeSeqFree_aliceInitiated_groups halice
  have hPutSessG := ckx_dirPut_opened_groups fineCostModel (dir := StoresGhost.opened.sessions) rfl
    (addressText w.x.peer.val) (encodeRecord w.r_rec)
  have hstore := w3BoxedStoreStepEnv_groupSpec fineCostModel 32 (hAddrG.seq (hSerG.seq hPutSessG))
  have hfull := w3InitiateFullEnvWide_groupSpec fineCostModel w.x.peer.name.bytes.length
    htrust hload hkp hspqrG hreg hsave hstore
  exact hfull.mono (by decide)

/-- Binary-kit W3 (`init`) `SingleSlotFineSpec` at `W3InitBinaryKitSlotEnvFixed` under the
`105`-byte `identity-key-pair` cap. -/
def binaryKitW3Fixed_fineSpec (g : RunCall)
    (hikp : ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd (runFiles g.i) (utf8 "identity-key-pair") =
        .ok bs → bs.length ≤ 105) :
    SingleSlotFineSpec
      (match g.c with
       | .init _ _ => fun evs =>
         ∃ w : W3BinaryInitParams,
           W3BinaryInitDom g.c g.i w ∧ W3InitBinaryKitSlotEnvFixed w evs
       | _ => fun _ => False) where
  cum := w3InitRealCum + 4500000
  live := w3InitRealLive + 65536
  peak := w3InitRealPeak + 65536
  maxReq := w3InitRealMaxReq + 65536
  grpS := w3InitRealGrpS + 1500 * FineScale
  credit := by
    cases g.c with
    | keygen _ _ | send _ | recv _ =>
      exact (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
        |>.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | init peerAddr dir =>
      exact ckx_phaseCreditSpec_exists fun w hdom => ckx_w3Fixed_credit hdom hikp
  live_le_peak := Nat.add_le_add_right w3InitReal_caps_le.2.2.1 65536
  groups := by
    cases g.c with
    | keygen _ _ | send _ | recv _ =>
      exact (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
        |>.mono (Nat.zero_le _)
    | init peerAddr dir =>
      exact ckx_phaseGroupSpec_exists fun w hdom => ckx_w3Fixed_groups hdom hikp

/-! ## `identity-key-pair` `≤ 105` B Domain Bound and Slot `initEnv` Spec -/

private def ckx_EntriesFromNorm (files : List (String × List (BitVec 8))) (fs : Arm64.FsState) :
    Prop :=
  ∀ k bs, fs.entries k = some (.file bs) → ∃ p, Arm64.normalizePath p = k ∧ (p, bs) ∈ files

private theorem ckx_entriesFromNorm_empty (files : List (String × List (BitVec 8))) :
    ckx_EntriesFromNorm files ({} : Arm64.FsState) := by
  intro k bs hk; dsimp only at hk; split at hk <;> cases hk

private theorem ckx_entriesFromNorm_setEntry_dir {files : List (String × List (BitVec 8))}
    {fs : Arm64.FsState} (h : ckx_EntriesFromNorm files fs) (pref : Arm64.FsPath) :
    ckx_EntriesFromNorm files (fs.setEntry pref (some .dir)) := by
  intro k bs hk; unfold Arm64.FsState.setEntry at hk; dsimp only at hk
  split at hk
  · cases hk
  · exact h k bs hk

private theorem ckx_entriesFromNorm_foldl_dirs {files : List (String × List (BitVec 8))}
    (prefs : List Arm64.FsPath) {fs : Arm64.FsState} (h : ckx_EntriesFromNorm files fs) :
    ckx_EntriesFromNorm files (prefs.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs) := by
  induction prefs generalizing fs with
  | nil => exact h
  | cons hd tl ih => exact ih (ckx_entriesFromNorm_setEntry_dir h hd)

private theorem ckx_entriesFromNorm_foldl_outer_dirs {files : List (String × List (BitVec 8))}
    (dirs : List String) {fs : Arm64.FsState} (h : ckx_EntriesFromNorm files fs) :
    ckx_EntriesFromNorm files
      (dirs.foldl
        (fun acc d => (Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath d)).foldl
          (fun a pref => a.setEntry pref (some .dir)) acc) fs) := by
  induction dirs generalizing fs with
  | nil => exact h
  | cons hd tl ih => exact ih (ckx_entriesFromNorm_foldl_dirs _ h)

private theorem ckx_entriesFromNorm_setFile {files : List (String × List (BitVec 8))}
    {fs : Arm64.FsState} (h : ckx_EntriesFromNorm files fs) {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ files) :
    ckx_EntriesFromNorm files (fs.setFile p (some (.file bs))) := by
  intro k bs' hk; unfold Arm64.FsState.setFile Arm64.FsState.setEntry at hk; dsimp only at hk
  split at hk
  · rename_i heq
    have hk_eq : Arm64.normalizePath p = k := (beq_iff_eq.mp heq).symm
    injection hk with hfile; injection hfile with hbs; subst hbs
    exact ⟨p, hk_eq, hmem⟩
  · exact h k bs' hk

private theorem ckx_entriesFromNorm_foldl_files {allFiles : List (String × List (BitVec 8))}
    (rem : List (String × List (BitVec 8)))
    (hsub : ∀ x ∈ rem, x ∈ allFiles)
    {fs : Arm64.FsState} (h : ckx_EntriesFromNorm allFiles fs) :
    ckx_EntriesFromNorm allFiles
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
    have hanc := ckx_entriesFromNorm_foldl_dirs
      ((Arm64.FsPath.nonEmptyPrefixes (Arm64.normalizePath p)).dropLast) h
    have hset := ckx_entriesFromNorm_setFile hanc (hsub (p, bs) (List.mem_cons_self ..))
    exact ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) hset

private theorem ckx_initFsState_files_mem_norm {inputs : ProcessInputs} {q : String}
    {bs : List (BitVec 8)}
    (h : (initFsState inputs).files q = some (.file bs)) :
    ∃ p, Arm64.normalizePath p = Arm64.normalizePath q ∧ (p, bs) ∈ inputs.files := by
  have hd := ckx_entriesFromNorm_foldl_outer_dirs inputs.dirs (ckx_entriesFromNorm_empty inputs.files)
  have hf := ckx_entriesFromNorm_foldl_files inputs.files (fun _ hx => hx) hd
  unfold Arm64.FsState.files Arm64.FsState.getEntry at h
  split at h
  · cases h
  · exact hf (Arm64.normalizePath q) bs h

private theorem ckx_splitSlash_go_append_slash (cur a b : List Char) :
    Arm64.splitSlash.go cur (a ++ ('/' :: b)) =
      Arm64.splitSlash.go cur a ++ Arm64.splitSlash.go [] b := by
  induction a generalizing cur with
  | nil => rfl
  | cons c cs ih =>
    by_cases hc : c = '/'
    · subst hc; simp only [List.cons_append, Arm64.splitSlash.go, ih []]
    · rw [List.cons_append, Arm64.splitSlash.go.eq_3 cur c (cs ++ '/' :: b) hc,
        Arm64.splitSlash.go.eq_3 cur c cs hc, ih (c :: cur)]

private theorem ckx_normalizePath_append_slash (a b : String) :
    Arm64.normalizePath (a ++ "/" ++ b) = Arm64.normalizePath a ++ Arm64.normalizePath b := by
  have htl : (a ++ "/" ++ b).toList = a.toList ++ ('/' :: b.toList) := by
    simp [String.toList_append]
  unfold Arm64.normalizePath Arm64.splitSlash
  rw [htl, ckx_splitSlash_go_append_slash [] a.toList b.toList, List.filter_append]

private theorem ckx_norm_subdir_ne_ikp {dir sub : String}
    (hdir : Arm64.normalizePath dir = [dir]) (hne : dir ≠ "identity-key-pair") :
    Arm64.normalizePath ((dir ++ "/") ++ sub) ≠ ["identity-key-pair"] := by
  rw [ckx_normalizePath_append_slash dir sub, hdir, List.singleton_append]
  intro h
  injection h with hd _
  exact hne hd

private def ckx_kutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem ckx_utf8_eq_kutf8 (s : String) : utf8 s = ckx_kutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, ckx_kutf8, List.utf8Encode, ckx_byteArray_toList_eq_data]

private theorem ckx_ikp_encode_len_le_105 (P : PEParams) (st : PqParty) :
    (IdentityKeyPairStructure.encode
      ⟨djbKey (keyPairOf P.C st.me.idPriv).publicKey.bytes,
        st.me.idPriv.toList⟩).length ≤ 105 := by
  let pub := djbKey (keyPairOf P.C st.me.idPriv).publicKey.bytes
  let priv := st.me.idPriv.toList
  have hpub_len : pub.length = 33 := by simp [pub, djbKey]
  have hpriv_len : priv.length = 32 := st.me.idPriv.toList_length
  have hpub_ne : pub ≠ [] := by intro h; rw [h] at hpub_len; contradiction
  have hpriv_ne : priv ≠ [] := by intro h; rw [h] at hpriv_len; contradiction
  change (IdentityKeyPairStructure.encode ⟨pub, priv⟩).length ≤ 105
  unfold IdentityKeyPairStructure.encode encodeProto3BytesField encodeBytesField
  simp only [hpub_ne, hpriv_ne, ↓reduceIte, List.length_append, hpub_len, hpriv_len]
  decide

private theorem ckx_cliIo_rd_eq_ok_nil_or_files_some {i : Inputs} {path bs : List (BitVec 8)}
    (hrd : cliIo.rd (runFiles i) path = .ok bs) :
    bs = [] ∨
      (initFsState (cliInputs i)).files (pathStr path) = some (.file bs) := by
  change cliRd (initFsState (cliInputs i)).files path = .ok bs at hrd
  unfold cliRd at hrd; split at hrd
  · cases hrd
  · rename_i rbs hrv; injection hrd with h; subst h
    unfold readViewF at hrv; split at hrv
    · cases hrv
    · injection hrv with h; subst h; exact Or.inl rfl
    · split at hrv
      · rename_i fbs hfp
        split at hrv
        · injection hrv with h; subst h; exact Or.inr hfp
        · cases hrv
      · cases hrv
      · injection hrv with h; subst h; exact Or.inl rfl

private theorem ckx_encodeDir_norm_ikp_len_le_105
    {P : PEParams} {st : PqParty} {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ encodeDir P st)
    (hnorm : Arm64.normalizePath p = ["identity-key-pair"]) :
    bs.length ≤ 105 := by
  unfold encodeDir at hmem
  simp only [List.mem_append] at hmem
  rcases hmem with ((((((hf_hdr | hf_peer) | hf_sess) | hf_sig) | hf_ot) | hf_kot) | hf_klr)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_hdr
    rcases hf_hdr with h | h | h
    · injection h with hp _; subst hp; exact absurd hnorm (by decide)
    · injection h with _ hbs; subst hbs; exact ckx_ikp_encode_len_le_105 P st
    · injection h with hp _; subst hp; exact absurd hnorm (by decide)
  · cases hp : st.peerId with
    | none => simp [hp] at hf_peer
    | some k =>
      simp only [hp, List.mem_singleton] at hf_peer
      injection hf_peer with hp_eq _; subst hp_eq
      exact absurd hnorm (ckx_norm_subdir_ne_ikp (dir := "identities") (by decide) (by decide))
  · cases hs : st.session with
    | none => simp [hs] at hf_sess
    | some xg =>
      rcases xg with ⟨_, _⟩
      simp only [hs, List.mem_singleton] at hf_sess
      injection hf_sess with hp_eq _; subst hp_eq
      exact absurd hnorm (ckx_norm_subdir_ne_ikp (dir := "sessions") (by decide) (by decide))
  · rw [List.mem_map] at hf_sig
    rcases hf_sig with ⟨⟨_, _⟩, _, h⟩
    injection h with hp_eq _; subst hp_eq
    exact absurd hnorm (ckx_norm_subdir_ne_ikp (dir := "signed-pre-keys") (by decide) (by decide))
  · rw [List.mem_map] at hf_ot
    rcases hf_ot with ⟨⟨_, _⟩, _, h⟩
    injection h with hp_eq _; subst hp_eq
    exact absurd hnorm (ckx_norm_subdir_ne_ikp (dir := "one-time-pre-keys") (by decide) (by decide))
  · rw [List.mem_map] at hf_kot
    rcases hf_kot with ⟨⟨_, _⟩, _, h⟩
    injection h with hp_eq _; subst hp_eq
    exact absurd hnorm
      (ckx_norm_subdir_ne_ikp (dir := "one-time-kyber-pre-keys") (by decide) (by decide))
  · rw [List.mem_flatten] at hf_klr
    rcases hf_klr with ⟨sub, hsub, hf_in⟩
    rw [List.mem_map] at hsub
    rcases hsub with ⟨⟨_, _, _⟩, _, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf_in
    rcases hf_in with h1 | h2
    · injection h1 with hp_eq _; subst hp_eq
      exact absurd hnorm
        (ckx_norm_subdir_ne_ikp (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))
    · injection h2 with hp_eq _; subst hp_eq
      unfold baseKeysFile at hnorm
      rw [String.append_assoc] at hnorm
      exact absurd hnorm
        (ckx_norm_subdir_ne_ikp (dir := "last-resort-kyber-pre-keys") (by decide) (by decide))

private theorem ckx_bundle_norm_ne_ikp {b : PreKeyBundleFields}
    {p : String} {bs : List (BitVec 8)}
    (hmem : (p, bs) ∈ (publicBundleOf b).files bundleDir) :
    Arm64.normalizePath p ≠ ["identity-key-pair"] := by
  unfold PublicBundle.files publicBundleOf at hmem
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

/-- Under `CliPqxdhInputs P i`, reading `"identity-key-pair"` from `StoresGhost.opened.identity.own`
yields at most `105` bytes. -/
theorem cliIo_rd_ownIkp_le_105_of_cliPqInputs
    {P : PEParams} {i : Inputs} (hi : CliPqxdhInputs P i) :
    ∀ bs,
      StoresGhost.opened.identity.own.get cliIo.rd (runFiles i) (utf8 "identity-key-pair") =
        .ok bs → bs.length ≤ 105 := by
  intro bs hrd
  change cliIo.rd (runFiles i)
      (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) = .ok bs at hrd
  rcases ckx_cliIo_rd_eq_ok_nil_or_files_some hrd with rfl | hfile
  · exact Nat.zero_le 105
  · have hpth :
        pathStr (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) =
          "identity-key-pair" := by
      change pathStr (utf8 "identity-key-pair") = "identity-key-pair"
      unfold pathStr
      rw [ckx_utf8_eq_kutf8]
      rfl
    rw [hpth] at hfile
    obtain ⟨p, hp_norm, hp_mem⟩ := ckx_initFsState_files_mem_norm hfile
    have hikp_norm : Arm64.normalizePath "identity-key-pair" = ["identity-key-pair"] := by decide
    rw [hikp_norm] at hp_norm
    have hp_files : (p, bs) ∈ i.files := hp_mem
    obtain ⟨st, _, hcase⟩ := hi
    rcases hcase with ⟨_, b, t, rfl⟩ | ⟨_, r, _, rfl⟩ | ⟨_, rc, _, rfl⟩ |
        ⟨_, rc, _, rfl⟩ | ⟨_, rc, _, _, _, rfl⟩
    · simp only [pqInitInputs, pqInputs, List.mem_append, List.mem_singleton] at hp_files
      rcases hp_files with (hed | hbun) | hcoins
      · exact ckx_encodeDir_norm_ikp_len_le_105 hed hp_norm
      · exact absurd hp_norm (ckx_bundle_norm_ne_ikp hbun)
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
    · simp only [pqSendInputs, pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp_files
      rcases hp_files with hed | hcoins
      · exact ckx_encodeDir_norm_ikp_len_le_105 hed hp_norm
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
    · simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp_files
      rcases hp_files with hed | hcoins
      · exact ckx_encodeDir_norm_ikp_len_le_105 hed hp_norm
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
    · simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp_files
      rcases hp_files with hed | hcoins
      · exact ckx_encodeDir_norm_ikp_len_le_105 hed hp_norm
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)
    · simp only [pqRecvInputs, pqInputs, List.append_nil, List.mem_append,
        List.mem_singleton] at hp_files
      rcases hp_files with hed | hcoins
      · exact ckx_encodeDir_norm_ikp_len_le_105 hed hp_norm
      · injection hcoins with hp_c _; subst hp_c; exact absurd hp_norm (by decide)

private theorem ckx_binaryKitSlotInit_imp_w3Fixed [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : RunCall} (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i) :
    ∀ evs, (mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).initEnv evs →
      (match g.c with
       | .init _ _ => fun evs =>
         ∃ w : W3BinaryInitParams,
           W3BinaryInitDom g.c g.i w ∧ W3InitBinaryKitSlotEnvFixed w evs
       | _ => fun _ => False) evs := by
  dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
  rcases g with ⟨gi, gc, ga, gres, gcall, gstores, ginp, gcoins⟩
  intro evs h
  cases gc with
  | keygen _ _ => exact False.elim h
  | send _ => exact False.elim h
  | recv _ => exact False.elim h
  | init peerAddr dir =>
    rcases h with ⟨w, hw, hevs⟩
    exact ⟨w, hw,
      (w3InitBinaryKitSlotEnvFixed_eq_plain hi_g (hw peerAddr dir rfl).2.2.1).symm ▸ hevs⟩

theorem binaryKitSlotInit_credit [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i) :
    PhaseCreditSpec fineCostModel
      ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).initEnv)
      (w3InitRealCum + 4500000) (w3InitRealLive + 65536)
      (w3InitRealPeak + 65536) (w3InitRealMaxReq + 65536) :=
  PhaseCreditSpec.of_imp
    (ckx_binaryKitSlotInit_imp_w3Fixed EncSlot DecSigSlot img S X W hi_g)
    (binaryKitW3Fixed_fineSpec g (cliIo_rd_ownIkp_le_105_of_cliPqInputs hi_g)).credit

theorem binaryKitSlotInit_groups [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i) :
    PhaseGroupSpec fineCostModel
      ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).initEnv)
      (w3InitRealGrpS + 1500 * FineScale) :=
  PhaseGroupSpec.of_imp
    (binaryKitW3Fixed_fineSpec g (cliIo_rd_ownIkp_le_105_of_cliPqInputs hi_g)).groups
    (ckx_binaryKitSlotInit_imp_w3Fixed EncSlot DecSigSlot img S X W hi_g)

/-- `SingleSlotFineSpec` on `(mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).initEnv`
under `CliPqxdhInputs ⟨W.C, W.Q⟩ g.i`. -/
def binaryKitSlotInit_fineSpec [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (g : RunCall) (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i) :
    SingleSlotFineSpec
      ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).initEnv) where
  cum := w3InitRealCum + 4500000
  live := w3InitRealLive + 65536
  peak := w3InitRealPeak + 65536
  maxReq := w3InitRealMaxReq + 65536
  grpS := w3InitRealGrpS + 1500 * FineScale
  credit := binaryKitSlotInit_credit EncSlot DecSigSlot img S X W g hi_g
  live_le_peak :=
    (binaryKitW3Fixed_fineSpec g (cliIo_rd_ownIkp_le_105_of_cliPqInputs hi_g)).live_le_peak
  groups := binaryKitSlotInit_groups EncSlot DecSigSlot img S X W g hi_g

/-! ## Exact-Kit Ceiling Constants -/

def w3InitExactCum : Nat := w3InitRealCum + 4500000
def w3InitExactLive : Nat := w3InitRealLive + 65536
def w3InitExactPeak : Nat := w3InitRealPeak + 65536
def w3InitExactMaxReq : Nat := w3InitRealMaxReq + 65536
def w3InitExactGrpS : Nat := w3InitRealGrpS + 1500 * FineScale

/-- W1 (`send`) Exact-kit ceiling (`maxDecodeOps ≤ 128`, `+45` ops above `83`). -/
def w1EncExactCum : Nat := w1SendRealDcanCum + 45 * 738
def w1EncExactLive : Nat := w1SendRealDcanPeak
def w1EncExactPeak : Nat := w1SendRealDcanPeak
def w1EncExactMaxReq : Nat := w1SendRealDcanMaxReq
def w1EncExactGrpS : Nat := w1SendRealDcanGrpS + 45 * (3 * FineScale)

/-- W2 (`recv` whisper) Exact-kit ceiling (`maxDecodeOps ≤ 128` + `25,000`-jump `CmkSeg4Env`,
covering both `10`-grow tight and `11 * 143,484` bounds without subtracting `oldSeg4`). -/
def w2DecSigExactCum : Nat :=
  w2RecvWhisperRealDcanCum + ((25000 + 2) * 738 + 11 * 143484) + 45 * 738
def w2DecSigExactLive : Nat := w2RecvWhisperRealDcanPeak
def w2DecSigExactPeak : Nat := w2RecvWhisperRealDcanPeak
def w2DecSigExactMaxReq : Nat := w2RecvWhisperRealDcanMaxReq
def w2DecSigExactGrpS : Nat :=
  w2RecvWhisperRealDcanGrpS + ((25000 + 2) * 16659 + 11 * (3 * FineScale)) + 45 * (3 * FineScale)

/-- W4 (`recv-prekey`) Exact-kit ceiling (`d3RecvW4ExtCum + 20,000,000`), covering `0..1`
archived sessions, `25,000`-jump `CmkSeg4Env`, `VerNe-prev1` deserialization, and `maxDecodeOps ≤ 128`. -/
def w4DecPkExactCum : Nat := d3RecvW4ExtCum + 20000000
def w4DecPkExactLive : Nat := d3RecvW4ExtLive
def w4DecPkExactPeak : Nat := d3RecvW4ExtPeak
def w4DecPkExactMaxReq : Nat := 4194368
def w4DecPkExactGrpS : Nat := d3RecvW4ExtGrpS + 2000 * FineScale

def exactMainCumOf (encCum decSigCum decPkCum : Nat) : Nat :=
  let runCum := cliRunBinary1MiBCustomPksmCum
    (pksmCanonSliceCum msgCapBytes) w3InitExactCum encCum decSigCum decPkCum
  123250 + m3PhaseDeltaCum_tight + runCum +
    cliMaxDirtyEntries *
      (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
    m6DeltaCum

def exactMainLiveOf (encLive decSigLive decPkLive : Nat) : Nat :=
  cliMainTightLiveOf
    (cliRun1MiBCustomPksmLive
      (pksmCanonSliceLive msgCapBytes) w3InitExactLive encLive decSigLive decPkLive)

def exactMainPeakOf (encLive encPeak decSigPeak decPkPeak : Nat) : Nat :=
  cliMainTightPeakOf
    (cliRun1MiBCustomPksmLive
      (pksmCanonSliceLive msgCapBytes) w3InitExactLive encLive decSigPeak decPkLive)
    (cliRun1MiBCustomPksmPeak
      (pksmCanonSliceLive msgCapBytes) (pksmCanonSlicePeak msgCapBytes)
      w3InitExactPeak encLive encPeak decSigPeak decPkPeak)
where
  decPkLive := decPkPeak

def exactMainPeakGenOf
    (encLive encPeak decSigLive decSigPeak decPkLive decPkPeak : Nat) : Nat :=
  cliMainTightPeakOf
    (cliRun1MiBCustomPksmLive
      (pksmCanonSliceLive msgCapBytes) w3InitExactLive encLive decSigLive decPkLive)
    (cliRun1MiBCustomPksmPeak
      (pksmCanonSliceLive msgCapBytes) (pksmCanonSlicePeak msgCapBytes)
      w3InitExactPeak encLive encPeak decSigPeak decPkPeak)

def exactMainReqOf (encMaxReq decSigMaxReq decPkMaxReq : Nat) : Nat :=
  max (max (16 * 2048) 16384)
    (cliMainTightReqOf
      (cliRunBinary1MiBCustomPksmMaxReq
        (pksmCanonSliceMaxReq msgCapBytes) w3InitExactMaxReq encMaxReq decSigMaxReq decPkMaxReq))

def exactMainGrpSOf (encGrpS decSigGrpS decPkGrpS : Nat) : Nat :=
  let runGrpS := cliRunOpenedCustomPksmGrpS msgCapBytes
    (pksmCanonSliceGrpS msgCapBytes) w3InitExactGrpS encGrpS decSigGrpS decPkGrpS +
    27 * FineScale
  cliMainWidenedSetupFineGrpS + runGrpS +
    cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale

def exactCeilingMainCum : Nat :=
  exactMainCumOf w1EncExactCum w2DecSigExactCum w4DecPkExactCum

def exactCeilingMainLive : Nat :=
  exactMainLiveOf w1EncExactLive w2DecSigExactLive w4DecPkExactLive

def exactCeilingMainPeak : Nat :=
  exactMainPeakGenOf
    w1EncExactLive w1EncExactPeak
    w2DecSigExactLive w2DecSigExactPeak
    w4DecPkExactLive w4DecPkExactPeak

def exactCeilingMainReq : Nat :=
  exactMainReqOf w1EncExactMaxReq w2DecSigExactMaxReq w4DecPkExactMaxReq

def exactCeilingMainGrpS : Nat :=
  exactMainGrpSOf w1EncExactGrpS w2DecSigExactGrpS w4DecPkExactGrpS

/-- The `@128` + `25,000`-jump + `6`-trial Exact-kit ceiling fits within `1 GiB` RAM and `2 ^ 48` VA. -/
theorem exactCeilingMain_fits_oneGiB :
    234 * FineScale + w3InitExactGrpS ≤
      cliRunOpenedCustomPksmGrpS msgCapBytes
        (pksmCanonSliceGrpS msgCapBytes) w3InitExactGrpS
        w1EncExactGrpS w2DecSigExactGrpS w4DecPkExactGrpS - 15 * FineScale ∧
    cliDecoupledRamNeed cliDefaultStaticBytes
      exactCeilingMainCum exactCeilingMainPeak exactCeilingMainReq
      ((exactCeilingMainGrpS + FineScale - 1) / FineScale) ≤ cliOneGiB ∧
    cliDecoupledVaNeed cliDefaultStaticBytes cliDefaultStaticCount
      exactCeilingMainCum exactCeilingMainPeak exactCeilingMainReq
      ((exactCeilingMainGrpS + FineScale - 1) / FineScale) ≤ 2 ^ 48 := by
  decide

/-! ## Cap-Parametric, Ceiling-Specialized, and Curried `FitsEnv` Theorems -/

private theorem ckx_max_mono {a1 a2 b1 b2 : Nat} (ha : a1 ≤ a2) (hb : b1 ≤ b2) :
    max a1 b1 ≤ max a2 b2 :=
  Nat.max_le.mpr ⟨Nat.le_trans ha (Nat.le_max_left _ _), Nat.le_trans hb (Nat.le_max_right _ _)⟩

private theorem ckx_optStage_phaseCredit {P : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec fineCostModel P c l p r) :
    PhaseCreditSpec fineCostModel (OptStageEnv P) c l p r :=
  phaseCredit_or_freeOnly_left fineCostModel_modelHyps (fun _ hf => hf) h

private theorem ckx_optStage_groupSpec {P : List AllocEvent → Prop} {g : Nat}
    (h : PhaseGroupSpec fineCostModel P g) :
    PhaseGroupSpec fineCostModel (OptStageEnv P) g :=
  ((PhaseGroupSpec.freeOnly fineCostModel).or h).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private def ckx_slotCalleeFineSpecs [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : RunCall}
    (Senc : SingleSlotFineSpec
      ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).encEnv))
    (Sds : SingleSlotFineSpec
      ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decSigEnv))
    (Spk : SingleSlotFineSpec
      ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decPkEnv))
    (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i) :
    CliRealCalleeFineSpecs
      (mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g) where
  initCum := w3InitExactCum
  initLive := w3InitExactLive
  initPeak := w3InitExactPeak
  initMaxReq := w3InitExactMaxReq
  initGrpS := w3InitExactGrpS
  init_spec := (binaryKitSlotInit_fineSpec EncSlot DecSigSlot img S X W g hi_g).credit
  init_lp := (binaryKitSlotInit_fineSpec EncSlot DecSigSlot img S X W g hi_g).live_le_peak
  init_grp := (binaryKitSlotInit_fineSpec EncSlot DecSigSlot img S X W g hi_g).groups
  encCum := Senc.cum
  encLive := Senc.live
  encPeak := Senc.peak
  encMaxReq := Senc.maxReq
  encGrpS := Senc.grpS
  enc_spec := Senc.credit
  enc_lp := Senc.live_le_peak
  enc_grp := Senc.groups
  decSigCum := Sds.cum
  decSigLive := Sds.live
  decSigPeak := Sds.peak
  decSigMaxReq := Sds.maxReq
  decSigGrpS := Sds.grpS
  decSig_spec := Sds.credit
  decSig_lp := Sds.live_le_peak
  decSig_grp := Sds.groups
  pksmCum := pksmCanonSliceCum msgCapBytes
  pksmLive := pksmCanonSliceLive msgCapBytes
  pksmPeak := pksmCanonSlicePeak msgCapBytes
  pksmMaxReq := pksmCanonSliceMaxReq msgCapBytes
  pksmGrpS := pksmCanonSliceGrpS msgCapBytes
  pksm_spec := fun _ hrest => pksmCanonSlice_fine_phaseCredit hrest
  pksm_lp := pksmCanonSliceLive_le_peak msgCapBytes
  pksm_grp := fun _ hrest => pksmCanonSlice_fine_groupSpec hrest
  decPkCum := Spk.cum
  decPkLive := Spk.live
  decPkPeak := Spk.peak
  decPkMaxReq := Spk.maxReq
  decPkGrpS := Spk.grpS
  decPk_spec := Spk.credit
  decPk_lp := Spk.live_le_peak
  decPk_grp := Spk.groups

private theorem ckx_slotCalleeFineSpecs_bounds [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {g : RunCall}
    (Senc : SingleSlotFineSpec
      ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).encEnv))
    (Sds : SingleSlotFineSpec
      ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decSigEnv))
    (Spk : SingleSlotFineSpec
      ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decPkEnv))
    {encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
     decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS : Nat}
    (hEnc : Senc.cum ≤ encCum ∧ Senc.live ≤ encLive ∧ Senc.peak ≤ encPeak ∧
      Senc.maxReq ≤ encMaxReq ∧ Senc.grpS ≤ encGrpS)
    (hDs : Sds.cum ≤ decSigCum ∧ Sds.live ≤ decSigLive ∧ Sds.peak ≤ decSigPeak ∧
      Sds.maxReq ≤ decSigMaxReq ∧ Sds.grpS ≤ decSigGrpS)
    (hPk : Spk.cum ≤ decPkCum ∧ Spk.live ≤ decPkLive ∧ Spk.peak ≤ decPkPeak ∧
      Spk.maxReq ≤ decPkMaxReq ∧ Spk.grpS ≤ decPkGrpS)
    (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i) :
    let SE := ckx_slotCalleeFineSpecs EncSlot DecSigSlot img S X W Senc Sds Spk hi_g
    cliRunBinary1MiBCustomPksmCum
      SE.pksmCum SE.initCum SE.encCum SE.decSigCum SE.decPkCum ≤
      cliRunBinary1MiBCustomPksmCum
        (pksmCanonSliceCum msgCapBytes) w3InitExactCum encCum decSigCum decPkCum ∧
    cliRun1MiBCustomPksmLive
      SE.pksmLive SE.initLive SE.encLive SE.decSigLive SE.decPkLive ≤
      cliRun1MiBCustomPksmLive
        (pksmCanonSliceLive msgCapBytes) w3InitExactLive encLive decSigLive decPkLive ∧
    cliRun1MiBCustomPksmPeak
      SE.pksmLive SE.pksmPeak SE.initPeak SE.encLive SE.encPeak SE.decSigPeak SE.decPkPeak ≤
      cliRun1MiBCustomPksmPeak
        (pksmCanonSliceLive msgCapBytes) (pksmCanonSlicePeak msgCapBytes)
        w3InitExactPeak encLive encPeak decSigPeak decPkPeak ∧
    cliRunBinary1MiBCustomPksmMaxReq
      SE.pksmMaxReq SE.initMaxReq SE.encMaxReq SE.decSigMaxReq SE.decPkMaxReq ≤
      cliRunBinary1MiBCustomPksmMaxReq
        (pksmCanonSliceMaxReq msgCapBytes) w3InitExactMaxReq encMaxReq decSigMaxReq decPkMaxReq ∧
    cliRunOpenedCustomPksmGrpS msgCapBytes
      SE.pksmGrpS SE.initGrpS SE.encGrpS SE.decSigGrpS SE.decPkGrpS ≤
      cliRunOpenedCustomPksmGrpS msgCapBytes
        (pksmCanonSliceGrpS msgCapBytes) w3InitExactGrpS encGrpS decSigGrpS decPkGrpS := by
  rcases hEnc with ⟨hec, hel, hep, her, heg⟩
  rcases hDs with ⟨hdc, hdl, hdp, hdr, hdg⟩
  rcases hPk with ⟨hpc, hpl, hpp, hpr, hpg⟩
  dsimp only [ckx_slotCalleeFineSpecs]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold cliRunBinary1MiBCustomPksmCum
    exact Nat.add_le_add (Nat.le_refl _)
      (ckx_max_mono (Nat.le_refl _)
        (ckx_max_mono (Nat.add_le_add hec (Nat.le_refl _))
          (ckx_max_mono (Nat.add_le_add (Nat.le_refl _) hdc)
            (Nat.add_le_add (Nat.le_refl _) hpc))))
  · unfold cliRun1MiBCustomPksmLive
    have hr2l :
        CliRunArmsPeak.r2DeltaLive fineCostModel Senc.live sessionCapBytes ≤
          CliRunArmsPeak.r2DeltaLive fineCostModel encLive sessionCapBytes := by
      unfold CliRunArmsPeak.r2DeltaLive
      exact Nat.add_le_add hel (Nat.le_refl _)
    exact Nat.add_le_add (Nat.le_refl _)
      (ckx_max_mono (Nat.le_refl _)
        (ckx_max_mono hr2l
          (ckx_max_mono (Nat.add_le_add (Nat.le_refl _) hdl)
            (Nat.add_le_add (Nat.le_refl _) hpl))))
  · unfold cliRun1MiBCustomPksmPeak
    have hr2p :
        CliRunArmsPeak.r2DeltaPeak fineCostModel Senc.live Senc.peak sessionCapBytes ≤
          CliRunArmsPeak.r2DeltaPeak fineCostModel encLive encPeak sessionCapBytes := by
      unfold CliRunArmsPeak.r2DeltaPeak
      exact ckx_max_mono hep (Nat.add_le_add hel (Nat.le_refl _))
    exact ckx_max_mono (Nat.le_refl _)
      (Nat.add_le_add (Nat.le_refl _)
        (ckx_max_mono (Nat.le_refl _)
          (ckx_max_mono hr2p
            (ckx_max_mono (ckx_max_mono (Nat.le_refl _) (Nat.add_le_add (Nat.le_refl _) hdp))
              (ckx_max_mono (Nat.le_refl _) (Nat.add_le_add (Nat.le_refl _) hpp))))))
  · unfold cliRunBinary1MiBCustomPksmMaxReq
    have hr2r :
        CliRunArmsPeak.r2MaxReq Senc.maxReq sessionCapBytes ≤
          CliRunArmsPeak.r2MaxReq encMaxReq sessionCapBytes := by
      unfold CliRunArmsPeak.r2MaxReq
      exact ckx_max_mono her (Nat.le_refl _)
    exact ckx_max_mono (Nat.le_refl _)
      (ckx_max_mono (Nat.le_refl _)
        (ckx_max_mono hr2r
          (ckx_max_mono (ckx_max_mono (Nat.le_refl _) hdr)
            (ckx_max_mono (Nat.le_refl _) hpr))))
  · unfold cliRunOpenedCustomPksmGrpS
    exact Nat.add_le_add (Nat.le_refl _)
      (ckx_max_mono (Nat.le_refl _)
        (ckx_max_mono (Nat.add_le_add heg (Nat.le_refl _))
          (ckx_max_mono (Nat.add_le_add (Nat.le_refl _) hdg)
            (Nat.add_le_add (Nat.le_refl _) hpg))))

/-- Cap-parametric whole-`main` `FitsEnv fineCostModel` on
`realCliMainBinaryKitEnvOfSlot EncSlot DecSigSlot img S X W i` for arbitrary slot caps and
`SingleSlotFineSpec` witnesses. -/
theorem realCliMainBinaryKitEnvOfSlot_fitsEnv_of_caps [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    {encCum encLive encPeak encMaxReq encGrpS
     decSigCum decSigLive decSigPeak decSigMaxReq decSigGrpS
     decPkCum decPkLive decPkPeak decPkMaxReq decPkGrpS : Nat}
    (S_enc : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).encEnv))
    (S_decSig : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decSigEnv))
    (S_decPk : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decPkEnv))
    (hEncCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      let se := S_enc g hi_g hparse
      se.cum ≤ encCum ∧ se.live ≤ encLive ∧ se.peak ≤ encPeak ∧
      se.maxReq ≤ encMaxReq ∧ se.grpS ≤ encGrpS)
    (hDecSigCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      let sd := S_decSig g hi_g hparse
      sd.cum ≤ decSigCum ∧ sd.live ≤ decSigLive ∧ sd.peak ≤ decSigPeak ∧
      sd.maxReq ≤ decSigMaxReq ∧ sd.grpS ≤ decSigGrpS)
    (hDecPkCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      let sp := S_decPk g hi_g hparse
      sp.cum ≤ decPkCum ∧ sp.live ≤ decPkLive ∧ sp.peak ≤ decPkPeak ∧
      sp.maxReq ≤ decPkMaxReq ∧ sp.grpS ≤ decPkGrpS)
    (hinit_grp :
      234 * FineScale + w3InitExactGrpS ≤
        cliRunOpenedCustomPksmGrpS msgCapBytes
          (pksmCanonSliceGrpS msgCapBytes) w3InitExactGrpS encGrpS decSigGrpS decPkGrpS -
        15 * FineScale)
    (hram :
      cliDecoupledRamNeed lim.staticBytes
        (exactMainCumOf encCum decSigCum decPkCum)
        (exactMainPeakGenOf encLive encPeak decSigLive decSigPeak decPkLive decPkPeak)
        (exactMainReqOf encMaxReq decSigMaxReq decPkMaxReq)
        ((exactMainGrpSOf encGrpS decSigGrpS decPkGrpS + FineScale - 1) / FineScale) ≤
      lim.physCap)
    (hva :
      cliDecoupledVaNeed lim.staticBytes lim.staticCount
        (exactMainCumOf encCum decSigCum decPkCum)
        (exactMainPeakGenOf encLive encPeak decSigLive decSigPeak decPkLive decPkPeak)
        (exactMainReqOf encMaxReq decSigMaxReq decPkMaxReq)
        ((exactMainGrpSOf encGrpS decSigGrpS decPkGrpS + FineScale - 1) / FineScale) ≤
      2 ^ 48) :
    ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel lim fineCostModel.init
        (realCliMainBinaryKitEnvOfSlot EncSlot DecSigSlot img S X W i) := by
  intro i hi
  let rCum := cliRunBinary1MiBCustomPksmCum
    (pksmCanonSliceCum msgCapBytes) w3InitExactCum encCum decSigCum decPkCum
  let rLive := cliRun1MiBCustomPksmLive
    (pksmCanonSliceLive msgCapBytes) w3InitExactLive encLive decSigLive decPkLive
  let rPeak := cliRun1MiBCustomPksmPeak
    (pksmCanonSliceLive msgCapBytes) (pksmCanonSlicePeak msgCapBytes)
    w3InitExactPeak encLive encPeak decSigPeak decPkPeak
  let rMaxReq := cliRunBinary1MiBCustomPksmMaxReq
    (pksmCanonSliceMaxReq msgCapBytes) w3InitExactMaxReq encMaxReq decSigMaxReq decPkMaxReq
  let rGrpS := cliRunOpenedCustomPksmGrpS msgCapBytes
    (pksmCanonSliceGrpS msgCapBytes) w3InitExactGrpS encGrpS decSigGrpS decPkGrpS
  have hsm1024 :
      1024 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    decide
  have hw (w : ValidPostSetupWitness i) : PhaseCreditSpec fineCostModel
      (SeqEnv
        (CliRunBinaryEnv cliIo.rd
          (mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W w.g)
          sessionCapBytes w.g)
        (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
      (rCum + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
        m6DeltaCum)
      rLive
      (max rPeak
        (rLive + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max rMaxReq
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) := by
    have hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ w.g.i := w.g_i.symm ▸ hi
    let Senc := S_enc w.g hi_g w.parse_ok
    let Sds := S_decSig w.g hi_g w.parse_ok
    let Spk := S_decPk w.g hi_g w.parse_ok
    let SE := ckx_slotCalleeFineSpecs EncSlot DecSigSlot img S X W Senc Sds Spk hi_g
    obtain ⟨h1, h2, h3, h4, _⟩ :=
      ckx_slotCalleeFineSpecs_bounds EncSlot DecSigSlot img S X W Senc Sds Spk
        (hEncCaps w.g hi_g w.parse_ok)
        (hDecSigCaps w.g hi_g w.parse_ok)
        (hDecPkCaps w.g hi_g w.parse_ok) hi_g
    have hrun :=
      (cliRunBinaryEnv_real_1MiB_fine_phaseCredit_of_cliPqInputs
        SE hi_g w.stdin_le w.parse_ok).mono h1 h2 h3 h4
    refine (hrun.seq
      ((m5Phase_Bounded_phaseCredit_fine w.dirs_sum_le w.dirs_bounds).seq
        (m6_phaseCredit_small1024 fineCostModel_modelHyps hsm1024 w.ok))).mono ?_ ?_ ?_ ?_
    · rw [Nat.add_assoc]; exact Nat.le_refl _
    · simp only [Nat.add_zero]; exact Nat.le_refl _
    · exact ckx_max_mono (Nat.le_refl _)
        (Nat.add_le_add_left (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩) _)
    · exact ckx_max_mono (Nat.le_refl _) (Nat.le_of_eq (Nat.max_comm _ _))
  have hex : PhaseCreditSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv
          (CliRunBinaryEnv cliIo.rd
            (mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W w.g)
            sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      (rCum + cliMaxDirtyEntries *
        (10 * max (4 * cliMaxDirPathBytes + cliMaxAddrTextBytes + 16) 16 + 4 * 9539) +
        m6DeltaCum)
      rLive
      (max rPeak
        (rLive + m5DirStepDeltaPeak cliMaxDirPathBytes cliMaxAddrTextBytes))
      (max rMaxReq
        (max 1024 (m5DirStepMaxReq cliMaxDirPathBytes cliMaxAddrTextBytes))) :=
    { req_align := fun evs ⟨w, _, hseq⟩ ev hev => (hw w).req_align evs hseq ev hev
      credit_le := fun st0 {_} ⟨w, _, hseq⟩ => (hw w).credit_le st0 hseq }
  have hcr : PhaseCreditSpec fineCostModel
      (realCliMainBinaryKitEnvOfSlot EncSlot DecSigSlot img S X W i)
      (exactMainCumOf encCum decSigCum decPkCum)
      (exactMainLiveOf encLive decSigLive decPkLive)
      (exactMainPeakGenOf encLive encPeak decSigLive decSigPeak decPkLive decPkPeak)
      (exactMainReqOf encMaxReq decSigMaxReq decPkMaxReq) := by
    refine ((cliMainBoundedSetup_phaseCredit_fine
        (argv_length_le_of_cliPqInputs hi)).seq
      (ckx_optStage_phaseCredit hex)).mono ?_ ?_ ?_ ?_
    · unfold exactMainCumOf
      dsimp only [rCum]
      simp only [Nat.add_assoc]
      exact Nat.le_refl _
    · unfold exactMainLiveOf cliMainTightLiveOf cliMainDeltaLive_tight
      exact Nat.le_refl _
    · unfold exactMainPeakGenOf cliMainTightPeakOf cliMainDeltaPeak_tight
      exact Nat.le_refl _
    · unfold exactMainReqOf cliMainTightReqOf cliMainMaxReq
      have h16k :
          max 16384 (m3PhaseMaxReq msgCapBytes sessionCapBytes) =
          m3PhaseMaxReq msgCapBytes sessionCapBytes := by
        unfold m3PhaseMaxReq msgCapBytes sessionCapBytes
        decide
      rw [h16k]
      exact Nat.le_max_right _ _
  have hex_grp : PhaseGroupSpec fineCostModel
      (fun evs' => ∃ w : ValidPostSetupWitness i, w.g.i = i ∧
        SeqEnv
          (CliRunBinaryEnv cliIo.rd
            (mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W w.g)
            sessionCapBytes w.g)
          (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)) evs')
      ((rGrpS + 27 * FineScale) +
        cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
    { groups_le := fun st0 {_} ⟨w, _, hseq⟩ => by
        have hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ w.g.i := w.g_i.symm ▸ hi
        let Senc := S_enc w.g hi_g w.parse_ok
        let Sds := S_decSig w.g hi_g w.parse_ok
        let Spk := S_decPk w.g hi_g w.parse_ok
        let SE := ckx_slotCalleeFineSpecs EncSlot DecSigSlot img S X W Senc Sds Spk hi_g
        obtain ⟨_, _, _, _, h5⟩ :=
          ckx_slotCalleeFineSpecs_bounds EncSlot DecSigSlot img S X W Senc Sds Spk
            (hEncCaps w.g hi_g w.parse_ok)
            (hDecSigCaps w.g hi_g w.parse_ok)
            (hDecPkCaps w.g hi_g w.parse_ok) hi_g
        have h15 : 15 * FineScale ≤ rGrpS := by
          dsimp only [rGrpS]
          unfold cliRunOpenedCustomPksmGrpS
          exact Nat.le_add_right (15 * FineScale) _
        have hinit_sub : 234 * FineScale + SE.initGrpS ≤ rGrpS - 15 * FineScale := hinit_grp
        have hrun := cliRunBinaryEnv_fine_groupSpec_of_cap SE w.stdin_le h15 hinit_sub h5
        have hm5 := (m5PhaseEnv_groupSpec fineCostModel w.dirs).mono
          (Nat.mul_le_mul_right (12 * FineScale) w.dirs_sum_le)
        have htot : PhaseGroupSpec fineCostModel
            (SeqEnv
              (CliRunBinaryEnv cliIo.rd
                (mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W w.g)
                sessionCapBytes w.g)
              (SeqEnv (M5PhaseEnv w.dirs) (M6Env w.ok)))
            ((rGrpS + 27 * FineScale) +
              cliMaxDirtyEntries * (12 * FineScale) + 3 * FineScale) :=
          (hrun.seq (hm5.seq (m6Env_groupSpec fineCostModel w.ok))).mono
            (by generalize FineScale = fs; omega)
        exact htot.groups_le st0 hseq }
  have hgrp : PhaseGroupSpec fineCostModel
      (realCliMainBinaryKitEnvOfSlot EncSlot DecSigSlot img S X W i)
      (exactMainGrpSOf encGrpS decSigGrpS decPkGrpS) :=
    ((cliMainBoundedSetup_fine_groupSpec
        (argv_length_le_of_cliPqInputs hi)).seq
      (ckx_optStage_groupSpec hex_grp)).mono
      (by unfold exactMainGrpSOf
          dsimp only [rGrpS]
          generalize FineScale = fs; omega)
  have hlp :
      exactMainLiveOf encLive decSigLive decPkLive ≤
      exactMainPeakGenOf encLive encPeak decSigLive decSigPeak decPkLive decPkPeak := by
    unfold exactMainLiveOf exactMainPeakGenOf
      cliMainTightLiveOf cliMainTightPeakOf cliMainDeltaLive_tight cliMainDeltaPeak_tight
    exact Nat.le_trans
      (Nat.add_le_add_left (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)) _)
      (Nat.le_max_right _ _)
  exact fitsEnv_fineCostModel_of_group_literal_bounds hcr hgrp
    (Nat.le_refl _) hlp (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) henf hram hva

/-- `SingleSlotFineSpec`-parametric whole-`main` `FitsEnv fineCostModel` at the Exact-kit
ceiling under `1 GiB` `BudgetLimits`. -/
theorem realCliMainBinaryKitEnvOfSlot_fitsEnv_of_slotSpecs [LibsignalPlacement]
    {lim : BudgetLimits}
    (henf : lim.enforced = true)
    (hsb : lim.staticBytes ≤ cliDefaultStaticBytes)
    (hsc : lim.staticCount ≤ cliDefaultStaticCount)
    (hcap1G : cliOneGiB ≤ lim.physCap)
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (S_enc : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).encEnv))
    (S_decSig : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decSigEnv))
    (S_decPk : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decPkEnv))
    (hEncCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      let se := S_enc g hi_g hparse
      se.cum ≤ w1EncExactCum ∧ se.live ≤ w1EncExactLive ∧ se.peak ≤ w1EncExactPeak ∧
      se.maxReq ≤ w1EncExactMaxReq ∧ se.grpS ≤ w1EncExactGrpS)
    (hDecSigCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      let sd := S_decSig g hi_g hparse
      sd.cum ≤ w2DecSigExactCum ∧ sd.live ≤ w2DecSigExactLive ∧ sd.peak ≤ w2DecSigExactPeak ∧
      sd.maxReq ≤ w2DecSigExactMaxReq ∧ sd.grpS ≤ w2DecSigExactGrpS)
    (hDecPkCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      let sp := S_decPk g hi_g hparse
      sp.cum ≤ w4DecPkExactCum ∧ sp.live ≤ w4DecPkExactLive ∧ sp.peak ≤ w4DecPkExactPeak ∧
      sp.maxReq ≤ w4DecPkExactMaxReq ∧ sp.grpS ≤ w4DecPkExactGrpS) :
    ∀ i : Inputs, CliPqxdhInputs ⟨W.C, W.Q⟩ i →
      FitsEnv fineCostModel lim fineCostModel.init
        (realCliMainBinaryKitEnvOfSlot EncSlot DecSigSlot img S X W i) := by
  obtain ⟨hinit_grp, hram0, hva0⟩ := exactCeilingMain_fits_oneGiB
  have hram :
      cliDecoupledRamNeed lim.staticBytes
        exactCeilingMainCum exactCeilingMainPeak exactCeilingMainReq
        ((exactCeilingMainGrpS + FineScale - 1) / FineScale) ≤ lim.physCap :=
    Nat.le_trans
      (cliDecoupledRamNeed_mono hsb
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      (Nat.le_trans hram0 hcap1G)
  have hva :
      cliDecoupledVaNeed lim.staticBytes lim.staticCount
        exactCeilingMainCum exactCeilingMainPeak exactCeilingMainReq
        ((exactCeilingMainGrpS + FineScale - 1) / FineScale) ≤ 2 ^ 48 :=
    Nat.le_trans
      (cliDecoupledVaNeed_mono hsb hsc
        (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _))
      hva0
  exact realCliMainBinaryKitEnvOfSlot_fitsEnv_of_caps henf
    EncSlot DecSigSlot img S X W S_enc S_decSig S_decPk
    hEncCaps hDecSigCaps hDecPkCaps hinit_grp hram hva

/-- Specialization of `realCliMainBinaryKitEnvOfSlot_fitsEnv_of_slotSpecs` to `cliBudgetLimits`. -/
theorem realCliMainBinaryKitEnvOfSlot_fitsEnv_cliBudgetLimits_of_slotSpecs [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (S_enc : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).encEnv))
    (S_decSig : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decSigEnv))
    (S_decPk : ∀ (g : RunCall),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c →
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decPkEnv))
    (hEncCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      let se := S_enc g hi_g hparse
      se.cum ≤ w1EncExactCum ∧ se.live ≤ w1EncExactLive ∧ se.peak ≤ w1EncExactPeak ∧
      se.maxReq ≤ w1EncExactMaxReq ∧ se.grpS ≤ w1EncExactGrpS)
    (hDecSigCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      let sd := S_decSig g hi_g hparse
      sd.cum ≤ w2DecSigExactCum ∧ sd.live ≤ w2DecSigExactLive ∧ sd.peak ≤ w2DecSigExactPeak ∧
      sd.maxReq ≤ w2DecSigExactMaxReq ∧ sd.grpS ≤ w2DecSigExactGrpS)
    (hDecPkCaps : ∀ (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c),
      let sp := S_decPk g hi_g hparse
      sp.cum ≤ w4DecPkExactCum ∧ sp.live ≤ w4DecPkExactLive ∧ sp.peak ≤ w4DecPkExactPeak ∧
      sp.maxReq ≤ w4DecPkExactMaxReq ∧ sp.grpS ≤ w4DecPkExactGrpS) :
    realCliMainBinaryKitEnvOfSlot_fitsEnv_cliBudgetLimits_Stmt
      EncSlot DecSigSlot img S X W :=
  realCliMainBinaryKitEnvOfSlot_fitsEnv_of_slotSpecs
    rfl (Nat.le_refl _) (Nat.le_refl _) (by unfold cliBudgetLimits cliOneGiB; decide)
    EncSlot DecSigSlot img S X W S_enc S_decSig S_decPk
    hEncCaps hDecSigCaps hDecPkCaps

/-- Unpacks the `.send` and `.recv` call-site wrappers of `mkBinaryKitRealCalleeEnvsSlotOf`
into curried `PhaseCreditSpec` and `PhaseGroupSpec` obligations. -/
theorem realCliMainBinaryKitEnvOfSlot_fitsEnv_cliBudgetLimits_of_curried [LibsignalPlacement]
    (EncSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → EncGhost → List AllocEvent → Prop)
    (DecSigSlot : ∀ {M : AllocCostModel},
      RustCliAllocBudget M → RunBudgets → DecSigGhost → List AllocEvent → Prop)
    (img : Image) (S : RunSem) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (hEncCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseCreditSpec fineCostModel (EncSlot A w1R.B w1R.x)
        w1EncExactCum w1EncExactLive w1EncExactPeak w1EncExactMaxReq)
    (hEncGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w1R : W1BinarySendParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) →
      g.c = .send peerV →
      w1R.repAlloc = A.repAlloc →
      W1BinarySendDom (.send peerV) g.i w1R →
      PhaseGroupSpec fineCostModel (EncSlot A w1R.B w1R.x) w1EncExactGrpS)
    (hDecSigCredit : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseCreditSpec fineCostModel (DecSigSlot A w2R.B w2R.x)
        w2DecSigExactCum w2DecSigExactLive w2DecSigExactPeak w2DecSigExactMaxReq)
    (hDecSigGrp : ∀ (g : RunCall) (peerV : AddrV) (M : AllocCostModel)
      (A : RustCliAllocBudget M) (w2R : W2BinaryWhisperParams),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      w2R.repAlloc = A.repAlloc →
      W2BinaryWhisperDom (.recv peerV) g.i w2R →
      PhaseGroupSpec fineCostModel (DecSigSlot A w2R.B w2R.x) w2DecSigExactGrpS)
    (hDecPkCredit : ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      pksmParse rest = some pm →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PhaseCreditSpec fineCostModel
        (cliDecPkCanonSlotEnvExact X W (r3bDecPkGhost g meV peerV pm))
        w4DecPkExactCum w4DecPkExactLive w4DecPkExactPeak w4DecPkExactMaxReq)
    (hDecPkGrp : ∀ (g : RunCall) (peerV meV : AddrV) (rest : List (BitVec 8))
      (pm : PreKeySignalMessage),
      CliPqxdhInputs ⟨W.C, W.Q⟩ g.i →
      parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) →
      g.c = .recv peerV →
      g.i.stdin = 3#8 :: rest →
      pksmParse rest = some pm →
      pm.message.ciphertext.length ≤ msgCapBytes →
      PhaseGroupSpec fineCostModel
        (cliDecPkCanonSlotEnvExact X W (r3bDecPkGhost g meV peerV pm))
        w4DecPkExactGrpS) :
    realCliMainBinaryKitEnvOfSlot_fitsEnv_cliBudgetLimits_Stmt
      EncSlot DecSigSlot img S X W := by
  let S_enc (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).encEnv) :=
    { cum := w1EncExactCum
      live := w1EncExactLive
      peak := w1EncExactPeak
      maxReq := w1EncExactMaxReq
      grpS := w1EncExactGrpS
      credit := by
        dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | recv _ =>
          exact (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        | send peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) :=
            hgc ▸ hparse
          exact
            { req_align := fun evs ⟨M, A, w1R, hrep, hdom, he⟩ =>
                (hEncCredit g peerV M A w1R hi_g hp hgc hrep hdom).req_align evs he
              credit_le := fun st0 {_} ⟨M, A, w1R, hrep, hdom, he⟩ =>
                (hEncCredit g peerV M A w1R hi_g hp hgc hrep hdom).credit_le st0 he }
      live_le_peak := Nat.le_refl _
      groups := by
        dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | recv _ =>
          exact (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _)
        | send peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.send peerV) :=
            hgc ▸ hparse
          exact
            { groups_le := fun st0 {_} ⟨M, A, w1R, hrep, hdom, he⟩ =>
                (hEncGrp g peerV M A w1R hi_g hp hgc hrep hdom).groups_le st0 he } }
  let S_decSig (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decSigEnv) :=
    { cum := w2DecSigExactCum
      live := w2DecSigExactLive
      peak := w2DecSigExactPeak
      maxReq := w2DecSigExactMaxReq
      grpS := w2DecSigExactGrpS
      credit := by
        dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | send _ =>
          exact (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        | recv peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
            hgc ▸ hparse
          exact
            { req_align := fun evs ⟨M, A, w2R, hrep, hdom, he⟩ =>
                (hDecSigCredit g peerV M A w2R hi_g hp hgc hrep hdom).req_align evs he
              credit_le := fun st0 {_} ⟨M, A, w2R, hrep, hdom, he⟩ =>
                (hDecSigCredit g peerV M A w2R hi_g hp hgc hrep hdom).credit_le st0 he }
      live_le_peak := Nat.le_refl _
      groups := by
        dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | send _ =>
          exact (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _)
        | recv peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
            hgc ▸ hparse
          exact
            { groups_le := fun st0 {_} ⟨M, A, w2R, hrep, hdom, he⟩ =>
                (hDecSigGrp g peerV M A w2R hi_g hp hgc hrep hdom).groups_le st0 he } }
  let S_decPk (g : RunCall)
      (hi_g : CliPqxdhInputs ⟨W.C, W.Q⟩ g.i)
      (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c) :
      SingleSlotFineSpec
        ((mkBinaryKitRealCalleeEnvsSlotOf EncSlot DecSigSlot img S X W g).decPkEnv) :=
    { cum := w4DecPkExactCum
      live := w4DecPkExactLive
      peak := w4DecPkExactPeak
      maxReq := w4DecPkExactMaxReq
      grpS := w4DecPkExactGrpS
      credit := by
        dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | send _ =>
          exact (PhaseCreditSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        | recv peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
            hgc ▸ hparse
          exact
            { req_align := fun evs ⟨meV, rest, pm, hst, hpk, hct, he⟩ =>
                (hDecPkCredit g peerV meV rest pm hi_g hp hgc hst hpk hct).req_align evs he
              credit_le := fun st0 {_} ⟨meV, rest, pm, hst, hpk, hct, he⟩ =>
                (hDecPkCredit g peerV meV rest pm hi_g hp hgc hst hpk hct).credit_le st0 he }
      live_le_peak := d3RecvW4Ext_live_le_peak
      groups := by
        dsimp only [mkBinaryKitRealCalleeEnvsSlotOf]
        cases hgc : g.c with
        | keygen _ _ | init _ _ | send _ =>
          exact (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => False.elim h)
            |>.mono (Nat.zero_le _)
        | recv peerV =>
          have hp : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some (.recv peerV) :=
            hgc ▸ hparse
          exact
            { groups_le := fun st0 {_} ⟨meV, rest, pm, hst, hpk, hct, he⟩ =>
                (hDecPkGrp g peerV meV rest pm hi_g hp hgc hst hpk hct).groups_le st0 he } }
  exact realCliMainBinaryKitEnvOfSlot_fitsEnv_cliBudgetLimits_of_slotSpecs
    EncSlot DecSigSlot img S X W S_enc S_decSig S_decPk
    (fun _ _ _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ _ _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ _ _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)

end LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact
