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
public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
public import LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
public import LibsignalBinary.Proofs.PeakBudget.W1EncryptCalleesPeak
public import LibsignalBinary.Proofs.PeakBudget.W1EncryptPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak
public import LibsignalBinary.Proofs.PeakBudget.W3InitiateEnvBridges
public import LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySpec
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget

/-!
# Whole-`signal_session::run` Live-Heap Peak and Credit Interface

Composes `CliRunPeakHelpers`, `CliRunArmsPeak`, and the four stateful slot peak specifications
into the binary-order (`R0 → Arm → Join`) `CliRunTightEnv` envelope over `cliIo.rd`, proves
symbolic and `fineCostModel` `PhaseCreditSpec` / `FitsEnv` bounds, plugs into `CliMainPeakSpec`,
and evaluates closed-form `1 MiB` / `2 MiB` constants.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec

open Arm64 Arm64.Process
open CryptoGames.LibsignalSession (Crypto OutgoingTripleRatchet SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord execOk)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (recGhostOf)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (PreKeyMsgNewCall WithStoresEncGhost storedRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliPqxdhInputs Inputs)
open CryptoVerification.SignalSession.Cli
  (DirGhost ReadRule StoresGhost addressText cliInputs pathOf utf8)
open CryptoVerification.SignalSession.Cli.KitInst (cliIdentityStoreSpec cliSessionStoreSpec)
open CryptoVerification.SignalSession.Cli.MainHops
  (AddrV AddressCall CallV RunCall cliIo cliRd parseArgs pathStr readViewF)
open CryptoVerification.SignalSession.Cli.RunCompose
  (DecPkGhost DecSigGhost EncGhost InitGhost PksmGhost RunSem addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1IdKit w1SessKit)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (FilesOkPeer scopeIn scopeKit)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineCostModel_smallMaxReq_eq fineDynIvsOfCum fineStepReserveOfCum)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (CliPqDomainCaps DirDomainCaps FilesBounded dirDomainCaps_opened_own)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (CliMainEnv cliMainDeltaCum cliMainDeltaLive cliMainDeltaPeak cliMainMaxReq cliMain_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (BundleReadEnv CliRunCalleeEnvs CliRunEnv CliRunOfR0Env CliRunOpenedEnv CliRunSlotCalleeSpecs
   CliRunTightHyps CliRunWrapperEnvs CliRunWrapperSlotSpecs InitArmEnv InitBundlePathsSpec JoinEnv
   PksmTryFromSliceEnv R0Env R0OpenedEnv R1aEnv R1bEnv R1cEnv R2ConcatTailEnv R2Env R3aEnv R3bEnv
   RecvArmEnv RunArmEnv SigTryFromSliceEnv SplitIdEnv SplitSignedEnv TempFileBracketEnv
   addressTryParseDeltaCum addressTryParseDeltaLive addressTryParseDeltaPeak addressTryParseMaxReq
   bundleReadPostDeltaCum bundleReadPostDeltaLive bundleReadPostDeltaPeak bundleReadPostMaxReq
   bundleReadPost_phaseCredit cliRunDeltaCum cliRunDeltaLive cliRunDeltaPeak cliRunMaxReq
   cliRunOfR0_tight_phaseCredit_of_callees cliRunOpenedDeltaCum cliRunOpenedDeltaLive
   cliRunOpenedDeltaPeak cliRunOpenedMaxReq cliRunOpenedTightDeltaCum
   cliRunOpened_phaseCredit cliRunOpened_slots_phaseCredit cliRunOpened_slots_tight_phaseCredit
   cliRunOpened_tight_phaseCredit cliRunTightDeltaCum cliRun_phaseCredit cliRun_slots_phaseCredit
   cliRun_slots_tight_phaseCredit cliRun_tight_phaseCredit deserCloneDeltaCum deserCloneDeltaLive
   deserCloneDeltaPeak deserCloneMaxReq fineCostModel_cliRunTightHyps initArmDeltaCum
   initArmDeltaLive initArmDeltaPeak initArmMaxReq initBundlePaths_phaseCredit maxTryCloneSmallBytes
   phaseCredit_exists_guarded pksmSliceCum pksmSliceLive pksmSliceLive_le_peak pksmSliceMaxReq
   pksmSlicePeak pksmTryFromSlice_phaseCredit r0Opened_phaseCredit_of_path r2DeltaCum r2DeltaLive
   r2DeltaPeak r2MaxReq r2TailTightCum r2TightDeltaCum recvArmDeltaCum recvArmDeltaLive
   recvArmDeltaPeak recvArmMaxReq runArmDeltaCum runArmDeltaLive runArmDeltaLive_le_peak
   runArmDeltaPeak runArmMaxReq runArmTightDeltaCum sigSliceCum sigSliceLive sigSliceMaxReq
   sigSlicePeak sigTryFromSlice_phaseCredit splitIdDeltaCum splitIdDeltaLive splitIdDeltaPeak
   splitIdMaxReq splitId_phaseCredit splitSignedDeltaCum splitSignedDeltaLive splitSignedDeltaPeak
   splitSignedMaxReq splitSigned_phaseCredit tempFilePostCum tempFilePostLive tempFilePostMaxReq
   tempFilePostPeak utf8_address_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakHelpers
  (deallocBytes1OfLen freeOnlyEvs_of_seqEnv
   phaseCredit_or_freeOnly_left phaseCredit_runDispatch phaseCredit_seq_freeOnly_left
   phaseCredit_seq_freeOnly_right phaseCredit_tempAllocBytes1BodyFree_le)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
  (CliDirGetEnv CliPathEnv dirGetRuleDeltaCum dirGetRuleDeltaLive dirGetRuleDeltaPeak
   dirGetRuleMaxReq dirGet_rule_phaseCredit pathDeltaCum pathDeltaLive pathDeltaPeak pathMaxReq
   path_phaseCredit readFileRuleDeltaCum readFileRuleDeltaLive readFileRuleDeltaPeak
   readFileRuleMaxReq readFile_rule_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessLoadPollEnv CliSessStorePollEnv CliSmallStorePollEnv
   sessLoadPollDeltaCum sessLoadPollDeltaLive sessLoadPollDeltaPeak sessLoadPollMaxReq
   sessStorePollDeltaCum sessStorePollDeltaLive sessStorePollDeltaPeak sessStorePollMaxReq
   smallStorePollDeltaCum smallStorePollDeltaLive smallStorePollDeltaPeak smallStorePollMaxReq)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (recordSerializeCum recordSerializeMaxReq recordSerializeOutLarge recordSerializePeak)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrLowInterceptHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
  (msgCapBytes sessionCapBytes spqrStateTightCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
  (SpqrSendTightEnv spqrSendDeltaCum spqrSendDeltaLive spqrSendDeltaPeak spqrSendMaxReq
   spqrSend_phaseCreditSpec_tight640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
  (PeerSpqrTightValid640 PeerSpqrTightValidAt ValidChainParams ValidEncoderPtsAt
   peerSpqrTightValid640_of_cliPqInputs_recv peerSpqrTightValid640_of_cliPqInputs_send
   spqrEncTightPtsCap)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptCalleesPeak
  (peerSpqrTightValid640_of_fromSessionState)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptPeakSpec
  (OtrEncryptStepEnv WithStoresEncTightEnv w1CliEncryptSlot_withSpqrSendTight640_creditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak
  (otrAfterNone otrAfterSome w1CliEncryptSlot_scopedSend_creditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds (RecordGhostValid SessionCloneDom)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
  (DoublingChainLe W2TryDecryptEnv W2TryDecryptFailEnv w2CmkChainLive w2TryDecryptCum
   w2TryDecryptFail_phaseCreditSpec w2TryDecryptLive w2TryDecryptMaxReq w2TryDecryptPeak
   w2TryDecrypt_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak (w2CliDecryptSlot_polls_creditSpec_small)
open LibsignalBinary.Proofs.PeakBudget.W3InitiateEnvBridges
  (mkW3InitiateSlotParams recordSerializePeak_eq_zero_of_maxReq_le
   w3InitiateSlot_at_initCallSite_phaseCredit w3InitiateSlot_at_initCallSite_small_phaseCredit
   w3InitiateSlot_small_live_le_peak)
open LibsignalBinary.Proofs.PeakBudget.W3InitiatePeakSpec
  (W3InitiateSlotEnv W3InitiateSlotParams w3InitiateSlotDeltaCum w3InitiateSlotDeltaLive
   w3InitiateSlotDeltaPeak w3InitiateSlotMaxReq w3InitiateSlotSmallDeltaLive
   w3InitiateSlotSmallDeltaPeak)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (W4DecryptPrekeySlotEnv W4DecryptPrekeySlotParams W4SlotR3bEnv
   w4DecryptPrekeySlotDeltaCum w4DecryptPrekeySlotDeltaLive w4DecryptPrekeySlotDeltaPeak
   w4DecryptPrekeySlotMaxReq w4DecryptPrekeySlot_live_le_peak
   w4DecryptPrekeySlot_opened_small_phaseCredit w4SlotR3b_live_le_peak w4SlotR3b_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (PreKeyMsgNewEnv WireLowInterceptHyps fineCostModel_wireLowInterceptHyps
   preKeyMsgNewDeltaCum preKeyMsgNewDeltaLive preKeyMsgNewDeltaPeak
   preKeyMsgNewMaxReq signalMessageNewDeltaCum signalMessageNewDeltaLive signalMessageNewDeltaPeak
   signalMessageNewMaxReq)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers
  (tryCloneLargeDelta tryCloneSmallDelta)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec (PksmTryFromBoundedEnv)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (SessionGhostValid WithStoresDecEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.CallSiteFacts (InitCallSite)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.SemPlacedBudget (RunSlotEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.SkeletonPlacedBudget (RunCalleesEnvs)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (TryDecryptEnvArgs recordTryDecryptEnvArgs)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
  (SignalMessageNewEnv SignalMessageNewGhost)

/-! ## 1. Re-Exports -/

export CliRunPeakHelpers (phaseCredit_or_freeOnly_left phaseCredit_runDispatch)
export CliRunPeakHelpers (phaseCredit_seq_freeOnly_left phaseCredit_seq_freeOnly_right)
export CliRunArmsPeak (CliRunCalleeEnvs CliRunSlotCalleeSpecs CliRunWrapperEnvs CliRunWrapperSlotSpecs)
export CliRunArmsPeak (CliRunEnv CliRunOpenedEnv CliRunTightHyps fineCostModel_cliRunTightHyps)
export CliRunArmsPeak (cliRunOpenedTightDeltaCum cliRunOpenedDeltaLive cliRunOpenedDeltaPeak cliRunOpenedMaxReq)
export CliRunArmsPeak (cliRunOpened_slots_tight_phaseCredit cliRun_slots_tight_phaseCredit phaseCredit_exists_guarded)
export W3InitiateEnvBridges (mkW3InitiateSlotParams w3InitiateSlot_at_initCallSite_small_phaseCredit w3InitiateSlot_small_live_le_peak)
export W4OuterPeakSpec (w4DecryptPrekeySlot_opened_small_phaseCredit w4DecryptPrekeySlot_live_le_peak)

/-! ## 2. `cliIo.rd` File-Cap Bridges & `RunCalleesEnvs` / `RunSlotEnvs` Instantiation -/

/-- Any file returned by `readViewF F p` has length `≤ fileCap` whenever every `.file bs` entry in
`F` has length `≤ fileCap` (missing paths and missing-ancestor paths return `[]`). -/
theorem readViewF_length_le_of_files_le {F : FsFiles} {fileCap : Nat}
    (hfiles : ∀ p bs, F p = some (.file bs) → bs.length ≤ fileCap)
    {p : String} {bs : List (BitVec 8)} (hrv : readViewF F p = some bs) :
    bs.length ≤ fileCap := by
  unfold readViewF at hrv
  split at hrv
  · cases hrv
  · injection hrv with h
    subst h
    exact Nat.zero_le _
  · split at hrv
    · rename_i fbs hfp
      split at hrv
      · injection hrv with h
        subst h
        exact hfiles p fbs hfp
      · cases hrv
    · cases hrv
    · injection hrv with h
      subst h
      exact Nat.zero_le _

/-- Any file read via `cliIo.rd F path = .ok bs` has `bs.length ≤ fileCap` whenever all `.file`
entries of `F` satisfy `≤ fileCap`. -/
theorem cliIo_rd_length_le_of_files_le {F : FsFiles} {fileCap : Nat}
    (hfiles : ∀ p bs, F p = some (.file bs) → bs.length ≤ fileCap)
    (path : List (BitVec 8)) (bs : List (BitVec 8))
    (hrd : cliIo.rd F path = .ok bs) :
    bs.length ≤ fileCap := by
  change cliRd F path = .ok bs at hrd
  unfold cliRd at hrd
  split at hrd
  · cases hrd
  · rename_i rbs hrv
    injection hrd with h
    subst h
    exact readViewF_length_le_of_files_le hfiles hrv

/-- Direct bridge from `CliPqDomainCaps.files_bounded` (`FilesBounded fileCap (initFsState (cliInputs i))`)
to `cliIo.rd (runFiles i) path = .ok bs → bs.length ≤ fileCap`. -/
theorem cliIo_rd_runFiles_length_le_of_filesBounded {i : Inputs} {fileCap : Nat}
    (hfb : FilesBounded fileCap (initFsState (cliInputs i)))
    (path : List (BitVec 8)) (bs : List (BitVec 8))
    (hrd : cliIo.rd (runFiles i) path = .ok bs) :
    bs.length ≤ fileCap :=
  cliIo_rd_length_le_of_files_le hfb path bs hrd

/-- Canonical `RunCalleesEnvs` (`SkeletonPlacedBudget`) instantiated with `ReadFileRuleEnv`,
`CliDirGetEnv`, `BundleReadEnv`, `SplitIdEnv`, and `SplitSignedEnv`. -/
def cliRunCalleesEnvs (rd : ReadRule) : RunCalleesEnvs where
  readFile := ReadFileRuleEnv rd
  dirGet := CliDirGetEnv (ReadFileRuleEnv rd)
  bundleRead := BundleReadEnv rd
  splitId := SplitIdEnv
  splitSigned := SplitSignedEnv

/-- Canonical `RunSlotEnvs` (`SemPlacedBudget`) constructor from the four ghost-indexed slot
envelopes. -/
def mkRunSlotEnvs
    (enc : EncGhost → List AllocEvent → Prop)
    (decSig : DecSigGhost → List AllocEvent → Prop)
    (init : InitGhost → List AllocEvent → Prop)
    (decPk : DecPkGhost → List AllocEvent → Prop) : RunSlotEnvs where
  encrypt := enc
  decryptSignal := decSig
  initiate := init
  decryptPrekey := decPk

theorem cliRunCallees_readFile_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (rd : ReadRule) (files : FsFiles) (path : List (BitVec 8))
    {fileCap : Nat} (hcap : ∀ bs, rd files path = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M ((cliRunCalleesEnvs rd).readFile files path)
      (readFileRuleDeltaCum fileCap) (readFileRuleDeltaLive fileCap)
      (readFileRuleDeltaPeak fileCap) (readFileRuleMaxReq fileCap) :=
  readFile_rule_phaseCredit hM rd files path hcap

theorem cliRunCallees_dirGet_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (rd : ReadRule) (files : FsFiles) (dir : DirGhost)
    (name : List (BitVec 8)) {maxDir maxEntries maxVal maxName fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hname : name.length ≤ maxName)
    (hcap : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M ((cliRunCalleesEnvs rd).dirGet files dir name)
      (dirGetRuleDeltaCum maxDir maxName maxVal fileCap)
      (dirGetRuleDeltaLive maxDir maxName maxVal fileCap)
      (dirGetRuleDeltaPeak maxDir maxName maxVal fileCap)
      (dirGetRuleMaxReq maxDir maxName maxVal fileCap) :=
  dirGet_rule_phaseCredit hM rd files dir name hdc hname hcap

theorem cliRunCallees_bundleRead_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (rd : ReadRule) (files : FsFiles) (dir name : List (BitVec 8))
    {maxDir maxName fileCap : Nat} (hdir : dir.length ≤ maxDir) (hname : name.length ≤ maxName)
    (hcap : ∀ bs, rd files (pathOf dir name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M ((cliRunCalleesEnvs rd).bundleRead files dir name)
      (pathDeltaCum maxDir maxName + bundleReadPostDeltaCum fileCap)
      (pathDeltaLive maxDir maxName + bundleReadPostDeltaLive fileCap)
      (max (pathDeltaPeak maxDir maxName)
        (pathDeltaLive maxDir maxName + bundleReadPostDeltaPeak fileCap))
      (max (pathMaxReq maxDir maxName) (bundleReadPostMaxReq fileCap)) :=
  (path_phaseCredit hM hdir hname).seq
    (bundleReadPost_phaseCredit hM rd files (pathOf dir name) hcap)

theorem cliRunCallees_splitId_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (rd : ReadRule) (file : List (BitVec 8)) :
    PhaseCreditSpec M ((cliRunCalleesEnvs rd).splitId file)
      splitIdDeltaCum splitIdDeltaLive splitIdDeltaPeak splitIdMaxReq :=
  splitId_phaseCredit hM file

theorem cliRunCallees_splitSigned_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (rd : ReadRule) (file : List (BitVec 8)) :
    PhaseCreditSpec M ((cliRunCalleesEnvs rd).splitSigned file)
      splitSignedDeltaCum splitSignedDeltaLive splitSignedDeltaPeak splitSignedMaxReq :=
  splitSigned_phaseCredit hM file

/-! ## 3. `StoresGhost.opened` Slot Wrappers and `Δlive ≤ Δpeak` Bounds -/

/-! ### 3.1 W3 (`initiate`) at `StoresGhost.opened` -/

def w3CliOpenedCum (fileCap serCum : Nat) : Nat :=
  w3InitiateSlotDeltaCum fileCap 0 0 serCum

def w3CliOpenedLive (fileCap serLive : Nat) : Nat :=
  w3InitiateSlotSmallDeltaLive fileCap 0 0 serLive

def w3CliOpenedPeak (fileCap serPeak : Nat) : Nat :=
  w3InitiateSlotSmallDeltaPeak fileCap 0 0 0 serPeak

def w3CliOpenedMaxReq (fileCap serMaxReq : Nat) : Nat :=
  w3InitiateSlotMaxReq fileCap 0 0 serMaxReq

theorem w3CliOpened_live_le_peak {fileCap serLive serPeak : Nat} (hser : serLive ≤ serPeak) :
    w3CliOpenedLive fileCap serLive ≤ w3CliOpenedPeak fileCap serPeak :=
  w3InitiateSlot_small_live_le_peak hser

/-- Small-regime W3 `PhaseCreditSpec M` at an `InitCallSite` (`StoresGhost.opened`); when
`recordSerializeMaxReq g_rec r_rec ≤ smallMaxReq M`, `serLive = 0` and `serPeak = 0`. -/
theorem w3CliOpened_at_initCallSite_smallSer_phaseCredit
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    {img : Arm64.Obj.Image} {S : RunSem} {g : RunCall} {x : InitGhost}
    (hsite : InitCallSite img S g x)
    {rd : ReadRule} {ownKeyName ownRegName : List (BitVec 8)}
    {F : ShaCompress} {x_spqr : InitialStateGhost}
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))}
    {fileCap : Nat}
    (hkeyName : ownKeyName.length ≤ 64)
    (hregName : ownRegName.length ≤ 64)
    (hspqrKey : x_spqr.p.authKey.length ≤ 32)
    (hfileCap : ∀ p bs, rd x.F p = .ok bs → bs.length ≤ fileCap)
    (hserSmall : recordSerializeMaxReq g_rec r_rec ≤ HasFineReallocCredit.smallMaxReq M) :
    let P := mkW3InitiateSlotParams rd x ownKeyName ownRegName F x_spqr g_rec r_rec
    PhaseCreditSpec M (W3InitiateSlotEnv P)
      (w3CliOpenedCum fileCap (recordSerializeCum g_rec r_rec))
      (w3CliOpenedLive fileCap 0)
      (w3CliOpenedPeak fileCap 0)
      (w3CliOpenedMaxReq fileCap (recordSerializeMaxReq g_rec r_rec)) := by
  intro P
  have h := w3InitiateSlot_at_initCallSite_small_phaseCredit
    (F := F) (g_rec := g_rec) (r_rec := r_rec) hM hsmall hsite
    hkeyName hregName hspqrKey hfileCap
  obtain ⟨hp0, ho0⟩ := recordSerializePeak_eq_zero_of_maxReq_le M hserSmall
  unfold w3CliOpenedCum w3CliOpenedLive w3CliOpenedPeak w3CliOpenedMaxReq
  rwa [hp0, ho0] at h

/-! ### 3.2 W1 (`encrypt`) at `StoresGhost.opened` -/

/-- Parametric-send W1 (`encrypt`) `Δcum` at `StoresGhost.opened`. -/
def w1CliOpenedCustomSendCum (M : AllocCostModel) [HasFineReallocCredit M]
    (c_s ptextLen nameCum fileCap deserCum c_sig c_pk c_st : Nat) : Nat :=
  let ctLen := (ptextLen / 16 + 1) * 16
  let c_otr := c_s + HasFineReallocCredit.smallAllocCost M 32 + tryCloneSmallDelta M ctLen + c_sig
  let c_ld := sessLoadPollDeltaCum fileCap deserCum
  let c_id := smallStorePollDeltaCum fileCap 0
  let c_ap := HasFineReallocCredit.smallAllocCost M 32 + HasFineReallocCredit.smallAllocCost M 32 + c_st
  let c_save := (HasFineReallocCredit.smallAllocCost M 32 + c_id) + c_ap
  let c_cm := (HasFineReallocCredit.smallAllocCost M 32 + c_id) + max nameCum c_save
  let c_fo := max nameCum (HasFineReallocCredit.smallAllocCost M 1569 + c_otr + c_pk + c_cm)
  (HasFineReallocCredit.smallAllocCost M 24 + c_ld) + max nameCum c_fo

/-- Parametric-send W1 (`encrypt`) `Δlive` at `StoresGhost.opened`. -/
def w1CliOpenedCustomSendLive (M : AllocCostModel) [HasFineReallocCredit M]
    (l_s ptextLen fileCap deserLive l_sig l_pk l_st : Nat) : Nat :=
  let ctLen := (ptextLen / 16 + 1) * 16
  let l_otr := l_s + tryCloneLargeDelta M ctLen + l_sig
  let l_ld := sessLoadPollDeltaLive fileCap deserLive
  let l_id := smallStorePollDeltaLive fileCap 0
  let l_cm := l_id + (l_id + l_st)
  let l_fo := l_otr + l_pk + l_cm
  l_ld + l_fo

/-- Parametric-send W1 (`encrypt`) `Δpeak` at `StoresGhost.opened`. -/
def w1CliOpenedCustomSendPeak (M : AllocCostModel) [HasFineReallocCredit M]
    (l_s p_s ptextLen fileCap deserLive deserPeak l_sig p_sig l_pk p_pk p_st : Nat) : Nat :=
  let ctLen := (ptextLen / 16 + 1) * 16
  let l_otr := l_s + tryCloneLargeDelta M ctLen + l_sig
  let p_otr := max p_s (l_s + tryCloneLargeDelta M ctLen + p_sig)
  let l_ld := sessLoadPollDeltaLive fileCap deserLive
  let p_ld := sessLoadPollDeltaPeak fileCap deserPeak
  let l_id := smallStorePollDeltaLive fileCap 0
  let p_id := smallStorePollDeltaPeak fileCap 0
  let p_cm := max p_id (l_id + max p_id (l_id + p_st))
  let p_fo := max p_otr (l_otr + max p_pk (l_pk + p_cm))
  max p_ld (l_ld + p_fo)

/-- Parametric-send W1 (`encrypt`) `maxReq` at `StoresGhost.opened`. -/
def w1CliOpenedCustomSendMaxReq
    (r_s ptextLen fileCap deserMaxReq r_sig r_pk r_st : Nat) : Nat :=
  let ctLen := (ptextLen / 16 + 1) * 16
  let r_otr := max r_s (max 32 (max ctLen r_sig))
  let r_ld := sessLoadPollMaxReq fileCap deserMaxReq
  let r_id := smallStorePollMaxReq fileCap 0
  let r_cm := max (max 32 r_id) (max 40 (max (max 32 r_id) (max 32 (max 32 r_st))))
  let r_fo := max 40 (max 1569 (max r_otr (max r_pk r_cm)))
  max (max 24 r_ld) (max 40 r_fo)

theorem w1CliOpenedCustomSend_live_le_peak (M : AllocCostModel) [HasFineReallocCredit M]
    {l_s p_s ptextLen fileCap deserLive deserPeak l_sig p_sig l_pk p_pk l_st p_st : Nat}
    (hsig : l_sig ≤ p_sig) (hpk : l_pk ≤ p_pk) (hst : l_st ≤ p_st) :
    w1CliOpenedCustomSendLive M l_s ptextLen fileCap deserLive l_sig l_pk l_st ≤
      w1CliOpenedCustomSendPeak M l_s p_s ptextLen fileCap deserLive deserPeak
        l_sig p_sig l_pk p_pk p_st := by
  unfold w1CliOpenedCustomSendLive w1CliOpenedCustomSendPeak
  dsimp only
  set ctLen := (ptextLen / 16 + 1) * 16
  set l_otr := l_s + tryCloneLargeDelta M ctLen + l_sig
  set p_otr := max p_s (l_s + tryCloneLargeDelta M ctLen + p_sig)
  set l_ld := sessLoadPollDeltaLive fileCap deserLive
  set p_ld := sessLoadPollDeltaPeak fileCap deserPeak
  set l_id := smallStorePollDeltaLive fileCap 0
  set p_id := smallStorePollDeltaPeak fileCap 0
  have hcm1 : l_id + l_st ≤ max p_id (l_id + p_st) :=
    Nat.le_trans (Nat.add_le_add_left hst l_id) (Nat.le_max_right _ _)
  have hcm : l_id + (l_id + l_st) ≤ max p_id (l_id + max p_id (l_id + p_st)) :=
    Nat.le_trans (Nat.add_le_add_left hcm1 l_id) (Nat.le_max_right _ _)
  have hpkcm : l_pk + (l_id + (l_id + l_st)) ≤
      max p_pk (l_pk + max p_id (l_id + max p_id (l_id + p_st))) :=
    let _ := hpk
    Nat.le_trans (Nat.add_le_add_left hcm l_pk) (Nat.le_max_right _ _)
  have hfo : l_otr + l_pk + (l_id + (l_id + l_st)) ≤
      max p_otr (l_otr + max p_pk (l_pk + max p_id (l_id + max p_id (l_id + p_st)))) := by
    have _ := hsig
    rw [Nat.add_assoc l_otr l_pk _]
    exact Nat.le_trans (Nat.add_le_add_left hpkcm l_otr) (Nat.le_max_right _ _)
  exact Nat.le_trans (Nat.add_le_add_left hfo l_ld) (Nat.le_max_right p_ld _)

/-- `StoresGhost.opened` wrapper around `w1CliEncryptSlot_scopedSend_creditSpec_tight` parametric in `E_send` and `(c_s, l_s, p_s, r_s)`. -/
theorem w1CliOpenedCustomSend_phaseCredit
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle1569 : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (B : RunBudgets) (img : Arm64.Obj.Image) (F : FsFiles) (peer : AddrGhost)
    (C : Crypto) (S : SpqrModel) (x : WithStoresEncGhost)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (peerIdKeyName : List (BitVec 8))
    (kitEnv : SessionStoreBudgetEnv (w1SessKit B img F peer))
    (ikitEnv : IdentityStoreBudgetEnv (w1IdKit B img F peer))
    (E_send : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (SigNoneGuard SigSomeGuard :
      SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      OutgoingTripleRatchet (List (BitVec 8)) → SessionState (List (BitVec 8)) →
      SignalMessageNewGhost → Prop)
    (PkCallGuard :
      SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      OutgoingTripleRatchet (List (BitVec 8)) → SessionState (List (BitVec 8)) →
      PreKeyMsgNewCall → Prop)
    {nameCum fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    {c_s l_s p_s r_s c_sig l_sig p_sig r_sig c_pk l_pk p_pk r_pk c_st l_st p_st r_st : Nat}
    (hpeer : peer.name.bytes.length ≤ 40)
    (hremName : x.rem.name.bytes.length ≤ 40)
    (hNameCum : ∀ n, 0 < n → n ≤ 40 → HasFineReallocCredit.smallAllocCost M n ≤ nameCum)
    (hidKeyLen : peerIdKeyName.length ≤ 64)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hIdFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.identity.peers.path peerIdKeyName) = .ok bs →
      bs.length ≤ fileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hLoadEq : ∀ evs,
      kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv F StoresGhost.opened.sessions peer evs)
    (hTrustEq : ∀ k evs,
      ikitEnv.trustPollEnv StoresGhost.opened.identity x.rem.val k .sending evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSaveEq : ∀ k evs,
      ikitEnv.savePollEnv
        ((w1IdKit B img F peer).trustUpdate StoresGhost.opened.identity x.rem.val k .sending (.ok true))
        x.rem.val k evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSend : ∀ r sess otr taken,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseCreditSpec M (E_send otr.pqrState x.rest) c_s l_s p_s r_s)
    (hSigNone : ∀ r sess otr taken g, SigNoneGuard r sess otr taken g →
      signalMessageNewDeltaCum uuidTryParse g ≤ c_sig ∧
      signalMessageNewDeltaLive uuidTryParse g ≤ l_sig ∧
      signalMessageNewDeltaPeak uuidTryParse g ≤ p_sig ∧
      signalMessageNewMaxReq uuidTryParse g ≤ r_sig)
    (hSigSome : ∀ r sess otr taken g, SigSomeGuard r sess otr taken g →
      signalMessageNewDeltaCum uuidTryParse g ≤ c_sig ∧
      signalMessageNewDeltaLive uuidTryParse g ≤ l_sig ∧
      signalMessageNewDeltaPeak uuidTryParse g ≤ p_sig ∧
      signalMessageNewMaxReq uuidTryParse g ≤ r_sig)
    (hPkCap : ∀ r sess otr taken call, PkCallGuard r sess otr taken call →
      preKeyMsgNewDeltaCum call ≤ c_pk ∧
      preKeyMsgNewDeltaLive call ≤ l_pk ∧
      preKeyMsgNewDeltaPeak call ≤ p_pk ∧
      preKeyMsgNewMaxReq call ≤ r_pk)
    (hStoreNone : ∀ r sess otr taken k,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M
        (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val
          (storedRecord sess (otrAfterNone C S x otr) taken))
        c_st l_st p_st r_st)
    (hStoreSome : ∀ r sess otr taken k,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M
        (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val
          (storedRecord sess (otrAfterSome C S uuidTryParse x otr) taken))
        c_st l_st p_st r_st) :
    PhaseCreditSpec M
      (WithStoresEncTightEnv scopeKit
        (w1SessKit B img F peer) kitEnv StoresGhost.opened.sessions
        (w1IdKit B img F peer) ikitEnv StoresGhost.opened.identity
        C S uuidTryParse x
        (fun r sess otr taken =>
          OtrEncryptStepEnv (E_send otr.pqrState x.rest) x.ptext.length
            (fun evs => ∃ g, SigNoneGuard r sess otr taken g ∧ SignalMessageNewEnv uuidTryParse g evs))
        (fun r sess otr taken =>
          OtrEncryptStepEnv (E_send otr.pqrState x.rest) x.ptext.length
            (fun evs => ∃ g, SigSomeGuard r sess otr taken g ∧ SignalMessageNewEnv uuidTryParse g evs))
        (fun r sess otr taken evs =>
          ∃ call, PkCallGuard r sess otr taken call ∧ PreKeyMsgNewEnv call evs))
      (w1CliOpenedCustomSendCum M c_s x.ptext.length nameCum fileCap deserCum c_sig c_pk c_st)
      (w1CliOpenedCustomSendLive M l_s x.ptext.length fileCap deserLive l_sig l_pk l_st)
      (w1CliOpenedCustomSendPeak M l_s p_s x.ptext.length fileCap deserLive deserPeak
        l_sig p_sig l_pk p_pk p_st)
      (w1CliOpenedCustomSendMaxReq r_s x.ptext.length fileCap deserMaxReq r_sig r_pk r_st) := by
  have h := w1CliEncryptSlot_scopedSend_creditSpec_tight
    hM hle1569 B img F peer C S x DeserEnv peerIdKeyName kitEnv ikitEnv E_send
    SigNoneGuard SigSomeGuard PkCallGuard
    hpeer hremName hNameCum hidKeyLen hSessFileCap hIdFileCap hDeser
    hLoadEq hTrustEq hSaveEq hSend hSigNone hSigSome hPkCap hStoreNone hStoreSome
  dsimp only at h
  unfold w1CliOpenedCustomSendCum w1CliOpenedCustomSendLive
    w1CliOpenedCustomSendPeak w1CliOpenedCustomSendMaxReq
  simpa only [Nat.zero_max] using h

/-- `pqCap`-capped W1 (`encrypt`) `Δcum` at `StoresGhost.opened`. -/
def w1CliOpenedPqCapCum (M : AllocCostModel) [HasFineReallocCredit M]
    (pqCap restLen ptextLen nameCum fileCap deserCum c_sig c_pk c_st : Nat) : Nat :=
  w1CliOpenedCustomSendCum M (spqrSendDeltaCum pqCap restLen spqrEncTightPtsCap)
    ptextLen nameCum fileCap deserCum c_sig c_pk c_st

def w1CliOpenedPqCapLive (M : AllocCostModel) [HasFineReallocCredit M]
    (pqCap restLen ptextLen fileCap deserLive l_sig l_pk l_st : Nat) : Nat :=
  w1CliOpenedCustomSendLive M (spqrSendDeltaLive pqCap restLen spqrEncTightPtsCap)
    ptextLen fileCap deserLive l_sig l_pk l_st

def w1CliOpenedPqCapPeak (M : AllocCostModel) [HasFineReallocCredit M]
    (pqCap restLen ptextLen fileCap deserLive deserPeak l_sig p_sig l_pk p_pk p_st : Nat) : Nat :=
  w1CliOpenedCustomSendPeak M
    (spqrSendDeltaLive pqCap restLen spqrEncTightPtsCap)
    (spqrSendDeltaPeak pqCap restLen spqrEncTightPtsCap)
    ptextLen fileCap deserLive deserPeak l_sig p_sig l_pk p_pk p_st

def w1CliOpenedPqCapMaxReq
    (pqCap restLen ptextLen fileCap deserMaxReq r_sig r_pk r_st : Nat) : Nat :=
  w1CliOpenedCustomSendMaxReq (spqrSendMaxReq pqCap restLen spqrEncTightPtsCap)
    ptextLen fileCap deserMaxReq r_sig r_pk r_st

theorem w1CliOpenedPqCap_live_le_peak (M : AllocCostModel) [HasFineReallocCredit M]
    {pqCap restLen ptextLen fileCap deserLive deserPeak l_sig p_sig l_pk p_pk l_st p_st : Nat}
    (hsig : l_sig ≤ p_sig) (hpk : l_pk ≤ p_pk) (hst : l_st ≤ p_st) :
    w1CliOpenedPqCapLive M pqCap restLen ptextLen fileCap deserLive l_sig l_pk l_st ≤
      w1CliOpenedPqCapPeak M pqCap restLen ptextLen fileCap deserLive deserPeak
        l_sig p_sig l_pk p_pk p_st :=
  w1CliOpenedCustomSend_live_le_peak M hsig hpk hst

/-- `pqCap`-capped W1 `PhaseCreditSpec M` at `StoresGhost.opened` under `otr.pqrState.length ≤ pqCap`. -/
theorem w1CliOpenedPqCap_phaseCredit
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    (hle1569 : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (B : RunBudgets) (img : Arm64.Obj.Image) (F : FsFiles) (peer : AddrGhost)
    (C : Crypto) (S : SpqrModel) (x : WithStoresEncGhost)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (peerIdKeyName : List (BitVec 8))
    (kitEnv : SessionStoreBudgetEnv (w1SessKit B img F peer))
    (ikitEnv : IdentityStoreBudgetEnv (w1IdKit B img F peer))
    (SigNoneGuard SigSomeGuard :
      SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      OutgoingTripleRatchet (List (BitVec 8)) → SessionState (List (BitVec 8)) →
      SignalMessageNewGhost → Prop)
    (PkCallGuard :
      SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      OutgoingTripleRatchet (List (BitVec 8)) → SessionState (List (BitVec 8)) →
      PreKeyMsgNewCall → Prop)
    {pqCap nameCum fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    {c_sig l_sig p_sig r_sig c_pk l_pk p_pk r_pk c_st l_st p_st r_st : Nat}
    (hpeer : peer.name.bytes.length ≤ 40)
    (hremName : x.rem.name.bytes.length ≤ 40)
    (hNameCum : ∀ n, 0 < n → n ≤ 40 → HasFineReallocCredit.smallAllocCost M n ≤ nameCum)
    (hidKeyLen : peerIdKeyName.length ≤ 64)
    (hValid : PeerSpqrTightValid640 F x.rem.val)
    (hPqCap : ∀ r sess otr taken,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      otr.pqrState.length ≤ pqCap)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hIdFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.identity.peers.path peerIdKeyName) = .ok bs →
      bs.length ≤ fileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hLoadEq : ∀ evs,
      kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv F StoresGhost.opened.sessions peer evs)
    (hTrustEq : ∀ k evs,
      ikitEnv.trustPollEnv StoresGhost.opened.identity x.rem.val k .sending evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSaveEq : ∀ k evs,
      ikitEnv.savePollEnv
        ((w1IdKit B img F peer).trustUpdate StoresGhost.opened.identity x.rem.val k .sending (.ok true))
        x.rem.val k evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSigNone : ∀ r sess otr taken g, SigNoneGuard r sess otr taken g →
      signalMessageNewDeltaCum uuidTryParse g ≤ c_sig ∧
      signalMessageNewDeltaLive uuidTryParse g ≤ l_sig ∧
      signalMessageNewDeltaPeak uuidTryParse g ≤ p_sig ∧
      signalMessageNewMaxReq uuidTryParse g ≤ r_sig)
    (hSigSome : ∀ r sess otr taken g, SigSomeGuard r sess otr taken g →
      signalMessageNewDeltaCum uuidTryParse g ≤ c_sig ∧
      signalMessageNewDeltaLive uuidTryParse g ≤ l_sig ∧
      signalMessageNewDeltaPeak uuidTryParse g ≤ p_sig ∧
      signalMessageNewMaxReq uuidTryParse g ≤ r_sig)
    (hPkCap : ∀ r sess otr taken call, PkCallGuard r sess otr taken call →
      preKeyMsgNewDeltaCum call ≤ c_pk ∧
      preKeyMsgNewDeltaLive call ≤ l_pk ∧
      preKeyMsgNewDeltaPeak call ≤ p_pk ∧
      preKeyMsgNewMaxReq call ≤ r_pk)
    (hStoreNone : ∀ r sess otr taken k,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M
        (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val
          (storedRecord sess (otrAfterNone C S x otr) taken))
        c_st l_st p_st r_st)
    (hStoreSome : ∀ r sess otr taken k,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M
        (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val
          (storedRecord sess (otrAfterSome C S uuidTryParse x otr) taken))
        c_st l_st p_st r_st) :
    PhaseCreditSpec M
      (WithStoresEncTightEnv scopeKit
        (w1SessKit B img F peer) kitEnv StoresGhost.opened.sessions
        (w1IdKit B img F peer) ikitEnv StoresGhost.opened.identity
        C S uuidTryParse x
        (fun r sess otr taken =>
          OtrEncryptStepEnv (SpqrSendTightEnv otr.pqrState x.rest) x.ptext.length
            (fun evs => ∃ g, SigNoneGuard r sess otr taken g ∧ SignalMessageNewEnv uuidTryParse g evs))
        (fun r sess otr taken =>
          OtrEncryptStepEnv (SpqrSendTightEnv otr.pqrState x.rest) x.ptext.length
            (fun evs => ∃ g, SigSomeGuard r sess otr taken g ∧ SignalMessageNewEnv uuidTryParse g evs))
        (fun r sess otr taken evs =>
          ∃ call, PkCallGuard r sess otr taken call ∧ PreKeyMsgNewEnv call evs))
      (w1CliOpenedPqCapCum M pqCap x.rest.length x.ptext.length nameCum fileCap deserCum c_sig c_pk c_st)
      (w1CliOpenedPqCapLive M pqCap x.rest.length x.ptext.length fileCap deserLive l_sig l_pk l_st)
      (w1CliOpenedPqCapPeak M pqCap x.rest.length x.ptext.length fileCap deserLive deserPeak
        l_sig p_sig l_pk p_pk p_st)
      (w1CliOpenedPqCapMaxReq pqCap x.rest.length x.ptext.length fileCap deserMaxReq r_sig r_pk r_st) :=
  w1CliOpenedCustomSend_phaseCredit
    hM hle1569 B img F peer C S x DeserEnv peerIdKeyName kitEnv ikitEnv SpqrSendTightEnv
    SigNoneGuard SigSomeGuard PkCallGuard
    hpeer hremName hNameCum hidKeyLen hSessFileCap hIdFileCap hDeser
    hLoadEq hTrustEq hSaveEq
    (fun r sess otr taken hsc hcur hfrom =>
      let ⟨hve, _hcp, _hpq⟩ := peerSpqrTightValid640_of_fromSessionState hsc hcur hfrom hValid
      spqrSend_phaseCreditSpec_tight640 hM hLow hve
        (hPqCap r sess otr taken hsc hcur hfrom) (Nat.le_refl x.rest.length))
    hSigNone hSigSome hPkCap hStoreNone hStoreSome

def w1CliOpenedCum (M : AllocCostModel) [HasFineReallocCredit M]
    (restLen ptextLen nameCum fileCap deserCum c_sig c_pk c_st : Nat) : Nat :=
  w1CliOpenedPqCapCum M 2147483647 restLen ptextLen nameCum fileCap deserCum c_sig c_pk c_st

def w1CliOpenedLive (M : AllocCostModel) [HasFineReallocCredit M]
    (restLen ptextLen fileCap deserLive l_sig l_pk l_st : Nat) : Nat :=
  w1CliOpenedPqCapLive M 2147483647 restLen ptextLen fileCap deserLive l_sig l_pk l_st

def w1CliOpenedPeak (M : AllocCostModel) [HasFineReallocCredit M]
    (restLen ptextLen fileCap deserLive deserPeak l_sig p_sig l_pk p_pk p_st : Nat) : Nat :=
  w1CliOpenedPqCapPeak M 2147483647 restLen ptextLen fileCap deserLive deserPeak
    l_sig p_sig l_pk p_pk p_st

def w1CliOpenedMaxReq
    (restLen ptextLen fileCap deserMaxReq r_sig r_pk r_st : Nat) : Nat :=
  w1CliOpenedPqCapMaxReq 2147483647 restLen ptextLen fileCap deserMaxReq r_sig r_pk r_st

theorem w1CliOpened_live_le_peak (M : AllocCostModel) [HasFineReallocCredit M]
    {restLen ptextLen fileCap deserLive deserPeak l_sig p_sig l_pk p_pk l_st p_st : Nat}
    (hsig : l_sig ≤ p_sig) (hpk : l_pk ≤ p_pk) (hst : l_st ≤ p_st) :
    w1CliOpenedLive M restLen ptextLen fileCap deserLive l_sig l_pk l_st ≤
      w1CliOpenedPeak M restLen ptextLen fileCap deserLive deserPeak
        l_sig p_sig l_pk p_pk p_st :=
  w1CliOpenedPqCap_live_le_peak M hsig hpk hst

/-- `StoresGhost.opened` wrapper around `w1CliEncryptSlot_withSpqrSendTight640_creditSpec_tight`. -/
theorem w1CliOpened_phaseCredit
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    (hle1569 : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (B : RunBudgets) (img : Arm64.Obj.Image) (F : FsFiles) (peer : AddrGhost)
    (C : Crypto) (S : SpqrModel) (x : WithStoresEncGhost)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (peerIdKeyName : List (BitVec 8))
    (kitEnv : SessionStoreBudgetEnv (w1SessKit B img F peer))
    (ikitEnv : IdentityStoreBudgetEnv (w1IdKit B img F peer))
    (SigNoneGuard SigSomeGuard :
      SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      OutgoingTripleRatchet (List (BitVec 8)) → SessionState (List (BitVec 8)) →
      SignalMessageNewGhost → Prop)
    (PkCallGuard :
      SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      OutgoingTripleRatchet (List (BitVec 8)) → SessionState (List (BitVec 8)) →
      PreKeyMsgNewCall → Prop)
    {nameCum fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    {c_sig l_sig p_sig r_sig c_pk l_pk p_pk r_pk c_st l_st p_st r_st : Nat}
    (hpeer : peer.name.bytes.length ≤ 40)
    (hremName : x.rem.name.bytes.length ≤ 40)
    (hNameCum : ∀ n, 0 < n → n ≤ 40 → HasFineReallocCredit.smallAllocCost M n ≤ nameCum)
    (hidKeyLen : peerIdKeyName.length ≤ 64)
    (hValid : PeerSpqrTightValid640 F x.rem.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hIdFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.identity.peers.path peerIdKeyName) = .ok bs →
      bs.length ≤ fileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hLoadEq : ∀ evs,
      kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv F StoresGhost.opened.sessions peer evs)
    (hTrustEq : ∀ k evs,
      ikitEnv.trustPollEnv StoresGhost.opened.identity x.rem.val k .sending evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSaveEq : ∀ k evs,
      ikitEnv.savePollEnv
        ((w1IdKit B img F peer).trustUpdate StoresGhost.opened.identity x.rem.val k .sending (.ok true))
        x.rem.val k evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSigNone : ∀ r sess otr taken g, SigNoneGuard r sess otr taken g →
      signalMessageNewDeltaCum uuidTryParse g ≤ c_sig ∧
      signalMessageNewDeltaLive uuidTryParse g ≤ l_sig ∧
      signalMessageNewDeltaPeak uuidTryParse g ≤ p_sig ∧
      signalMessageNewMaxReq uuidTryParse g ≤ r_sig)
    (hSigSome : ∀ r sess otr taken g, SigSomeGuard r sess otr taken g →
      signalMessageNewDeltaCum uuidTryParse g ≤ c_sig ∧
      signalMessageNewDeltaLive uuidTryParse g ≤ l_sig ∧
      signalMessageNewDeltaPeak uuidTryParse g ≤ p_sig ∧
      signalMessageNewMaxReq uuidTryParse g ≤ r_sig)
    (hPkCap : ∀ r sess otr taken call, PkCallGuard r sess otr taken call →
      preKeyMsgNewDeltaCum call ≤ c_pk ∧
      preKeyMsgNewDeltaLive call ≤ l_pk ∧
      preKeyMsgNewDeltaPeak call ≤ p_pk ∧
      preKeyMsgNewMaxReq call ≤ r_pk)
    (hStoreNone : ∀ r sess otr taken k,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M
        (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val
          (storedRecord sess (otrAfterNone C S x otr) taken))
        c_st l_st p_st r_st)
    (hStoreSome : ∀ r sess otr taken k,
      (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions x.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M
        (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val
          (storedRecord sess (otrAfterSome C S uuidTryParse x otr) taken))
        c_st l_st p_st r_st) :
    PhaseCreditSpec M
      (WithStoresEncTightEnv scopeKit
        (w1SessKit B img F peer) kitEnv StoresGhost.opened.sessions
        (w1IdKit B img F peer) ikitEnv StoresGhost.opened.identity
        C S uuidTryParse x
        (fun r sess otr taken =>
          OtrEncryptStepEnv (SpqrSendTightEnv otr.pqrState x.rest) x.ptext.length
            (fun evs => ∃ g, SigNoneGuard r sess otr taken g ∧ SignalMessageNewEnv uuidTryParse g evs))
        (fun r sess otr taken =>
          OtrEncryptStepEnv (SpqrSendTightEnv otr.pqrState x.rest) x.ptext.length
            (fun evs => ∃ g, SigSomeGuard r sess otr taken g ∧ SignalMessageNewEnv uuidTryParse g evs))
        (fun r sess otr taken evs =>
          ∃ call, PkCallGuard r sess otr taken call ∧ PreKeyMsgNewEnv call evs))
      (w1CliOpenedCum M x.rest.length x.ptext.length nameCum fileCap deserCum c_sig c_pk c_st)
      (w1CliOpenedLive M x.rest.length x.ptext.length fileCap deserLive l_sig l_pk l_st)
      (w1CliOpenedPeak M x.rest.length x.ptext.length fileCap deserLive deserPeak
        l_sig p_sig l_pk p_pk p_st)
      (w1CliOpenedMaxReq x.rest.length x.ptext.length fileCap deserMaxReq r_sig r_pk r_st) := by
  have h := w1CliEncryptSlot_withSpqrSendTight640_creditSpec_tight
    hM hLow hle1569 B img F peer C S x DeserEnv peerIdKeyName kitEnv ikitEnv
    SigNoneGuard SigSomeGuard PkCallGuard
    hpeer hremName hNameCum hidKeyLen hValid hSessFileCap hIdFileCap hDeser
    hLoadEq hTrustEq hSaveEq hSigNone hSigSome hPkCap hStoreNone hStoreSome
  dsimp only at h
  unfold w1CliOpenedCum w1CliOpenedLive w1CliOpenedPeak w1CliOpenedMaxReq
    w1CliOpenedPqCapCum w1CliOpenedPqCapLive w1CliOpenedPqCapPeak w1CliOpenedPqCapMaxReq
    w1CliOpenedCustomSendCum w1CliOpenedCustomSendLive
    w1CliOpenedCustomSendPeak w1CliOpenedCustomSendMaxReq
  simpa only [Nat.zero_max] using h

/-! ### 3.3 W2 (`decryptSignal`) at `StoresGhost.opened` -/

def w2CliOpenedCum (fileCap idFileCap deserCum c_td : Nat) : Nat :=
  let pqCap' := fileCap + 1128000
  let encCap' := fileCap + 3225192
  let c_ld := sessLoadPollDeltaCum fileCap deserCum
  let c_rd := 98382860 + 2 * fileCap + c_td
  let c_id := smallStorePollDeltaCum idFileCap 0
  let c_st := sessStorePollDeltaCum (98372903 + 2 * pqCap' + 2 * encCap') 0
  let c_ld_step := 2 * 24 + 9539 + c_ld
  let c_id_step := 2 * 32 + 9539 + c_id
  let c_st_step := 2 * 32 + 9539 + c_st
  let c_sc := 2 * 40 + 9539
  let c_kr := c_id_step + max c_sc (c_id_step + c_st_step)
  c_ld_step + max (max c_sc 9573) (c_rd + c_kr)

def w2CliOpenedLive (fileCap idFileCap deserLive l_td : Nat) : Nat :=
  let encCap' := fileCap + 3225192
  let l_ld := sessLoadPollDeltaLive fileCap deserLive
  let l_rd := 1089170 + fileCap + l_td
  let l_id := smallStorePollDeltaLive idFileCap 0
  let l_st := sessStorePollDeltaLive (encCap' + 8195) 0
  let l_kr := l_id + (l_id + l_st)
  l_ld + (l_rd + l_kr)

def w2CliOpenedPeak (fileCap idFileCap deserLive deserPeak l_td p_td : Nat) : Nat :=
  let pqCap' := fileCap + 1128000
  let encCap' := fileCap + 3225192
  let l_ld := sessLoadPollDeltaLive fileCap deserLive
  let p_ld := sessLoadPollDeltaPeak fileCap deserPeak
  let l_rd := 1089170 + fileCap + l_td
  let p_rd := 1089170 + fileCap + max p_td l_td
  let l_id := smallStorePollDeltaLive idFileCap 0
  let p_id := smallStorePollDeltaPeak idFileCap 0
  let p_st := sessStorePollDeltaPeak (1097365 + pqCap' + encCap') 0
  let p_kr := max p_id (l_id + max p_id (l_id + p_st))
  max p_ld (l_ld + max p_rd (l_rd + p_kr))

def w2CliOpenedMaxReq (fileCap idFileCap deserMaxReq r_td : Nat) : Nat :=
  let pqCap' := fileCap + 1128000
  let encCap' := fileCap + 3225192
  let r_ld := sessLoadPollMaxReq fileCap deserMaxReq
  let r_rd := max (max 208000 fileCap) (max r_td 192)
  let r_id := smallStorePollMaxReq idFileCap 0
  let r_st := sessStorePollMaxReq (max (max 208000 pqCap') encCap') 0
  let r_kr := max (max 32 r_id) (max 40 (max (max 32 r_id) (max 32 r_st)))
  max (max 24 r_ld) (max (max 40 17) (max r_rd r_kr))

theorem w2CliOpened_live_le_peak (fileCap idFileCap deserLive deserPeak l_td p_td : Nat) :
    w2CliOpenedLive fileCap idFileCap deserLive l_td ≤
      w2CliOpenedPeak fileCap idFileCap deserLive deserPeak l_td p_td := by
  unfold w2CliOpenedLive w2CliOpenedPeak
  dsimp only
  set pqCap' := fileCap + 1128000
  set encCap' := fileCap + 3225192
  set l_ld := sessLoadPollDeltaLive fileCap deserLive
  set p_ld := sessLoadPollDeltaPeak fileCap deserPeak
  set l_rd := 1089170 + fileCap + l_td
  set p_rd := 1089170 + fileCap + max p_td l_td
  set l_id := smallStorePollDeltaLive idFileCap 0
  set p_id := smallStorePollDeltaPeak idFileCap 0
  have hst : sessStorePollDeltaLive (encCap' + 8195) 0 ≤
      sessStorePollDeltaPeak (1097365 + pqCap' + encCap') 0 := by
    unfold sessStorePollDeltaLive sessStorePollDeltaPeak
    have hinner : encCap' + 8195 ≤ 1097365 + pqCap' + encCap' := by omega
    exact Nat.add_le_add_right (Nat.add_le_add_left hinner 32768) _
  have hkr1 : l_id + sessStorePollDeltaLive (encCap' + 8195) 0 ≤
      max p_id (l_id + sessStorePollDeltaPeak (1097365 + pqCap' + encCap') 0) :=
    Nat.le_trans (Nat.add_le_add_left hst l_id) (Nat.le_max_right _ _)
  have hkr : l_id + (l_id + sessStorePollDeltaLive (encCap' + 8195) 0) ≤
      max p_id (l_id + max p_id (l_id + sessStorePollDeltaPeak (1097365 + pqCap' + encCap') 0)) :=
    Nat.le_trans (Nat.add_le_add_left hkr1 l_id) (Nat.le_max_right _ _)
  have hrd : l_rd + (l_id + (l_id + sessStorePollDeltaLive (encCap' + 8195) 0)) ≤
      max p_rd (l_rd + max p_id (l_id + max p_id
        (l_id + sessStorePollDeltaPeak (1097365 + pqCap' + encCap') 0))) :=
    Nat.le_trans (Nat.add_le_add_left hkr l_rd) (Nat.le_max_right p_rd _)
  exact Nat.le_trans (Nat.add_le_add_left hrd l_ld) (Nat.le_max_right p_ld _)

/-- `StoresGhost.opened` wrapper around `w2CliDecryptSlot_polls_creditSpec_small`. -/
theorem w2CliOpened_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} (hM : ModelHyps M) (hsmall : 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (F : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 t1 t2 t3 t4 : Nat)
    (C : Crypto) (K : MlKem) (parse : UuidParser) (x : DecryptGhost)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (peerIdKeyName : List (BitVec 8))
    (kitEnv : SessionStoreBudgetEnv
      (cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4))
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    {Kspqr fileCap idFileCap deserCum deserLive deserPeak deserMaxReq
     c_td l_td p_td r_td : Nat}
    (hrem : x.rem.val = peer.val)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hremName : x.rem.name.bytes.length ≤ 40)
    (hidKeyLen : peerIdKeyName.length ≤ 64)
    (hFilesOk : FilesOkPeer scopeIn F peer.val)
    (hValid : PeerSpqrTightValidAt Kspqr F x.rem.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hIdFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.identity.peers.path peerIdKeyName) = .ok bs →
      bs.length ≤ idFileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hLoadEq : ∀ evs,
      kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv F StoresGhost.opened.sessions peer evs)
    (hTrustEq : ∀ k evs,
      ikitEnv.trustPollEnv StoresGhost.opened.identity x.rem.val k .receiving evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSaveEq : ∀ k evs,
      ikitEnv.savePollEnv StoresGhost.opened.identity x.rem.val k evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hStoreEq : ∀ rec' evs,
      scopeKit rec' →
      kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val rec' evs →
      ∃ g : RecordGhost, RecordGhostValid g rec' ∧
        CliSessStorePollEnv StoresGhost.opened.sessions peer g rec' evs)
    (hTd : ∀ rec ses G G₁,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      ValidEncoderPtsAt Kspqr ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      PhaseCreditSpec M
        (tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁))
        c_td l_td p_td r_td) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4
    PhaseCreditSpec M
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity C (spqrV1 C.F K) parse tdEnv scopeKit x)
      (w2CliOpenedCum fileCap idFileCap deserCum c_td)
      (w2CliOpenedLive fileCap idFileCap deserLive l_td)
      (w2CliOpenedPeak fileCap idFileCap deserLive deserPeak l_td p_td)
      (w2CliOpenedMaxReq fileCap idFileCap deserMaxReq r_td) := by
  intro kit ikit
  have h := w2CliDecryptSlot_polls_creditSpec_small hM hsmall F pathOk peer s1 s2 s3 s4 t1 t2 t3 t4
    C K parse x DeserEnv peerIdKeyName kitEnv ikitEnv tdEnv
    hrem hpeer hremName hidKeyLen hFilesOk hValid hSessFileCap hIdFileCap hDeser
    hLoadEq hTrustEq hSaveEq hStoreEq hTd
  dsimp only at h
  unfold w2CliOpenedCum w2CliOpenedLive w2CliOpenedPeak w2CliOpenedMaxReq
  simpa only [Nat.zero_max] using h

/-! ### 3.4 W4 (`decryptPrekey`) `R3b` Envelope Bridge -/

theorem w4SlotR3bEnv_eq_r3bEnv (x_pksm : PksmGhost) (DecPkEnv : List AllocEvent → Prop) :
    W4SlotR3bEnv x_pksm DecPkEnv = R3bEnv (PksmTryFromBoundedEnv x_pksm) DecPkEnv :=
  rfl

/-! ## 4. Whole-`run` Envelope (`CliRunTightSpqrCaps`, `CliRunTightEnv`) & `CliMainPeakSpec` Composition -/

/-- Domain-cap bundle for `signal_session::run` (`RunCall`), capturing `.init` `<bundle-dir>` path
and file caps together with tight `K = 640` SPQR encoder-point and chain-parameter invariants on
`.send` and `.recv` peers. -/
structure CliRunSpqrAndInitCaps (maxInitDir bundleCap : Nat) (g : RunCall) : Prop where
  init_caps : ∀ peer dir, g.c = .init peer dir → dir.length ≤ maxInitDir ∧
    (∀ name bs, cliIo.rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)
  send_spqr_tight : ∀ peer, g.c = .send peer → PeerSpqrTightValid640 (runFiles g.i) (addrValOf peer)
  recv_spqr_tight : ∀ peer, g.c = .recv peer → PeerSpqrTightValid640 (runFiles g.i) (addrValOf peer)

/-- Canonical `1 MiB` / tight-domain `CliRunTightSpqrCaps` (`maxInitDir = 26`, `bundleCap = 1,637` B). -/
abbrev CliRunTightSpqrCaps (g : RunCall) : Prop :=
  CliRunSpqrAndInitCaps 26 1637 g

/-- Derives `CliRunSpqrAndInitCaps` directly from `CliPqxdhInputs W g.i` and `parseArgs` agreement
together with the `.init` `<bundle-dir>` path/file cap. -/
theorem cliRunSpqrAndInitCaps_of_cliPqInputs {W : PEParams} {maxInitDir bundleCap : Nat}
    {g : RunCall} (hi : CliPqxdhInputs W g.i)
    (hparse : parseArgs uuidTryParse (g.i.argv.map bytesOfString) = some g.c)
    (hinit : ∀ peer dir, g.c = .init peer dir → dir.length ≤ maxInitDir ∧
      (∀ name bs, cliIo.rd (runFiles g.i) (pathOf dir name) = .ok bs → bs.length ≤ bundleCap)) :
    CliRunSpqrAndInitCaps maxInitDir bundleCap g where
  init_caps := hinit
  send_spqr_tight _peer hc :=
    peerSpqrTightValid640_of_cliPqInputs_send hi (hc ▸ hparse)
  recv_spqr_tight _peer hc :=
    peerSpqrTightValid640_of_cliPqInputs_recv hi (hc ▸ hparse)

/-- Binary-order (`R0 → Arm → Join`) allocation-event envelope for `signal_session::run` at
`StoresGhost.opened` over `cliIo.rd`, parameterized by `W : RunCall → CliRunWrapperEnvs` and
`wireOutCap : Nat`. -/
abbrev CliRunTightEnvOf (W : RunCall → CliRunWrapperEnvs) (wireOutCap : Nat)
    (g : RunCall) (evs : List AllocEvent) : Prop :=
  CliRunOpenedEnv cliIo.rd (W g).toCalleeEnvs wireOutCap g evs

/-- Canonical `sessionCapBytes` (`2 MiB`) `RunEnv` for `CliMainPeakSpec.cliMain_phaseCredit`. -/
abbrev CliRunTightEnv (W : RunCall → CliRunWrapperEnvs)
    (g : RunCall) (evs : List AllocEvent) : Prop :=
  CliRunTightEnvOf W sessionCapBytes g evs

theorem cliRunOpenedDeltaLive_le_peak {M : AllocCostModel} [HasFineReallocCredit M]
    {E : CliRunCalleeEnvs} {stdinCap : Nat} (S : CliRunSlotCalleeSpecs M E stdinCap)
    (maxInitDir fileCap bundleCap wireOutCap : Nat) :
    cliRunOpenedDeltaLive S maxInitDir wireOutCap ≤
      cliRunOpenedDeltaPeak S maxInitDir fileCap bundleCap wireOutCap :=
  Nat.le_trans
    (Nat.add_le_add_left (runArmDeltaLive_le_peak S)
      (pathDeltaLive 26 7 + tempFilePostLive addressTryParseDeltaLive))
    (Nat.le_max_right _ _)

/-- Symbolic `PhaseCreditSpec M` for `signal_session::run`, composing
`R0 → (InitArm | R2 | RecvArm | Keygen) → Join` in binary call order under `CliRunTightHyps M`
and `WireLowInterceptHyps M`. -/
theorem cliRunTight_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : CliRunTightHyps M) (hLow : WireLowInterceptHyps M)
    {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {stdinCap maxInitDir fileCap bundleCap wireOutCap : Nat}
    (SW : CliRunWrapperSlotSpecs M (W g))
    (hcaps : CliPqDomainCaps stdinCap fileCap g.i)
    (hspqr : CliRunSpqrAndInitCaps maxInitDir bundleCap g) :
    let S := SW.toCalleeSpecs hM hLow stdinCap
    PhaseCreditSpec M (CliRunTightEnvOf W wireOutCap g)
      (cliRunOpenedTightDeltaCum S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedDeltaLive S maxInitDir wireOutCap)
      (cliRunOpenedDeltaPeak S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedMaxReq S maxInitDir fileCap bundleCap wireOutCap) :=
  cliRunOpened_slots_tight_phaseCredit hM hT hLow SW wireOutCap
    hcaps.stdin_le
    (fun bs hrd => cliIo_rd_runFiles_length_le_of_filesBounded hcaps.files_bounded _ bs hrd)
    hspqr.init_caps

/-- Canonical `1 MiB` (`msgCapBytes`, `sessionCapBytes`, `maxInitDir = 26`, `bundleCap = 1,637` B)
specialization of `cliRunTight_phaseCredit`. -/
theorem cliRunTight_phaseCredit_1MiB_caps {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : CliRunTightHyps M) (hLow : WireLowInterceptHyps M)
    {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    (SW : CliRunWrapperSlotSpecs M (W g))
    (hcaps : CliPqDomainCaps msgCapBytes sessionCapBytes g.i)
    (hspqr : CliRunTightSpqrCaps g) :
    let S := SW.toCalleeSpecs hM hLow msgCapBytes
    PhaseCreditSpec M (CliRunTightEnv W g)
      (cliRunOpenedTightDeltaCum S 26 sessionCapBytes 1637 sessionCapBytes)
      (cliRunOpenedDeltaLive S 26 sessionCapBytes)
      (cliRunOpenedDeltaPeak S 26 sessionCapBytes 1637 sessionCapBytes)
      (cliRunOpenedMaxReq S 26 sessionCapBytes 1637 sessionCapBytes) :=
  cliRunTight_phaseCredit hM hT hLow SW hcaps hspqr

theorem cliRunTight_phaseCredit_fine
    {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {stdinCap maxInitDir fileCap bundleCap wireOutCap : Nat}
    (SW : CliRunWrapperSlotSpecs fineCostModel (W g))
    (hcaps : CliPqDomainCaps stdinCap fileCap g.i)
    (hspqr : CliRunSpqrAndInitCaps maxInitDir bundleCap g) :
    let S := SW.toCalleeSpecs fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps stdinCap
    PhaseCreditSpec fineCostModel (CliRunTightEnvOf W wireOutCap g)
      (cliRunOpenedTightDeltaCum S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedDeltaLive S maxInitDir wireOutCap)
      (cliRunOpenedDeltaPeak S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedMaxReq S maxInitDir fileCap bundleCap wireOutCap) :=
  cliRunTight_phaseCredit fineCostModel_modelHyps fineCostModel_cliRunTightHyps
    fineCostModel_wireLowInterceptHyps SW hcaps hspqr

/-- `FitsEnv fineCostModel` at `fineCostModel.init` for `CliRunTightEnvOf W`. -/
theorem cliRunTight_fitsEnv_fineCostModel
    {lim : BudgetLimits} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {stdinCap maxInitDir fileCap bundleCap wireOutCap : Nat}
    (SW : CliRunWrapperSlotSpecs fineCostModel (W g))
    (hcaps : CliPqDomainCaps stdinCap fileCap g.i)
    (hspqr : CliRunSpqrAndInitCaps maxInitDir bundleCap g)
    (henf : lim.enforced = true)
    (hram :
      let S := SW.toCalleeSpecs fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps stdinCap
      let cumB := cliRunOpenedTightDeltaCum S maxInitDir fileCap bundleCap wireOutCap
      let peakB := cliRunOpenedDeltaPeak S maxInitDir fileCap bundleCap wireOutCap
      let maxReq := cliRunOpenedMaxReq S maxInitDir fileCap bundleCap wireOutCap
      lim.staticBytes + (18686152 + cumB + peakB) +
        2 * fineStepReserveOfCum maxReq 16 cumB ≤ lim.physCap)
    (hva :
      let S := SW.toCalleeSpecs fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps stdinCap
      let cumB := cliRunOpenedTightDeltaCum S maxInitDir fileCap bundleCap wireOutCap
      let peakB := cliRunOpenedDeltaPeak S maxInitDir fileCap bundleCap wireOutCap
      let maxReq := cliRunOpenedMaxReq S maxInitDir fileCap bundleCap wireOutCap
      MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
        fineStepReserveOfCum maxReq 16 cumB +
        (lim.staticCount + fineDynIvsOfCum cumB + 16) *
          (fineStepReserveOfCum maxReq 16 cumB + PAGE_SIZE) +
        fineStepReserveOfCum maxReq 16 cumB ≤ 2 ^ 48) :
    FitsEnv fineCostModel lim fineCostModel.init (CliRunTightEnvOf W wireOutCap g) := by
  have hSpec := cliRunTight_phaseCredit_fine (wireOutCap := wireOutCap) SW hcaps hspqr
  have hlp := cliRunOpenedDeltaLive_le_peak
    (SW.toCalleeSpecs fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps stdinCap)
    maxInitDir fileCap bundleCap wireOutCap
  exact fitsEnv_fineCostModel_of_phaseCredit hSpec hlp henf hram hva

/-- Plugs `cliRunTight_phaseCredit` into `CliMainPeakSpec.cliMain_phaseCredit` for `CliMainEnv`. -/
theorem cliMain_with_cliRunTight_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : CliRunTightHyps M) (hLow : WireLowInterceptHyps M)
    {uuidParse : UuidParser} {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {stdinCap maxInitDir fileCap bundleCap wireOutCap maxDir maxName : Nat}
    {addrOpt : Option AddressCall} {needStdin : Bool}
    {dirs : List (List (BitVec 8) × List (List (BitVec 8)))} {ok : Bool}
    (SW : CliRunWrapperSlotSpecs M (W g))
    (hcaps : CliPqDomainCaps stdinCap fileCap g.i)
    (hspqr : CliRunSpqrAndInitCaps maxInitDir bundleCap g)
    (haddr : match addrOpt with | none => True | some ag => ag.bs.length ≤ 64)
    (hdirs : ∀ dn ∈ dirs, dn.1.length ≤ maxDir ∧ ∀ nm ∈ dn.2, nm.length ≤ maxName) :
    let S := SW.toCalleeSpecs hM hLow stdinCap
    let runCum := cliRunOpenedTightDeltaCum S maxInitDir fileCap bundleCap wireOutCap
    let runLive := cliRunOpenedDeltaLive S maxInitDir wireOutCap
    let runPeak := cliRunOpenedDeltaPeak S maxInitDir fileCap bundleCap wireOutCap
    let runMaxReq := cliRunOpenedMaxReq S maxInitDir fileCap bundleCap wireOutCap
    PhaseCreditSpec M (CliMainEnv uuidParse (CliRunTightEnvOf W wireOutCap) g addrOpt needStdin dirs ok)
      (cliMainDeltaCum stdinCap fileCap runCum ((dirs.map (fun dn => dn.2.length)).sum) maxDir maxName)
      (cliMainDeltaLive stdinCap fileCap runLive)
      (cliMainDeltaPeak stdinCap fileCap runLive runPeak maxDir maxName)
      (cliMainMaxReq stdinCap fileCap runMaxReq maxDir maxName) :=
  cliMain_phaseCredit hM hcaps haddr hdirs (cliRunTight_phaseCredit hM hT hLow SW hcaps hspqr)

/-! ### 4.1 Tightened Wire-Decode Composition (`sigSliceTightCum` / `pksmSliceFullTightCum`) -/

/-- Closed-form `SignalMessage::try_from` cumulative small-allocation bound (`97 * stdinCap + 48,520` B) under `WireLowInterceptHyps`. -/
def sigSliceTightCum (stdinCap : Nat) : Nat :=
  97 * stdinCap + 48520

/-- `PreKeySignalMessage::try_from` cumulative bound with `sigSliceTightCum` substituted for the inner `SignalMessage::try_from` call. -/
def pksmSliceTightInnerCum (stdinCap : Nat) : Nat :=
  (9552 * stdinCap + 48351) + sigSliceTightCum stdinCap

/-- Fully tightened `PreKeySignalMessage::try_from` cumulative bound (`97 * stdinCap` on both outer and inner prost loops). -/
def pksmSliceFullTightCum (stdinCap : Nat) : Nat :=
  (97 * stdinCap + 48520) + sigSliceTightCum stdinCap

/-- Custom-wire `PhaseCreditSpec M` for `CliRunTightEnvOf W` accepting caller-supplied `SigTryFromSliceEnv` and `PksmTryFromSliceEnv` bounds `(c_sig, c_pksm)`. -/
theorem cliRunOpened_slots_tight_phaseCredit_customWire
    {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : CliRunTightHyps M)
    {W : RunCall → CliRunWrapperEnvs} {g : RunCall}
    {stdinCap maxInitDir fileCap bundleCap wireOutCap c_sig c_pksm : Nat}
    (SW : CliRunWrapperSlotSpecs M (W g))
    (hcaps : CliPqDomainCaps stdinCap fileCap g.i)
    (hspqr : CliRunSpqrAndInitCaps maxInitDir bundleCap g)
    (hsig : ∀ rest, rest.length ≤ stdinCap →
      PhaseCreditSpec M (SigTryFromSliceEnv rest)
        c_sig (sigSliceLive stdinCap) (sigSlicePeak stdinCap) (sigSliceMaxReq stdinCap))
    (hpksm : ∀ rest, rest.length ≤ stdinCap →
      PhaseCreditSpec M (PksmTryFromSliceEnv rest)
        c_pksm (pksmSliceLive stdinCap) (pksmSlicePeak stdinCap) (pksmSliceMaxReq stdinCap)) :
    let S : CliRunSlotCalleeSpecs M (W g).toCalleeEnvs stdinCap :=
      { initCum := SW.initCum
        initLive := SW.initLive
        initPeak := SW.initPeak
        initMaxReq := SW.initMaxReq
        init_spec := SW.init_spec
        init_lp := SW.init_lp
        encCum := SW.encCum
        encLive := SW.encLive
        encPeak := SW.encPeak
        encMaxReq := SW.encMaxReq
        enc_spec := SW.enc_spec
        enc_lp := SW.enc_lp
        decSigCum := SW.decSigCum
        decSigLive := SW.decSigLive
        decSigPeak := SW.decSigPeak
        decSigMaxReq := SW.decSigMaxReq
        decSig_spec := SW.decSig_spec
        decSig_lp := SW.decSig_lp
        pksmCum := c_pksm
        pksmLive := pksmSliceLive stdinCap
        pksmPeak := pksmSlicePeak stdinCap
        pksmMaxReq := pksmSliceMaxReq stdinCap
        pksm_spec := hpksm
        pksm_lp := pksmSliceLive_le_peak stdinCap
        decPkCum := SW.decPkCum
        decPkLive := SW.decPkLive
        decPkPeak := SW.decPkPeak
        decPkMaxReq := SW.decPkMaxReq
        decPk_spec := SW.decPk_spec
        decPk_lp := SW.decPk_lp }
    PhaseCreditSpec M (CliRunTightEnvOf W wireOutCap g)
      ((pathDeltaCum 26 7 + tempFilePostCum fileCap addressTryParseDeltaCum) +
        runArmTightDeltaCum S (pathDeltaCum maxInitDir 16) bundleCap wireOutCap c_sig)
      (cliRunOpenedDeltaLive S maxInitDir wireOutCap)
      (cliRunOpenedDeltaPeak S maxInitDir fileCap bundleCap wireOutCap)
      (cliRunOpenedMaxReq S maxInitDir fileCap bundleCap wireOutCap) :=
  cliRunOfR0_tight_phaseCredit_of_callees hM hT _ wireOutCap
    (r0Opened_phaseCredit_of_path hM
      (path_phaseCredit hM dirDomainCaps_opened_own.path_len_le utf8_address_length_le)
      (fun bs hrd => cliIo_rd_runFiles_length_le_of_filesBounded hcaps.files_bounded _ bs hrd))
    hcaps.stdin_le
    (initBundlePaths_phaseCredit hM hspqr.init_caps)
    hsig

/-! ## 5. Closed-Form `1 MiB` Profile and Tight SPQR `recv` Constants -/

/-- Tight SPQR `recv` `Δcum` (`23,313,687` B). -/
def c09bTightSpqrCum : Nat := 23313687

/-- Tight SPQR `recv` `Δlive` (`294,391` B). -/
def c09bTightSpqrLive : Nat := 294391

/-- Tight SPQR `recv` `Δpeak` (`294,391` B). -/
def c09bTightSpqrPeak : Nat := 294391

/-- Tight SPQR `recv` `maxReq` (`302,480` B). -/
def c09bTightSpqrMaxReq : Nat := 302480

/-- Unconditional-history SPQR `recv` `Δlive` (`605,066` B). -/
def c09bTightUncondSpqrLive : Nat := 605066

/-- Unconditional-history SPQR `recv` `Δpeak` (`621,350` B). -/
def c09bTightUncondSpqrPeak : Nat := 621350

/-- Prologue `R0` (`StoresGhost.opened`) closed-form `(cum, live, peak, maxReq)` at `1 MiB`
(`fileCap = sessionCapBytes = 2,097,152` B). -/
def r0Opened1MiBCum : Nat :=
  pathDeltaCum 26 7 + tempFilePostCum sessionCapBytes addressTryParseDeltaCum

def r0Opened1MiBLive : Nat :=
  pathDeltaLive 26 7 + tempFilePostLive addressTryParseDeltaLive

def r0Opened1MiBPeak : Nat :=
  max (pathDeltaPeak 26 7)
    (pathDeltaLive 26 7 + tempFilePostPeak sessionCapBytes addressTryParseDeltaPeak)

def r0Opened1MiBMaxReq : Nat :=
  max (pathMaxReq 26 7) (tempFilePostMaxReq sessionCapBytes addressTryParseMaxReq)

/-- Parametric whole-`run` closed-form `(cum, cumPostC0506t, live, peak, maxReq)` at the canonical
`1 MiB` domain (`msgCapBytes = 1,048,576`, `sessionCapBytes = 2,097,152`, `maxInitDir = 26`,
`bundleCap = 1,637`, `wireOutCap = 2,097,152`) on `fineCostModel`, given the four stateful slot
tuples `(init*, enc*, decSig*, decPk*)`. -/
def cliRun1MiBSlotCum
    (initCum encCum decSigCum decPkCum : Nat) : Nat :=
  r0Opened1MiBCum +
    max (initArmDeltaCum (pathDeltaCum 26 16) 1637 initCum)
      (max (r2TightDeltaCum encCum sessionCapBytes)
        (max (sigSliceCum msgCapBytes + decSigCum)
          (pksmSliceCum msgCapBytes + decPkCum)))

/-- Whole-`run` `Δcum` at `1 MiB` with `sigSliceTightCum` and `pksmSliceFullTightCum` substituted. -/
def cliRun1MiBSlotCumPostC0506t
    (initCum encCum decSigCum decPkCum : Nat) : Nat :=
  r0Opened1MiBCum +
    max (initArmDeltaCum (pathDeltaCum 26 16) 1637 initCum)
      (max (r2TightDeltaCum encCum sessionCapBytes)
        (max (sigSliceTightCum msgCapBytes + decSigCum)
          (pksmSliceFullTightCum msgCapBytes + decPkCum)))

def cliRun1MiBSlotLive
    (initLive encLive decSigLive decPkLive : Nat) : Nat :=
  r0Opened1MiBLive +
    max (initArmDeltaLive (pathDeltaLive 26 16) initLive)
      (max (r2DeltaLive fineCostModel encLive sessionCapBytes)
        (max (sigSliceLive msgCapBytes + decSigLive)
          (pksmSliceLive msgCapBytes + decPkLive)))

def cliRun1MiBSlotPeak
    (initPeak encLive encPeak decSigPeak decPkPeak : Nat) : Nat :=
  max r0Opened1MiBPeak
    (r0Opened1MiBLive +
      max (initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637 initPeak)
        (max (r2DeltaPeak fineCostModel encLive encPeak sessionCapBytes)
          (max (max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + decSigPeak))
            (max (pksmSlicePeak msgCapBytes) (pksmSliceLive msgCapBytes + decPkPeak)))))

def cliRun1MiBSlotMaxReq
    (initMaxReq encMaxReq decSigMaxReq decPkMaxReq : Nat) : Nat :=
  max r0Opened1MiBMaxReq
    (max (initArmMaxReq (pathMaxReq 26 16) 1637 initMaxReq)
      (max (r2MaxReq encMaxReq sessionCapBytes)
        (max (max (sigSliceMaxReq msgCapBytes) decSigMaxReq)
          (max (pksmSliceMaxReq msgCapBytes) decPkMaxReq))))

theorem cliRunOpened_1MiB_eq_slotProfile {W : CliRunWrapperEnvs}
    (SW : CliRunWrapperSlotSpecs fineCostModel W) :
    let S := SW.toCalleeSpecs fineCostModel_modelHyps fineCostModel_wireLowInterceptHyps msgCapBytes
    cliRunOpenedTightDeltaCum S 26 sessionCapBytes 1637 sessionCapBytes =
      cliRun1MiBSlotCum SW.initCum SW.encCum SW.decSigCum SW.decPkCum ∧
    cliRunOpenedDeltaLive S 26 sessionCapBytes =
      cliRun1MiBSlotLive SW.initLive SW.encLive SW.decSigLive SW.decPkLive ∧
    cliRunOpenedDeltaPeak S 26 sessionCapBytes 1637 sessionCapBytes =
      cliRun1MiBSlotPeak SW.initPeak SW.encLive SW.encPeak SW.decSigPeak SW.decPkPeak ∧
    cliRunOpenedMaxReq S 26 sessionCapBytes 1637 sessionCapBytes =
      cliRun1MiBSlotMaxReq SW.initMaxReq SW.encMaxReq SW.decSigMaxReq SW.decPkMaxReq :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `1 MiB` closed-form `(cum, live, peak, maxReq)` for prologue `R0` at `StoresGhost.opened`. -/
theorem r0Opened1MiB_profile_eq :
    r0Opened1MiBCum = 4242841 ∧
    r0Opened1MiBLive = 16557 ∧
    r0Opened1MiBPeak = 2121904 ∧
    r0Opened1MiBMaxReq = 2097152 := by
  decide

/-- `1 MiB` closed-form wire `SignalMessage::try_from` bounds. -/
theorem sigSlice1MiB_profile_eq :
    sigSliceCum msgCapBytes = 102312877 ∧
    sigSliceTightCum msgCapBytes = 101760392 ∧
    sigSliceLive msgCapBytes = 5300277 ∧
    sigSlicePeak msgCapBytes = 5300277 ∧
    sigSliceMaxReq msgCapBytes = 2097152 := by
  decide

/-- `1 MiB` closed-form wire `PreKeySignalMessage::try_from` bounds. -/
theorem pksmSlice1MiB_profile_eq :
    pksmSliceCum msgCapBytes = 204355676 ∧
    pksmSliceFullTightCum msgCapBytes = 203520784 ∧
    pksmSliceLive msgCapBytes = 9543751 ∧
    pksmSlicePeak msgCapBytes = 14844028 ∧
    pksmSliceMaxReq msgCapBytes = 2097152 := by
  decide

/-- `1 MiB` closed-form `W3` (`initiate`) slot and `InitArmEnv` bounds on a fresh `0`-prev peer. -/
theorem initArm1MiB_fresh_profile_eq :
    w3CliOpenedCum sessionCapBytes 17179 = 48708660 ∧
    w3CliOpenedLive sessionCapBytes 0 = 14551466 ∧
    w3CliOpenedPeak sessionCapBytes 0 = 15010470 ∧
    w3CliOpenedMaxReq sessionCapBytes 3820 = 2097152 ∧
    initArmDeltaCum (pathDeltaCum 26 16) 1637 48708660 = 48999734 ∧
    initArmDeltaLive (pathDeltaLive 26 16) 14551466 = 14668672 ∧
    initArmDeltaPeak (pathDeltaLive 26 16) (pathDeltaPeak 26 16) 1637 15010470 = 15127676 ∧
    initArmMaxReq (pathMaxReq 26 16) 1637 2097152 = 2097152 := by
  decide

/-- `1 MiB` closed-form `W2` (`decryptSignal`) slot and `R3aEnv` bounds at tight SPQR `recv` caps. -/
theorem r3aArm1MiB_c09bTight_deser0_profile_eq :
    w2CliOpenedCum sessionCapBytes 64 0 147081330 = 392445787 ∧
    w2CliOpenedLive sessionCapBytes 64 0 4767229 = 20773816 ∧
    w2CliOpenedPeak sessionCapBytes 64 0 0 4767229 5128198 = 25088138 ∧
    w2CliOpenedMaxReq sessionCapBytes 64 0 3407872 = 5322344 ∧
    sigSliceCum msgCapBytes + 392445787 = 494758664 ∧
    sigSliceTightCum msgCapBytes + 392445787 = 494206179 ∧
    sigSliceLive msgCapBytes + 20773816 = 26074093 ∧
    max (sigSlicePeak msgCapBytes) (sigSliceLive msgCapBytes + 25088138) = 30388415 ∧
    max (sigSliceMaxReq msgCapBytes) 5322344 = 5322344 := by
  decide

/-- `1 MiB` closed-form `R3bEnv` (`W4` `decryptPrekey` Path A) bounds at tight SPQR `recv` caps. -/
theorem r3bArm1MiB_c09bTight_deser0_profile_eq :
    pksmSliceCum msgCapBytes + 205347739 = 409703415 ∧
    pksmSliceFullTightCum msgCapBytes + 205347739 = 408868523 ∧
    pksmSliceLive msgCapBytes + 34901913 = 44445664 ∧
    max (pksmSlicePeak msgCapBytes) (pksmSliceLive msgCapBytes + 34901913) = 44445664 ∧
    max (pksmSliceMaxReq msgCapBytes) 3407872 = 3407872 := by
  decide

end LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
