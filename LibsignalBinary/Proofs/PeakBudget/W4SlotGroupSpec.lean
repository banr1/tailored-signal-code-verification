/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudget
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvC09aWire
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec

@[expose] public section

set_option autoImplicit false

/-!
# Tight Slot Small-Allocation Group Bounds

Tight `PhaseGroupSpec fineCostModel` bounds across the whisper (`WithStoresDecEnv`) and pre-key
(`W4DecryptPrekeySlotEnv` / `W4DecryptPrekeySplitWideSlotEnv` / `W4SlotR3bEnv`) CLI decryption
slots, keeping `DeserEnv` parametric:
1. Tight `try_decrypt` and `WithStoresDecEnv` group bounds (`w2TryDecryptTight12_c07_c09a_fine_groupSpec`,
   `w2CliDecryptSlot_of_spqr_fine_groupSpec`, `w2CliDecryptSlot_tight_fine_groupSpec`).
2. Domain predicates (`StateCloneDom`, `RecordDom`, `SessionOutDom`) and group bounds for
   `W4BoundedEvs`, `DoReserveEnv`, `KemSerialize1569Env`, `GrowOneSpeEnv 0#64`, `W4ErrTailEnv`, and
   CLI boxed store steps.
3. Stage P1–P4, 4-arm `W4DecryptPrekeySlotEnv`, `W4SlotR3bEnv`, and widened
   `W4DecryptPrekeySplitWideSlotEnv` `PhaseGroupSpec` theorems.
-/

namespace LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec

open CryptoGames.LibsignalSession (Crypto SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (recGhostOf)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Message MlKem PqRatchetState States V1Recv V1State VersionNegotiationPB
   spqrAuthApi spqrPolyApi spqrV1)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost UuidParser)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule StoresGhost addressText keyName pathOf)
open CryptoVerification.SignalSession.Cli.KitInst (cliIdentityStoreSpec cliSessionStoreSpec)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost)
open CryptoVerification.SignalSession.Cli.Slots (FilesOkPeer scopeIn scopeKit)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (FineScale MmapThresholdReq fineCostModel)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudget
  (DoReserveEnv KemSerialize1569Env doReserveEvents)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (W2TryDecryptTightEnv cliSessLoadPollEnv_groupSpec cliSessStorePollEnv_dom_fine_groupSpec
   cliSessStorePollEnv_groupSpec cliSessStorePollPrev1Env_dom_fine_groupSpec
   cliSessStorePollPrev1Env_groupSpec cliSmallStorePollEnv_fine_groupSpec
   dropClonedSessionEvents_groupSpec fine_rustAlloc_le_28 fine_rustAlloc_le_44
   initialStateEnv_groupSpec optTailCloneEvents_groupSpec phaseGroupSpec_append_eq
   recordSerializeCancelEnv_dom_fine_groupSpec recordSerializeDomFineGrpS segCloneDomFineGrpS
   segCloneEnv_dom_fine_groupSpec senderChainCloneDomFineGrpS senderChainCloneEnv_dom_fine_groupSpec
   serializePrev1DomFineGrpS stringCloneEnv_groupSpec vecCloneEvents_groupSpec w2Seg4CmkFineGrpS
   w2TryDecryptTightEnv_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (HasFineGroupCredit NonFreeBound PhaseGroupSpec fineSmallAllocGroupS
   smallAllocGroupS_fineCostModel_eq)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv IterSeqEnv)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessLoadPollEnv CliSessStorePollEnv CliSessStorePollPrev1Env CliSmallStorePollEnv
   RecordSerializeCancelEnv SerializePrev1CancelEnv dropClonedSessionEvents)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvC09aWire
  (spqrRecvParts_c07_c09a_phaseGroupSpec_tight
   spqrRecvParts_c07_c09a_phaseGroupSpec_tight_rawEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvGroupSpec (chainRecvKeyTightGroupS)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (SpqrRecvC07TightEnv SpqrRecvTightDomain)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec (StatesRecvEnv StatesRecvProtoEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
  (PeerSpqrTightValidAt ValidChainParams ValidEncoderPtsAt)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (FreshBobCloneDom RecordGhostValid SessionCloneDom ghostCloneValid_of_sessionGhostValid)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak (w2CliDecryptSlot_polls_phaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
  (ArchivedTrialIterEnv PromoteStateArchiveEnv)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
  (W4BobSessionBuildEnv W4BoundedEvs W4InitBobEnv W4InitBobSpqrEnv
   W4PqxdhAcceptEnv W4PqxdhAcceptOkEnv W4PqxdhDhKeysEnv W4StageP2OverBobEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4DecryptPrekeyPathAEnv W4DecryptPrekeyPathAWideEnv W4DecryptPrekeyPathBEnv
   W4DecryptPrekeyPathBWideEnv W4DecryptPrekeyPathCEnv W4DecryptPrekeyPathCWideEnv
   W4DecryptPrekeySlotEnv W4DecryptPrekeySlotParams W4DecryptPrekeySplitWideSlotEnv
   W4DecryptPrekeyWideSlotEnv W4ErrTailEnv W4ErrTailWideEnv W4InitBobSpqrWideEnv W4InitBobWideEnv
   W4SlotR3bEnv W4StageP1OkCliEnv W4StageP1UntrustedCliEnv W4StageP2MatchedCheckEnv
   W4StageP2MatchedEnv W4StageP2MatchedErrStrEnv W4StageP2MatchedWideEnv W4StageP2OverBobWideEnv
   W4StageP2PathACliEnv W4StageP2PathACliWideEnv W4StageP2PathCCliEnv W4StageP2PathCCliWideEnv
   W4StageP3Env W4StageP3WideEnv W4StageP4MatchedCliEnv W4StageP4MatchedCliWideEnv
   W4StageP4PathACliEnv W4StageP4PathACliWideEnv W4StageP4PathCCliEnv W4StageP4PathCCliWideEnv
   W4TryDecryptCloneFailWideEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
  (W4BoxedStoreStepEnv W4SessLoadStepEnv W4SessStorePrev1StepEnv
   W4SessStoreStepEnv W4SmallStoreStepEnv)
open LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak (W4TryDecryptCloneFailEnv)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromPeakSpec
  (PksmTryFromBoundedEnv WireGroupHyps fineCostModel_wireGroupHyps
   pksmTryFromCapDeltaGrpS pksmTryFromDeltaGrpS pksmTryFromDeltaGrpS_le_cap
   pksmTryFrom_phaseGroup)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (SessionGhostValid WithStoresDecEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (GrowOneSpeEnv)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
  (chainCloneEvents senderChainCloneEvents)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (FromFEnv FromMEnv FromVPostTdEnv SegCloneEnv SegTailEnv TryDecryptEnvArgs
   recordTryDecryptEnvArgs segCloneEvents)

/-! ## Tight `try_decrypt` & `WithStoresDecEnv` Group Bounds -/

/-- Scaled group bound (`701,273,904` = `10,701` groups) for `SpqrRecvC07TightEnv`
(`SpqrRecvC09aWire.spqrRecvParts_c07_c09a_phaseGroupSpec_tight`). -/
def spqrRecvTightFineGrpS : Nat := 701273904

/-- Tight `fineCostModel` outer `try_decrypt` scaled group overhead before `SpqrStepEnv`
(`38,540,818` scaled units = `589` groups at `maxSteps = 12`). -/
def w2TryDecryptBaseFineGrpS (maxSteps : Nat) : Nat :=
  42 * FineScale + 6 * 16659 + 11056 + w2Seg4CmkFineGrpS maxSteps

/-- Scaled group bound (`739,814,722` = `11,289` groups) for a 12-step `W2TryDecryptTightEnv`
with `SpqrRecvC07TightEnv`. -/
def w2TryDecryptTight12FineGrpS : Nat :=
  w2TryDecryptBaseFineGrpS 12 + spqrRecvTightFineGrpS

/-- Fresh-Bob responder Stage P3 scaled group bound (`319,767,460` = `4,880` groups) when
`chainRecvKeyTightGroupS` (`420,047,262`) is absent. -/
def w2TryDecryptBobFresh12FineGrpS : Nat :=
  w2TryDecryptTight12FineGrpS - chainRecvKeyTightGroupS

/-- Tight W2 CLI slot scaled group base (`407,700,082` = `369,159,264 + 38,540,818`) before
`g_deser + g_spqr`. -/
def w2CliDecryptSlotBaseFineGrpS : Nat :=
  369159264 + w2TryDecryptBaseFineGrpS 12

/-- Whisper CLI slot scaled group bound (`1,108,973,986` = `16,922` groups) before `g_deser`. -/
def w2CliDecryptSlotTightFineGrpS : Nat :=
  369159264 + w2TryDecryptTight12FineGrpS

theorem w2TryDecryptBaseFineGrpS_12_eq : w2TryDecryptBaseFineGrpS 12 = 38540818 := by decide
theorem w2TryDecryptTight12FineGrpS_eq : w2TryDecryptTight12FineGrpS = 739814722 := by decide
theorem w2TryDecryptBobFresh12FineGrpS_eq : w2TryDecryptBobFresh12FineGrpS = 319767460 := by decide
theorem w2CliDecryptSlotBaseFineGrpS_eq : w2CliDecryptSlotBaseFineGrpS = 407700082 := by decide
theorem w2CliDecryptSlotTightFineGrpS_eq : w2CliDecryptSlotTightFineGrpS = 1108973986 := by decide

/-- Existentially-packaged `W2TryDecryptTightEnv` witness at step cap `maxSteps`, convenient for
composing `tdEnv` refinements without carrying outer ghost parameters. -/
def W2TryDecryptTightExistsEnv (maxSteps : Nat)
    (SpqrStepEnv : List AllocEvent → Prop) (evs : List AllocEvent) : Prop :=
  ∃ (dhCap : Nat) (needGrow : Bool) (caps : List Nat) (withAddr errAlloc : Bool) (ctLen : Nat),
    caps.length ≤ maxSteps ∧
    W2TryDecryptTightEnv dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen evs

theorem w2TryDecryptTightExistsEnv_fine_groupSpec {maxSteps g_spqr : Nat}
    {SpqrStepEnv : List AllocEvent → Prop}
    (hspqr : PhaseGroupSpec fineCostModel SpqrStepEnv g_spqr) :
    PhaseGroupSpec fineCostModel (W2TryDecryptTightExistsEnv maxSteps SpqrStepEnv)
      (w2TryDecryptBaseFineGrpS maxSteps + g_spqr) where
  groups_le st0 {_} := fun ⟨dhCap, needGrow, _caps, withAddr, errAlloc, ctLen, hcaps, hEnv⟩ =>
    (w2TryDecryptTightEnv_fine_groupSpec dhCap needGrow withAddr errAlloc ctLen hcaps
      hspqr).groups_le st0 hEnv

/-- Bundled `SpqrRecvC07TightEnv` witness tuple (data bundle, not an `Env` predicate) for clean
guarded-witness composition without unguarded existential `Env` wrappers. -/
structure SpqrRecvC07Witness (F : ShaCompress) : Type where
  pre_pb : PqRatchetState
  vn : VersionNegotiationPB
  pb : V1State
  st0 : States spqrPolyApi (spqrAuthApi F)
  sckaMsg : Message spqrPolyApi
  v : V1Recv spqrPolyApi (spqrAuthApi F)
  xInit : InitInnerGhost
  xNew : ChainNewGhost
  xAdd : ChainAddEpochGhost
  xRk : ChainRecvKeyGhost
  xSInto : StatesIntoPbGhost F
  xCInto : ChainIntoPbCall

/-- Curried `SpqrRecvC07TightEnv F K StatesRecvProtoEnv` at a concrete `SpqrRecvC07Witness F`. -/
abbrev SpqrRecvC07ProtoStep (F : ShaCompress) (K : MlKem) (stBytes : Bytes)
    (w : SpqrRecvC07Witness F) : List AllocEvent → Prop :=
  SpqrRecvC07TightEnv F K StatesRecvProtoEnv
    stBytes w.pre_pb w.vn w.pb w.st0 w.sckaMsg w.v w.xInit w.xNew w.xAdd w.xRk w.xSInto w.xCInto

/-- Curried `SpqrRecvC07TightEnv F K StatesRecvEnv` at a concrete `SpqrRecvC07Witness F`. -/
abbrev SpqrRecvC07RawStep (F : ShaCompress) (K : MlKem) (stBytes : Bytes)
    (w : SpqrRecvC07Witness F) : List AllocEvent → Prop :=
  SpqrRecvC07TightEnv F K StatesRecvEnv
    stBytes w.pre_pb w.vn w.pb w.st0 w.sckaMsg w.v w.xInit w.xNew w.xAdd w.xRk w.xSInto w.xCInto

theorem spqrRecvC07_c09a_witness_fine_groupSpec
    (F : ShaCompress) (K : MlKem) (stBytes : Bytes) (w : SpqrRecvC07Witness F)
    (hDom : SpqrRecvTightDomain F K stBytes w.xAdd w.xRk) :
    PhaseGroupSpec fineCostModel (SpqrRecvC07ProtoStep F K stBytes w) spqrRecvTightFineGrpS :=
  spqrRecvParts_c07_c09a_phaseGroupSpec_tight F K
    stBytes w.pre_pb w.vn w.pb w.st0 w.sckaMsg w.v w.xInit w.xNew w.xAdd w.xRk w.xSInto w.xCInto
    hDom

theorem spqrRecvC07_c09a_rawEnv_witness_fine_groupSpec
    (F : ShaCompress) (K : MlKem) (stBytes : Bytes) (w : SpqrRecvC07Witness F)
    (hDom : SpqrRecvTightDomain F K stBytes w.xAdd w.xRk) :
    PhaseGroupSpec fineCostModel (SpqrRecvC07RawStep F K stBytes w) spqrRecvTightFineGrpS :=
  spqrRecvParts_c07_c09a_phaseGroupSpec_tight_rawEnv F K
    stBytes w.pre_pb w.vn w.pb w.st0 w.sckaMsg w.v w.xInit w.xNew w.xAdd w.xRk w.xSInto w.xCInto
    hDom

theorem spqrRecvC07_c09a_guarded_fine_groupSpec
    (F : ShaCompress) (K : MlKem) (stBytes : Bytes)
    {Guard : SpqrRecvC07Witness F → Prop}
    (hDom : ∀ w, Guard w → SpqrRecvTightDomain F K stBytes w.xAdd w.xRk) :
    PhaseGroupSpec fineCostModel
      (fun evs => ∃ w, Guard w ∧ SpqrRecvC07ProtoStep F K stBytes w evs)
      spqrRecvTightFineGrpS where
  groups_le st_m {_} := fun ⟨w, hG, hEnv⟩ =>
    (spqrRecvC07_c09a_witness_fine_groupSpec F K stBytes w (hDom w hG)).groups_le st_m hEnv

theorem spqrRecvC07_c09a_rawEnv_guarded_fine_groupSpec
    (F : ShaCompress) (K : MlKem) (stBytes : Bytes)
    {Guard : SpqrRecvC07Witness F → Prop}
    (hDom : ∀ w, Guard w → SpqrRecvTightDomain F K stBytes w.xAdd w.xRk) :
    PhaseGroupSpec fineCostModel
      (fun evs => ∃ w, Guard w ∧ SpqrRecvC07RawStep F K stBytes w evs)
      spqrRecvTightFineGrpS where
  groups_le st_m {_} := fun ⟨w, hG, hEnv⟩ =>
    (spqrRecvC07_c09a_rawEnv_witness_fine_groupSpec F K stBytes w (hDom w hG)).groups_le st_m hEnv

/-- Concrete `W2TryDecryptTightEnv` + `SpqrRecvC07TightEnv` (`StatesRecvProtoEnv`) `PhaseGroupSpec`
at arbitrary `maxSteps`. -/
theorem w2TryDecryptTight_c07_c09a_fine_groupSpec
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat} {maxSteps : Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (hcaps : caps.length ≤ maxSteps)
    (F : ShaCompress) (K : MlKem) (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptBaseFineGrpS maxSteps + spqrRecvTightFineGrpS) :=
  w2TryDecryptTightEnv_fine_groupSpec dhCap needGrow withAddr errAlloc ctLen hcaps
    (spqrRecvParts_c07_c09a_phaseGroupSpec_tight F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom)

/-- `maxSteps = 12` specialization of `w2TryDecryptTight_c07_c09a_fine_groupSpec`:
`w2TryDecryptTight12FineGrpS = 739,814,722` (`11,289` groups). -/
theorem w2TryDecryptTight12_c07_c09a_fine_groupSpec
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (hcaps : caps.length ≤ 12)
    (F : ShaCompress) (K : MlKem) (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvProtoEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      w2TryDecryptTight12FineGrpS :=
  w2TryDecryptTight_c07_c09a_fine_groupSpec dhCap needGrow withAddr errAlloc ctLen hcaps
    F K stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom

/-- Plain-`StatesRecvEnv` `maxSteps = 12` companion (`739,814,722`). -/
theorem w2TryDecryptTight12_c07_c09a_rawEnv_fine_groupSpec
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat}
    (withAddr errAlloc : Bool) (ctLen : Nat)
    (hcaps : caps.length ≤ 12)
    (F : ShaCompress) (K : MlKem) (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      w2TryDecryptTight12FineGrpS :=
  w2TryDecryptTightEnv_fine_groupSpec dhCap needGrow withAddr errAlloc ctLen hcaps
    (spqrRecvParts_c07_c09a_phaseGroupSpec_tight_rawEnv F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom)

/-- Witness-guarded `maxSteps = 12` `try_decrypt` + `SpqrRecvC07ProtoStep` bound (`739,814,722`),
compatible with any pure pre-state guard `Guard` (`spqrDecodeState` / `chainFrom` / `v1ChainAfterKey`). -/
theorem w2TryDecryptTightExists12_c07_c09a_guarded_fine_groupSpec
    (F : ShaCompress) (K : MlKem) (stBytes : Bytes)
    {Guard : SpqrRecvC07Witness F → Prop}
    (hDom : ∀ w, Guard w → SpqrRecvTightDomain F K stBytes w.xAdd w.xRk) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightExistsEnv 12
        (fun evs => ∃ w, Guard w ∧ SpqrRecvC07ProtoStep F K stBytes w evs))
      w2TryDecryptTight12FineGrpS :=
  w2TryDecryptTightExistsEnv_fine_groupSpec (spqrRecvC07_c09a_guarded_fine_groupSpec F K stBytes hDom)

/-- Plain-`StatesRecvEnv` witness-guarded `maxSteps = 12` companion (`739,814,722`). -/
theorem w2TryDecryptTightExists12_c07_c09a_rawEnv_guarded_fine_groupSpec
    (F : ShaCompress) (K : MlKem) (stBytes : Bytes)
    {Guard : SpqrRecvC07Witness F → Prop}
    (hDom : ∀ w, Guard w → SpqrRecvTightDomain F K stBytes w.xAdd w.xRk) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptTightExistsEnv 12
        (fun evs => ∃ w, Guard w ∧ SpqrRecvC07RawStep F K stBytes w evs))
      w2TryDecryptTight12FineGrpS :=
  w2TryDecryptTightExistsEnv_fine_groupSpec
    (spqrRecvC07_c09a_rawEnv_guarded_fine_groupSpec F K stBytes hDom)

private theorem w2Slot_reassoc (a b c d : Nat) :
    a + b + (c + d) ≤ (a + c) + b + d := by
  omega

/-- Parametric-`g_spqr` whisper CLI slot `PhaseGroupSpec`: wraps
`W2DecryptSlotPeak.w2CliDecryptSlot_polls_phaseGroupSpec` for any `tdEnv` bounded by
`W2TryDecryptTightExistsEnv 12 (SpqrStepEnv ...)` with `PhaseGroupSpec fineCostModel (SpqrStepEnv ...) g_spqr`,
yielding `w2CliDecryptSlotBaseFineGrpS + g_deser + g_spqr` (`407,700,082 + g_deser + g_spqr`). -/
theorem w2CliDecryptSlot_of_spqr_fine_groupSpec {A : RustAlloc}
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
    (SpqrStepEnv : SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      SessionGhost → SessionGhost → List AllocEvent → Prop)
    {Kspqr fileCap g_deser g_spqr : Nat}
    (hrem : x.rem.val = peer.val)
    (hFilesOk : FilesOkPeer scopeIn F peer.val)
    (hValid : PeerSpqrTightValidAt Kspqr F x.rem.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (DeserEnv bs) g_deser)
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
    (hTdImp : ∀ rec ses G G₁,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      ValidEncoderPtsAt Kspqr ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      ∀ evs, tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁) evs →
        W2TryDecryptTightExistsEnv 12 (SpqrStepEnv rec ses G G₁) evs)
    (hSpqr : ∀ rec ses G G₁,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      ValidEncoderPtsAt Kspqr ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      PhaseGroupSpec fineCostModel (SpqrStepEnv rec ses G G₁) g_spqr) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4
    PhaseGroupSpec fineCostModel
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity C (spqrV1 C.F K) parse tdEnv scopeKit x)
      (w2CliDecryptSlotBaseFineGrpS + g_deser + g_spqr) := by
  intro kit ikit
  have hSlot := w2CliDecryptSlot_polls_phaseGroupSpec
    F pathOk peer s1 s2 s3 s4 t1 t2 t3 t4 C K parse x DeserEnv peerIdKeyName kitEnv ikitEnv tdEnv
    hrem hFilesOk hValid hSessFileCap hDeser hLoadEq hTrustEq hSaveEq hStoreEq
    (fun rec ses G G₁ hIn hcur hgv hDom hRel hVe hVcp hLt hLe =>
      (w2TryDecryptTightExistsEnv_fine_groupSpec
        (hSpqr rec ses G G₁ hIn hcur hgv hDom hRel hVe hVcp hLt hLe)).of_imp
        (hTdImp rec ses G G₁ hIn hcur hgv hDom hRel hVe hVcp hLt hLe))
  exact hSlot.mono (w2Slot_reassoc 369159264 g_deser (w2TryDecryptBaseFineGrpS 12) g_spqr)

/-- Whisper CLI slot `PhaseGroupSpec` specializing `w2CliDecryptSlot_of_spqr_fine_groupSpec` at
`g_spqr = spqrRecvTightFineGrpS` (`701,273,904`) for any pure-guarded `SpqrStepEnv`, yielding
`1,108,973,986 + g_deser`. -/
theorem w2CliDecryptSlot_tight_fine_groupSpec {A : RustAlloc}
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
    (SpqrStepEnv : SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      SessionGhost → SessionGhost → List AllocEvent → Prop)
    {Kspqr fileCap g_deser : Nat}
    (hrem : x.rem.val = peer.val)
    (hFilesOk : FilesOkPeer scopeIn F peer.val)
    (hValid : PeerSpqrTightValidAt Kspqr F x.rem.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (DeserEnv bs) g_deser)
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
    (hTdImp : ∀ rec ses G G₁,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      ValidEncoderPtsAt Kspqr ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      ∀ evs, tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁) evs →
        W2TryDecryptTightExistsEnv 12 (SpqrStepEnv rec ses G G₁) evs)
    (hSpqr : ∀ rec ses G G₁,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      ValidEncoderPtsAt Kspqr ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      PhaseGroupSpec fineCostModel (SpqrStepEnv rec ses G G₁) spqrRecvTightFineGrpS) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4
    PhaseGroupSpec fineCostModel
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity C (spqrV1 C.F K) parse tdEnv scopeKit x)
      (w2CliDecryptSlotTightFineGrpS + g_deser) := by
  intro kit ikit
  have h := w2CliDecryptSlot_of_spqr_fine_groupSpec
    F pathOk peer s1 s2 s3 s4 t1 t2 t3 t4 C K parse x DeserEnv peerIdKeyName kitEnv ikitEnv tdEnv
    SpqrStepEnv hrem hFilesOk hValid hSessFileCap hDeser hLoadEq hTrustEq hSaveEq hStoreEq
    hTdImp hSpqr
  refine h.mono ?_
  have heq : w2CliDecryptSlotBaseFineGrpS + spqrRecvTightFineGrpS = w2CliDecryptSlotTightFineGrpS := by
    decide
  omega

/-- Concrete `C07 + C09a` (`StatesRecvProtoEnv`) W2 CLI Slot `PhaseGroupSpec`
(`1,108,973,986 + g_deser`) discharging `hSpqr` via a pure pre-state guard `Guard`. -/
theorem w2CliDecryptSlot_tight_c07_c09a_fine_groupSpec {A : RustAlloc}
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
    (Guard : SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      SessionGhost → SessionGhost → SpqrRecvC07Witness C.F → Prop)
    {Kspqr fileCap g_deser : Nat}
    (hrem : x.rem.val = peer.val)
    (hFilesOk : FilesOkPeer scopeIn F peer.val)
    (hValid : PeerSpqrTightValidAt Kspqr F x.rem.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (DeserEnv bs) g_deser)
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
    (hGuardDom : ∀ rec ses G G₁ w,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      ValidEncoderPtsAt Kspqr ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      Guard rec ses G G₁ w →
      SpqrRecvTightDomain C.F K ses.state.pqRatchetState w.xAdd w.xRk)
    (hTdImp : ∀ rec ses G G₁,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      ValidEncoderPtsAt Kspqr ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      ∀ evs, tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁) evs →
        W2TryDecryptTightExistsEnv 12
          (fun evs' => ∃ w, Guard rec ses G G₁ w ∧
            SpqrRecvC07ProtoStep C.F K ses.state.pqRatchetState w evs') evs) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4
    PhaseGroupSpec fineCostModel
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity C (spqrV1 C.F K) parse tdEnv scopeKit x)
      (w2CliDecryptSlotTightFineGrpS + g_deser) :=
  w2CliDecryptSlot_tight_fine_groupSpec
    F pathOk peer s1 s2 s3 s4 t1 t2 t3 t4 C K parse x DeserEnv peerIdKeyName kitEnv ikitEnv tdEnv
    (fun rec ses G G₁ evs' =>
      ∃ w, Guard rec ses G G₁ w ∧ SpqrRecvC07ProtoStep C.F K ses.state.pqRatchetState w evs')
    hrem hFilesOk hValid hSessFileCap hDeser hLoadEq hTrustEq hSaveEq hStoreEq hTdImp
    (fun rec ses G G₁ hIn hcur hgv hDom hRel hVe hVcp hLt hLe =>
      spqrRecvC07_c09a_guarded_fine_groupSpec C.F K ses.state.pqRatchetState
        (fun w hG => hGuardDom rec ses G G₁ w hIn hcur hgv hDom hRel hVe hVcp hLt hLe hG))

/-- Plain-`StatesRecvEnv` companion to `w2CliDecryptSlot_tight_c07_c09a_fine_groupSpec`
(`1,108,973,986 + g_deser`). -/
theorem w2CliDecryptSlot_tight_c07_c09a_rawEnv_fine_groupSpec {A : RustAlloc}
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
    (Guard : SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      SessionGhost → SessionGhost → SpqrRecvC07Witness C.F → Prop)
    {Kspqr fileCap g_deser : Nat}
    (hrem : x.rem.val = peer.val)
    (hFilesOk : FilesOkPeer scopeIn F peer.val)
    (hValid : PeerSpqrTightValidAt Kspqr F x.rem.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (DeserEnv bs) g_deser)
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
    (hGuardDom : ∀ rec ses G G₁ w,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      ValidEncoderPtsAt Kspqr ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      Guard rec ses G G₁ w →
      SpqrRecvTightDomain C.F K ses.state.pqRatchetState w.xAdd w.xRk)
    (hTdImp : ∀ rec ses G G₁,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      ValidEncoderPtsAt Kspqr ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      ∀ evs, tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁) evs →
        W2TryDecryptTightExistsEnv 12
          (fun evs' => ∃ w, Guard rec ses G G₁ w ∧
            SpqrRecvC07RawStep C.F K ses.state.pqRatchetState w evs') evs) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4
    PhaseGroupSpec fineCostModel
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity C (spqrV1 C.F K) parse tdEnv scopeKit x)
      (w2CliDecryptSlotTightFineGrpS + g_deser) :=
  w2CliDecryptSlot_tight_fine_groupSpec
    F pathOk peer s1 s2 s3 s4 t1 t2 t3 t4 C K parse x DeserEnv peerIdKeyName kitEnv ikitEnv tdEnv
    (fun rec ses G G₁ evs' =>
      ∃ w, Guard rec ses G G₁ w ∧ SpqrRecvC07RawStep C.F K ses.state.pqRatchetState w evs')
    hrem hFilesOk hValid hSessFileCap hDeser hLoadEq hTrustEq hSaveEq hStoreEq hTdImp
    (fun rec ses G G₁ hIn hcur hgv hDom hRel hVe hVcp hLt hLe =>
      spqrRecvC07_c09a_rawEnv_guarded_fine_groupSpec C.F K ses.state.pqRatchetState
        (fun w hG => hGuardDom rec ses G G₁ w hIn hcur hgv hDom hRel hVe hVcp hLt hLe hG))

/-! ## Primitives, Domain Predicates, & Unconditional CLI Store Steps -/

/-- Domain witness lifting `SessionGhostValid` + `SessionCloneDom` to a bare `SessionState`. -/
def StateCloneDom (pqCap : Nat) (G : SessionGhost) (st : SessionState (List (BitVec 8))) : Prop :=
  ∃ ses : Session (List (BitVec 8)),
    ses.state = st ∧ SessionGhostValid G ses ∧ SessionCloneDom pqCap ses

/-- Bundled `RecordGhostValid` + `SessionCloneDom` invariant on a `SessionRecord`. -/
def RecordDom (pqCap : Nat) (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) : Prop :=
  RecordGhostValid g r ∧ ∀ ses, r.currentSession = some ses → SessionCloneDom pqCap ses

/-- Bundled `SessionGhostValid` + `SessionCloneDom` invariant on a `prev1` output `Session`. -/
def SessionOutDom (pqCap : Nat) (G : SessionGhost) (ses : Session (List (BitVec 8))) : Prop :=
  SessionGhostValid G ses ∧ SessionCloneDom pqCap ses

theorem segCloneEnv_stateDom_fine_groupSpec {pqCap : Nat}
    {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    (hdom : StateCloneDom pqCap G st) :
    PhaseGroupSpec fineCostModel (SegCloneEnv G st) segCloneDomFineGrpS := by
  obtain ⟨ses, hst, hgv, hd⟩ := hdom
  subst hst
  exact segCloneEnv_dom_fine_groupSpec hgv hd

theorem recordSerializeCancelEnv_recordDom_fine_groupSpec {pqCap : Nat}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    (hdom : RecordDom pqCap g r) :
    PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv g r) recordSerializeDomFineGrpS :=
  recordSerializeCancelEnv_dom_fine_groupSpec hdom.1 hdom.2

private theorem w4NonFreeCount_eq :
    ∀ evs : List AllocEvent,
      LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak.nonFreeCount evs =
        LibsignalBinary.Proofs.PeakBudget.GroupCreditKit.nonFreeCount evs
  | [] => rfl
  | ev :: tl => by
    cases ev <;>
      simp [LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak.nonFreeCount,
        LibsignalBinary.Proofs.PeakBudget.GroupCreditKit.nonFreeCount,
        w4NonFreeCount_eq tl]

theorem w4BoundedEvs_nonFreeBound (maxOps maxReq : Nat) :
    NonFreeBound (W4BoundedEvs maxOps maxReq) maxOps := by
  intro evs h
  rw [← w4NonFreeCount_eq]
  exact h.1

theorem w4BoundedEvs_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (maxOps maxReq : Nat) :
    PhaseGroupSpec M (W4BoundedEvs maxOps maxReq) (3 * FineScale * maxOps) :=
  PhaseGroupSpec.of_nonFreeBound M (w4BoundedEvs_nonFreeBound maxOps maxReq)

theorem leavesDoReserveEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (x : DoReserveCall) :
    PhaseGroupSpec M (DoReserveEnv x) (3 * FineScale) := by
  by_cases hc : x.cap = 0#64
  · refine (PhaseGroupSpec.rustAlloc_any M
      (reserveCap x.cap.toNat x.bs.length x.additional) 1).of_imp ?_
    intro evs he
    simpa [DoReserveEnv, doReserveEvents, hc] using he
  · refine (PhaseGroupSpec.rustRealloc_any M x.cap.toNat
      (reserveCap x.cap.toNat x.bs.length x.additional) 1).of_imp ?_
    intro evs he
    simpa [DoReserveEnv, doReserveEvents, hc] using he

/-- Exact `fineCostModel` scaled group weight for `KemSerialize1569Env` (`1569 B` small alloc). -/
def kemSerialize1569FineGrpS : Nat := fineSmallAllocGroupS 1569

/-- Exact `fineCostModel` scaled group weight for `GrowOneSpeEnv 0#64` / `W4ErrTailEnv`
(`192 B` `SignalProtocolError` box alloc). -/
def w4ErrTailFineGrpS : Nat := fineSmallAllocGroupS 192

theorem kemSerialize1569Env_fine_groupSpec :
    PhaseGroupSpec fineCostModel KemSerialize1569Env kemSerialize1569FineGrpS := by
  have hm : (1569 : Nat) ≤ MmapThresholdReq := by decide
  have h := PhaseGroupSpec.rustAlloc_small fineCostModel (size := 1569) (align := 1) (by decide) hm
  rw [smallAllocGroupS_fineCostModel_eq] at h
  exact h.of_imp (fun _ he => he)

theorem growOneSpeZero_fine_groupSpec :
    PhaseGroupSpec fineCostModel (GrowOneSpeEnv 0#64) w4ErrTailFineGrpS := by
  have hm : (192 : Nat) ≤ MmapThresholdReq := by decide
  have h := PhaseGroupSpec.rustAlloc_small fineCostModel (size := 192) (align := 8) (by decide) hm
  rw [smallAllocGroupS_fineCostModel_eq] at h
  refine h.of_imp ?_
  rintro _ (⟨_, he⟩ | ⟨hne, _⟩)
  · exact he
  · exact False.elim (hne rfl)

theorem w4ErrTail_fine_groupSpec :
    PhaseGroupSpec fineCostModel W4ErrTailEnv w4ErrTailFineGrpS := by
  have hSpe : PhaseGroupSpec fineCostModel (SeqEnv (GrowOneSpeEnv 0#64) FreeOnlyEvs)
      w4ErrTailFineGrpS :=
    (growOneSpeZero_fine_groupSpec.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
      (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hSpe).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem boxAllocEnv_le_28_fine_groupSpec {boxSz : Nat} (hbox : boxSz ≤ 28) :
    PhaseGroupSpec fineCostModel (BoxAllocEnv boxSz) 11056 := by
  have h0 : PhaseGroupSpec fineCostModel (fun evs => boxSz = 0 ∧ evs = []) 0 :=
    (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => h.2)
  have h1 : PhaseGroupSpec fineCostModel
      (fun evs => 0 < boxSz ∧ evs = rustAllocEvents boxSz 8) 11056 :=
    (fine_rustAlloc_le_28 (sz := boxSz) (al := 8) (by decide) hbox).of_imp (fun _ h => h.2)
  exact (h0.or h1).mono (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem boxAllocEnv_le_44_fine_groupSpec {boxSz : Nat} (hbox : boxSz ≤ 44) :
    PhaseGroupSpec fineCostModel (BoxAllocEnv boxSz) 16659 := by
  have h0 : PhaseGroupSpec fineCostModel (fun evs => boxSz = 0 ∧ evs = []) 0 :=
    (PhaseGroupSpec.nil fineCostModel).of_imp (fun _ h => h.2)
  have h1 : PhaseGroupSpec fineCostModel
      (fun evs => 0 < boxSz ∧ evs = rustAllocEvents boxSz 8) 16659 :=
    (fine_rustAlloc_le_44 (sz := boxSz) (al := 8) (by decide) hbox).of_imp (fun _ h => h.2)
  exact (h0.or h1).mono (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem w4BoxedStoreStep_le_28_fine_groupSpec {boxSz g_p : Nat} (hbox : boxSz ≤ 28)
    {E_poll : List AllocEvent → Prop}
    (hpoll : PhaseGroupSpec fineCostModel E_poll g_p) :
    PhaseGroupSpec fineCostModel (W4BoxedStoreStepEnv boxSz E_poll) (11056 + g_p) :=
  ((boxAllocEnv_le_28_fine_groupSpec hbox).seq
    (hpoll.seq (PhaseGroupSpec.freeOnly fineCostModel))).mono (by omega)

theorem w4BoxedStoreStep_le_44_fine_groupSpec {boxSz g_p : Nat} (hbox : boxSz ≤ 44)
    {E_poll : List AllocEvent → Prop}
    (hpoll : PhaseGroupSpec fineCostModel E_poll g_p) :
    PhaseGroupSpec fineCostModel (W4BoxedStoreStepEnv boxSz E_poll) (16659 + g_p) :=
  ((boxAllocEnv_le_44_fine_groupSpec hbox).seq
    (hpoll.seq (PhaseGroupSpec.freeOnly fineCostModel))).mono (by omega)

theorem phaseGroupSpec_ite_nil {M : AllocCostModel} [HasFineGroupCredit M]
    (b : Bool) {E : List AllocEvent → Prop} {g : Nat}
    (h : b = true → PhaseGroupSpec M E g) :
    PhaseGroupSpec M (if b then E else (· = [])) g := by
  cases b
  · exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
  · simpa using h rfl

/-- Scaled group bound (`9,268,291`) for `16 B`-box `W4SmallStoreStepEnv 16` (`spkGet`, `kpkGet`,
`pkGet`, `pkRemove`, `idKp`, `idRegId`). -/
def w4SmallStoreStep16FineGrpS : Nat := 11056 + (16659 + 141 * FineScale)

/-- Scaled group bound (`9,273,894`) for `32 B`-box `W4SmallStoreStepEnv 32` (`idTrust`, `idSave`,
`kpkMark`). -/
def w4SmallStoreStep32FineGrpS : Nat := 16659 + (16659 + 141 * FineScale)

/-- Base scaled group bound (`2,763,568`) for `24 B`-box `W4SessLoadStepEnv` before `g_deser`. -/
def w4SessLoadStepBaseFineGrpS : Nat := 11056 + 42 * FineScale

/-- Scaled group bound (`169,069,209`) for `32 B`-box `0`-prev `W4SessStoreStepEnv` under
`RecordDom`. -/
def w4SessStoreStepDomFineGrpS : Nat := 16659 + (6 * FineScale + recordSerializeDomFineGrpS)

/-- Scaled group bound (`169,276,873`) for `32 B`-box `prev1` `W4SessStorePrev1StepEnv` under
`SessionOutDom`. -/
def w4SessStorePrev1StepDomFineGrpS : Nat := 16659 + (6 * FineScale + serializePrev1DomFineGrpS)

theorem w4SmallStoreStep16FineGrpS_eq : w4SmallStoreStep16FineGrpS = 9268291 := by decide
theorem w4SmallStoreStep32FineGrpS_eq : w4SmallStoreStep32FineGrpS = 9273894 := by decide
theorem w4SessLoadStepBaseFineGrpS_eq : w4SessLoadStepBaseFineGrpS = 2763568 := by decide
theorem w4SessStoreStepDomFineGrpS_eq : w4SessStoreStepDomFineGrpS = 169069209 := by decide
theorem w4SessStorePrev1StepDomFineGrpS_eq : w4SessStorePrev1StepDomFineGrpS = 169276873 := by
  decide

theorem w4SmallStoreStep16_fine_groupSpec
    (rd : ReadRule) (files : FsFiles) (dir : DirGhost) (name : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (W4SmallStoreStepEnv 16 rd files dir name)
      w4SmallStoreStep16FineGrpS :=
  w4BoxedStoreStep_le_28_fine_groupSpec (by decide)
    (cliSmallStorePollEnv_fine_groupSpec rd files dir name)

theorem w4SmallStoreStep32_fine_groupSpec
    (rd : ReadRule) (files : FsFiles) (dir : DirGhost) (name : List (BitVec 8)) :
    PhaseGroupSpec fineCostModel (W4SmallStoreStepEnv 32 rd files dir name)
      w4SmallStoreStep32FineGrpS :=
  w4BoxedStoreStep_le_44_fine_groupSpec (by decide)
    (cliSmallStorePollEnv_fine_groupSpec rd files dir name)

theorem w4SessLoadStep_fine_groupSpec
    (rd : ReadRule) {DeserEnv : List (BitVec 8) → List AllocEvent → Prop} {g_deser : Nat}
    (files : FsFiles) (sessDir : DirGhost) (peer : AddrGhost)
    (hdeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (DeserEnv bs) g_deser) :
    PhaseGroupSpec fineCostModel (W4SessLoadStepEnv rd DeserEnv files sessDir peer)
      (w4SessLoadStepBaseFineGrpS + g_deser) := by
  have h := w4BoxedStoreStep_le_28_fine_groupSpec (boxSz := 24) (by decide)
    (cliSessLoadPollEnv_groupSpec fineCostModel (rd := rd) files sessDir peer hdeser)
  refine h.mono ?_
  unfold w4SessLoadStepBaseFineGrpS
  omega

theorem w4SessStoreStep_fine_groupSpec
    (sessDir : DirGhost) (peer : AddrGhost)
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))} {g_ser : Nat}
    (hser : PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv g_rec r_rec) g_ser) :
    PhaseGroupSpec fineCostModel (W4SessStoreStepEnv sessDir peer g_rec r_rec)
      (16659 + (6 * FineScale + g_ser)) :=
  w4BoxedStoreStep_le_44_fine_groupSpec (by decide)
    (cliSessStorePollEnv_groupSpec fineCostModel sessDir peer hser)

theorem w4SessStoreStep_dom_fine_groupSpec {pqCap : Nat}
    (sessDir : DirGhost) (peer : AddrGhost)
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))}
    (hdom : RecordDom pqCap g_rec r_rec) :
    PhaseGroupSpec fineCostModel (W4SessStoreStepEnv sessDir peer g_rec r_rec)
      w4SessStoreStepDomFineGrpS :=
  w4BoxedStoreStep_le_44_fine_groupSpec (by decide)
    (cliSessStorePollEnv_dom_fine_groupSpec sessDir peer hdom.1 hdom.2)

theorem w4SessStorePrev1Step_fine_groupSpec
    (sessDir : DirGhost) (peer : AddrGhost)
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)} {g_ser1 : Nat}
    (hser1 : PhaseGroupSpec fineCostModel (SerializePrev1CancelEnv G sess enc) g_ser1) :
    PhaseGroupSpec fineCostModel (W4SessStorePrev1StepEnv sessDir peer G sess enc)
      (16659 + (6 * FineScale + g_ser1)) :=
  w4BoxedStoreStep_le_44_fine_groupSpec (by decide)
    (cliSessStorePollPrev1Env_groupSpec fineCostModel sessDir peer hser1)

theorem w4SessStorePrev1Step_dom_fine_groupSpec {pqCap : Nat}
    (sessDir : DirGhost) (peer : AddrGhost)
    {G : SessionGhost} {sess : Session (List (BitVec 8))} (enc : List (BitVec 8))
    (hdom : SessionOutDom pqCap G sess) :
    PhaseGroupSpec fineCostModel (W4SessStorePrev1StepEnv sessDir peer G sess enc)
      w4SessStorePrev1StepDomFineGrpS :=
  w4BoxedStoreStep_le_44_fine_groupSpec (by decide)
    (cliSessStorePollPrev1Env_dom_fine_groupSpec sessDir peer enc hdom.1 hdom.2)

/-! ## Stages P1–P4, 4-Arm `W4DecryptPrekeySlotEnv`, & Outer `W4SlotR3bEnv` -/

/-! ### 3.1 Stage P1 (`load_session` → `is_trusted_identity` → optional untrusted `StringCloneEnv`) -/

def w4StageP1OkBaseFineGrpS : Nat :=
  w4SessLoadStepBaseFineGrpS + w4SmallStoreStep32FineGrpS

def w4StageP1UntrustedBaseFineGrpS : Nat :=
  w4StageP1OkBaseFineGrpS + 3 * FineScale

theorem w4StageP1OkBaseFineGrpS_eq : w4StageP1OkBaseFineGrpS = 12037462 := by decide
theorem w4StageP1UntrustedBaseFineGrpS_eq : w4StageP1UntrustedBaseFineGrpS = 12234070 := by decide

private theorem add_right_comm_le (a b c : Nat) : (a + b) + c ≤ (a + c) + b := by omega

theorem w4StageP1OkCli_fine_groupSpec
    (rd : ReadRule) {DeserEnv : List (BitVec 8) → List AllocEvent → Prop} {g_deser : Nat}
    (files : FsFiles) (sessDir peersDir : DirGhost) (peer : AddrGhost)
    (hdeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (DeserEnv bs) g_deser) :
    PhaseGroupSpec fineCostModel (W4StageP1OkCliEnv rd DeserEnv files sessDir peersDir peer)
      (w4StageP1OkBaseFineGrpS + g_deser) := by
  have hLoad := w4SessLoadStep_fine_groupSpec rd files sessDir peer hdeser
  have hTrust := w4SmallStoreStep32_fine_groupSpec rd files peersDir (addressText peer.val)
  exact (hLoad.seq hTrust).mono
    (add_right_comm_le w4SessLoadStepBaseFineGrpS g_deser w4SmallStoreStep32FineGrpS)

theorem w4StageP1UntrustedCli_fine_groupSpec
    (rd : ReadRule) {DeserEnv : List (BitVec 8) → List AllocEvent → Prop} {g_deser : Nat}
    (files : FsFiles) (sessDir peersDir : DirGhost) (peer : AddrGhost)
    (hdeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (DeserEnv bs) g_deser) :
    PhaseGroupSpec fineCostModel (W4StageP1UntrustedCliEnv rd DeserEnv files sessDir peersDir peer)
      (w4StageP1UntrustedBaseFineGrpS + g_deser) := by
  have hLoad := w4SessLoadStep_fine_groupSpec rd files sessDir peer hdeser
  have hTrust := w4SmallStoreStep32_fine_groupSpec rd files peersDir (addressText peer.val)
  have hClone : PhaseGroupSpec fineCostModel
      (SeqEnv (LibsignalBinary.Heap.RustStdAllocBudgetBridge.StringCloneEnv peer.name) FreeOnlyEvs)
      (3 * FineScale) :=
    ((stringCloneEnv_groupSpec fineCostModel peer.name).seq
      (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  refine (hLoad.seq (hTrust.seq hClone)).mono ?_
  have hsum : w4SessLoadStepBaseFineGrpS + (w4SmallStoreStep32FineGrpS + 3 * FineScale) =
      w4StageP1UntrustedBaseFineGrpS := by
    unfold w4StageP1UntrustedBaseFineGrpS w4StageP1OkBaseFineGrpS
    omega
  omega

/-! ### 3.2 Stage P2 (`Matched`, `PathA`, `init_bob`, and `PathC`) -/

theorem archivedTrialIter_groupSpec {α : Type} (M : AllocCostModel) [HasFineGroupCredit M]
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop} {g_dec g_tr : Nat} {x : α}
    (hDec : PhaseGroupSpec M (DecEnv x) g_dec)
    (hTr : PhaseGroupSpec M (TrialEnv x) g_tr)
    (hDrop : PhaseGroupSpec M (DropEnv x) 0) :
    PhaseGroupSpec M (ArchivedTrialIterEnv DecEnv TrialEnv DropEnv x) (g_dec + g_tr) :=
  ((hDec.concat hTr).concat hDrop).mono (Nat.le_of_eq (Nat.add_zero _))

theorem archivedTrialLoop_le4_groupSpec {α : Type} (M : AllocCostModel) [HasFineGroupCredit M]
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop} {g_dec g_tr : Nat} {xs : List α}
    (hlen4 : xs.length ≤ 4)
    (hDec : ∀ x ∈ xs, PhaseGroupSpec M (DecEnv x) g_dec)
    (hTr : ∀ x ∈ xs, PhaseGroupSpec M (TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ xs, PhaseGroupSpec M (DropEnv x) 0) :
    PhaseGroupSpec M (IterSeqEnv (ArchivedTrialIterEnv DecEnv TrialEnv DropEnv) xs)
      (4 * (g_dec + g_tr)) :=
  (PhaseGroupSpec.iterSeq_const (g_dec + g_tr) xs
    (fun x hx => archivedTrialIter_groupSpec M (hDec x hx) (hTr x hx) (hDrop x hx))).mono
    (Nat.mul_le_mul_right (g_dec + g_tr) hlen4)

theorem promoteStateArchive_groupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    {SerializeArchivedEnv VecPushEnv : List AllocEvent → Prop} {g_ser g_push : Nat}
    (hSer : PhaseGroupSpec M SerializeArchivedEnv g_ser)
    (hPush : PhaseGroupSpec M VecPushEnv g_push) :
    PhaseGroupSpec M (PromoteStateArchiveEnv SerializeArchivedEnv VecPushEnv) (g_ser + g_push) :=
  ((hSer.concat hPush).concat (PhaseGroupSpec.freeOnly M)).mono (Nat.le_of_eq (Nat.add_zero _))

theorem w4StageP2Matched_groupSpec {α : Type} (M : AllocCostModel) [HasFineGroupCredit M]
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop} {xs : List α}
    {g_arch : RecordGhost} {r_arch : SessionRecord (List (BitVec 8))}
    {VecPushEnv : List AllocEvent → Prop}
    {g_dec g_tr g_archSer g_push : Nat}
    (hlen4 : xs.length ≤ 4)
    (hDec : ∀ x ∈ xs, PhaseGroupSpec M (DecEnv x) g_dec)
    (hTr : ∀ x ∈ xs, PhaseGroupSpec M (TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ xs, PhaseGroupSpec M (DropEnv x) 0)
    (hArchSer : PhaseGroupSpec M (RecordSerializeCancelEnv g_arch r_arch) g_archSer)
    (hPush : PhaseGroupSpec M VecPushEnv g_push) :
    PhaseGroupSpec M
      (W4StageP2MatchedEnv DecEnv TrialEnv DropEnv xs g_arch r_arch VecPushEnv)
      (4 * (g_dec + g_tr) + g_archSer + g_push) := by
  have hLoop := archivedTrialLoop_le4_groupSpec M hlen4 hDec hTr hDrop
  have hProm : PhaseGroupSpec M
      (SeqEnv (PromoteStateArchiveEnv (RecordSerializeCancelEnv g_arch r_arch) VecPushEnv)
        FreeOnlyEvs)
      (g_archSer + g_push) :=
    ((promoteStateArchive_groupSpec M hArchSer hPush).seq (PhaseGroupSpec.freeOnly M)).mono
      (Nat.le_of_eq (Nat.add_zero _))
  have hTail := ((PhaseGroupSpec.freeOnly M).or hProm).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
  exact ((PhaseGroupSpec.freeOnly M).or (hLoop.seq hTail)).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, by omega⟩)

theorem w4StageP2Matched_dom_fine_groupSpec {α : Type} {pqCap : Nat}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop} {xs : List α}
    {g_arch : RecordGhost} {r_arch : SessionRecord (List (BitVec 8))}
    {VecPushEnv : List AllocEvent → Prop}
    {g_dec g_tr g_push : Nat}
    (hlen4 : xs.length ≤ 4)
    (hDec : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DecEnv x) g_dec)
    (hTr : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DropEnv x) 0)
    (hArchDom : RecordDom pqCap g_arch r_arch)
    (hPush : PhaseGroupSpec fineCostModel VecPushEnv g_push) :
    PhaseGroupSpec fineCostModel
      (W4StageP2MatchedEnv DecEnv TrialEnv DropEnv xs g_arch r_arch VecPushEnv)
      (4 * (g_dec + g_tr) + recordSerializeDomFineGrpS + g_push) :=
  w4StageP2Matched_groupSpec fineCostModel hlen4 hDec hTr hDrop
    (recordSerializeCancelEnv_recordDom_fine_groupSpec hArchDom) hPush

/-- Scaled group bound for `W4PqxdhAcceptEnv` on `fineCostModel`:
`3 * FineScale` (`DoReserveEnv`) + `12 * FineScale` (`≤ 4` EC key serializations) +
`kemSerialize1569FineGrpS` + `w4ErrTailFineGrpS`. -/
def w4PqxdhAcceptFineGrpS : Nat :=
  3 * FineScale + 12 * FineScale + kemSerialize1569FineGrpS + w4ErrTailFineGrpS

/-- Scaled group bound (`1,179,648` = `18` groups) for `W4BobSessionBuildEnv`. -/
def w4BobSessionBuildFineGrpS : Nat := 18 * FineScale

/-- Scaled group overhead around `E_spqrInit` in `W4InitBobEnv`. -/
def w4InitBobOuterFineGrpS : Nat :=
  w4PqxdhAcceptFineGrpS + w4BobSessionBuildFineGrpS

/-- Total scaled group bound for `W4InitBobSpqrEnv` (`InitialStateEnv` = `384 * FineScale`). -/
def w4InitBobSpqrFineGrpS : Nat :=
  w4InitBobOuterFineGrpS + 384 * FineScale

theorem w4PqxdhDhKeysEnv_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] (hasOpk : Bool) :
    PhaseGroupSpec M (W4PqxdhDhKeysEnv hasOpk) (12 * FineScale) := by
  refine (w4BoundedEvs_groupSpec M (if hasOpk then 4 else 3) 33).mono ?_
  cases hasOpk <;> decide

theorem w4PqxdhAcceptOk_fine_groupSpec (x_res : DoReserveCall) (hasOpk : Bool) :
    PhaseGroupSpec fineCostModel (W4PqxdhAcceptOkEnv x_res hasOpk)
      (3 * FineScale + 12 * FineScale + kemSerialize1569FineGrpS) := by
  have hRes := leavesDoReserveEnv_groupSpec fineCostModel x_res
  have hDh := w4PqxdhDhKeysEnv_groupSpec fineCostModel hasOpk
  have hKem := (kemSerialize1569Env_fine_groupSpec.seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  exact (hRes.seq (hDh.seq hKem)).mono (by omega)

theorem w4PqxdhAccept_fine_groupSpec (x_res : DoReserveCall) (hasOpk : Bool) :
    PhaseGroupSpec fineCostModel (W4PqxdhAcceptEnv x_res hasOpk) w4PqxdhAcceptFineGrpS := by
  have hOk := w4PqxdhAcceptOk_fine_groupSpec x_res hasOpk
  have hSpe := (growOneSpeZero_fine_groupSpec.seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  refine (hOk.or (hOk.seq hSpe)).mono ?_
  unfold w4PqxdhAcceptFineGrpS
  omega

theorem w4BobSessionBuild_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M W4BobSessionBuildEnv w4BobSessionBuildFineGrpS := by
  refine ((w4BoundedEvs_groupSpec M 6 68).seq (PhaseGroupSpec.freeOnly M)).mono ?_
  unfold w4BobSessionBuildFineGrpS
  decide

theorem w4InitBobEnv_fine_groupSpec (x_res : DoReserveCall) (hasOpk : Bool)
    {E_spqrInit : List AllocEvent → Prop} {g_spqrInit : Nat}
    (hSpqr : PhaseGroupSpec fineCostModel E_spqrInit g_spqrInit) :
    PhaseGroupSpec fineCostModel (W4InitBobEnv x_res hasOpk E_spqrInit)
      (w4InitBobOuterFineGrpS + g_spqrInit) := by
  have hPq := w4PqxdhAccept_fine_groupSpec x_res hasOpk
  have hBuild := w4BobSessionBuild_groupSpec fineCostModel
  refine (hPq.seq (hSpqr.seq hBuild)).mono ?_
  unfold w4InitBobOuterFineGrpS
  omega

theorem w4InitBobSpqr_fine_groupSpec (F : ShaCompress) (x_res : DoReserveCall) (hasOpk : Bool)
    (x_spqr : InitialStateGhost) :
    PhaseGroupSpec fineCostModel (W4InitBobSpqrEnv F x_res hasOpk x_spqr)
      w4InitBobSpqrFineGrpS := by
  have hSpqr : PhaseGroupSpec fineCostModel (InitialStateEnv F x_spqr) (384 * FineScale) :=
    (initialStateEnv_groupSpec fineCostModel F x_spqr).mono (by decide)
  exact w4InitBobEnv_fine_groupSpec x_res hasOpk hSpqr

/-- Unconditional scaled group bound for `W4StageP2PathACliEnv`. -/
def w4StageP2PathACliFineGrpS : Nat :=
  5 * w4SmallStoreStep16FineGrpS + w4InitBobSpqrFineGrpS + w4ErrTailFineGrpS

private theorem p2a_grp_le (s16 init err : Nat) :
    s16 + (s16 + (s16 + (s16 + (init + (s16 + err))))) ≤ 5 * s16 + init + err := by
  omega

theorem w4StageP2PathACli_fine_groupSpec
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (spkDir kpkDir opkDir ownDir : DirGhost)
    (spkId kpkId opkId : BitVec 32)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost) :
    PhaseGroupSpec fineCostModel
      (W4StageP2PathACliEnv hasOpk rd files spkDir kpkDir opkDir ownDir
        spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr)
      w4StageP2PathACliFineGrpS := by
  have hSpk := w4SmallStoreStep16_fine_groupSpec rd files spkDir (keyName spkId)
  have hKpk := w4SmallStoreStep16_fine_groupSpec rd files kpkDir (keyName kpkId)
  have hOptPk := phaseGroupSpec_ite_nil hasOpk fun _ =>
    w4SmallStoreStep16_fine_groupSpec rd files opkDir (keyName opkId)
  have hKp := w4SmallStoreStep16_fine_groupSpec rd files ownDir ownKeyName
  have hBob := w4InitBobSpqr_fine_groupSpec F x_res hasOpk x_spqr
  have hReg := w4SmallStoreStep16_fine_groupSpec rd files ownDir ownRegName
  have hErr := w4ErrTail_fine_groupSpec
  exact (hSpk.seq (hKpk.seq (hOptPk.seq (hKp.seq (hBob.seq (hReg.seq hErr)))))).mono
    (p2a_grp_le w4SmallStoreStep16FineGrpS w4InitBobSpqrFineGrpS w4ErrTailFineGrpS)

theorem w4TryDecryptCloneFail_fine_groupSpec
    {CloneEnv TrialFailEnv DropCloneEnv : List AllocEvent → Prop} {g_cl g_cur : Nat}
    (hCl : PhaseGroupSpec fineCostModel CloneEnv g_cl)
    (hCur : PhaseGroupSpec fineCostModel TrialFailEnv g_cur)
    (hDrop : PhaseGroupSpec fineCostModel DropCloneEnv 0) :
    PhaseGroupSpec fineCostModel
      (W4TryDecryptCloneFailEnv CloneEnv TrialFailEnv DropCloneEnv)
      (g_cl + g_cur + w4ErrTailFineGrpS) := by
  have hBody : PhaseGroupSpec fineCostModel
      (ConcatEnv (ConcatEnv CloneEnv TrialFailEnv) DropCloneEnv) (g_cl + g_cur) :=
    ((hCl.concat hCur).concat hDrop).mono (Nat.le_of_eq (Nat.add_zero _))
  have hSpe : PhaseGroupSpec fineCostModel (SeqEnv (GrowOneSpeEnv 0#64) FreeOnlyEvs)
      w4ErrTailFineGrpS :=
    (growOneSpeZero_fine_groupSpec.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
      (Nat.le_of_eq (Nat.add_zero _))
  exact hBody.seq hSpe

theorem w4TryDecryptCloneFail_dom_fine_groupSpec {pqCap : Nat}
    {G_cur : SessionGhost} {st_cur : SessionState (List (BitVec 8))}
    {CurTrialFailEnv : List AllocEvent → Prop} {g_cur : Nat}
    (hCurDom : StateCloneDom pqCap G_cur st_cur)
    (hCur : PhaseGroupSpec fineCostModel CurTrialFailEnv g_cur) :
    PhaseGroupSpec fineCostModel
      (W4TryDecryptCloneFailEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
        (· = dropClonedSessionEvents G_cur st_cur))
      (segCloneDomFineGrpS + g_cur + w4ErrTailFineGrpS) :=
  w4TryDecryptCloneFail_fine_groupSpec
    (segCloneEnv_stateDom_fine_groupSpec hCurDom) hCur
    (dropClonedSessionEvents_groupSpec fineCostModel G_cur st_cur)

theorem w4StageP2OverBob_fine_groupSpec
    {SerializeArchivedEnv VecPushEnv : List AllocEvent → Prop} {g_ser g_push : Nat}
    (x_res : DoReserveCall) (hasOpk : Bool)
    (F : ShaCompress) (x_spqr : InitialStateGhost)
    (hSer : PhaseGroupSpec fineCostModel SerializeArchivedEnv g_ser)
    (hPush : PhaseGroupSpec fineCostModel VecPushEnv g_push) :
    PhaseGroupSpec fineCostModel
      (W4StageP2OverBobEnv SerializeArchivedEnv VecPushEnv x_res hasOpk (InitialStateEnv F x_spqr))
      (g_ser + g_push + w4InitBobSpqrFineGrpS) :=
  (promoteStateArchive_groupSpec fineCostModel hSer hPush).seq
    (w4InitBobSpqr_fine_groupSpec F x_res hasOpk x_spqr)

theorem w4StageP2OverBob_dom_fine_groupSpec {pqCap : Nat}
    {g_arch : RecordGhost} {r_arch : SessionRecord (List (BitVec 8))}
    {VecPushEnv : List AllocEvent → Prop} {g_push : Nat}
    (x_res : DoReserveCall) (hasOpk : Bool)
    (F : ShaCompress) (x_spqr : InitialStateGhost)
    (hArchDom : RecordDom pqCap g_arch r_arch)
    (hPush : PhaseGroupSpec fineCostModel VecPushEnv g_push) :
    PhaseGroupSpec fineCostModel
      (W4StageP2OverBobEnv (RecordSerializeCancelEnv g_arch r_arch) VecPushEnv
        x_res hasOpk (InitialStateEnv F x_spqr))
      (recordSerializeDomFineGrpS + g_push + w4InitBobSpqrFineGrpS) :=
  w4StageP2OverBob_fine_groupSpec x_res hasOpk F x_spqr
    (recordSerializeCancelEnv_recordDom_fine_groupSpec hArchDom) hPush

/-- Fixed `Dom` base constant inside `W4StageP2PathCCliEnv` before `g_cur`, `4 * (g_dec + g_tr)`,
and `g_push`. -/
def w4StageP2PathCCliDomBaseFineGrpS : Nat :=
  segCloneDomFineGrpS + w4ErrTailFineGrpS + 5 * w4SmallStoreStep16FineGrpS +
    recordSerializeDomFineGrpS + w4InitBobSpqrFineGrpS + w4ErrTailFineGrpS

/-- Total `Dom` scaled group bound for `W4StageP2PathCCliEnv`. -/
def w4StageP2PathCCliDomFineGrpS (g_cur g_dec g_tr g_push : Nat) : Nat :=
  w4StageP2PathCCliDomBaseFineGrpS + g_cur + 4 * (g_dec + g_tr) + g_push

private theorem p2c_grp_le (gCl gCur gErr gLoop s16 gSer gPush gBob : Nat) :
    (gCl + gCur + gErr) +
      (gLoop + (s16 + (s16 + (s16 + (s16 + ((gSer + gPush + gBob) + (s16 + gErr))))))) ≤
      (gCl + gErr + 5 * s16 + gSer + gBob + gErr) + gCur + gLoop + gPush := by
  omega

theorem w4StageP2PathCCli_fine_groupSpec {α : Type}
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
    {g_segCur g_cur g_dec g_tr g_archSer g_push : Nat}
    (hSegCur : PhaseGroupSpec fineCostModel (SegCloneEnv G_cur st_cur) g_segCur)
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
      ((g_segCur + w4ErrTailFineGrpS + 5 * w4SmallStoreStep16FineGrpS +
          g_archSer + w4InitBobSpqrFineGrpS + w4ErrTailFineGrpS) +
        g_cur + 4 * (g_dec + g_tr) + g_push) := by
  have hE1 := ((PhaseGroupSpec.freeOnly fineCostModel).or
    (w4TryDecryptCloneFail_fine_groupSpec hSegCur hCur
      (dropClonedSessionEvents_groupSpec fineCostModel G_cur st_cur))).mono
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
    (p2c_grp_le g_segCur g_cur w4ErrTailFineGrpS (4 * (g_dec + g_tr))
      w4SmallStoreStep16FineGrpS g_archSer g_push w4InitBobSpqrFineGrpS)

theorem w4StageP2PathCCli_dom_fine_groupSpec {α : Type} {pqCap : Nat}
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
    {g_cur g_dec g_tr g_push : Nat}
    (hCurDom : StateCloneDom pqCap G_cur st_cur)
    (hCur : PhaseGroupSpec fineCostModel CurTrialFailEnv g_cur)
    (hlen4 : xs.length ≤ 4)
    (hDec : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DecEnv x) g_dec)
    (hTr : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DropEnv x) 0)
    (hArchDom : RecordDom pqCap g_arch r_arch)
    (hPush : PhaseGroupSpec fineCostModel VecPushEnv g_push) :
    PhaseGroupSpec fineCostModel
      (W4StageP2PathCCliEnv G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
        g_arch r_arch VecPushEnv hasOpk rd files spkDir kpkDir opkDir ownDir
        spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr)
      (w4StageP2PathCCliDomFineGrpS g_cur g_dec g_tr g_push) :=
  w4StageP2PathCCli_fine_groupSpec hasOpk rd files spkDir kpkDir opkDir ownDir
    spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr
    (segCloneEnv_stateDom_fine_groupSpec hCurDom) hCur hlen4 hDec hTr hDrop
    (recordSerializeCancelEnv_recordDom_fine_groupSpec hArchDom) hPush

/-! ### 3.3 Stage P3 & Stage P4 (`Matched`, `PathA`, and `PathC`) -/

def w4StageP3FineGrpS (g_td : Nat) : Nat :=
  g_td + w4ErrTailFineGrpS

theorem w4StageP3_fine_groupSpec {TryDecEnv : List AllocEvent → Prop} {g_td : Nat}
    (hTd : PhaseGroupSpec fineCostModel TryDecEnv g_td) :
    PhaseGroupSpec fineCostModel (W4StageP3Env TryDecEnv) (w4StageP3FineGrpS g_td) :=
  hTd.seq w4ErrTail_fine_groupSpec

def w4StageP4MatchedDomFineGrpS : Nat :=
  w4SmallStoreStep32FineGrpS + w4SessStoreStepDomFineGrpS

def w4StageP4PathADomFineGrpS : Nat :=
  2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS + w4SessStoreStepDomFineGrpS

def w4StageP4PathCDomFineGrpS : Nat :=
  2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS + w4SessStorePrev1StepDomFineGrpS

theorem w4StageP4MatchedDomFineGrpS_eq : w4StageP4MatchedDomFineGrpS = 178343103 := by decide
theorem w4StageP4PathADomFineGrpS_eq : w4StageP4PathADomFineGrpS = 196885288 := by decide
theorem w4StageP4PathCDomFineGrpS_eq : w4StageP4PathCDomFineGrpS = 197092952 := by decide

private theorem p4_ac_grp_le (s32 s16 st : Nat) :
    s32 + (s32 + (s16 + st)) ≤ 2 * s32 + s16 + st := by
  omega

theorem w4StageP4MatchedCli_fine_groupSpec
    (rd : ReadRule) (files : FsFiles) (peersDir sessDir : DirGhost) (peer : AddrGhost)
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))} {g_ser : Nat}
    (hSer : PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv g_rec r_rec) g_ser) :
    PhaseGroupSpec fineCostModel
      (W4StageP4MatchedCliEnv rd files peersDir sessDir peer g_rec r_rec)
      (w4SmallStoreStep32FineGrpS + (16659 + (6 * FineScale + g_ser))) := by
  have hSave := w4SmallStoreStep32_fine_groupSpec rd files peersDir (addressText peer.val)
  have hStore := ((w4SessStoreStep_fine_groupSpec sessDir peer hSer).seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  exact hSave.seq hStore

theorem w4StageP4MatchedCli_dom_fine_groupSpec {pqCap : Nat}
    (rd : ReadRule) (files : FsFiles) (peersDir sessDir : DirGhost) (peer : AddrGhost)
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))}
    (hDom : RecordDom pqCap g_rec r_rec) :
    PhaseGroupSpec fineCostModel
      (W4StageP4MatchedCliEnv rd files peersDir sessDir peer g_rec r_rec)
      w4StageP4MatchedDomFineGrpS :=
  w4StageP4MatchedCli_fine_groupSpec rd files peersDir sessDir peer
    (recordSerializeCancelEnv_recordDom_fine_groupSpec hDom)

theorem w4StageP4PathACli_fine_groupSpec
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peersDir kpkDir opkDir sessDir : DirGhost) (peer : AddrGhost)
    (kpkName : List (BitVec 8)) (opkId : BitVec 32)
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))} {g_ser : Nat}
    (hSer : PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv g_rec r_rec) g_ser) :
    PhaseGroupSpec fineCostModel
      (W4StageP4PathACliEnv hasOpk rd files peersDir kpkDir opkDir sessDir
        peer kpkName opkId g_rec r_rec)
      (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
        (16659 + (6 * FineScale + g_ser))) := by
  have hSave := w4SmallStoreStep32_fine_groupSpec rd files peersDir (addressText peer.val)
  have hMark := w4SmallStoreStep32_fine_groupSpec rd files kpkDir kpkName
  have hRem := phaseGroupSpec_ite_nil hasOpk fun _ =>
    w4SmallStoreStep16_fine_groupSpec rd files opkDir (keyName opkId)
  have hStore := ((w4SessStoreStep_fine_groupSpec sessDir peer hSer).seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  exact (hSave.seq (hMark.seq (hRem.seq hStore))).mono
    (p4_ac_grp_le w4SmallStoreStep32FineGrpS w4SmallStoreStep16FineGrpS
      (16659 + (6 * FineScale + g_ser)))

theorem w4StageP4PathACli_dom_fine_groupSpec {pqCap : Nat}
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peersDir kpkDir opkDir sessDir : DirGhost) (peer : AddrGhost)
    (kpkName : List (BitVec 8)) (opkId : BitVec 32)
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))}
    (hDom : RecordDom pqCap g_rec r_rec) :
    PhaseGroupSpec fineCostModel
      (W4StageP4PathACliEnv hasOpk rd files peersDir kpkDir opkDir sessDir
        peer kpkName opkId g_rec r_rec)
      w4StageP4PathADomFineGrpS :=
  w4StageP4PathACli_fine_groupSpec hasOpk rd files peersDir kpkDir opkDir sessDir
    peer kpkName opkId (recordSerializeCancelEnv_recordDom_fine_groupSpec hDom)

theorem w4StageP4PathCCli_fine_groupSpec
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peersDir kpkDir opkDir sessDir : DirGhost) (peer : AddrGhost)
    (kpkName : List (BitVec 8)) (opkId : BitVec 32)
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)} {g_ser1 : Nat}
    (hSer1 : PhaseGroupSpec fineCostModel (SerializePrev1CancelEnv G sess enc) g_ser1) :
    PhaseGroupSpec fineCostModel
      (W4StageP4PathCCliEnv hasOpk rd files peersDir kpkDir opkDir sessDir
        peer kpkName opkId G sess enc)
      (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
        (16659 + (6 * FineScale + g_ser1))) := by
  have hSave := w4SmallStoreStep32_fine_groupSpec rd files peersDir (addressText peer.val)
  have hMark := w4SmallStoreStep32_fine_groupSpec rd files kpkDir kpkName
  have hRem := phaseGroupSpec_ite_nil hasOpk fun _ =>
    w4SmallStoreStep16_fine_groupSpec rd files opkDir (keyName opkId)
  have hStore := ((w4SessStorePrev1Step_fine_groupSpec sessDir peer hSer1).seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  exact (hSave.seq (hMark.seq (hRem.seq hStore))).mono
    (p4_ac_grp_le w4SmallStoreStep32FineGrpS w4SmallStoreStep16FineGrpS
      (16659 + (6 * FineScale + g_ser1)))

theorem w4StageP4PathCCli_dom_fine_groupSpec {pqCap : Nat}
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peersDir kpkDir opkDir sessDir : DirGhost) (peer : AddrGhost)
    (kpkName : List (BitVec 8)) (opkId : BitVec 32)
    {G : SessionGhost} {sess : Session (List (BitVec 8))} (enc : List (BitVec 8))
    (hDom : SessionOutDom pqCap G sess) :
    PhaseGroupSpec fineCostModel
      (W4StageP4PathCCliEnv hasOpk rd files peersDir kpkDir opkDir sessDir
        peer kpkName opkId G sess enc)
      w4StageP4PathCDomFineGrpS := by
  have hSave := w4SmallStoreStep32_fine_groupSpec rd files peersDir (addressText peer.val)
  have hMark := w4SmallStoreStep32_fine_groupSpec rd files kpkDir kpkName
  have hRem := phaseGroupSpec_ite_nil hasOpk fun _ =>
    w4SmallStoreStep16_fine_groupSpec rd files opkDir (keyName opkId)
  have hStore := ((w4SessStorePrev1Step_dom_fine_groupSpec sessDir peer enc hDom).seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  exact (hSave.seq (hMark.seq (hRem.seq hStore))).mono
    (p4_ac_grp_le w4SmallStoreStep32FineGrpS w4SmallStoreStep16FineGrpS
      w4SessStorePrev1StepDomFineGrpS)

/-! ### 3.4 End-to-End 4-Arm `W4DecryptPrekeySlotEnv` (`Untrusted | PathB | PathA | PathC`) -/

/-- Closed-form scaled group bound for the `Untrusted` arm of `W4DecryptPrekeySlotEnv P`. -/
def w4DecryptPrekeyUntrustedFineGrpS (g_deser : Nat) : Nat :=
  w4StageP1UntrustedBaseFineGrpS + g_deser

/-- Closed-form `Dom` scaled group bound for `W4DecryptPrekeyPathBEnv P` (`Matched`). -/
def w4DecryptPrekeyPathBDomFineGrpS (g_deser g_dec g_tr g_push g_td_B : Nat) : Nat :=
  (w4StageP1OkBaseFineGrpS + g_deser) +
    (4 * (g_dec + g_tr) + recordSerializeDomFineGrpS + g_push) +
    w4StageP3FineGrpS g_td_B +
    w4StageP4MatchedDomFineGrpS

/-- Closed-form `Dom` scaled group bound for `W4DecryptPrekeyPathAEnv P` (`0`-prev fresh Bob). -/
def w4DecryptPrekeyPathADomFineGrpS (g_deser g_td_AC : Nat) : Nat :=
  (w4StageP1OkBaseFineGrpS + g_deser) +
    w4StageP2PathACliFineGrpS +
    w4StageP3FineGrpS g_td_AC +
    w4StageP4PathADomFineGrpS

/-- Closed-form `Dom` scaled group bound for `W4DecryptPrekeyPathCEnv P` (`Over` / `prev1`). -/
def w4DecryptPrekeyPathCDomFineGrpS (g_deser g_cur g_dec g_tr g_push g_td_AC : Nat) : Nat :=
  (w4StageP1OkBaseFineGrpS + g_deser) +
    w4StageP2PathCCliDomFineGrpS g_cur g_dec g_tr g_push +
    w4StageP3FineGrpS g_td_AC +
    w4StageP4PathCDomFineGrpS

/-- Split-P3 (`g_td_B` vs `g_td_AC`) 4-arm `Dom` scaled group bound for
`W4DecryptPrekeySlotEnv P`. -/
def w4DecryptPrekeySlotSplitDomFineGrpS
    (g_deser g_cur g_dec g_tr g_push g_td_B g_td_AC : Nat) : Nat :=
  max
    (max (w4DecryptPrekeyUntrustedFineGrpS g_deser)
         (w4DecryptPrekeyPathBDomFineGrpS g_deser g_dec g_tr g_push g_td_B))
    (max (w4DecryptPrekeyPathADomFineGrpS g_deser g_td_AC)
         (w4DecryptPrekeyPathCDomFineGrpS g_deser g_cur g_dec g_tr g_push g_td_AC))

/-- Uniform-P3 (`g_td_B = g_td_AC = g_td`) 4-arm `Dom` scaled group bound for
`W4DecryptPrekeySlotEnv P`. -/
abbrev w4DecryptPrekeySlotDomFineGrpS
    (g_deser g_cur g_dec g_tr g_push g_td : Nat) : Nat :=
  w4DecryptPrekeySlotSplitDomFineGrpS g_deser g_cur g_dec g_tr g_push g_td g_td

private theorem fourStages_grp_le (p1 p2 p3 p4 : Nat) :
    p1 + (p2 + (p3 + p4)) ≤ p1 + p2 + p3 + p4 := by
  omega

theorem w4DecryptPrekeyPathB_dom_fine_groupSpec {α : Type} {pqCap : Nat}
    (P : W4DecryptPrekeySlotParams α)
    {g_deser g_dec g_tr g_push g_td_B : Nat}
    (hDeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (P.DeserEnv bs) g_deser)
    (hlen4 : P.archivedTrials.length ≤ 4)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DecEnv x) g_dec)
    (hTr : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DropEnv x) 0)
    (hArchDom : RecordDom pqCap P.g_arch P.r_arch)
    (hPush : PhaseGroupSpec fineCostModel P.VecPushEnv g_push)
    (hTdB : PhaseGroupSpec fineCostModel P.TryDecEnv g_td_B)
    (hOut0Dom : RecordDom pqCap P.g_out0 P.r_out0) :
    PhaseGroupSpec fineCostModel (W4DecryptPrekeyPathBEnv P)
      (w4DecryptPrekeyPathBDomFineGrpS g_deser g_dec g_tr g_push g_td_B) := by
  have h1 := w4StageP1OkCli_fine_groupSpec P.rd P.files P.sessDir P.peersDir P.peer hDeser
  have h2 := w4StageP2Matched_dom_fine_groupSpec hlen4 hDec hTr hDrop hArchDom hPush
  have h3 := w4StageP3_fine_groupSpec hTdB
  have h4 := w4StageP4MatchedCli_dom_fine_groupSpec P.rd P.files P.peersDir P.sessDir P.peer hOut0Dom
  exact (h1.seq (h2.seq (h3.seq h4))).mono (fourStages_grp_le _ _ _ _)

theorem w4DecryptPrekeyPathA_dom_fine_groupSpec {α : Type} {pqCap : Nat}
    (P : W4DecryptPrekeySlotParams α)
    {g_deser g_td_AC : Nat}
    (hDeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (P.DeserEnv bs) g_deser)
    (hTdAC : PhaseGroupSpec fineCostModel P.TryDecEnv g_td_AC)
    (hOut0Dom : RecordDom pqCap P.g_out0 P.r_out0) :
    PhaseGroupSpec fineCostModel (W4DecryptPrekeyPathAEnv P)
      (w4DecryptPrekeyPathADomFineGrpS g_deser g_td_AC) := by
  have h1 := w4StageP1OkCli_fine_groupSpec P.rd P.files P.sessDir P.peersDir P.peer hDeser
  have h2 := w4StageP2PathACli_fine_groupSpec P.hasOpk P.rd P.files
    P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
    P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr
  have h3 := w4StageP3_fine_groupSpec hTdAC
  have h4 := w4StageP4PathACli_dom_fine_groupSpec P.hasOpk P.rd P.files
    P.peersDir P.kpkDir P.opkDir P.sessDir P.peer P.kpkMarkName P.opkId hOut0Dom
  exact (h1.seq (h2.seq (h3.seq h4))).mono (fourStages_grp_le _ _ _ _)

theorem w4DecryptPrekeyPathC_dom_fine_groupSpec {α : Type} {pqCap : Nat}
    (P : W4DecryptPrekeySlotParams α)
    {g_deser g_cur g_dec g_tr g_push g_td_AC : Nat}
    (hDeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (P.DeserEnv bs) g_deser)
    (hCurDom : StateCloneDom pqCap P.G_cur P.st_cur)
    (hCur : PhaseGroupSpec fineCostModel P.CurTrialFailEnv g_cur)
    (hlen4 : P.archivedTrials.length ≤ 4)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DecEnv x) g_dec)
    (hTr : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DropEnv x) 0)
    (hArchDom : RecordDom pqCap P.g_arch P.r_arch)
    (hPush : PhaseGroupSpec fineCostModel P.VecPushEnv g_push)
    (hTdAC : PhaseGroupSpec fineCostModel P.TryDecEnv g_td_AC)
    (hOut1Dom : SessionOutDom pqCap P.G_out1 P.sess_out1) :
    PhaseGroupSpec fineCostModel (W4DecryptPrekeyPathCEnv P)
      (w4DecryptPrekeyPathCDomFineGrpS g_deser g_cur g_dec g_tr g_push g_td_AC) := by
  have h1 := w4StageP1OkCli_fine_groupSpec P.rd P.files P.sessDir P.peersDir P.peer hDeser
  have h2 := w4StageP2PathCCli_dom_fine_groupSpec P.hasOpk P.rd P.files
    P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
    P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr
    hCurDom hCur hlen4 hDec hTr hDrop hArchDom hPush
  have h3 := w4StageP3_fine_groupSpec hTdAC
  have h4 := w4StageP4PathCCli_dom_fine_groupSpec P.hasOpk P.rd P.files
    P.peersDir P.kpkDir P.opkDir P.sessDir P.peer P.kpkMarkName P.opkId P.enc_prev1 hOut1Dom
  exact (h1.seq (h2.seq (h3.seq h4))).mono (fourStages_grp_le _ _ _ _)

/-- Split-P3 4-arm `PhaseGroupSpec` bounding `W4DecryptPrekeySlotEnv P` across all four arms
(`Untrusted | PathB | PathA | PathC`) with arm-guarded domain and `TryDecEnv` hypotheses
(`g_td_B` on `PathB` vs `g_td_AC` on `PathA`/`PathC`). -/
theorem w4DecryptPrekeySlot_splitP3_dom_fine_groupSpec {α : Type} {pqCap : Nat}
    (P : W4DecryptPrekeySlotParams α)
    {g_deser g_cur g_dec g_tr g_push g_td_B g_td_AC : Nat}
    (hDeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (P.DeserEnv bs) g_deser)
    (hCurDom : (∃ e, W4DecryptPrekeyPathCEnv P e) → StateCloneDom pqCap P.G_cur P.st_cur)
    (hCur : (∃ e, W4DecryptPrekeyPathCEnv P e) →
      PhaseGroupSpec fineCostModel P.CurTrialFailEnv g_cur)
    (hlen4 : P.archivedTrials.length ≤ 4)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DecEnv x) g_dec)
    (hTr : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DropEnv x) 0)
    (hArchDom : (∃ e, W4DecryptPrekeyPathBEnv P e ∨ W4DecryptPrekeyPathCEnv P e) →
      RecordDom pqCap P.g_arch P.r_arch)
    (hPush : PhaseGroupSpec fineCostModel P.VecPushEnv g_push)
    (hTdB : (∃ e, W4DecryptPrekeyPathBEnv P e) →
      PhaseGroupSpec fineCostModel P.TryDecEnv g_td_B)
    (hTdAC : (∃ e, W4DecryptPrekeyPathAEnv P e ∨ W4DecryptPrekeyPathCEnv P e) →
      PhaseGroupSpec fineCostModel P.TryDecEnv g_td_AC)
    (hOut0Dom : (∃ e, W4DecryptPrekeyPathBEnv P e ∨ W4DecryptPrekeyPathAEnv P e) →
      RecordDom pqCap P.g_out0 P.r_out0)
    (hOut1Dom : (∃ e, W4DecryptPrekeyPathCEnv P e) →
      SessionOutDom pqCap P.G_out1 P.sess_out1) :
    PhaseGroupSpec fineCostModel (W4DecryptPrekeySlotEnv P)
      (w4DecryptPrekeySlotSplitDomFineGrpS g_deser g_cur g_dec g_tr g_push g_td_B g_td_AC) := by
  let gAll := w4DecryptPrekeySlotSplitDomFineGrpS g_deser g_cur g_dec g_tr g_push g_td_B g_td_AC
  have hLeU : w4DecryptPrekeyUntrustedFineGrpS g_deser ≤ gAll :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hLeB : w4DecryptPrekeyPathBDomFineGrpS g_deser g_dec g_tr g_push g_td_B ≤ gAll :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hLeA : w4DecryptPrekeyPathADomFineGrpS g_deser g_td_AC ≤ gAll :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hLeC : w4DecryptPrekeyPathCDomFineGrpS g_deser g_cur g_dec g_tr g_push g_td_AC ≤ gAll :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hArms : PhaseGroupSpec fineCostModel
      (fun e =>
        W4StageP1UntrustedCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer e ∨
        W4DecryptPrekeyPathBEnv P e ∨
        W4DecryptPrekeyPathAEnv P e ∨
        W4DecryptPrekeyPathCEnv P e)
      gAll :=
    { groups_le := fun st0 {e} hArm => by
        rcases hArm with hU | hB | hA | hC
        · exact ((w4StageP1UntrustedCli_fine_groupSpec P.rd P.files P.sessDir P.peersDir P.peer
            hDeser).mono hLeU).groups_le st0 hU
        · exact ((w4DecryptPrekeyPathB_dom_fine_groupSpec P hDeser hlen4 hDec hTr hDrop
            (hArchDom ⟨e, Or.inl hB⟩) hPush (hTdB ⟨e, hB⟩)
            (hOut0Dom ⟨e, Or.inl hB⟩)).mono hLeB).groups_le st0 hB
        · exact ((w4DecryptPrekeyPathA_dom_fine_groupSpec P hDeser
            (hTdAC ⟨e, Or.inl hA⟩) (hOut0Dom ⟨e, Or.inr hA⟩)).mono hLeA).groups_le st0 hA
        · exact ((w4DecryptPrekeyPathC_dom_fine_groupSpec P hDeser
            (hCurDom ⟨e, hC⟩) (hCur ⟨e, hC⟩) hlen4 hDec hTr hDrop
            (hArchDom ⟨e, Or.inr hC⟩) hPush (hTdAC ⟨e, Or.inr hC⟩)
            (hOut1Dom ⟨e, hC⟩)).mono hLeC).groups_le st0 hC }
  have hSeq := (hArms.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hSeq).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

/-- Uniform-P3 (`g_td_B = g_td_AC = g_td`) unguarded corollary of
`w4DecryptPrekeySlot_splitP3_dom_fine_groupSpec`. -/
theorem w4DecryptPrekeySlot_dom_fine_groupSpec {α : Type} {pqCap : Nat}
    (P : W4DecryptPrekeySlotParams α)
    {g_deser g_cur g_dec g_tr g_push g_td : Nat}
    (hDeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (P.DeserEnv bs) g_deser)
    (hCurDom : StateCloneDom pqCap P.G_cur P.st_cur)
    (hCur : PhaseGroupSpec fineCostModel P.CurTrialFailEnv g_cur)
    (hlen4 : P.archivedTrials.length ≤ 4)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DecEnv x) g_dec)
    (hTr : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DropEnv x) 0)
    (hArchDom : RecordDom pqCap P.g_arch P.r_arch)
    (hPush : PhaseGroupSpec fineCostModel P.VecPushEnv g_push)
    (hTd : PhaseGroupSpec fineCostModel P.TryDecEnv g_td)
    (hOut0Dom : RecordDom pqCap P.g_out0 P.r_out0)
    (hOut1Dom : SessionOutDom pqCap P.G_out1 P.sess_out1) :
    PhaseGroupSpec fineCostModel (W4DecryptPrekeySlotEnv P)
      (w4DecryptPrekeySlotDomFineGrpS g_deser g_cur g_dec g_tr g_push g_td) :=
  w4DecryptPrekeySlot_splitP3_dom_fine_groupSpec P hDeser
    (fun _ => hCurDom) (fun _ => hCur) hlen4 hDec hTr hDrop
    (fun _ => hArchDom) hPush (fun _ => hTd) (fun _ => hTd)
    (fun _ => hOut0Dom) (fun _ => hOut1Dom)

/-- Parametric (clone/serialize-abstract) split-P3 `PhaseGroupSpec` for
`W4DecryptPrekeySlotEnv P` from explicit `SegCloneEnv` / `RecordSerializeCancelEnv` /
`SerializePrev1CancelEnv` group bounds. -/
theorem w4DecryptPrekeySlot_splitP3_fine_groupSpec {α : Type}
    (P : W4DecryptPrekeySlotParams α)
    {g_deser g_segCur g_cur g_dec g_tr g_archSer g_push g_td_B g_td_AC g_out0Ser g_out1Ser : Nat}
    (hDeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (P.DeserEnv bs) g_deser)
    (hSegCur : (∃ e, W4DecryptPrekeyPathCEnv P e) →
      PhaseGroupSpec fineCostModel (SegCloneEnv P.G_cur P.st_cur) g_segCur)
    (hCur : (∃ e, W4DecryptPrekeyPathCEnv P e) →
      PhaseGroupSpec fineCostModel P.CurTrialFailEnv g_cur)
    (hlen4 : P.archivedTrials.length ≤ 4)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DecEnv x) g_dec)
    (hTr : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DropEnv x) 0)
    (hArchSer : (∃ e, W4DecryptPrekeyPathBEnv P e ∨ W4DecryptPrekeyPathCEnv P e) →
      PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv P.g_arch P.r_arch) g_archSer)
    (hPush : PhaseGroupSpec fineCostModel P.VecPushEnv g_push)
    (hTdB : (∃ e, W4DecryptPrekeyPathBEnv P e) →
      PhaseGroupSpec fineCostModel P.TryDecEnv g_td_B)
    (hTdAC : (∃ e, W4DecryptPrekeyPathAEnv P e ∨ W4DecryptPrekeyPathCEnv P e) →
      PhaseGroupSpec fineCostModel P.TryDecEnv g_td_AC)
    (hOut0Ser : (∃ e, W4DecryptPrekeyPathBEnv P e ∨ W4DecryptPrekeyPathAEnv P e) →
      PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv P.g_out0 P.r_out0) g_out0Ser)
    (hOut1Ser : (∃ e, W4DecryptPrekeyPathCEnv P e) →
      PhaseGroupSpec fineCostModel (SerializePrev1CancelEnv P.G_out1 P.sess_out1 P.enc_prev1)
        g_out1Ser) :
    let gU := w4StageP1UntrustedBaseFineGrpS + g_deser
    let gB := (w4StageP1OkBaseFineGrpS + g_deser) +
      (4 * (g_dec + g_tr) + g_archSer + g_push) +
      w4StageP3FineGrpS g_td_B +
      (w4SmallStoreStep32FineGrpS + (16659 + (6 * FineScale + g_out0Ser)))
    let gA := (w4StageP1OkBaseFineGrpS + g_deser) +
      w4StageP2PathACliFineGrpS +
      w4StageP3FineGrpS g_td_AC +
      (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
        (16659 + (6 * FineScale + g_out0Ser)))
    let gC := (w4StageP1OkBaseFineGrpS + g_deser) +
      ((g_segCur + w4ErrTailFineGrpS + 5 * w4SmallStoreStep16FineGrpS +
          g_archSer + w4InitBobSpqrFineGrpS + w4ErrTailFineGrpS) +
        g_cur + 4 * (g_dec + g_tr) + g_push) +
      w4StageP3FineGrpS g_td_AC +
      (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
        (16659 + (6 * FineScale + g_out1Ser)))
    PhaseGroupSpec fineCostModel (W4DecryptPrekeySlotEnv P) (max (max gU gB) (max gA gC)) := by
  intro gU gB gA gC
  let gAll := max (max gU gB) (max gA gC)
  have hLeU : gU ≤ gAll := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hLeB : gB ≤ gAll := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hLeA : gA ≤ gAll := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hLeC : gC ≤ gAll := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hP1 := w4StageP1OkCli_fine_groupSpec P.rd P.files P.sessDir P.peersDir P.peer hDeser
  have hArms : PhaseGroupSpec fineCostModel
      (fun e =>
        W4StageP1UntrustedCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer e ∨
        W4DecryptPrekeyPathBEnv P e ∨
        W4DecryptPrekeyPathAEnv P e ∨
        W4DecryptPrekeyPathCEnv P e)
      gAll :=
    { groups_le := fun st0 {e} hArm => by
        rcases hArm with hU | hB | hA | hC
        · exact ((w4StageP1UntrustedCli_fine_groupSpec P.rd P.files P.sessDir P.peersDir P.peer
            hDeser).mono hLeU).groups_le st0 hU
        · have hp2 := w4StageP2Matched_groupSpec fineCostModel hlen4 hDec hTr hDrop
            (hArchSer ⟨e, Or.inl hB⟩) hPush
          have hp3 := w4StageP3_fine_groupSpec (hTdB ⟨e, hB⟩)
          have hp4 := w4StageP4MatchedCli_fine_groupSpec P.rd P.files P.peersDir P.sessDir P.peer
            (hOut0Ser ⟨e, Or.inl hB⟩)
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (fourStages_grp_le _ _ _ _)).mono hLeB).groups_le st0 hB
        · have hp2 := w4StageP2PathACli_fine_groupSpec P.hasOpk P.rd P.files
            P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
            P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr
          have hp3 := w4StageP3_fine_groupSpec (hTdAC ⟨e, Or.inl hA⟩)
          have hp4 := w4StageP4PathACli_fine_groupSpec P.hasOpk P.rd P.files
            P.peersDir P.kpkDir P.opkDir P.sessDir P.peer P.kpkMarkName P.opkId
            (hOut0Ser ⟨e, Or.inr hA⟩)
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (fourStages_grp_le _ _ _ _)).mono hLeA).groups_le st0 hA
        · have hp2 := w4StageP2PathCCli_fine_groupSpec P.hasOpk P.rd P.files
            P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
            P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr
            (hSegCur ⟨e, hC⟩) (hCur ⟨e, hC⟩) hlen4 hDec hTr hDrop
            (hArchSer ⟨e, Or.inr hC⟩) hPush
          have hp3 := w4StageP3_fine_groupSpec (hTdAC ⟨e, Or.inr hC⟩)
          have hp4 := w4StageP4PathCCli_fine_groupSpec P.hasOpk P.rd P.files
            P.peersDir P.kpkDir P.opkDir P.sessDir P.peer P.kpkMarkName P.opkId
            (hOut1Ser ⟨e, hC⟩)
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (fourStages_grp_le _ _ _ _)).mono hLeC).groups_le st0 hC }
  have hSeq := (hArms.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hSeq).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

/-! ### 3.5 Outer `SlotW4` / `R3b` Wire + Slot Group Composition (`W4SlotR3bEnv`) -/

def w4SlotR3bDeltaGrpS (x_pksm : PksmGhost) (g_decPk : Nat) : Nat :=
  pksmTryFromDeltaGrpS x_pksm + g_decPk

def w4SlotR3bCapDeltaGrpS (N g_decPk : Nat) : Nat :=
  pksmTryFromCapDeltaGrpS N + g_decPk

theorem w4SlotR3b_groupSpec {M : AllocCostModel} [HasFineGroupCredit M]
    (hGrp : WireGroupHyps M) (x_pksm : PksmGhost)
    {DecPkEnv : List AllocEvent → Prop} {g_decPk : Nat}
    (hDec : PhaseGroupSpec M DecPkEnv g_decPk) :
    PhaseGroupSpec M (W4SlotR3bEnv x_pksm DecPkEnv) (w4SlotR3bDeltaGrpS x_pksm g_decPk) := by
  have hPksm := pksmTryFrom_phaseGroup hGrp x_pksm
  have hDecFree := (hDec.seq (PhaseGroupSpec.freeOnly M)).mono (Nat.le_of_eq (Nat.add_zero _))
  have hTail := ((PhaseGroupSpec.freeOnly M).or hDecFree).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
  exact ((PhaseGroupSpec.freeOnly M).or (hPksm.seq hTail)).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem w4SlotR3b_fine_groupSpec (x_pksm : PksmGhost)
    {DecPkEnv : List AllocEvent → Prop} {g_decPk : Nat}
    (hDec : PhaseGroupSpec fineCostModel DecPkEnv g_decPk) :
    PhaseGroupSpec fineCostModel (W4SlotR3bEnv x_pksm DecPkEnv)
      (w4SlotR3bDeltaGrpS x_pksm g_decPk) :=
  w4SlotR3b_groupSpec fineCostModel_wireGroupHyps x_pksm hDec

theorem w4SlotR3b_cap_fine_groupSpec {x_pksm : PksmGhost} {N g_decPk : Nat}
    {DecPkEnv : List AllocEvent → Prop}
    (hlen : x_pksm.bytes.length ≤ N)
    (hDec : PhaseGroupSpec fineCostModel DecPkEnv g_decPk) :
    PhaseGroupSpec fineCostModel (W4SlotR3bEnv x_pksm DecPkEnv)
      (w4SlotR3bCapDeltaGrpS N g_decPk) :=
  (w4SlotR3b_fine_groupSpec x_pksm hDec).mono
    (Nat.add_le_add_right (pksmTryFromDeltaGrpS_le_cap hlen) g_decPk)

/-! ## Widened Binary-Complete `PhaseGroupSpec`s

`PhaseGroupSpec fineCostModel` bounds for the widened envelopes in `W4OuterPeakSpec`
(`OptStageEnv`, `W4ErrTailWideEnv`, `W4TryDecryptCloneFailWideEnv`, `W4StageP2MatchedWideEnv`,
`W4InitBobWideEnv` / `W4InitBobSpqrWideEnv`, `W4StageP2OverBobWideEnv`, `W4StageP2PathACliWideEnv`,
`W4StageP2PathCCliWideEnv`, `W4StageP3WideEnv`, `W4StageP4{Matched,PathA,PathC}CliWideEnv`, and
4-arm `W4DecryptPrekeySplitWideSlotEnv`). -/

section WidenedBinaryCompleteGroupSpecs

theorem phaseGroupSpec_optStage {M : AllocCostModel} [HasFineGroupCredit M]
    {E : List AllocEvent → Prop} {g : Nat}
    (h : PhaseGroupSpec M E g) :
    PhaseGroupSpec M (OptStageEnv E) g :=
  ((PhaseGroupSpec.freeOnly M).or h).mono (Nat.max_le.mpr ⟨Nat.zero_le g, Nat.le_refl g⟩)

/-- Scaled group weight (`11,056`) for `SegTailEnv` (`17 B` `"decryption failed"` string). -/
def w4SegTailFineGrpS : Nat := fineSmallAllocGroupS 17

/-- Scaled group weight (`86,439`) for `W4ErrTailWideEnv`
(`w4ErrTailFineGrpS + w4SegTailFineGrpS`). -/
def w4ErrTailWideFineGrpS : Nat := w4ErrTailFineGrpS + w4SegTailFineGrpS

/-- Scaled group weight (`51,536`) for `W4StageP2MatchedCheckEnv` (`33 B` `PublicKey::serialize` +
`70 B` mismatch error string). -/
def w4StageP2MatchedCheckFineGrpS : Nat :=
  fineSmallAllocGroupS 33 + fineSmallAllocGroupS 70

/-- Fresh-Bob (`receiverChains = []`) scaled group bound for `SegCloneEnv`
(`senderChainCloneDomFineGrpS + 21 * FineScale`). -/
def segCloneFreshBobFineGrpS : Nat :=
  senderChainCloneDomFineGrpS + 21 * FineScale

theorem segTailEnv_fine_groupSpec :
    PhaseGroupSpec fineCostModel SegTailEnv w4SegTailFineGrpS := by
  have hm : (17 : Nat) ≤ MmapThresholdReq := by decide
  have h17 := PhaseGroupSpec.rustAlloc_small fineCostModel (size := 17) (align := 1) (by decide) hm
  rw [smallAllocGroupS_fineCostModel_eq] at h17
  exact ((PhaseGroupSpec.freeOnly fineCostModel).seq h17).mono (Nat.le_of_eq (Nat.zero_add _))

theorem fromFEnv_fine_groupSpec :
    PhaseGroupSpec fineCostModel FromFEnv w4SegTailFineGrpS :=
  (segTailEnv_fine_groupSpec.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))

theorem fromMEnv_fine_groupSpec :
    PhaseGroupSpec fineCostModel FromMEnv w4ErrTailWideFineGrpS :=
  growOneSpeZero_fine_groupSpec.seq fromFEnv_fine_groupSpec

theorem fromVPostTdEnv_fine_groupSpec :
    PhaseGroupSpec fineCostModel FromVPostTdEnv w4ErrTailWideFineGrpS :=
  ((PhaseGroupSpec.freeOnly fineCostModel).or fromMEnv_fine_groupSpec).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem w4ErrTailWide_fine_groupSpec :
    PhaseGroupSpec fineCostModel W4ErrTailWideEnv w4ErrTailWideFineGrpS := by
  have h1 : PhaseGroupSpec fineCostModel W4ErrTailEnv w4ErrTailWideFineGrpS :=
    w4ErrTail_fine_groupSpec.mono (Nat.le_add_right w4ErrTailFineGrpS w4SegTailFineGrpS)
  have h2 : PhaseGroupSpec fineCostModel FromFEnv w4ErrTailWideFineGrpS :=
    fromFEnv_fine_groupSpec.mono (Nat.le_add_left w4SegTailFineGrpS w4ErrTailFineGrpS)
  have h23 := (h2.or fromMEnv_fine_groupSpec).mono (Nat.le_of_eq (Nat.max_self _))
  exact (h1.or h23).mono (Nat.le_of_eq (Nat.max_self _))

theorem segCloneEnv_freshBobCloneDom_fine_groupSpec {bobPqCap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))}
    (hbob : FreshBobCloneDom bobPqCap G ses) :
    PhaseGroupSpec fineCostModel (SegCloneEnv G ses.state) segCloneFreshBobFineGrpS := by
  obtain ⟨_, _, _, _, hsend_ok, _, _, _, _⟩ := ghostCloneValid_of_sessionGhostValid hbob.gv
  have hloc := vecCloneEvents_groupSpec fineCostModel G.localIk
  have hrem := vecCloneEvents_groupSpec fineCostModel G.remoteIk
  have hroot := PhaseGroupSpec.rustAlloc_any fineCostModel 32 1
  have hsnd : PhaseGroupSpec fineCostModel
      (· = match G.sender, ses.state.senderChain with
           | some gs, some sc => senderChainCloneEvents gs sc
           | _, _ => [])
      senderChainCloneDomFineGrpS := by
    rcases hsend_ok with ⟨hn1, hn2⟩ | ⟨gs, sc, hgs, hsc, hsrk, hpriv⟩
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

theorem w4TryDecryptCloneFailWide_fine_groupSpec
    {CloneEnv TrialFailEnv DropCloneEnv : List AllocEvent → Prop} {g_cl g_cur : Nat}
    (hCl : PhaseGroupSpec fineCostModel CloneEnv g_cl)
    (hCur : PhaseGroupSpec fineCostModel TrialFailEnv g_cur)
    (hDrop : PhaseGroupSpec fineCostModel DropCloneEnv 0) :
    PhaseGroupSpec fineCostModel
      (W4TryDecryptCloneFailWideEnv CloneEnv TrialFailEnv DropCloneEnv)
      (g_cl + g_cur + w4ErrTailWideFineGrpS) := by
  have hBody : PhaseGroupSpec fineCostModel
      (ConcatEnv (ConcatEnv CloneEnv TrialFailEnv) DropCloneEnv) (g_cl + g_cur) :=
    ((hCl.concat hCur).concat hDrop).mono (Nat.le_of_eq (Nat.add_zero _))
  exact hBody.seq w4ErrTailWide_fine_groupSpec

theorem w4TryDecryptCloneFailWide_dom_fine_groupSpec {pqCap : Nat}
    {G_cur : SessionGhost} {st_cur : SessionState (List (BitVec 8))}
    {CurTrialFailEnv : List AllocEvent → Prop} {g_cur : Nat}
    (hCurDom : StateCloneDom pqCap G_cur st_cur)
    (hCur : PhaseGroupSpec fineCostModel CurTrialFailEnv g_cur) :
    PhaseGroupSpec fineCostModel
      (W4TryDecryptCloneFailWideEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
        (· = dropClonedSessionEvents G_cur st_cur))
      (segCloneDomFineGrpS + g_cur + w4ErrTailWideFineGrpS) :=
  w4TryDecryptCloneFailWide_fine_groupSpec
    (segCloneEnv_stateDom_fine_groupSpec hCurDom) hCur
    (dropClonedSessionEvents_groupSpec fineCostModel G_cur st_cur)

theorem w4StageP2MatchedErrStr_fine_groupSpec :
    PhaseGroupSpec fineCostModel W4StageP2MatchedErrStrEnv (fineSmallAllocGroupS 70) := by
  have hm70 : (70 : Nat) ≤ MmapThresholdReq := by decide
  have hm14 : (14 : Nat) ≤ MmapThresholdReq := by decide
  have h70 := PhaseGroupSpec.rustAlloc_small fineCostModel (size := 70) (align := 1) (by decide) hm70
  rw [smallAllocGroupS_fineCostModel_eq] at h70
  have h14 := PhaseGroupSpec.rustAlloc_small fineCostModel (size := 14) (align := 1) (by decide) hm14
  rw [smallAllocGroupS_fineCostModel_eq] at h14
  have h70f := (h70.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  have h14f := ((h14.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))).mono
    (by decide : fineSmallAllocGroupS 14 ≤ fineSmallAllocGroupS 70)
  have h70_14 := (h70f.or h14f).mono (Nat.le_of_eq (Nat.max_self _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or h70_14).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem w4StageP2MatchedCheck_fine_groupSpec :
    PhaseGroupSpec fineCostModel W4StageP2MatchedCheckEnv w4StageP2MatchedCheckFineGrpS := by
  have hm33 : (33 : Nat) ≤ MmapThresholdReq := by decide
  have h33 := PhaseGroupSpec.rustAlloc_small fineCostModel (size := 33) (align := 1) (by decide) hm33
  rw [smallAllocGroupS_fineCostModel_eq] at h33
  have hd33 := PhaseGroupSpec.rustDealloc fineCostModel 33 1
  have hTail := (hd33.seq w4StageP2MatchedErrStr_fine_groupSpec).mono (Nat.le_of_eq (Nat.zero_add _))
  have hCheck := h33.seq hTail
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hCheck).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem p2b_wide_grp_le (c l s p : Nat) :
    c + (l + s + p) ≤ c + l + s + p := by
  omega

theorem w4StageP2MatchedWide_fine_groupSpec {α : Type}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop} {xs : List α}
    {g_arch : RecordGhost} {r_arch : SessionRecord (List (BitVec 8))}
    {VecPushEnv : List AllocEvent → Prop}
    {g_dec g_tr g_archSer g_push : Nat}
    (hlen4 : xs.length ≤ 4)
    (hDec : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DecEnv x) g_dec)
    (hTr : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DropEnv x) 0)
    (hArchSer : PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv g_arch r_arch) g_archSer)
    (hPush : PhaseGroupSpec fineCostModel VecPushEnv g_push) :
    PhaseGroupSpec fineCostModel
      (W4StageP2MatchedWideEnv DecEnv TrialEnv DropEnv xs g_arch r_arch VecPushEnv)
      (w4StageP2MatchedCheckFineGrpS + 4 * (g_dec + g_tr) + g_archSer + g_push) :=
  (w4StageP2MatchedCheck_fine_groupSpec.seq
    (phaseGroupSpec_optStage
      (w4StageP2Matched_groupSpec fineCostModel hlen4 hDec hTr hDrop hArchSer hPush))).mono
    (p2b_wide_grp_le _ _ _ _)

theorem w4StageP2MatchedWide_dom_fine_groupSpec {α : Type} {pqCap : Nat}
    {DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop} {xs : List α}
    {g_arch : RecordGhost} {r_arch : SessionRecord (List (BitVec 8))}
    {VecPushEnv : List AllocEvent → Prop}
    {g_dec g_tr g_push : Nat}
    (hlen4 : xs.length ≤ 4)
    (hDec : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DecEnv x) g_dec)
    (hTr : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DropEnv x) 0)
    (hArchDom : RecordDom pqCap g_arch r_arch)
    (hPush : PhaseGroupSpec fineCostModel VecPushEnv g_push) :
    PhaseGroupSpec fineCostModel
      (W4StageP2MatchedWideEnv DecEnv TrialEnv DropEnv xs g_arch r_arch VecPushEnv)
      (w4StageP2MatchedCheckFineGrpS + 4 * (g_dec + g_tr) + recordSerializeDomFineGrpS + g_push) :=
  w4StageP2MatchedWide_fine_groupSpec hlen4 hDec hTr hDrop
    (recordSerializeCancelEnv_recordDom_fine_groupSpec hArchDom) hPush

/-- Scaled group bound (`1,769,472` = `27` groups) for `W4BobSessionBuildEnv9` (`9` small ops `≤ 68` B). -/
def w4BobSessionBuild9FineGrpS : Nat := 27 * FineScale

/-- Scaled group overhead around `E_spqrInit` in `W4InitBobWideEnv` (`+9` groups over `w4InitBobOuterFineGrpS`). -/
def w4InitBobOuter9FineGrpS : Nat :=
  w4PqxdhAcceptFineGrpS + w4BobSessionBuild9FineGrpS

/-- Total scaled group bound for `W4InitBobSpqrWideEnv` (`InitialStateEnv` = `384 * FineScale`). -/
def w4InitBobSpqr9FineGrpS : Nat :=
  w4InitBobOuter9FineGrpS + 384 * FineScale

theorem w4BobSessionBuild9_groupSpec (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M W4OuterPeakSpec.W4BobSessionBuildEnv9 w4BobSessionBuild9FineGrpS := by
  refine ((w4BoundedEvs_groupSpec M 9 68).seq (PhaseGroupSpec.freeOnly M)).mono ?_
  unfold w4BobSessionBuild9FineGrpS
  decide

theorem w4InitBobWide_fine_groupSpec (x_res : DoReserveCall) (hasOpk : Bool)
    {E_spqrInit : List AllocEvent → Prop} {g_spqrInit : Nat}
    (hSpqr : PhaseGroupSpec fineCostModel E_spqrInit g_spqrInit) :
    PhaseGroupSpec fineCostModel (W4InitBobWideEnv x_res hasOpk E_spqrInit)
      (w4InitBobOuter9FineGrpS + g_spqrInit) := by
  have hPq := w4PqxdhAccept_fine_groupSpec x_res hasOpk
  have hBuild := phaseGroupSpec_optStage (w4BobSessionBuild9_groupSpec fineCostModel)
  refine (hPq.seq (phaseGroupSpec_optStage (hSpqr.seq hBuild))).mono ?_
  unfold w4InitBobOuter9FineGrpS
  omega

theorem w4InitBobSpqrWide_fine_groupSpec (F : ShaCompress) (x_res : DoReserveCall) (hasOpk : Bool)
    (x_spqr : InitialStateGhost) :
    PhaseGroupSpec fineCostModel (W4InitBobSpqrWideEnv F x_res hasOpk x_spqr)
      w4InitBobSpqr9FineGrpS := by
  have hSpqr : PhaseGroupSpec fineCostModel (InitialStateEnv F x_spqr) (384 * FineScale) :=
    (initialStateEnv_groupSpec fineCostModel F x_spqr).mono (by decide)
  exact w4InitBobWide_fine_groupSpec x_res hasOpk hSpqr

theorem w4StageP2OverBobWide_fine_groupSpec
    {SerializeArchivedEnv VecPushEnv : List AllocEvent → Prop} {g_ser g_push : Nat}
    (x_res : DoReserveCall) (hasOpk : Bool)
    (F : ShaCompress) (x_spqr : InitialStateGhost)
    (hSer : PhaseGroupSpec fineCostModel SerializeArchivedEnv g_ser)
    (hPush : PhaseGroupSpec fineCostModel VecPushEnv g_push) :
    PhaseGroupSpec fineCostModel
      (W4StageP2OverBobWideEnv SerializeArchivedEnv VecPushEnv x_res hasOpk
        (InitialStateEnv F x_spqr))
      (g_ser + g_push + w4InitBobSpqr9FineGrpS) :=
  (phaseGroupSpec_optStage (promoteStateArchive_groupSpec fineCostModel hSer hPush)).seq
    (phaseGroupSpec_optStage (w4InitBobSpqrWide_fine_groupSpec F x_res hasOpk x_spqr))

theorem w4StageP2OverBobWide_dom_fine_groupSpec {pqCap : Nat}
    {g_arch : RecordGhost} {r_arch : SessionRecord (List (BitVec 8))}
    {VecPushEnv : List AllocEvent → Prop} {g_push : Nat}
    (x_res : DoReserveCall) (hasOpk : Bool)
    (F : ShaCompress) (x_spqr : InitialStateGhost)
    (hArchDom : RecordDom pqCap g_arch r_arch)
    (hPush : PhaseGroupSpec fineCostModel VecPushEnv g_push) :
    PhaseGroupSpec fineCostModel
      (W4StageP2OverBobWideEnv (RecordSerializeCancelEnv g_arch r_arch) VecPushEnv
        x_res hasOpk (InitialStateEnv F x_spqr))
      (recordSerializeDomFineGrpS + g_push + w4InitBobSpqr9FineGrpS) :=
  w4StageP2OverBobWide_fine_groupSpec x_res hasOpk F x_spqr
    (recordSerializeCancelEnv_recordDom_fine_groupSpec hArchDom) hPush

/-- Unconditional scaled group bound for `W4StageP2PathACliWideEnv`. -/
def w4StageP2PathACliWideFineGrpS : Nat :=
  5 * w4SmallStoreStep16FineGrpS + w4InitBobSpqr9FineGrpS + w4ErrTailWideFineGrpS

theorem w4StageP2PathACliWide_fine_groupSpec
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (spkDir kpkDir opkDir ownDir : DirGhost)
    (spkId kpkId opkId : BitVec 32)
    (ownKeyName ownRegName : List (BitVec 8))
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost) :
    PhaseGroupSpec fineCostModel
      (W4StageP2PathACliWideEnv hasOpk rd files spkDir kpkDir opkDir ownDir
        spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr)
      w4StageP2PathACliWideFineGrpS := by
  have hSpk := phaseGroupSpec_optStage (w4SmallStoreStep16_fine_groupSpec rd files spkDir (keyName spkId))
  have hKpk := phaseGroupSpec_optStage (w4SmallStoreStep16_fine_groupSpec rd files kpkDir (keyName kpkId))
  have hOptPk := phaseGroupSpec_optStage (phaseGroupSpec_ite_nil hasOpk fun _ =>
    w4SmallStoreStep16_fine_groupSpec rd files opkDir (keyName opkId))
  have hKp := phaseGroupSpec_optStage (w4SmallStoreStep16_fine_groupSpec rd files ownDir ownKeyName)
  have hBob := phaseGroupSpec_optStage (w4InitBobSpqrWide_fine_groupSpec F x_res hasOpk x_spqr)
  have hReg := phaseGroupSpec_optStage (w4SmallStoreStep16_fine_groupSpec rd files ownDir ownRegName)
  have hErr := w4ErrTailWide_fine_groupSpec
  exact (hSpk.seq (hKpk.seq (hOptPk.seq (hKp.seq (hBob.seq (hReg.seq hErr)))))).mono
    (p2a_grp_le w4SmallStoreStep16FineGrpS w4InitBobSpqr9FineGrpS w4ErrTailWideFineGrpS)

/-- Fixed `Dom` base constant inside `W4StageP2PathCCliWideEnv` before `g_cur`,
`4 * (g_dec + g_tr)`, and `g_push`. -/
def w4StageP2PathCCliWideDomBaseFineGrpS : Nat :=
  segCloneDomFineGrpS + w4ErrTailWideFineGrpS + 5 * w4SmallStoreStep16FineGrpS +
    recordSerializeDomFineGrpS + w4InitBobSpqr9FineGrpS + w4ErrTailWideFineGrpS

/-- Total `Dom` scaled group bound for `W4StageP2PathCCliWideEnv`. -/
def w4StageP2PathCCliWideDomFineGrpS (g_cur g_dec g_tr g_push : Nat) : Nat :=
  w4StageP2PathCCliWideDomBaseFineGrpS + g_cur + 4 * (g_dec + g_tr) + g_push

theorem w4StageP2PathCCliWide_fine_groupSpec {α : Type}
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
    {g_segCur g_cur g_dec g_tr g_archSer g_push : Nat}
    (hSegCur : PhaseGroupSpec fineCostModel (SegCloneEnv G_cur st_cur) g_segCur)
    (hCur : PhaseGroupSpec fineCostModel CurTrialFailEnv g_cur)
    (hlen4 : xs.length ≤ 4)
    (hDec : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DecEnv x) g_dec)
    (hTr : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DropEnv x) 0)
    (hArchSer : PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv g_arch r_arch) g_archSer)
    (hPush : PhaseGroupSpec fineCostModel VecPushEnv g_push) :
    PhaseGroupSpec fineCostModel
      (W4StageP2PathCCliWideEnv G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
        g_arch r_arch VecPushEnv hasOpk rd files spkDir kpkDir opkDir ownDir
        spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr)
      ((g_segCur + w4ErrTailWideFineGrpS + 5 * w4SmallStoreStep16FineGrpS +
          g_archSer + w4InitBobSpqr9FineGrpS + w4ErrTailWideFineGrpS) +
        g_cur + 4 * (g_dec + g_tr) + g_push) := by
  have hE1 := phaseGroupSpec_optStage
    (w4TryDecryptCloneFailWide_fine_groupSpec hSegCur hCur
      (dropClonedSessionEvents_groupSpec fineCostModel G_cur st_cur))
  have hE2 := phaseGroupSpec_optStage
    (archivedTrialLoop_le4_groupSpec fineCostModel hlen4 hDec hTr hDrop)
  have hSpk := phaseGroupSpec_optStage (w4SmallStoreStep16_fine_groupSpec rd files spkDir (keyName spkId))
  have hKpk := phaseGroupSpec_optStage (w4SmallStoreStep16_fine_groupSpec rd files kpkDir (keyName kpkId))
  have hOptPk := phaseGroupSpec_optStage (phaseGroupSpec_ite_nil hasOpk fun _ =>
    w4SmallStoreStep16_fine_groupSpec rd files opkDir (keyName opkId))
  have hKp := phaseGroupSpec_optStage (w4SmallStoreStep16_fine_groupSpec rd files ownDir ownKeyName)
  have hOver := phaseGroupSpec_optStage
    (w4StageP2OverBobWide_fine_groupSpec x_res hasOpk F x_spqr hArchSer hPush)
  have hReg := phaseGroupSpec_optStage (w4SmallStoreStep16_fine_groupSpec rd files ownDir ownRegName)
  have hErr := w4ErrTailWide_fine_groupSpec
  exact (hE1.seq (hE2.seq (hSpk.seq (hKpk.seq (hOptPk.seq
    (hKp.seq (hOver.seq (hReg.seq hErr)))))))).mono
    (p2c_grp_le g_segCur g_cur w4ErrTailWideFineGrpS (4 * (g_dec + g_tr))
      w4SmallStoreStep16FineGrpS g_archSer g_push w4InitBobSpqr9FineGrpS)

theorem w4StageP2PathCCliWide_curDom_fine_groupSpec {α : Type} {pqCap : Nat}
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
    (hCurDom : (∀ evs, ¬ CurTrialFailEnv evs) ∨ StateCloneDom pqCap G_cur st_cur)
    (hCur : PhaseGroupSpec fineCostModel CurTrialFailEnv g_cur)
    (hlen4 : xs.length ≤ 4)
    (hDec : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DecEnv x) g_dec)
    (hTr : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DropEnv x) 0)
    (hArchSer : PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv g_arch r_arch) g_archSer)
    (hPush : PhaseGroupSpec fineCostModel VecPushEnv g_push) :
    PhaseGroupSpec fineCostModel
      (W4StageP2PathCCliWideEnv G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
        g_arch r_arch VecPushEnv hasOpk rd files spkDir kpkDir opkDir ownDir
        spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr)
      ((segCloneDomFineGrpS + w4ErrTailWideFineGrpS + 5 * w4SmallStoreStep16FineGrpS +
          g_archSer + w4InitBobSpqr9FineGrpS + w4ErrTailWideFineGrpS) +
        g_cur + 4 * (g_dec + g_tr) + g_push) := by
  have hE1 : PhaseGroupSpec fineCostModel
      (OptStageEnv
        (W4TryDecryptCloneFailWideEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
          (· = dropClonedSessionEvents G_cur st_cur)))
      (segCloneDomFineGrpS + g_cur + w4ErrTailWideFineGrpS) := by
    rcases hCurDom with hNo | hDom
    · have hEmpty : PhaseGroupSpec fineCostModel
          (W4TryDecryptCloneFailWideEnv (SegCloneEnv G_cur st_cur) CurTrialFailEnv
            (· = dropClonedSessionEvents G_cur st_cur)) 0 :=
        { groups_le := fun _ {_} hE => by
            rcases hE with h1 | ⟨_, _, _, h1, _⟩
            · obtain ⟨_, _, _, ⟨_, e2, _, _, htf⟩, _⟩ := h1
              exact False.elim (hNo e2 htf)
            · obtain ⟨_, _, _, ⟨_, e2, _, _, htf⟩, _⟩ := h1
              exact False.elim (hNo e2 htf) }
      exact (phaseGroupSpec_optStage hEmpty).mono (Nat.zero_le _)
    · exact phaseGroupSpec_optStage (w4TryDecryptCloneFailWide_dom_fine_groupSpec hDom hCur)
  have hE2 := phaseGroupSpec_optStage
    (archivedTrialLoop_le4_groupSpec fineCostModel hlen4 hDec hTr hDrop)
  have hSpk := phaseGroupSpec_optStage (w4SmallStoreStep16_fine_groupSpec rd files spkDir (keyName spkId))
  have hKpk := phaseGroupSpec_optStage (w4SmallStoreStep16_fine_groupSpec rd files kpkDir (keyName kpkId))
  have hOptPk := phaseGroupSpec_optStage (phaseGroupSpec_ite_nil hasOpk fun _ =>
    w4SmallStoreStep16_fine_groupSpec rd files opkDir (keyName opkId))
  have hKp := phaseGroupSpec_optStage (w4SmallStoreStep16_fine_groupSpec rd files ownDir ownKeyName)
  have hOver := phaseGroupSpec_optStage
    (w4StageP2OverBobWide_fine_groupSpec x_res hasOpk F x_spqr hArchSer hPush)
  have hReg := phaseGroupSpec_optStage (w4SmallStoreStep16_fine_groupSpec rd files ownDir ownRegName)
  have hErr := w4ErrTailWide_fine_groupSpec
  exact (hE1.seq (hE2.seq (hSpk.seq (hKpk.seq (hOptPk.seq
    (hKp.seq (hOver.seq (hReg.seq hErr)))))))).mono
    (p2c_grp_le segCloneDomFineGrpS g_cur w4ErrTailWideFineGrpS (4 * (g_dec + g_tr))
      w4SmallStoreStep16FineGrpS g_archSer g_push w4InitBobSpqr9FineGrpS)

theorem w4StageP2PathCCliWide_dom_fine_groupSpec {α : Type} {pqCap : Nat}
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
    {g_cur g_dec g_tr g_push : Nat}
    (hCurDom : StateCloneDom pqCap G_cur st_cur)
    (hCur : PhaseGroupSpec fineCostModel CurTrialFailEnv g_cur)
    (hlen4 : xs.length ≤ 4)
    (hDec : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DecEnv x) g_dec)
    (hTr : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ xs, PhaseGroupSpec fineCostModel (DropEnv x) 0)
    (hArchDom : RecordDom pqCap g_arch r_arch)
    (hPush : PhaseGroupSpec fineCostModel VecPushEnv g_push) :
    PhaseGroupSpec fineCostModel
      (W4StageP2PathCCliWideEnv G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
        g_arch r_arch VecPushEnv hasOpk rd files spkDir kpkDir opkDir ownDir
        spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr)
      (w4StageP2PathCCliWideDomFineGrpS g_cur g_dec g_tr g_push) :=
  w4StageP2PathCCliWide_fine_groupSpec hasOpk rd files spkDir kpkDir opkDir ownDir
    spkId kpkId opkId ownKeyName ownRegName F x_res x_spqr
    (segCloneEnv_stateDom_fine_groupSpec hCurDom) hCur hlen4 hDec hTr hDrop
    (recordSerializeCancelEnv_recordDom_fine_groupSpec hArchDom) hPush

/-- Scaled group bound (`g_cl + g_td + w4ErrTailWideFineGrpS`) for `W4StageP3WideEnv`. -/
def w4StageP3WideFineGrpS (g_cl g_td : Nat) : Nat :=
  g_cl + g_td + w4ErrTailWideFineGrpS

private theorem p3_wide_grp_le (a b c : Nat) : a + (b + c) ≤ a + b + c := by
  omega

theorem w4StageP3Wide_fine_groupSpec {CloneEnv TryDecEnv : List AllocEvent → Prop} {g_cl g_td : Nat}
    (hCl : PhaseGroupSpec fineCostModel CloneEnv g_cl)
    (hTd : PhaseGroupSpec fineCostModel TryDecEnv g_td) :
    PhaseGroupSpec fineCostModel (W4StageP3WideEnv CloneEnv TryDecEnv)
      (w4StageP3WideFineGrpS g_cl g_td) :=
  (hCl.seq ((phaseGroupSpec_optStage hTd).seq w4ErrTailWide_fine_groupSpec)).mono
    (p3_wide_grp_le g_cl g_td w4ErrTailWideFineGrpS)

theorem w4StageP4MatchedCliWide_fine_groupSpec
    (rd : ReadRule) (files : FsFiles) (peersDir sessDir : DirGhost) (peer : AddrGhost)
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))} {g_ser : Nat}
    (hSer : PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv g_rec r_rec) g_ser) :
    PhaseGroupSpec fineCostModel
      (W4StageP4MatchedCliWideEnv rd files peersDir sessDir peer g_rec r_rec)
      (w4SmallStoreStep32FineGrpS + (16659 + (6 * FineScale + g_ser))) := by
  have hSave := phaseGroupSpec_optStage
    (w4SmallStoreStep32_fine_groupSpec rd files peersDir (addressText peer.val))
  have hStore := ((phaseGroupSpec_optStage (w4SessStoreStep_fine_groupSpec sessDir peer hSer)).seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  exact hSave.seq hStore

theorem w4StageP4MatchedCliWide_dom_fine_groupSpec {pqCap : Nat}
    (rd : ReadRule) (files : FsFiles) (peersDir sessDir : DirGhost) (peer : AddrGhost)
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))}
    (hDom : RecordDom pqCap g_rec r_rec) :
    PhaseGroupSpec fineCostModel
      (W4StageP4MatchedCliWideEnv rd files peersDir sessDir peer g_rec r_rec)
      w4StageP4MatchedDomFineGrpS :=
  w4StageP4MatchedCliWide_fine_groupSpec rd files peersDir sessDir peer
    (recordSerializeCancelEnv_recordDom_fine_groupSpec hDom)

theorem w4StageP4PathACliWide_fine_groupSpec
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peersDir kpkDir opkDir sessDir : DirGhost) (peer : AddrGhost)
    (kpkName : List (BitVec 8)) (opkId : BitVec 32)
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))} {g_ser : Nat}
    (hSer : PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv g_rec r_rec) g_ser) :
    PhaseGroupSpec fineCostModel
      (W4StageP4PathACliWideEnv hasOpk rd files peersDir kpkDir opkDir sessDir
        peer kpkName opkId g_rec r_rec)
      (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
        (16659 + (6 * FineScale + g_ser))) := by
  have hSave := phaseGroupSpec_optStage
    (w4SmallStoreStep32_fine_groupSpec rd files peersDir (addressText peer.val))
  have hMark := phaseGroupSpec_optStage (w4SmallStoreStep32_fine_groupSpec rd files kpkDir kpkName)
  have hRem := phaseGroupSpec_optStage (phaseGroupSpec_ite_nil hasOpk fun _ =>
    w4SmallStoreStep16_fine_groupSpec rd files opkDir (keyName opkId))
  have hStore := ((phaseGroupSpec_optStage (w4SessStoreStep_fine_groupSpec sessDir peer hSer)).seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  exact (hSave.seq (hMark.seq (hRem.seq hStore))).mono
    (p4_ac_grp_le w4SmallStoreStep32FineGrpS w4SmallStoreStep16FineGrpS
      (16659 + (6 * FineScale + g_ser)))

theorem w4StageP4PathACliWide_dom_fine_groupSpec {pqCap : Nat}
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peersDir kpkDir opkDir sessDir : DirGhost) (peer : AddrGhost)
    (kpkName : List (BitVec 8)) (opkId : BitVec 32)
    {g_rec : RecordGhost} {r_rec : SessionRecord (List (BitVec 8))}
    (hDom : RecordDom pqCap g_rec r_rec) :
    PhaseGroupSpec fineCostModel
      (W4StageP4PathACliWideEnv hasOpk rd files peersDir kpkDir opkDir sessDir
        peer kpkName opkId g_rec r_rec)
      w4StageP4PathADomFineGrpS :=
  w4StageP4PathACliWide_fine_groupSpec hasOpk rd files peersDir kpkDir opkDir sessDir
    peer kpkName opkId (recordSerializeCancelEnv_recordDom_fine_groupSpec hDom)

theorem w4StageP4PathCCliWide_fine_groupSpec
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peersDir kpkDir opkDir sessDir : DirGhost) (peer : AddrGhost)
    (kpkName : List (BitVec 8)) (opkId : BitVec 32)
    {G : SessionGhost} {sess : Session (List (BitVec 8))} {enc : List (BitVec 8)} {g_ser1 : Nat}
    (hSer1 : PhaseGroupSpec fineCostModel (SerializePrev1CancelEnv G sess enc) g_ser1) :
    PhaseGroupSpec fineCostModel
      (W4StageP4PathCCliWideEnv hasOpk rd files peersDir kpkDir opkDir sessDir
        peer kpkName opkId G sess enc)
      (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
        (16659 + (6 * FineScale + g_ser1))) := by
  have hSave := phaseGroupSpec_optStage
    (w4SmallStoreStep32_fine_groupSpec rd files peersDir (addressText peer.val))
  have hMark := phaseGroupSpec_optStage (w4SmallStoreStep32_fine_groupSpec rd files kpkDir kpkName)
  have hRem := phaseGroupSpec_optStage (phaseGroupSpec_ite_nil hasOpk fun _ =>
    w4SmallStoreStep16_fine_groupSpec rd files opkDir (keyName opkId))
  have hStore := ((phaseGroupSpec_optStage (w4SessStorePrev1Step_fine_groupSpec sessDir peer hSer1)).seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  exact (hSave.seq (hMark.seq (hRem.seq hStore))).mono
    (p4_ac_grp_le w4SmallStoreStep32FineGrpS w4SmallStoreStep16FineGrpS
      (16659 + (6 * FineScale + g_ser1)))

theorem w4StageP4PathCCliWide_dom_fine_groupSpec {pqCap : Nat}
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peersDir kpkDir opkDir sessDir : DirGhost) (peer : AddrGhost)
    (kpkName : List (BitVec 8)) (opkId : BitVec 32)
    {G : SessionGhost} {sess : Session (List (BitVec 8))} (enc : List (BitVec 8))
    (hDom : SessionOutDom pqCap G sess) :
    PhaseGroupSpec fineCostModel
      (W4StageP4PathCCliWideEnv hasOpk rd files peersDir kpkDir opkDir sessDir
        peer kpkName opkId G sess enc)
      w4StageP4PathCDomFineGrpS := by
  have hSave := phaseGroupSpec_optStage
    (w4SmallStoreStep32_fine_groupSpec rd files peersDir (addressText peer.val))
  have hMark := phaseGroupSpec_optStage (w4SmallStoreStep32_fine_groupSpec rd files kpkDir kpkName)
  have hRem := phaseGroupSpec_optStage (phaseGroupSpec_ite_nil hasOpk fun _ =>
    w4SmallStoreStep16_fine_groupSpec rd files opkDir (keyName opkId))
  have hStore := ((phaseGroupSpec_optStage
    (w4SessStorePrev1Step_dom_fine_groupSpec sessDir peer enc hDom)).seq
    (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero _))
  exact (hSave.seq (hMark.seq (hRem.seq hStore))).mono
    (p4_ac_grp_le w4SmallStoreStep32FineGrpS w4SmallStoreStep16FineGrpS
      w4SessStorePrev1StepDomFineGrpS)

/-- Parametric 4-arm scaled group formula for `W4DecryptPrekeySplitWideSlotEnv`. -/
def w4DecryptPrekeySplitWideSlotFineGrpS
    (g_deser g_segCur g_cur g_dec g_tr g_archSer g_push
     g_segB g_td_B g_segAC g_td_AC g_out0Ser g_out1Ser : Nat) : Nat :=
  let gU := w4StageP1UntrustedBaseFineGrpS + g_deser
  let gB := (w4StageP1OkBaseFineGrpS + g_deser) +
    (w4StageP2MatchedCheckFineGrpS + 4 * (g_dec + g_tr) + g_archSer + g_push) +
    w4StageP3WideFineGrpS g_segB g_td_B +
    (w4SmallStoreStep32FineGrpS + (16659 + (6 * FineScale + g_out0Ser)))
  let gA := (w4StageP1OkBaseFineGrpS + g_deser) +
    w4StageP2PathACliWideFineGrpS +
    w4StageP3WideFineGrpS g_segAC g_td_AC +
    (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
      (16659 + (6 * FineScale + g_out0Ser)))
  let gC := (w4StageP1OkBaseFineGrpS + g_deser) +
    ((g_segCur + w4ErrTailWideFineGrpS + 5 * w4SmallStoreStep16FineGrpS +
        g_archSer + w4InitBobSpqr9FineGrpS + w4ErrTailWideFineGrpS) +
      g_cur + 4 * (g_dec + g_tr) + g_push) +
    w4StageP3WideFineGrpS g_segAC g_td_AC +
    (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
      (16659 + (6 * FineScale + g_out1Ser)))
  max (max gU gB) (max gA gC)

/-- Parametric 4-arm `PhaseGroupSpec` for `W4DecryptPrekeySplitWideSlotEnv`, supporting split
Stage P3 `CloneB` vs `CloneAC` and `P.TryDecEnv` vs `TryDecAC`. -/
theorem w4DecryptPrekeySplitWideSlot_fine_groupSpec {α : Type}
    (P : W4DecryptPrekeySlotParams α)
    (CloneB CloneAC TryDecAC : List AllocEvent → Prop)
    {g_deser g_segCur g_cur g_dec g_tr g_archSer g_push
     g_segB g_td_B g_segAC g_td_AC g_out0Ser g_out1Ser : Nat}
    (hDeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (P.DeserEnv bs) g_deser)
    (hSegCur : (∃ e, W4DecryptPrekeyPathCWideEnv P CloneAC TryDecAC e) →
      PhaseGroupSpec fineCostModel (SegCloneEnv P.G_cur P.st_cur) g_segCur)
    (hCur : (∃ e, W4DecryptPrekeyPathCWideEnv P CloneAC TryDecAC e) →
      PhaseGroupSpec fineCostModel P.CurTrialFailEnv g_cur)
    (hlen4 : P.archivedTrials.length ≤ 4)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DecEnv x) g_dec)
    (hTr : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DropEnv x) 0)
    (hArchSer : (∃ e, W4DecryptPrekeyPathBWideEnv P CloneB e ∨
        W4DecryptPrekeyPathCWideEnv P CloneAC TryDecAC e) →
      PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv P.g_arch P.r_arch) g_archSer)
    (hPush : PhaseGroupSpec fineCostModel P.VecPushEnv g_push)
    (hSegB : (∃ e, W4DecryptPrekeyPathBWideEnv P CloneB e) →
      PhaseGroupSpec fineCostModel CloneB g_segB)
    (hTdB : (∃ e, W4DecryptPrekeyPathBWideEnv P CloneB e) →
      PhaseGroupSpec fineCostModel P.TryDecEnv g_td_B)
    (hSegAC : (∃ e, W4DecryptPrekeyPathAWideEnv P CloneAC TryDecAC e ∨
        W4DecryptPrekeyPathCWideEnv P CloneAC TryDecAC e) →
      PhaseGroupSpec fineCostModel CloneAC g_segAC)
    (hTdAC : (∃ e, W4DecryptPrekeyPathAWideEnv P CloneAC TryDecAC e ∨
        W4DecryptPrekeyPathCWideEnv P CloneAC TryDecAC e) →
      PhaseGroupSpec fineCostModel TryDecAC g_td_AC)
    (hOut0Ser : (∃ e, W4DecryptPrekeyPathBWideEnv P CloneB e ∨
        W4DecryptPrekeyPathAWideEnv P CloneAC TryDecAC e) →
      PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv P.g_out0 P.r_out0) g_out0Ser)
    (hOut1Ser : (∃ e, W4DecryptPrekeyPathCWideEnv P CloneAC TryDecAC e) →
      PhaseGroupSpec fineCostModel (SerializePrev1CancelEnv P.G_out1 P.sess_out1 P.enc_prev1)
        g_out1Ser) :
    PhaseGroupSpec fineCostModel (W4DecryptPrekeySplitWideSlotEnv P CloneB CloneAC TryDecAC)
      (w4DecryptPrekeySplitWideSlotFineGrpS g_deser g_segCur g_cur g_dec g_tr g_archSer g_push
        g_segB g_td_B g_segAC g_td_AC g_out0Ser g_out1Ser) := by
  let gAll := w4DecryptPrekeySplitWideSlotFineGrpS g_deser g_segCur g_cur g_dec g_tr g_archSer
    g_push g_segB g_td_B g_segAC g_td_AC g_out0Ser g_out1Ser
  have hLeU : w4StageP1UntrustedBaseFineGrpS + g_deser ≤ gAll :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hLeB : (w4StageP1OkBaseFineGrpS + g_deser) +
      (w4StageP2MatchedCheckFineGrpS + 4 * (g_dec + g_tr) + g_archSer + g_push) +
      w4StageP3WideFineGrpS g_segB g_td_B +
      (w4SmallStoreStep32FineGrpS + (16659 + (6 * FineScale + g_out0Ser))) ≤ gAll :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hLeA : (w4StageP1OkBaseFineGrpS + g_deser) +
      w4StageP2PathACliWideFineGrpS +
      w4StageP3WideFineGrpS g_segAC g_td_AC +
      (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
        (16659 + (6 * FineScale + g_out0Ser))) ≤ gAll :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hLeC : (w4StageP1OkBaseFineGrpS + g_deser) +
      ((g_segCur + w4ErrTailWideFineGrpS + 5 * w4SmallStoreStep16FineGrpS +
          g_archSer + w4InitBobSpqr9FineGrpS + w4ErrTailWideFineGrpS) +
        g_cur + 4 * (g_dec + g_tr) + g_push) +
      w4StageP3WideFineGrpS g_segAC g_td_AC +
      (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
        (16659 + (6 * FineScale + g_out1Ser))) ≤ gAll :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hP1 := w4StageP1OkCli_fine_groupSpec P.rd P.files P.sessDir P.peersDir P.peer hDeser
  have hArms : PhaseGroupSpec fineCostModel
      (fun e =>
        W4StageP1UntrustedCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer e ∨
        W4DecryptPrekeyPathBWideEnv P CloneB e ∨
        W4DecryptPrekeyPathAWideEnv P CloneAC TryDecAC e ∨
        W4DecryptPrekeyPathCWideEnv P CloneAC TryDecAC e)
      gAll :=
    { groups_le := fun st0 {e} hArm => by
        rcases hArm with hU | hB | hA | hC
        · exact ((w4StageP1UntrustedCli_fine_groupSpec P.rd P.files P.sessDir P.peersDir P.peer
            hDeser).mono hLeU).groups_le st0 hU
        · have hp2 := phaseGroupSpec_optStage
            (w4StageP2MatchedWide_fine_groupSpec hlen4 hDec hTr hDrop
              (hArchSer ⟨e, Or.inl hB⟩) hPush)
          have hp3 := phaseGroupSpec_optStage
            (w4StageP3Wide_fine_groupSpec (hSegB ⟨e, hB⟩) (hTdB ⟨e, hB⟩))
          have hp4 := phaseGroupSpec_optStage
            (w4StageP4MatchedCliWide_fine_groupSpec P.rd P.files P.peersDir P.sessDir P.peer
              (hOut0Ser ⟨e, Or.inl hB⟩))
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (fourStages_grp_le _ _ _ _)).mono hLeB).groups_le st0 hB
        · have hp2 := phaseGroupSpec_optStage
            (w4StageP2PathACliWide_fine_groupSpec P.hasOpk P.rd P.files
              P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
              P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr)
          have hp3 := phaseGroupSpec_optStage
            (w4StageP3Wide_fine_groupSpec (hSegAC ⟨e, Or.inl hA⟩) (hTdAC ⟨e, Or.inl hA⟩))
          have hp4 := phaseGroupSpec_optStage
            (w4StageP4PathACliWide_fine_groupSpec P.hasOpk P.rd P.files
              P.peersDir P.kpkDir P.opkDir P.sessDir P.peer P.kpkMarkName P.opkId
              (hOut0Ser ⟨e, Or.inr hA⟩))
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (fourStages_grp_le _ _ _ _)).mono hLeA).groups_le st0 hA
        · have hp2 := phaseGroupSpec_optStage
            (w4StageP2PathCCliWide_fine_groupSpec P.hasOpk P.rd P.files
              P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
              P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr
              (hSegCur ⟨e, hC⟩) (hCur ⟨e, hC⟩) hlen4 hDec hTr hDrop
              (hArchSer ⟨e, Or.inr hC⟩) hPush)
          have hp3 := phaseGroupSpec_optStage
            (w4StageP3Wide_fine_groupSpec (hSegAC ⟨e, Or.inr hC⟩) (hTdAC ⟨e, Or.inr hC⟩))
          have hp4 := phaseGroupSpec_optStage
            (w4StageP4PathCCliWide_fine_groupSpec P.hasOpk P.rd P.files
              P.peersDir P.kpkDir P.opkDir P.sessDir P.peer P.kpkMarkName P.opkId
              (hOut1Ser ⟨e, hC⟩))
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (fourStages_grp_le _ _ _ _)).mono hLeC).groups_le st0 hC }
  have hSeq := (hArms.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hSeq).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

/-- `cur_dom`-guarded companion to `w4DecryptPrekeySplitWideSlot_fine_groupSpec` (matching
`W4DecryptPrekeyTightDom.cur_dom`: `(∀ evs, ¬ P.CurTrialFailEnv evs) ∨ StateCloneDom pqCap P.G_cur P.st_cur`),
discharging `g_segCur := segCloneDomFineGrpS` directly without dummy-session obligations when
`CurTrialFailEnv` is uninhabited. -/
theorem w4DecryptPrekeySplitWideSlot_curDom_fine_groupSpec {α : Type} {pqCap : Nat}
    (P : W4DecryptPrekeySlotParams α)
    (CloneB CloneAC TryDecAC : List AllocEvent → Prop)
    {g_deser g_cur g_dec g_tr g_archSer g_push
     g_segB g_td_B g_segAC g_td_AC g_out0Ser g_out1Ser : Nat}
    (hDeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (P.DeserEnv bs) g_deser)
    (hCurDom : (∀ evs, ¬ P.CurTrialFailEnv evs) ∨ StateCloneDom pqCap P.G_cur P.st_cur)
    (hCur : PhaseGroupSpec fineCostModel P.CurTrialFailEnv g_cur)
    (hlen4 : P.archivedTrials.length ≤ 4)
    (hDec : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DecEnv x) g_dec)
    (hTr : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.TrialEnv x) g_tr)
    (hDrop : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DropEnv x) 0)
    (hArchSer : PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv P.g_arch P.r_arch) g_archSer)
    (hPush : PhaseGroupSpec fineCostModel P.VecPushEnv g_push)
    (hSegB : PhaseGroupSpec fineCostModel CloneB g_segB)
    (hTdB : PhaseGroupSpec fineCostModel P.TryDecEnv g_td_B)
    (hSegAC : PhaseGroupSpec fineCostModel CloneAC g_segAC)
    (hTdAC : PhaseGroupSpec fineCostModel TryDecAC g_td_AC)
    (hOut0Ser : PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv P.g_out0 P.r_out0) g_out0Ser)
    (hOut1Ser : PhaseGroupSpec fineCostModel
      (SerializePrev1CancelEnv P.G_out1 P.sess_out1 P.enc_prev1) g_out1Ser) :
    PhaseGroupSpec fineCostModel (W4DecryptPrekeySplitWideSlotEnv P CloneB CloneAC TryDecAC)
      (w4DecryptPrekeySplitWideSlotFineGrpS g_deser segCloneDomFineGrpS g_cur g_dec g_tr g_archSer
        g_push g_segB g_td_B g_segAC g_td_AC g_out0Ser g_out1Ser) := by
  let gAll := w4DecryptPrekeySplitWideSlotFineGrpS g_deser segCloneDomFineGrpS g_cur g_dec g_tr
    g_archSer g_push g_segB g_td_B g_segAC g_td_AC g_out0Ser g_out1Ser
  have hLeU : w4StageP1UntrustedBaseFineGrpS + g_deser ≤ gAll :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hLeB : (w4StageP1OkBaseFineGrpS + g_deser) +
      (w4StageP2MatchedCheckFineGrpS + 4 * (g_dec + g_tr) + g_archSer + g_push) +
      w4StageP3WideFineGrpS g_segB g_td_B +
      (w4SmallStoreStep32FineGrpS + (16659 + (6 * FineScale + g_out0Ser))) ≤ gAll :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hLeA : (w4StageP1OkBaseFineGrpS + g_deser) +
      w4StageP2PathACliWideFineGrpS +
      w4StageP3WideFineGrpS g_segAC g_td_AC +
      (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
        (16659 + (6 * FineScale + g_out0Ser))) ≤ gAll :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hLeC : (w4StageP1OkBaseFineGrpS + g_deser) +
      ((segCloneDomFineGrpS + w4ErrTailWideFineGrpS + 5 * w4SmallStoreStep16FineGrpS +
          g_archSer + w4InitBobSpqr9FineGrpS + w4ErrTailWideFineGrpS) +
        g_cur + 4 * (g_dec + g_tr) + g_push) +
      w4StageP3WideFineGrpS g_segAC g_td_AC +
      (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
        (16659 + (6 * FineScale + g_out1Ser))) ≤ gAll :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hP1 := w4StageP1OkCli_fine_groupSpec P.rd P.files P.sessDir P.peersDir P.peer hDeser
  have hArms : PhaseGroupSpec fineCostModel
      (fun e =>
        W4StageP1UntrustedCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer e ∨
        W4DecryptPrekeyPathBWideEnv P CloneB e ∨
        W4DecryptPrekeyPathAWideEnv P CloneAC TryDecAC e ∨
        W4DecryptPrekeyPathCWideEnv P CloneAC TryDecAC e)
      gAll :=
    { groups_le := fun st0 {e} hArm => by
        rcases hArm with hU | hB | hA | hC
        · exact ((w4StageP1UntrustedCli_fine_groupSpec P.rd P.files P.sessDir P.peersDir P.peer
            hDeser).mono hLeU).groups_le st0 hU
        · have hp2 := phaseGroupSpec_optStage
            (w4StageP2MatchedWide_fine_groupSpec hlen4 hDec hTr hDrop hArchSer hPush)
          have hp3 := phaseGroupSpec_optStage (w4StageP3Wide_fine_groupSpec hSegB hTdB)
          have hp4 := phaseGroupSpec_optStage
            (w4StageP4MatchedCliWide_fine_groupSpec P.rd P.files P.peersDir P.sessDir P.peer hOut0Ser)
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (fourStages_grp_le _ _ _ _)).mono hLeB).groups_le st0 hB
        · have hp2 := phaseGroupSpec_optStage
            (w4StageP2PathACliWide_fine_groupSpec P.hasOpk P.rd P.files
              P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
              P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr)
          have hp3 := phaseGroupSpec_optStage (w4StageP3Wide_fine_groupSpec hSegAC hTdAC)
          have hp4 := phaseGroupSpec_optStage
            (w4StageP4PathACliWide_fine_groupSpec P.hasOpk P.rd P.files
              P.peersDir P.kpkDir P.opkDir P.sessDir P.peer P.kpkMarkName P.opkId hOut0Ser)
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (fourStages_grp_le _ _ _ _)).mono hLeA).groups_le st0 hA
        · have hp2 := phaseGroupSpec_optStage
            (w4StageP2PathCCliWide_curDom_fine_groupSpec P.hasOpk P.rd P.files
              P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
              P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr
              hCurDom hCur hlen4 hDec hTr hDrop hArchSer hPush)
          have hp3 := phaseGroupSpec_optStage (w4StageP3Wide_fine_groupSpec hSegAC hTdAC)
          have hp4 := phaseGroupSpec_optStage
            (w4StageP4PathCCliWide_fine_groupSpec P.hasOpk P.rd P.files
              P.peersDir P.kpkDir P.opkDir P.sessDir P.peer P.kpkMarkName P.opkId hOut1Ser)
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (fourStages_grp_le _ _ _ _)).mono hLeC).groups_le st0 hC }
  have hSeq := (hArms.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hSeq).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

end WidenedBinaryCompleteGroupSpecs

end LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec
