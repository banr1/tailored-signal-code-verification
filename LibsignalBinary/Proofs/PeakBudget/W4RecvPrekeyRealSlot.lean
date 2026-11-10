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
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak
public import LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738
public import LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
public import LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec
public import LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.DropSsLocal1Budget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget

/-!
# Witness-Free `recv-prekey` Real Slot Instance

Witness-free `CliSlotFineSpec.SingleSlotFineSpec` instantiation for the `decrypt_prekey` /
`process_prekey` CLI slot envelope:
1. Wires `W4OuterTightSpec.W4DecryptPrekeySplitSlotEnv` to `RecordDeserializeCancelEnv` and
   `SessDeserializeCancelEnv`, `StoresGhost.opened` directories, `SpqrRecvC07TightLinkedEnv` under
   `TopStateTight`, fresh-Bob `12`-seed `ChainRecvKeyZeroSkip` Stage P3 `try_decrypt` and
   `FreshBobPrev1Dom` Path C serialization, and `dropSessionStructureLocal1Events` /
   `optDeallocListEvs` drop cancellation.
2. Exports `w4RecvPrekeyReal_singleSlotFineSpec`, closed `Nat` cap checks (`w4RecvPrekeyReal_caps_le`),
   and an allocating non-vacuity witness (`w4RecvPrekeyRealEnv_nonvacuous_alloc`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot

open CryptoGames.LibsignalSession
  (MessageKeyGenerator ReceiverChain SenderChain SessionState ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (encodeRecordPrev1Mem)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalSessionRepr (ChainGhost MessageKeyGhost VecPin)
open CryptoVerification.LibsignalSpqrV1
  (Bytes MlKem spqrAuthApi spqrPolyApi)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SenderChainGhost SessionGhost)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule StoresGhost keyName)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds (fineCostModel_smallMaxReq_eq)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (W2TryDecryptTightEnv dropClonedSessionEvents_groupSpec dropVecVecClone1Events_groupSpec
   optTailCloneEvents_groupSpec phaseGroupSpec_append_eq recordSerializeDomFineGrpS
   segCloneDomFineGrpS segCloneEnv_dom_fine_groupSpec senderChainCloneDomFineGrpS
   senderChainCloneEnv_dom_fine_groupSpec serializeSomeCancelEnv_groupSpec vecCloneEvents_groupSpec
   vecVecClone1Events_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
  (cliRecvPrekeySlotCumCap cliRecvPrekeySlotGrpSCap cliRecvPrekeySlotLiveCap
   cliRecvPrekeySlotPeakCap cliRecvPrekeySlotReqCap)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (HasFineGroupCredit PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv DeallocCreditSpec FreeOnlyAlign16Evs IterSeqEnv PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (RecordSerializeCancelEnv dropClonedSessionEvents)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit (SerializePrev1CancelEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvC09aWire (c09aStatesRecvTightCreditSpec_inst)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
  (SpqrRecvC07TightLinkedEnv spqrRecvTightDomain_of_topStateTight_and_link)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit
  (w2TryDecryptFailTightEnv_linked_fine_groupSpec_split_12 w2TryDecryptFailTightGroupS_split_12
   w2TryDecryptFail_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738
   w2TryDecryptSeeds12GroupS_split_12 w2TryDecryptSeedsEnv_12_linked_fine_groupSpec_split_12
   w2TryDecryptTightEnv_linked_fine_groupSpec_split_12
   w2TryDecrypt_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit (w2TryDecryptTightGroupS_split_12)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec (StatesRecvProtoEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (TopStateTight)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (SessionCloneDom ghostCloneValid_of_sessionGhostValid)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
  (w2CmkChainTightLive w2TryDecryptMaxReq w2TryDecryptTightLive w2TryDecryptTightPeak)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak (DoublingChainLe)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak (optDeallocListEvs optDeallocListLarge)
open LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738
  (W2TryDecryptFailTightEnv W2TryDecryptSeedsEnv w2TryDecryptGenSeeds738Cum
   w2TryDecryptSeeds738Cum w2TryDecrypt_genSeeds_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak (ArchivedTrialIterEnv)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
  (W4BoundedEvs phaseCredit_w4BoundedEvs_small)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (W4DecryptPrekeyPathAEnv W4DecryptPrekeyPathBEnv W4DecryptPrekeyPathCEnv
   W4DecryptPrekeySlotParams W4StageP2PathCCliEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers (W4StageP1UntrustedCliEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec
  (W4DecryptPrekeySplitSlotEnv W4DecryptPrekeyTightDom w4DecryptPrekeySplitSlot_opened_fine_phaseCredit
   w4DecryptPrekeySplitTightCum w4DecryptPrekeySplitTightLive w4DecryptPrekeySplitTightMaxReq
   w4DecryptPrekeySplitTightPeak)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
  (ChainRecvKeyZeroSkip FreshBobPrev1Dom fineOptLarge
   spqrRecvParts_c07_zeroSkip_c09a_phaseCreditSpec_tight
   tryDecryptCloneFail_dom_fine_cancel_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec
  (SpqrRecvC07Witness archivedTrialLoop_le4_groupSpec phaseGroupSpec_ite_nil
   w4BoundedEvs_groupSpec w4ErrTailFineGrpS w4ErrTail_fine_groupSpec w4InitBobSpqrFineGrpS
   w4SmallStoreStep16FineGrpS w4SmallStoreStep16_fine_groupSpec w4SmallStoreStep32FineGrpS
   w4StageP1OkBaseFineGrpS w4StageP1OkCli_fine_groupSpec w4StageP1UntrustedBaseFineGrpS
   w4StageP1UntrustedCli_fine_groupSpec w4StageP2Matched_groupSpec w4StageP2OverBob_fine_groupSpec
   w4StageP2PathACliFineGrpS w4StageP2PathACli_fine_groupSpec w4StageP3FineGrpS
   w4StageP3_fine_groupSpec w4StageP4MatchedCli_fine_groupSpec w4StageP4PathACli_fine_groupSpec
   w4StageP4PathCCli_fine_groupSpec w4TryDecryptCloneFail_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak (W4TryDecryptCloneFailEnv)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.DropSsLocal1Budget
  (SessionDropCapsOk chainPairFreeEvents dropSessionStructureLocal1Events dropVecChainEvents
   dropVecMessageKeyEvents mkFreeEvents optCkCapVal optTailCapVal pinFreeEvents senderFreeEvents
   sgnCapFreeEvents ssFirst3FreeEvents ssTail3FreeEvents stepEvents_dropSessionStructureLocal1_bounds
   vec104FreeEvents)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (ssStateLargeLive)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
  (sessDeserLargeLive)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (deserCancelFineCum deserCancelFineGrpS deserCancelFineLive deserCancelFineMaxReq
   deserCancelFinePeak recordDeserializeCancelEnv_fine_groupSpec
   recordDeserializeCancelEnv_fine_phaseCreditSpec sessDeserializeCancelEnv_fine_groupSpec
   sessDeserializeCancelEnv_fine_phaseCreditSpec sessDeserializeCancelEnv_phaseCreditSpec)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
  (RecordDeserializeCancelEnv SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv segCloneEvents)

/-! ## Witness-Free Call Data Bundles & Exact Binary Envelopes -/

/-- Bundled call parameters for one linked `try_decrypt` invocation (`PathB`, `PathA/C`, or failed trial). -/
structure W4TryDecryptCall (F : ShaCompress) : Type where
  dhCap : Nat
  needGrow : Bool
  caps : List Nat
  withAddr : Bool
  errAlloc : Bool
  ctLen : Nat
  stBytes : Bytes
  w : SpqrRecvC07Witness F

/-- Bundled call parameters for a failed cloned-session `try_decrypt` trial plus its receiver-chain
`cmk` / SPQR temporary buffer drop list (`optDeallocListEvs failDropPairs`). -/
structure W4FailedTryDecryptCall (F : ShaCompress) : Type where
  td : W4TryDecryptCall F
  failDropPairs : List (Nat × Nat)

/-- Bundled call parameters for one archived-session `PrevDec` + `try_decrypt_pq` + drop iteration. -/
structure W4ArchivedTrial (F : ShaCompress) : Type where
  r_dec : SessionRecord (List (BitVec 8))
  G_dec : SessionGhost
  st_dec : SessionState (List (BitVec 8))
  G_tr : SessionGhost
  ses_tr : Session (List (BitVec 8))
  fc_tr : W4FailedTryDecryptCall F

/-- Curried `SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv` at a concrete `SpqrRecvC07Witness F`. -/
def W4SpqrLinkedStepEnv (F : ShaCompress) (K : MlKem) (stBytes : Bytes)
    (w : SpqrRecvC07Witness F) (evs : List AllocEvent) : Prop :=
  SpqrRecvC07TightLinkedEnv F K StatesRecvProtoEnv
    stBytes w.pre_pb w.vn w.pb w.st0 w.sckaMsg w.v
    w.xInit w.xNew w.xAdd w.xRk w.xSInto w.xCInto evs

/-- Path B Stage P3 `try_decrypt` envelope (`W2TryDecryptTightEnv` + linked `SpqrRecvC07TightLinkedEnv`). -/
def W4TryDecryptPathBEnv (F : ShaCompress) (K : MlKem) (td : W4TryDecryptCall F)
    (evs : List AllocEvent) : Prop :=
  W2TryDecryptTightEnv td.dhCap td.needGrow td.caps
    (W4SpqrLinkedStepEnv F K td.stBytes td.w)
    td.withAddr td.errAlloc td.ctLen evs

/-- Path A / Path C fresh-Bob (`maxSeeds = 12`, zero-skip) Stage P3 `try_decrypt` envelope. -/
def W4TryDecryptPathACEnv (F : ShaCompress) (K : MlKem) (td : W4TryDecryptCall F)
    (evs : List AllocEvent) : Prop :=
  W2TryDecryptSeedsEnv 12 td.dhCap td.needGrow td.caps
    (W4SpqrLinkedStepEnv F K td.stBytes td.w)
    td.withAddr td.errAlloc td.ctLen evs

/-- Failed-trial inner `W2TryDecryptFailTightEnv` at linked `SpqrRecvC07TightLinkedEnv`. -/
def W4TryDecryptFailLinkedEnv (F : ShaCompress) (K : MlKem) (td : W4TryDecryptCall F)
    (evs : List AllocEvent) : Prop :=
  W2TryDecryptFailTightEnv td.dhCap td.needGrow td.caps
    (W4SpqrLinkedStepEnv F K td.stBytes td.w)
    td.withAddr td.errAlloc td.ctLen evs

/-- Failed-trial `try_decrypt` + drop-cancellation envelope (`Δlive = 0`). -/
def W4FailedTdCancelEnv (F : ShaCompress) (K : MlKem) (fc : W4FailedTryDecryptCall F)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    ConcatEnv (W4TryDecryptFailLinkedEnv F K fc.td) (· = optDeallocListEvs fc.failDropPairs) evs

/-- Archived-trial `PrevDec` deserialization envelope (`SessDeserializeCancelEnv`). -/
def W4TrialDecEnv (F : ShaCompress) (x : W4ArchivedTrial F) (evs : List AllocEvent) : Prop :=
  SessDeserializeCancelEnv x.r_dec evs

/-- Archived-trial version-mismatch (`FreeOnlyEvs`) or cloned-session failed `try_decrypt_pq` envelope. -/
def W4TrialRunEnv (F : ShaCompress) (K : MlKem) (x : W4ArchivedTrial F)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    W4TryDecryptCloneFailEnv (SegCloneEnv x.G_tr x.ses_tr.state)
      (W4FailedTdCancelEnv F K x.fc_tr)
      (· = dropClonedSessionEvents x.G_tr x.ses_tr.state) evs

/-- Archived-trial deterministic `SessionStructure` drop envelope (`Block 6`). -/
def W4TrialDropEnv (F : ShaCompress) (x : W4ArchivedTrial F) (evs : List AllocEvent) : Prop :=
  evs = dropSessionStructureLocal1Events x.G_dec x.st_dec

/-- Concrete parameter bundle for the real W4 (`recv-prekey` / `decrypt_prekey`) CLI slot. -/
structure W4RecvPrekeyRealParams : Type where
  F : ShaCompress
  K : MlKem
  rd : ReadRule
  files : FsFiles
  kpkDir : DirGhost
  peer : AddrGhost
  hasOpk : Bool
  spkId : BitVec 32
  kpkId : BitVec 32
  opkId : BitVec 32
  kpkMarkName : List (BitVec 8)
  ownKeyName : List (BitVec 8)
  ownRegName : List (BitVec 8)
  x_res : DoReserveCall
  x_spqr : InitialStateGhost
  hasCurSession : Bool
  G_cur : SessionGhost
  st_cur : SessionState (List (BitVec 8))
  fc_cur : W4FailedTryDecryptCall F
  archivedTrials : List (W4ArchivedTrial F)
  isPathB : Bool
  td_B : W4TryDecryptCall F
  isPathAC : Bool
  td_AC : W4TryDecryptCall F
  g_arch : RecordGhost
  r_arch : SessionRecord (List (BitVec 8))
  g_out0 : RecordGhost
  r_out0 : SessionRecord (List (BitVec 8))
  G_out1 : SessionGhost
  sess_out1 : Session (List (BitVec 8))
  enc_prev1 : List (BitVec 8)

/-- Concrete `W4DecryptPrekeySlotParams` wired to `StoresGhost.opened` and `RecordDeserializeCancelEnv`. -/
def mkW4RecvPrekeySlotParams (R : W4RecvPrekeyRealParams) :
    W4DecryptPrekeySlotParams (W4ArchivedTrial R.F) where
  rd := R.rd
  DeserEnv := RecordDeserializeCancelEnv
  files := R.files
  ownDir := StoresGhost.opened.identity.own
  peersDir := StoresGhost.opened.identity.peers
  spkDir := StoresGhost.opened.signed
  kpkDir := R.kpkDir
  opkDir := StoresGhost.opened.oneTime
  sessDir := StoresGhost.opened.sessions
  peer := R.peer
  hasOpk := R.hasOpk
  spkId := R.spkId
  kpkId := R.kpkId
  opkId := R.opkId
  kpkMarkName := R.kpkMarkName
  ownKeyName := R.ownKeyName
  ownRegName := R.ownRegName
  F := R.F
  x_res := R.x_res
  x_spqr := R.x_spqr
  G_cur := R.G_cur
  st_cur := R.st_cur
  CurTrialFailEnv :=
    if R.hasCurSession then W4FailedTdCancelEnv R.F R.K R.fc_cur else fun _ => False
  DecEnv := W4TrialDecEnv R.F
  TrialEnv := W4TrialRunEnv R.F R.K
  DropEnv := W4TrialDropEnv R.F
  archivedTrials := R.archivedTrials
  g_arch := R.g_arch
  r_arch := R.r_arch
  VecPushEnv := W4BoundedEvs 1 192
  TryDecEnv :=
    if R.isPathB then W4TryDecryptPathBEnv R.F R.K R.td_B else fun _ => False
  g_out0 := R.g_out0
  r_out0 := R.r_out0
  G_out1 := R.G_out1
  sess_out1 := R.sess_out1
  enc_prev1 := R.enc_prev1

/-- Concrete Path A / Path C Stage P3 `try_decrypt` envelope for `R`. -/
def W4RecvPrekeyTryDecACEnv (R : W4RecvPrekeyRealParams) (evs : List AllocEvent) : Prop :=
  if R.isPathAC then W4TryDecryptPathACEnv R.F R.K R.td_AC evs else False

/-- Concrete `recv-prekey` / `decrypt_prekey` slot envelope (`W4DecryptPrekeySplitSlotEnv`). -/
def W4RecvPrekeyRealEnv (R : W4RecvPrekeyRealParams) (evs : List AllocEvent) : Prop :=
  W4DecryptPrekeySplitSlotEnv (mkW4RecvPrekeySlotParams R) (W4RecvPrekeyTryDecACEnv R) evs

/-! ## Witness-Free Domain Predicates -/

/-- Pure domain bounds for one `W4TryDecryptCall` (`dhCap ≤ 5`, `caps.length ≤ 12`,
`DoublingChainLe 2000`, `ctLen ≤ 65536`, and `TopStateTight F K stBytes`). -/
structure W4TryDecryptCallDom (F : ShaCompress) (K : MlKem) (td : W4TryDecryptCall F) : Prop where
  dh_le : td.dhCap ≤ 5
  caps_len : td.caps.length ≤ 12
  chain_le : DoublingChainLe 2000 td.caps
  top_tight : TopStateTight F K td.stBytes
  ct_le : td.ctLen ≤ 65536

/-- Domain bounds for a fresh-Bob Path A / Path C `try_decrypt` (`0` skipped keys). -/
structure W4TryDecryptPathACDom (F : ShaCompress) (K : MlKem) (td : W4TryDecryptCall F) : Prop where
  base : W4TryDecryptCallDom F K td
  zero_skip : ChainRecvKeyZeroSkip td.w.xRk

/-- Pure domain bounds for a failed `try_decrypt` trial with drop cancellation (`Δlive = 0`). -/
structure W4FailedTdDom (F : ShaCompress) (K : MlKem) (fc : W4FailedTryDecryptCall F) : Prop where
  td_dom : W4TryDecryptCallDom F K fc.td
  align_le : ∀ p ∈ fc.failDropPairs, p.2 ≤ 16
  cancel_live : w2CmkChainTightLive 2000 + 605066 ≤ optDeallocListLarge fineCostModel fc.failDropPairs

/-- Pure domain bounds for one archived-session trial (`PrevDec` + trial + `SessionStructure` drop). -/
structure W4ArchivedTrialDom (F : ShaCompress) (K : MlKem) (x : W4ArchivedTrial F) : Prop where
  enc_le : (encodeRecord x.r_dec).length ≤ deserCancelFineMaxReq
  live_le_peak : sessDeserLargeLive fineCostModel x.r_dec ≤ deserCancelFinePeak
  live_le_drop : sessDeserLargeLive fineCostModel x.r_dec ≤ ssStateLargeLive fineCostModel x.G_dec x.st_dec
  drop_caps : SessionDropCapsOk x.G_dec x.st_dec
  tr_gv : SessionGhostValid x.G_tr x.ses_tr
  tr_dom : SessionCloneDom 286196 x.ses_tr
  tr_fail : W4FailedTdDom F K x.fc_tr

/-- Pure witness-free domain bundle for `W4RecvPrekeyRealEnv R`. -/
structure W4RecvPrekeyRealDom (R : W4RecvPrekeyRealParams) : Prop where
  kpk_dir : R.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            R.kpkDir = StoresGhost.opened.kyber.lastResort
  outer_dom : W4DecryptPrekeyTightDom (mkW4RecvPrekeySlotParams R)
    2097152 4096 286196 286196 2097152 286196 2097152 16384 2097152 2457152 4096
  cur_fail_dom : R.hasCurSession = true → W4FailedTdDom R.F R.K R.fc_cur
  trials_dom : ∀ x ∈ R.archivedTrials, W4ArchivedTrialDom R.F R.K x
  tdB_dom : R.isPathB = true → W4TryDecryptCallDom R.F R.K R.td_B
  tdAC_dom : R.isPathAC = true → W4TryDecryptPathACDom R.F R.K R.td_AC

/-! ## Closed `Nat` Constants & Kernel `by decide` Cap Check -/

/-- Closed `c_cur = c_tdB` (`26,766,574` B) for `W2Seeds738` + `uncondHist` `spqr::recv`. -/
def w4RealFailTdCum : Nat := w2TryDecryptSeeds738Cum 5 true 12 23313687

/-- Closed `p_cur = p_tdB` (`1,264,538` B) for `uncondHist` `spqr::recv` + `maxOldCap = 2000`. -/
def w4RealFailTdPeak : Nat := w2TryDecryptTightPeak 2000 605066 621350 65536

/-- Closed `r_cur = r_tdB = r_tdAC` (`416,000` B) for `try_decrypt`. -/
def w4RealTdMaxReq : Nat := w2TryDecryptMaxReq 5 2000 302480 65536

/-- Closed `c_tr` (`35,052,216` B) for cloned-session failed trial. -/
def w4RealTrialCum : Nat := 8277456 + w4RealFailTdCum + 8186

/-- Closed `p_tr` (`2,640,425` B) for cloned-session failed trial. -/
def w4RealTrialPeak : Nat := 1080975 + fineOptLarge 286196 + w4RealFailTdPeak

/-- Closed `r_tr` (`416,000` B) for cloned-session failed trial. -/
def w4RealTrialMaxReq : Nat := max (max (max 208000 286196) w4RealTdMaxReq) 192

/-- Closed `c_tdAC` (`5,890,676` B) for fresh-Bob `try_decrypt` (`maxSeeds = 12`, `0` skipped keys). -/
def w4RealTdACCum : Nat := w2TryDecryptGenSeeds738Cum 12 5 true 12 3897904

/-- Closed `l_tdB` (`829,066` B). -/
def w4RealTdBLive : Nat := w2TryDecryptTightLive 2000 605066 65536

/-- Closed `l_tdAC` (`518,391` B). -/
def w4RealTdACLive : Nat := w2TryDecryptTightLive 2000 294391 65536

/-- Closed `p_tdAC` (`591,927` B). -/
def w4RealTdACPeak : Nat := w2TryDecryptTightPeak 2000 294391 294391 65536

/-- Concrete closed-`Nat` W4 (`recv-prekey`) `Δcum` bound. -/
def w4RecvPrekeyRealCum : Nat :=
  w4DecryptPrekeySplitTightCum 2097152 4096 0 deserCancelFineCum
    w4RealFailTdCum deserCancelFineCum w4RealTrialCum 9923
    w4RealFailTdCum w4RealTdACCum 4096

/-- Concrete closed-`Nat` W4 (`recv-prekey`) `Δlive` bound. -/
def w4RecvPrekeyRealLive : Nat :=
  w4DecryptPrekeySplitTightLive 2097152 4096 0 deserCancelFineLive
    2097152 2097152 2457152 w4RealTdBLive w4RealTdACLive

/-- Concrete closed-`Nat` W4 (`recv-prekey`) `Δpeak` bound. -/
def w4RecvPrekeyRealPeak : Nat :=
  w4DecryptPrekeySplitTightPeak 2097152 4096 0 deserCancelFineLive deserCancelFinePeak
    286196 286196 2097152 286196 2097152 16384 2097152 2457152
    w4RealFailTdPeak deserCancelFinePeak w4RealTrialPeak
    w4RealTdBLive w4RealFailTdPeak w4RealTdACLive w4RealTdACPeak

/-- Concrete closed-`Nat` W4 (`recv-prekey`) `maxReq` bound. -/
def w4RecvPrekeyRealMaxReq : Nat :=
  w4DecryptPrekeySplitTightMaxReq 2097152 4096 0 deserCancelFineMaxReq
    286196 286196 2097152 286196 2097152 16384 2097152 2457152
    w4RealTdMaxReq deserCancelFineMaxReq w4RealTrialMaxReq 192
    w4RealTdMaxReq w4RealTdMaxReq 4096

/-- Fresh-Bob (`receiverChains = []`) scaled group bound for `SegCloneEnv` (`1,803,209`). -/
def segCloneFreshBobFineGrpS : Nat :=
  senderChainCloneDomFineGrpS + 21 * FineScale

/-- Fresh-Bob (`receiverChains = []`) scaled group bound for `SerializePrev1CancelEnv` (`2,207,481`). -/
def serializePrev1FreshBobFineGrpS : Nat :=
  segCloneFreshBobFineGrpS + (11056 + 3 * FineScale) + 3 * FineScale

/-- Scaled group bound (`676,809,815`) for one `W4TrialRunEnv`. -/
def w4RealTrialFineGrpS : Nat :=
  segCloneDomFineGrpS + w2TryDecryptFailTightGroupS_split_12 + w4ErrTailFineGrpS

/-- Concrete closed-`Nat` W4 (`recv-prekey`) `grpS` bound across all 4 arms of
`W4DecryptPrekeySplitSlotEnv`. -/
def w4RecvPrekeyRealGrpS : Nat :=
  let gDeser := deserCancelFineGrpS
  let gCur := w2TryDecryptFailTightGroupS_split_12
  let gDec := deserCancelFineGrpS
  let gTr := w4RealTrialFineGrpS
  let gPush := 3 * FineScale
  let gArchSer := recordSerializeDomFineGrpS
  let gOut0Ser := recordSerializeDomFineGrpS
  let gOut1Ser := serializePrev1FreshBobFineGrpS
  let gTdB := w2TryDecryptTightGroupS_split_12
  let gTdAC := w2TryDecryptSeeds12GroupS_split_12
  let gU := w4StageP1UntrustedBaseFineGrpS + gDeser
  let gB := (w4StageP1OkBaseFineGrpS + gDeser) +
    (4 * (gDec + gTr) + gArchSer + gPush) +
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
      gCur + 4 * (gDec + gTr) + gPush) +
    w4StageP3FineGrpS gTdAC +
    (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
      (16659 + (6 * FineScale + gOut1Ser)))
  max (max gU gB) (max gA gC)

/-- All 5 `cliRecvPrekeySlot*Cap` inequalities and `live ≤ peak` hold on closed `Nat`s by `decide`. -/
theorem w4RecvPrekeyReal_caps_le :
    w4RecvPrekeyRealLive ≤ w4RecvPrekeyRealPeak ∧
    w4RecvPrekeyRealCum ≤ cliRecvPrekeySlotCumCap ∧
    w4RecvPrekeyRealLive ≤ cliRecvPrekeySlotLiveCap ∧
    w4RecvPrekeyRealPeak ≤ cliRecvPrekeySlotPeakCap ∧
    w4RecvPrekeyRealMaxReq ≤ cliRecvPrekeySlotReqCap ∧
    w4RecvPrekeyRealGrpS ≤ cliRecvPrekeySlotGrpSCap :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## Finite-Case Monotonicity, Drop-Glue `DeallocCreditSpec`, & Linked Credit Lemmas -/

private theorem dhSmall_of_le_5 {dhCap : Nat} (h : dhCap ≤ 5) :
    104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
  rw [fineCostModel_smallMaxReq_eq]
  match dhCap, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => decide

private theorem w2Seeds738Cum_le_5 {dhCap : Nat} (needGrow : Bool) (h : dhCap ≤ 5) :
    w2TryDecryptSeeds738Cum dhCap needGrow 12 23313687 ≤ w4RealFailTdCum := by
  unfold w4RealFailTdCum
  match dhCap, needGrow, h with
  | 0, false, _ | 0, true, _ | 1, false, _ | 1, true, _
  | 2, false, _ | 2, true, _ | 3, false, _ | 3, true, _
  | 4, false, _ | 4, true, _ | 5, false, _ | 5, true, _ => decide

private theorem w2GenSeeds12Cum_le_5 {dhCap : Nat} (needGrow : Bool) (h : dhCap ≤ 5) :
    w2TryDecryptGenSeeds738Cum 12 dhCap needGrow 12 3897904 ≤ w4RealTdACCum := by
  unfold w4RealTdACCum
  match dhCap, needGrow, h with
  | 0, false, _ | 0, true, _ | 1, false, _ | 1, true, _
  | 2, false, _ | 2, true, _ | 3, false, _ | 3, true, _
  | 4, false, _ | 4, true, _ | 5, false, _ | 5, true, _ => decide

private theorem w2MaxReq_le_5 {dhCap : Nat} (h : dhCap ≤ 5) :
    w2TryDecryptMaxReq dhCap 2000 302480 65536 ≤ w4RealTdMaxReq := by
  unfold w4RealTdMaxReq
  match dhCap, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => decide

private theorem deallocCreditSpec_mono_le {M : AllocCostModel} [HasFineReallocCredit M]
    {E : List AllocEvent → Prop} {d₁ d₂ : Nat}
    (h : DeallocCreditSpec M E d₂) (hd : d₁ ≤ d₂) :
    DeallocCreditSpec M E d₁ where
  req_align := h.req_align
  credit_sub st0 {_} hE := by
    obtain ⟨hc, hl, hp⟩ := h.credit_sub st0 hE
    exact ⟨hc, Nat.le_trans hl (Nat.sub_le_sub_left hd _), hp⟩

private theorem pinFreeEvents_freeOnlyAlign16 (pin : VecPin) :
    FreeOnlyAlign16Evs (pinFreeEvents pin) := by
  unfold pinFreeEvents
  split
  · exact FreeOnlyAlign16Evs.nil
  · exact FreeOnlyAlign16Evs.rustDealloc (by decide) pin.cap.toNat

private theorem sgnCapFreeEvents_freeOnlyAlign16 (cap : BitVec 64) :
    FreeOnlyAlign16Evs (sgnCapFreeEvents cap) := by
  unfold sgnCapFreeEvents
  split
  · exact FreeOnlyAlign16Evs.nil
  · exact FreeOnlyAlign16Evs.rustDealloc (by decide) cap.toNat

private theorem vec104FreeEvents_freeOnlyAlign16 (cap : BitVec 64) :
    FreeOnlyAlign16Evs (vec104FreeEvents cap) := by
  unfold vec104FreeEvents
  split
  · exact FreeOnlyAlign16Evs.nil
  · exact FreeOnlyAlign16Evs.rustDealloc (by decide) (cap.toNat * 104)

private theorem mkFreeEvents_freeOnlyAlign16 (mk : MessageKeyGhost) :
    FreeOnlyAlign16Evs (mkFreeEvents mk) := by
  unfold mkFreeEvents
  exact FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (FreeOnlyAlign16Evs.append
        (pinFreeEvents_freeOnlyAlign16 mk.cipher)
        (pinFreeEvents_freeOnlyAlign16 mk.mac))
      (pinFreeEvents_freeOnlyAlign16 mk.iv))
    (pinFreeEvents_freeOnlyAlign16 mk.seed)

private theorem mkListFreeEvents_freeOnlyAlign16
    (mks : List (MessageKeyGhost × MessageKeyGenerator)) :
    FreeOnlyAlign16Evs (mks.flatMap fun gk => mkFreeEvents gk.1) := by
  induction mks with
  | nil =>
    simp only [List.flatMap_nil]
    exact FreeOnlyAlign16Evs.nil
  | cons gk tl ih =>
    simp only [List.flatMap_cons]
    intro ev hev
    rcases List.mem_append.mp hev with h1 | h2
    · exact mkFreeEvents_freeOnlyAlign16 gk.1 ev h1
    · exact ih ev h2

private theorem dropVecMessageKeyEvents_freeOnlyAlign16 (cap : BitVec 64)
    (mks : List (MessageKeyGhost × MessageKeyGenerator)) :
    FreeOnlyAlign16Evs (dropVecMessageKeyEvents cap mks) := by
  intro ev hev
  dsimp only [dropVecMessageKeyEvents] at hev
  rcases List.mem_append.mp hev with h1 | h2
  · exact mkListFreeEvents_freeOnlyAlign16 mks ev h1
  · exact vec104FreeEvents_freeOnlyAlign16 cap ev h2

private theorem chainPairFreeEvents_freeOnlyAlign16 (gc : ChainGhost × ReceiverChain) :
    FreeOnlyAlign16Evs (chainPairFreeEvents gc) := by
  unfold chainPairFreeEvents
  exact FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (FreeOnlyAlign16Evs.append
        (pinFreeEvents_freeOnlyAlign16 ⟨gc.1.srk.cap, gc.1.srk.ptr⟩)
        (pinFreeEvents_freeOnlyAlign16 ⟨gc.1.priv.cap, gc.1.priv.ptr⟩))
      (sgnCapFreeEvents_freeOnlyAlign16 (optCkCapVal gc.1.ck gc.2.chainKey)))
    (dropVecMessageKeyEvents_freeOnlyAlign16 gc.1.mkCap (gc.1.keys.zip gc.2.messageKeys))

private theorem chainListFreeEvents_freeOnlyAlign16
    (cs : List (ChainGhost × ReceiverChain)) :
    FreeOnlyAlign16Evs (cs.flatMap chainPairFreeEvents) := by
  induction cs with
  | nil =>
    simp only [List.flatMap_nil]
    exact FreeOnlyAlign16Evs.nil
  | cons gc tl ih =>
    simp only [List.flatMap_cons]
    intro ev hev
    rcases List.mem_append.mp hev with h1 | h2
    · exact chainPairFreeEvents_freeOnlyAlign16 gc ev h1
    · exact ih ev h2

private theorem dropSessionStructureLocal1Events_freeOnlyAlign16
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    FreeOnlyAlign16Evs (dropSessionStructureLocal1Events G st) := by
  unfold dropSessionStructureLocal1Events ssFirst3FreeEvents ssTail3FreeEvents dropVecChainEvents
  have h1 : FreeOnlyAlign16Evs
      (pinFreeEvents ⟨G.localIk.cap, G.localIk.ptr⟩ ++
        pinFreeEvents ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ++
        pinFreeEvents G.root) :=
    FreeOnlyAlign16Evs.append
      (FreeOnlyAlign16Evs.append
        (pinFreeEvents_freeOnlyAlign16 ⟨G.localIk.cap, G.localIk.ptr⟩)
        (pinFreeEvents_freeOnlyAlign16 ⟨G.remoteIk.cap, G.remoteIk.ptr⟩))
      (pinFreeEvents_freeOnlyAlign16 G.root)
  have h2 : FreeOnlyAlign16Evs (senderFreeEvents G.sender) := by
    cases G.sender with
    | none => exact FreeOnlyAlign16Evs.nil
    | some sg =>
      unfold senderFreeEvents
      exact FreeOnlyAlign16Evs.append
        (FreeOnlyAlign16Evs.append
          (FreeOnlyAlign16Evs.append
            (pinFreeEvents_freeOnlyAlign16 ⟨sg.srk.cap, sg.srk.ptr⟩)
            (pinFreeEvents_freeOnlyAlign16 ⟨sg.priv.cap, sg.priv.ptr⟩))
          (sgnCapFreeEvents_freeOnlyAlign16 sg.ck.cap))
        (dropVecMessageKeyEvents_freeOnlyAlign16 sg.mkCap [])
  have h3 : FreeOnlyAlign16Evs
      (((G.chains.zip st.receiverChains).flatMap chainPairFreeEvents) ++
        vec104FreeEvents G.chainsCap) := by
    intro ev hev
    rcases List.mem_append.mp hev with h3a | h3b
    · exact chainListFreeEvents_freeOnlyAlign16 (G.chains.zip st.receiverChains) ev h3a
    · exact vec104FreeEvents_freeOnlyAlign16 G.chainsCap ev h3b
  have h4 : FreeOnlyAlign16Evs
      (sgnCapFreeEvents (optTailCapVal G.pending) ++
        sgnCapFreeEvents (optTailCapVal G.kyber) ++
        pinFreeEvents ⟨G.alice.cap, G.alice.ptr⟩) :=
    FreeOnlyAlign16Evs.append
      (FreeOnlyAlign16Evs.append
        (sgnCapFreeEvents_freeOnlyAlign16 (optTailCapVal G.pending))
        (sgnCapFreeEvents_freeOnlyAlign16 (optTailCapVal G.kyber)))
      (pinFreeEvents_freeOnlyAlign16 ⟨G.alice.cap, G.alice.ptr⟩)
  exact FreeOnlyAlign16Evs.append
    (FreeOnlyAlign16Evs.append
      (FreeOnlyAlign16Evs.append (FreeOnlyAlign16Evs.append h1 h2) h3) h4)
    (pinFreeEvents_freeOnlyAlign16 G.pq)

private theorem deallocCreditSpec_dropSessionStructureLocal1
    {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    (hok : SessionDropCapsOk G st) :
    DeallocCreditSpec fineCostModel
      (· = dropSessionStructureLocal1Events G st)
      (ssStateLargeLive fineCostModel G st) where
  req_align := by
    rintro _ rfl ev hev
    exact (PhaseCreditSpec.freeOnly_align16 fineCostModel).req_align _
      (dropSessionStructureLocal1Events_freeOnlyAlign16 G st) ev hev
  credit_sub := by
    rintro st0 _ rfl
    exact stepEvents_dropSessionStructureLocal1_bounds fineCostModel hok st0

private theorem optDeallocListEvs_freeOnly (pairs : List (Nat × Nat)) :
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

/-- Linked zero-skip (`ChainRecvKeyZeroSkip`) `spqr::recv` `PhaseCreditSpec`, deriving
`SpqrRecvTightDomain` internally from `TopStateTight` (`Δcum = 3,897,904`, `Δlive = 294,391`,
`Δpeak = 294,391`, `maxReq = 302,480`). -/
theorem spqrRecvLinked_zeroSkip_c09a_phaseCreditSpec
    (F : ShaCompress) (K : MlKem) (stBytes : Bytes) (w : SpqrRecvC07Witness F)
    (hTop : TopStateTight F K stBytes)
    (hZero : ChainRecvKeyZeroSkip w.xRk) :
    PhaseCreditSpec fineCostModel (W4SpqrLinkedStepEnv F K stBytes w)
      3897904 294391 294391 302480 where
  req_align evs hEnv ev hev := by
    obtain ⟨hTight, hLink⟩ := hEnv
    have hDom := spqrRecvTightDomain_of_topStateTight_and_link hTop hLink
    have hr : max 93776 286196 ≤ 302480 := by decide
    have hSpec : PhaseCreditSpec fineCostModel _ 3897904 294391 294391 302480 :=
      PhaseCreditSpec.mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hr
        (spqrRecvParts_c07_zeroSkip_c09a_phaseCreditSpec_tight F K
          (c09aStatesRecvTightCreditSpec_inst F)
          stBytes w.pre_pb w.vn w.pb w.st0 w.sckaMsg w.v
          w.xInit w.xNew w.xAdd w.xRk w.xSInto w.xCInto hDom hZero)
    exact hSpec.req_align evs hTight ev hev
  credit_le st_m {_} hEnv := by
    obtain ⟨hTight, hLink⟩ := hEnv
    have hDom := spqrRecvTightDomain_of_topStateTight_and_link hTop hLink
    have hr : max 93776 286196 ≤ 302480 := by decide
    have hSpec : PhaseCreditSpec fineCostModel _ 3897904 294391 294391 302480 :=
      PhaseCreditSpec.mono (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) hr
        (spqrRecvParts_c07_zeroSkip_c09a_phaseCreditSpec_tight F K
          (c09aStatesRecvTightCreditSpec_inst F)
          stBytes w.pre_pb w.vn w.pb w.st0 w.sckaMsg w.v
          w.xInit w.xNew w.xAdd w.xRk w.xSInto w.xCInto hDom hZero)
    exact hSpec.credit_le st_m hTight

private theorem w4TryDecryptPathB_phaseCredit
    {F : ShaCompress} {K : MlKem} {td : W4TryDecryptCall F}
    (hDom : W4TryDecryptCallDom F K td) :
    PhaseCreditSpec fineCostModel (W4TryDecryptPathBEnv F K td)
      w4RealFailTdCum w4RealTdBLive w4RealFailTdPeak w4RealTdMaxReq := by
  have hBase := w2TryDecrypt_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738 F K
    (needGrow := td.needGrow) (withAddr := td.withAddr) (errAlloc := td.errAlloc)
    td.stBytes td.w.pre_pb td.w.vn td.w.pb td.w.st0 td.w.sckaMsg td.w.v
    td.w.xInit td.w.xNew td.w.xAdd td.w.xRk td.w.xSInto td.w.xCInto
    (dhSmall_of_le_5 hDom.dh_le) hDom.caps_len hDom.chain_le hDom.top_tight hDom.ct_le
  exact hBase.mono
    (w2Seeds738Cum_le_5 td.needGrow hDom.dh_le)
    (Nat.le_refl _)
    (Nat.le_refl _)
    (w2MaxReq_le_5 hDom.dh_le)

private theorem w4TryDecryptPathAC_phaseCredit
    {F : ShaCompress} {K : MlKem} {td : W4TryDecryptCall F}
    (hDom : W4TryDecryptPathACDom F K td) :
    PhaseCreditSpec fineCostModel (W4TryDecryptPathACEnv F K td)
      w4RealTdACCum w4RealTdACLive w4RealTdACPeak w4RealTdMaxReq := by
  have hBase := w2TryDecrypt_genSeeds_fine_phaseCreditSpec (maxSeeds := 12)
    (needGrow := td.needGrow) (withAddr := td.withAddr) (errAlloc := td.errAlloc)
    (dhSmall_of_le_5 hDom.base.dh_le) hDom.base.caps_len hDom.base.chain_le
    (spqrRecvLinked_zeroSkip_c09a_phaseCreditSpec F K td.stBytes td.w
      hDom.base.top_tight hDom.zero_skip)
    hDom.base.ct_le
  exact hBase.mono
    (w2GenSeeds12Cum_le_5 td.needGrow hDom.base.dh_le)
    (Nat.le_refl _)
    (Nat.le_refl _)
    (w2MaxReq_le_5 hDom.base.dh_le)

private theorem w4FailedTdCancel_phaseCredit
    {F : ShaCompress} {K : MlKem} {fc : W4FailedTryDecryptCall F}
    (hDom : W4FailedTdDom F K fc) :
    PhaseCreditSpec fineCostModel (W4FailedTdCancelEnv F K fc)
      w4RealFailTdCum 0 w4RealFailTdPeak w4RealTdMaxReq := by
  have hTd0 : PhaseCreditSpec fineCostModel (W4TryDecryptFailLinkedEnv F K fc.td) _ _ _ _ :=
    w2TryDecryptFail_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738 F K
      (needGrow := fc.td.needGrow) (withAddr := fc.td.withAddr) (errAlloc := fc.td.errAlloc)
      fc.td.stBytes fc.td.w.pre_pb fc.td.w.vn fc.td.w.pb fc.td.w.st0 fc.td.w.sckaMsg fc.td.w.v
      fc.td.w.xInit fc.td.w.xNew fc.td.w.xAdd fc.td.w.xRk fc.td.w.xSInto fc.td.w.xCInto
      (dhSmall_of_le_5 hDom.td_dom.dh_le) hDom.td_dom.caps_len hDom.td_dom.chain_le
      hDom.td_dom.top_tight hDom.td_dom.ct_le
  have hTd := hTd0.mono
    (w2Seeds738Cum_le_5 fc.td.needGrow hDom.td_dom.dh_le)
    (Nat.le_of_eq (Nat.zero_add _).symm)
    (Nat.le_refl _)
    (w2MaxReq_le_5 hDom.td_dom.dh_le)
  have hDrop := deallocCreditSpec_mono_le
    (LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak.DeallocCreditSpec.optDeallocList
      fineCostModel fc.failDropPairs hDom.align_le)
    hDom.cancel_live
  have hCancel := hTd.concat_dealloc_cancel hDrop
  exact ((PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).or hCancel).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem w4TrialDec_phaseCredit
    {F : ShaCompress} {K : MlKem} {x : W4ArchivedTrial F}
    (hDom : W4ArchivedTrialDom F K x) :
    PhaseCreditSpec fineCostModel (W4TrialDecEnv F x)
      deserCancelFineCum (sessDeserLargeLive fineCostModel x.r_dec)
      deserCancelFinePeak deserCancelFineMaxReq := by
  have h33 : 33 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hmaxR : max 212992 (encodeRecord x.r_dec).length ≤ deserCancelFineMaxReq :=
    Nat.max_le.mpr ⟨by decide, hDom.enc_le⟩
  have hSym := sessDeserializeCancelEnv_phaseCreditSpec fineCostModel h33 hmaxR
  have hCl := sessDeserializeCancelEnv_fine_phaseCreditSpec hDom.enc_le
  exact
    { req_align := hCl.req_align
      credit_le := fun st0 {_} hE => by
        obtain ⟨hc, _, hp⟩ := hCl.credit_le st0 hE
        obtain ⟨_, hl, _⟩ := hSym.credit_le st0 hE
        exact ⟨hc, hl, hp⟩ }

private theorem w4TrialRun_phaseCredit
    {F : ShaCompress} {K : MlKem} {x : W4ArchivedTrial F}
    (hDom : W4ArchivedTrialDom F K x) :
    PhaseCreditSpec fineCostModel (W4TrialRunEnv F K x)
      w4RealTrialCum 0 w4RealTrialPeak w4RealTrialMaxReq := by
  have hCloneFail := tryDecryptCloneFail_dom_fine_cancel_phaseCredit
    (curPqCap := 286196)
    (Or.inr ⟨x.ses_tr, rfl, hDom.tr_gv, hDom.tr_dom⟩)
    (w4FailedTdCancel_phaseCredit hDom.tr_fail)
  exact ((PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).or hCloneFail).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

/-! ## Fresh-Bob `SerializePrev1CancelEnv` & Split-Slot `PhaseGroupSpec` Lemmas -/

private theorem segCloneEnv_freshBob_fine_groupSpec
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
           | some gs, some sc =>
             LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget.senderChainCloneEvents gs sc
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
             (G.chains.zip ses.state.receiverChains).flatMap
               LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget.chainCloneEvents)
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

private theorem serializePrev1CancelEnv_freshBob_fine_groupSpec
    {bobPqCap prevEncCap totalPrev1Cap : Nat}
    {G : SessionGhost} {ses : Session (List (BitVec 8))} {enc : List (BitVec 8)}
    (hbob : FreshBobPrev1Dom bobPqCap prevEncCap totalPrev1Cap G ses enc) :
    PhaseGroupSpec fineCostModel (SerializePrev1CancelEnv G ses enc)
      serializePrev1FreshBobFineGrpS := by
  unfold SerializePrev1CancelEnv serializePrev1FreshBobFineGrpS
  have hcl := segCloneEnv_freshBob_fine_groupSpec hbob
  have hvv := vecVecClone1Events_fine_groupSpec enc
  have hout := PhaseGroupSpec.rustAlloc_any fineCostModel (encodeRecordPrev1Mem G ses enc).length 1
  have hd1 := dropClonedSessionEvents_groupSpec fineCostModel G ses.state
  have hd2 := dropVecVecClone1Events_groupSpec fineCostModel enc
  exact (((hcl.concat hvv).concat hout).concat (hd1.concat hd2)).mono (by decide)

private theorem recordSerializeCancelEnv_of_valid_fine_groupSpec {pqCap : Nat}
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

private theorem w4FailedTdCancel_fine_groupSpec
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
      exact optDeallocListEvs_freeOnly fc.failDropPairs
  have hCat := (hFail.concat hDrop).mono (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hCat).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

private theorem p2c_grp_reassoc (gCl gCur gErr gLoop s16 gSer gPush gBob : Nat) :
    (gCl + gCur + gErr) +
      (gLoop + (s16 + (s16 + (s16 + (s16 + ((gSer + gPush + gBob) + (s16 + gErr))))))) ≤
      (gCl + gErr + 5 * s16 + gSer + gBob + gErr) + gCur + gLoop + gPush := by
  omega

private theorem four_stages_grp_reassoc (a b c d : Nat) :
    a + (b + (c + d)) ≤ a + b + c + d := by
  omega

private theorem w4StageP2PathCCli_curDom_fine_groupSpec {α : Type} {pqCap : Nat}
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
        { groups_le := fun _ {evs} hE => by
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
    (p2c_grp_reassoc segCloneDomFineGrpS g_cur w4ErrTailFineGrpS (4 * (g_dec + g_tr))
      w4SmallStoreStep16FineGrpS g_archSer g_push w4InitBobSpqrFineGrpS)

theorem w4RecvPrekeyReal_fine_groupSpec
    (R : W4RecvPrekeyRealParams) (hDom : W4RecvPrekeyRealDom R) :
    PhaseGroupSpec fineCostModel (W4RecvPrekeyRealEnv R) w4RecvPrekeyRealGrpS := by
  let P := mkW4RecvPrekeySlotParams R
  let TryDecAC := W4RecvPrekeyTryDecACEnv R
  have hDeser : ∀ bs : List (BitVec 8), bs.length ≤ 2097152 →
      PhaseGroupSpec fineCostModel (P.DeserEnv bs) deserCancelFineGrpS :=
    fun bs _ => recordDeserializeCancelEnv_fine_groupSpec bs
  have hCur : PhaseGroupSpec fineCostModel P.CurTrialFailEnv w2TryDecryptFailTightGroupS_split_12 := by
    change PhaseGroupSpec fineCostModel
      (if R.hasCurSession then W4FailedTdCancelEnv R.F R.K R.fc_cur else fun _ => False) _
    cases hcs : R.hasCurSession
    · exact { groups_le := fun _ {_} h => False.elim h }
    · exact w4FailedTdCancel_fine_groupSpec (hDom.cur_fail_dom hcs)
  have hDec : ∀ x ∈ P.archivedTrials,
      PhaseGroupSpec fineCostModel (P.DecEnv x) deserCancelFineGrpS :=
    fun x _ => sessDeserializeCancelEnv_fine_groupSpec x.r_dec
  have hTr : ∀ x ∈ P.archivedTrials,
      PhaseGroupSpec fineCostModel (P.TrialEnv x) w4RealTrialFineGrpS := by
    intro x hx
    have hxd := hDom.trials_dom x hx
    have hcf := w4TryDecryptCloneFail_fine_groupSpec
      (segCloneEnv_dom_fine_groupSpec hxd.tr_gv hxd.tr_dom)
      (w4FailedTdCancel_fine_groupSpec hxd.tr_fail)
      (dropClonedSessionEvents_groupSpec fineCostModel x.G_tr x.ses_tr.state)
    exact ((PhaseGroupSpec.freeOnly fineCostModel).or hcf).mono
      (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
  have hDrop : ∀ x ∈ P.archivedTrials, PhaseGroupSpec fineCostModel (P.DropEnv x) 0 := by
    intro x _
    exact (PhaseGroupSpec.freeOnly fineCostModel).of_imp fun _ h => by
      subst h
      exact FreeOnlyAlign16Evs.toFreeOnlyEvs
        (dropSessionStructureLocal1Events_freeOnlyAlign16 x.G_dec x.st_dec)
  have hPush : PhaseGroupSpec fineCostModel P.VecPushEnv (3 * FineScale) := by
    change PhaseGroupSpec fineCostModel (W4BoundedEvs 1 192) (3 * FineScale)
    simpa [Nat.one_mul] using w4BoundedEvs_groupSpec fineCostModel 1 192
  have hArchSer : PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv P.g_arch P.r_arch)
      recordSerializeDomFineGrpS :=
    recordSerializeCancelEnv_of_valid_fine_groupSpec hDom.outer_dom.arch_valid
  have hOut0Ser : PhaseGroupSpec fineCostModel (RecordSerializeCancelEnv P.g_out0 P.r_out0)
      recordSerializeDomFineGrpS :=
    recordSerializeCancelEnv_of_valid_fine_groupSpec hDom.outer_dom.out0_valid
  have hOut1Ser : PhaseGroupSpec fineCostModel
      (SerializePrev1CancelEnv P.G_out1 P.sess_out1 P.enc_prev1)
      serializePrev1FreshBobFineGrpS :=
    serializePrev1CancelEnv_freshBob_fine_groupSpec hDom.outer_dom.out1_freshBob
  have hTdB : PhaseGroupSpec fineCostModel P.TryDecEnv w2TryDecryptTightGroupS_split_12 := by
    change PhaseGroupSpec fineCostModel
      (if R.isPathB then W4TryDecryptPathBEnv R.F R.K R.td_B else fun _ => False) _
    cases hpb : R.isPathB
    · exact { groups_le := fun _ {_} h => False.elim h }
    · have hd := hDom.tdB_dom hpb
      exact w2TryDecryptTightEnv_linked_fine_groupSpec_split_12 R.F R.K
        R.td_B.dhCap R.td_B.needGrow R.td_B.withAddr R.td_B.errAlloc R.td_B.ctLen
        R.td_B.stBytes R.td_B.w.pre_pb R.td_B.w.vn R.td_B.w.pb R.td_B.w.st0
        R.td_B.w.sckaMsg R.td_B.w.v R.td_B.w.xInit R.td_B.w.xNew R.td_B.w.xAdd
        R.td_B.w.xRk R.td_B.w.xSInto R.td_B.w.xCInto hd.caps_len hd.top_tight
  have hTdAC : PhaseGroupSpec fineCostModel TryDecAC w2TryDecryptSeeds12GroupS_split_12 := by
    unfold TryDecAC W4RecvPrekeyTryDecACEnv
    cases hpac : R.isPathAC
    · exact { groups_le := fun _ {_} h => False.elim h }
    · have hd := (hDom.tdAC_dom hpac).base
      exact w2TryDecryptSeedsEnv_12_linked_fine_groupSpec_split_12 R.F R.K
        R.td_AC.dhCap R.td_AC.needGrow R.td_AC.withAddr R.td_AC.errAlloc R.td_AC.ctLen
        R.td_AC.stBytes R.td_AC.w.pre_pb R.td_AC.w.vn R.td_AC.w.pb R.td_AC.w.st0
        R.td_AC.w.sckaMsg R.td_AC.w.v R.td_AC.w.xInit R.td_AC.w.xNew R.td_AC.w.xAdd
        R.td_AC.w.xRk R.td_AC.w.xSInto R.td_AC.w.xCInto hd.caps_len hd.top_tight
  have hP1 := w4StageP1OkCli_fine_groupSpec P.rd P.files P.sessDir P.peersDir P.peer hDeser
  let gU := w4StageP1UntrustedBaseFineGrpS + deserCancelFineGrpS
  let gB := (w4StageP1OkBaseFineGrpS + deserCancelFineGrpS) +
    (4 * (deserCancelFineGrpS + w4RealTrialFineGrpS) + recordSerializeDomFineGrpS + 3 * FineScale) +
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
      4 * (deserCancelFineGrpS + w4RealTrialFineGrpS) + 3 * FineScale) +
    w4StageP3FineGrpS w2TryDecryptSeeds12GroupS_split_12 +
    (2 * w4SmallStoreStep32FineGrpS + w4SmallStoreStep16FineGrpS +
      (16659 + (6 * FineScale + serializePrev1FreshBobFineGrpS)))
  have hLeU : gU ≤ w4RecvPrekeyRealGrpS :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hLeB : gB ≤ w4RecvPrekeyRealGrpS :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hLeA : gA ≤ w4RecvPrekeyRealGrpS :=
    Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hLeC : gC ≤ w4RecvPrekeyRealGrpS :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hArms : PhaseGroupSpec fineCostModel
      (fun e =>
        W4StageP1UntrustedCliEnv P.rd P.DeserEnv P.files P.sessDir P.peersDir P.peer e ∨
        W4DecryptPrekeyPathBEnv P e ∨
        W4DecryptPrekeyPathAEnv ({ P with TryDecEnv := TryDecAC }) e ∨
        W4DecryptPrekeyPathCEnv ({ P with TryDecEnv := TryDecAC }) e)
      w4RecvPrekeyRealGrpS :=
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
            (four_stages_grp_reassoc _ _ _ _)).mono hLeB).groups_le st0 hB
        · have hp2 := w4StageP2PathACli_fine_groupSpec P.hasOpk P.rd P.files
            P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
            P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr
          have hp3 := w4StageP3_fine_groupSpec hTdAC
          have hp4 := w4StageP4PathACli_fine_groupSpec P.hasOpk P.rd P.files
            P.peersDir P.kpkDir P.opkDir P.sessDir P.peer P.kpkMarkName P.opkId hOut0Ser
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (four_stages_grp_reassoc _ _ _ _)).mono hLeA).groups_le st0 hA
        · have hp2 := w4StageP2PathCCli_curDom_fine_groupSpec P.hasOpk P.rd P.files
            P.spkDir P.kpkDir P.opkDir P.ownDir P.spkId P.kpkId P.opkId
            P.ownKeyName P.ownRegName P.F P.x_res P.x_spqr
            hDom.outer_dom.cur_dom hCur hDom.outer_dom.trials_len4
            hDec hTr hDrop hArchSer hPush
          have hp3 := w4StageP3_fine_groupSpec hTdAC
          have hp4 := w4StageP4PathCCli_fine_groupSpec P.hasOpk P.rd P.files
            P.peersDir P.kpkDir P.opkDir P.sessDir P.peer P.kpkMarkName P.opkId hOut1Ser
          exact (((hP1.seq (hp2.seq (hp3.seq hp4))).mono
            (four_stages_grp_reassoc _ _ _ _)).mono hLeC).groups_le st0 hC }
  have hSeq := (hArms.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono
    (Nat.le_of_eq (Nat.add_zero _))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hSeq).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

/-! ## Witness-Free `SingleSlotFineSpec` & Allocating Non-Vacuity -/

/-- Witness-free `PhaseCreditSpec fineCostModel` for `W4RecvPrekeyRealEnv R`. -/
theorem w4RecvPrekeyReal_phaseCreditSpec
    (R : W4RecvPrekeyRealParams) (hDom : W4RecvPrekeyRealDom R) :
    PhaseCreditSpec fineCostModel (W4RecvPrekeyRealEnv R)
      w4RecvPrekeyRealCum w4RecvPrekeyRealLive w4RecvPrekeyRealPeak w4RecvPrekeyRealMaxReq := by
  let P := mkW4RecvPrekeySlotParams R
  have hCur : PhaseCreditSpec fineCostModel P.CurTrialFailEnv
      w4RealFailTdCum 0 w4RealFailTdPeak w4RealTdMaxReq := by
    change PhaseCreditSpec fineCostModel
      (if R.hasCurSession then W4FailedTdCancelEnv R.F R.K R.fc_cur else fun _ => False)
      _ _ _ _
    cases hcs : R.hasCurSession
    · exact (PhaseCreditSpec.empty fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact w4FailedTdCancel_phaseCredit (hDom.cur_fail_dom hcs)
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
    · exact w4TryDecryptPathB_phaseCredit (hDom.tdB_dom hpb)
  have hTdAC : PhaseCreditSpec fineCostModel (W4RecvPrekeyTryDecACEnv R)
      w4RealTdACCum w4RealTdACLive w4RealTdACPeak w4RealTdMaxReq := by
    unfold W4RecvPrekeyTryDecACEnv
    cases hpac : R.isPathAC
    · exact (PhaseCreditSpec.empty fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    · exact w4TryDecryptPathAC_phaseCredit (hDom.tdAC_dom hpac)
  exact w4DecryptPrekeySplitSlot_opened_fine_phaseCredit P
    (l_dec := fun x => sessDeserLargeLive fineCostModel x.r_dec)
    rfl rfl rfl hDom.kpk_dir rfl rfl hDom.outer_dom
    (fun _ hbs => recordDeserializeCancelEnv_fine_phaseCreditSpec hbs)
    hCur
    (fun x hx => (hDom.trials_dom x hx).live_le_peak)
    (fun x hx => w4TrialDec_phaseCredit (hDom.trials_dom x hx))
    (fun x hx => w4TrialRun_phaseCredit (hDom.trials_dom x hx))
    (fun x hx => deallocCreditSpec_mono_le
      (deallocCreditSpec_dropSessionStructureLocal1 (hDom.trials_dom x hx).drop_caps)
      (hDom.trials_dom x hx).live_le_drop)
    hPush hTdB hTdAC

/-- Witness-free `SingleSlotFineSpec` for the real W4 (`recv-prekey` / `decrypt_prekey`) slot,
with zero `PhaseCreditSpec` / `PhaseGroupSpec` / `DeallocCreditSpec` binders and zero
`SpqrRecvTightDomain` in exported types. -/
def w4RecvPrekeyReal_singleSlotFineSpec
    (R : W4RecvPrekeyRealParams) (hDom : W4RecvPrekeyRealDom R) :
    SingleSlotFineSpec (W4RecvPrekeyRealEnv R) where
  cum := w4RecvPrekeyRealCum
  live := w4RecvPrekeyRealLive
  peak := w4RecvPrekeyRealPeak
  maxReq := w4RecvPrekeyRealMaxReq
  grpS := w4RecvPrekeyRealGrpS
  credit := w4RecvPrekeyReal_phaseCreditSpec R hDom
  live_le_peak := w4RecvPrekeyReal_caps_le.1
  groups := w4RecvPrekeyReal_fine_groupSpec R hDom

/-- Concrete allocating non-vacuity witness (`evs = rustAllocEvents 24 8 = [.aligned 8 24] ≠ []`)
for `W4RecvPrekeyRealEnv R` across every parameter bundle `R`. -/
theorem w4RecvPrekeyRealEnv_nonvacuous_alloc (R : W4RecvPrekeyRealParams) :
    ∃ evs : List AllocEvent, evs ≠ [] ∧ W4RecvPrekeyRealEnv R evs :=
  ⟨rustAllocEvents 24 8, by decide,
    Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨by decide, rfl⟩)))))⟩

end LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot
