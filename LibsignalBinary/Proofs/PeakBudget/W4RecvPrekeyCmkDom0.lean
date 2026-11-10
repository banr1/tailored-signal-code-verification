/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
public import LibsignalBinary.Proofs.PeakBudget.CmkLoopAdvanceCredit
public import LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvGroupSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0StageAux
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyDom0Record
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyDom0Tie
public import LibsignalBinary.Proofs.PeakBudget.W4SlotGroupSpec
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# `StatesRecv`-Parametric `25,000`-Jump `archivedTrials = []` Slot Domain & `SingleSlotFineSpec`

`StatesRecv`-parametric `Dom0` (`archivedTrials = []`) slot envelopes and `SingleSlotFineSpec`
bounds for `recv-prekey`:
1. `SR : W4StatesRecvEnv`-parametric slot envelopes (`W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf`,
   `W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf`) including `W4StageP3Prev1WideEnv`
   (`VerNeTightTopEnv`) on Path C Stage P3 and `W4BobSessionBuildEnv9` + `kpStep`.
2. `W4RecvPrekeyCmkDom0Of`, `W4BinaryCallSiteDomCmk0`, and `W4BinaryRecvPrekeyDomCmk0` domain
   bundles (`rc ≤ 5`, `mk ≤ 2000`, `25,000` forward jumps via `CmkLoopAdvanceEvs`,
   `archivedTrials = []`), parametric in `(SR, LoopAdvEnv, maxOps)`.
3. Producer lifts (`deserializeTie` and `loadRec_decodeTie`) on `CliPqOrD3RecvDom` from prost
   `RecordStructure` previous-session bounds (`W4RecvPrekeyDom0Tie`).
4. Closed `Nat` `SingleSlotFineSpec` constants (`w4CmkDom0{Cum,Live,Peak,MaxReq,GrpSOf,GrpS83,GrpS109,GrpS128}`)
   and `@StatesRecvProtoEnv'` specializations.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0

open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoGames.LibsignalSessionApi (Direction Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs Inputs pqRecvInputs)
open CryptoVerification.SignalSession.Cli (StoresGhost addressText pathOf)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV CallV cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.Slots (loadRec scopeKit)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (parseArgs_peer_name_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (W4BinaryPkRemoveStepEnv W4BinaryStageP1OkEnv W4BinaryStageP1UntrustedEnv
   W4BinaryStageP2MatchedWideEnv W4BinaryStageP2PathAWideEnv W4BinaryStageP2PathCWideEnv
   W4BinaryStageP4MatchedWideEnv W4CloneACDomEnv W4CloneBDomEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
  (cliIo_rd_ok_length_le_sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec (SingleSlotFineSpec)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (W4BinaryIdSaveStepEnvAllFixed W4BinaryIdTrustStepEnvAllFixed W4BinaryKpkGetStepEnvAllFixed
   W4BinaryPkGetStepEnvAllFixed W4BinaryPkRemoveStepEnvAllFixed W4BinarySelfKpStepEnvAllFixed
   W4BinarySelfRegIdStepEnvAllFixed W4BinarySessLoadStepEnvAllFixed W4BinarySpkGetStepEnvAllFixed
   W4BinaryStageP1OkEnvAllFixed W4BinaryStageP1UntrustedEnvAllFixed
   W4BinaryStageP2PathAWideEnvAllFixed W4BinaryStageP2PathCWideEnvAllFixed
   W4BinaryStageP4MatchedWideEnvAllFixed W4BinaryStageP4PathAWideEnvAllFixed
   W4BinaryStageP4PathAWideEnvFixed W4BinaryStageP4PathCWideEnvAllFixed
   W4BinaryStageP4PathCWideEnvFixed dirGetEnv_fixed_eq_of_not_overCap
   not_overCapFile_runFiles_identities not_overCapFile_runFiles_kyberLastResort_keyName
   not_overCapFile_runFiles_kyberOneTime not_overCapFile_runFiles_oneTime
   not_overCapFile_runFiles_own_ikp not_overCapFile_runFiles_own_regId
   not_overCapFile_runFiles_sessions not_overCapFile_runFiles_signed)
open LibsignalBinary.Proofs.PeakBudget.RealMainBinaryEnvAdapterD3
  (CliPqOrD3RecvDom cliPqxdhInputs_pqRecvInputs_nil runFiles_pqRecvInputs_eq_nil)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvGroupSpec (StatesRecvTightGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches (StatesRecvTightCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit (statesRecvTightGroupS_split)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds (SessionCloneDom)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak (W4BoundedEvs)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4DecryptPrekeySlotParams W4StageP3WideEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec (W4DecryptPrekeyTightDom)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs (W4StageP3Prev1WideEnv)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0TdAux
  (W4FailedTdCancelCmkSrEnvOf W4StatesRecvEnv w4c_TryDecryptCliLinkedSrEnvOf
   w4c_repairedStatesRecvEnvFam w4c_repairedStatesRecv_creditSpec
   w4c_repairedStatesRecv_split_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
  (W4ArchivedTrialCmk W4ArchivedTrialDomCmkOf W4BinaryCallSiteDomCmk W4BinaryRecvPrekeyParamsCmk
   W4FailedTdDomCmkOf W4LoopAdvEnv W4RecvPrekeyRealParamsCmk W4TrialDecCmkEnv W4TrialDropCmkEnv
   W4TryDecryptCallDomCmkOf W4TryDecryptPathACDomCmkOf w4c_defaultDecodeMaxOps)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyDom0Record (RecordStructure)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyDom0Tie
  (list_eq_nil_of_cliPqOrD3RecvDom_deserializeTie
   list_eq_nil_of_cliPqOrD3RecvDom_loadRec_decodeTie list_eq_nil_of_deserialize_tie
   list_eq_nil_of_loadRec_decode_tie)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSavePollEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitLoadPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget (CliKpkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkGetPoll.LayoutBudget (CliPkGetPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.LayoutPlacedBudget
  (CliPkRemovePollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.SpkGetPoll.CalleesBudget (CliSpkGetPollEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv)

/-! ## `SR`-Parametric `25,000`-Jump + `VerNe-prev1` Slot Envelopes -/

/-- `SR`-parametric archived-trial run envelope (`SegCloneEnv` → `W4FailedTdCancelCmkSrEnvOf`). -/
def W4TrialRunWideCmkSrEnvOf (SR : W4StatesRecvEnv) (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem) (x : W4ArchivedTrialCmk) (evs : List AllocEvent) : Prop :=
  SeqEnv (SegCloneEnv x.G_tr x.ses_tr.state)
    (W4FailedTdCancelCmkSrEnvOf SR LoopAdvEnv maxOps C K x.fc_tr) evs

/-- `SR`-parametric `W4DecryptPrekeySlotParams` wired to `RecordDeserializeCancelEnv` and `w4c_TryDecryptCliLinkedSrEnvOf`. -/
def mkW4RecvPrekeyWideCmkSrSlotParamsOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (R : W4RecvPrekeyRealParamsCmk) :
    W4DecryptPrekeySlotParams W4ArchivedTrialCmk where
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
  F := R.C.F
  x_res := R.x_res
  x_spqr := R.x_spqr
  G_cur := R.G_cur
  st_cur := R.st_cur
  CurTrialFailEnv :=
    if R.hasCurSession then W4FailedTdCancelCmkSrEnvOf SR LoopAdvEnv maxOps R.C R.K R.fc_cur
    else fun _ => False
  DecEnv := W4TrialDecCmkEnv
  TrialEnv := W4TrialRunWideCmkSrEnvOf SR LoopAdvEnv maxOps R.C R.K
  DropEnv := W4TrialDropCmkEnv
  archivedTrials := R.archivedTrials
  g_arch := R.g_arch
  r_arch := R.r_arch
  VecPushEnv := W4BoundedEvs 1 192
  TryDecEnv :=
    if R.isPathB then w4c_TryDecryptCliLinkedSrEnvOf SR LoopAdvEnv maxOps R.C R.K R.td_B.a
    else fun _ => False
  g_out0 := R.g_out0
  r_out0 := R.r_out0
  G_out1 := R.G_out1
  sess_out1 := R.sess_out1
  enc_prev1 := R.enc_prev1

/-- `SR`-parametric Path A / Path C Stage-P3 `try_decrypt` envelope. -/
def W4RecvPrekeyTryDecACCmkSrEnvOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (R : W4RecvPrekeyRealParamsCmk) (evs : List AllocEvent) : Prop :=
  if R.isPathAC then w4c_TryDecryptCliLinkedSrEnvOf SR LoopAdvEnv maxOps R.C R.K R.td_AC.a evs
  else False

/-- `SR`-parametric Path B (`Matched`) envelope. -/
def W4BinaryRecvPrekeyPathBWideCmkSrEnvOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  let P := mkW4RecvPrekeyWideCmkSrSlotParamsOf SR LoopAdvEnv maxOps w.base
  SeqEnv (W4BinaryStageP1OkEnv w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2MatchedWideEnv P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials
          w.base.g_arch w.base.r_arch))
      (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneBDomEnv P.TryDecEnv))
        (OptStageEnv
          (W4BinaryStageP4MatchedWideEnv w.base.rd w.base.files w.base.peer w.remoteIdKey
            w.base.g_out0 w.base.r_out0)))) evs

/-- `SR`-parametric Path A (`0`-prev) `Fixed` envelope. -/
def W4BinaryRecvPrekeyPathAWideCmkSrEnvFixedOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  SeqEnv (W4BinaryStageP1OkEnv w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2PathAWideEnv w.base.hasOpk w.base.rd w.base.files
          w.base.spkId w.base.kpkId w.base.opkId w.base.C.F w.base.x_res w.base.x_spqr))
      (SeqEnv
        (OptStageEnv
          (W4StageP3WideEnv W4CloneACDomEnv
            (W4RecvPrekeyTryDecACCmkSrEnvOf SR LoopAdvEnv maxOps w.base)))
        (OptStageEnv
          (W4BinaryStageP4PathAWideEnvFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
            w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
            w.base.g_out0 w.base.r_out0)))) evs

/-- `SR`-parametric Path C (`Over` / `prev1`) `Fixed` envelope with `W4StageP3Prev1WideEnv`
(`VerNeTightTopEnv`). -/
def W4BinaryRecvPrekeyPathCWideCmkVerNeSrEnvFixedOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  let P := mkW4RecvPrekeyWideCmkSrSlotParamsOf SR LoopAdvEnv maxOps w.base
  SeqEnv (W4BinaryStageP1OkEnv w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2PathCWideEnv w.base.G_cur w.base.st_cur P.CurTrialFailEnv
          P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials w.base.g_arch w.base.r_arch
          w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
          w.base.C.F w.base.x_res w.base.x_spqr))
      (SeqEnv
        (OptStageEnv
          (W4StageP3Prev1WideEnv W4CloneACDomEnv
            (W4RecvPrekeyTryDecACCmkSrEnvOf SR LoopAdvEnv maxOps w.base) w.base.enc_prev1))
        (OptStageEnv
          (W4BinaryStageP4PathCWideEnvFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
            w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
            w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) evs

/-- Complete 4-arm `SR`-parametric W4 (`recv-prekey`) `Fixed` slot envelope with `VerNe-prev1`. -/
def W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4BinaryStageP1UntrustedEnv w.base.rd w.base.files w.base.peer w.remoteIdKey e ∨
      W4BinaryRecvPrekeyPathBWideCmkSrEnvOf SR LoopAdvEnv maxOps w e ∨
      W4BinaryRecvPrekeyPathAWideCmkSrEnvFixedOf SR LoopAdvEnv maxOps w e ∨
      W4BinaryRecvPrekeyPathCWideCmkVerNeSrEnvFixedOf SR LoopAdvEnv maxOps w e)
    FreeOnlyEvs evs

/-- Complete 4-arm `SR`-parametric W4 (`recv-prekey`) `AllFixed` slot envelope with `VerNe-prev1`. -/
def W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  let P := mkW4RecvPrekeyWideCmkSrSlotParamsOf SR LoopAdvEnv maxOps w.base
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4BinaryStageP1UntrustedEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2MatchedWideEnv P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials
              w.base.g_arch w.base.r_arch))
          (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneBDomEnv P.TryDecEnv))
            (OptStageEnv
              (W4BinaryStageP4MatchedWideEnvAllFixed w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.g_out0 w.base.r_out0)))) e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2PathAWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files
              w.base.spkId w.base.kpkId w.base.opkId w.base.C.F w.base.x_res w.base.x_spqr))
          (SeqEnv
            (OptStageEnv
              (W4StageP3WideEnv W4CloneACDomEnv
                (W4RecvPrekeyTryDecACCmkSrEnvOf SR LoopAdvEnv maxOps w.base)))
            (OptStageEnv
              (W4BinaryStageP4PathAWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
                w.base.g_out0 w.base.r_out0)))) e ∨
      SeqEnv (W4BinaryStageP1OkEnvAllFixed w.base.rd w.base.files w.base.peer w.remoteIdKey)
        (SeqEnv
          (OptStageEnv
            (W4BinaryStageP2PathCWideEnvAllFixed w.base.G_cur w.base.st_cur P.CurTrialFailEnv
              P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials w.base.g_arch w.base.r_arch
              w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
              w.base.C.F w.base.x_res w.base.x_spqr))
          (SeqEnv
            (OptStageEnv
              (W4StageP3Prev1WideEnv W4CloneACDomEnv
                (W4RecvPrekeyTryDecACCmkSrEnvOf SR LoopAdvEnv maxOps w.base) w.base.enc_prev1))
            (OptStageEnv
              (W4BinaryStageP4PathCWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
                w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) e)
    FreeOnlyEvs evs

theorem w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {w : W4BinaryRecvPrekeyParamsCmk}
    (hfiles : w.base.files = runFiles i) (hrd : w.base.rd = cliIo.rd) :
    W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf SR LoopAdvEnv maxOps w =
      W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf SR LoopAdvEnv maxOps w := by
  have hsessLoad : ∀ a : AddrVal,
      cliSessionKitLoadPollEnv cliIo.rd scopeKit (AddrTextValEnv DecimalEnv)
          (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          (ofBytesEnv RecordDeserializeCancelEnv) (runFiles i) StoresGhost.opened.sessions a =
        cliSessionKitLoadPollEnv cliIo.rd scopeKit (AddrTextValEnv DecimalEnv)
          (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
          (ofBytesEnv RecordDeserializeCancelEnv) (runFiles i) StoresGhost.opened.sessions a := by
    intro a; unfold cliSessionKitLoadPollEnv
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_sessions hi _)]
  have htrustPoll : ∀ (a : AddrVal) (k : CryptoGames.LibsignalSession.IdentityKey) (d : Direction),
      cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          (runFiles i) StoresGhost.opened.identity a k d =
        cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
          (runFiles i) StoresGhost.opened.identity a k d := by
    intro a k d; unfold cliIdentityKitTrustPollEnv
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_identities hi _)]
  have hsavePoll : ∀ (a : AddrVal) (k : CryptoGames.LibsignalSession.IdentityKey),
      cliIdentityKitSavePollEnv cliIo.rd (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          DirPutStrEnv (runFiles i) StoresGhost.opened.identity a k =
        cliIdentityKitSavePollEnv cliIo.rd (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
          DirPutStrEnv (runFiles i) StoresGhost.opened.identity a k := by
    intro a k; unfold cliIdentityKitSavePollEnv
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_identities hi _)]
  have hsess : ∀ peer,
      W4BinarySessLoadStepEnvAllFixed cliIo.rd (runFiles i) peer =
        CliRealBinaryKitEnvs.W4BinarySessLoadStepEnv cliIo.rd (runFiles i) peer := by
    intro peer; unfold W4BinarySessLoadStepEnvAllFixed CliRealBinaryKitEnvs.W4BinarySessLoadStepEnv
    rw [hsessLoad peer.val]
  have htrust : ∀ peer k,
      W4BinaryIdTrustStepEnvAllFixed cliIo.rd (runFiles i) peer k =
        CliRealBinaryKitEnvs.W4BinaryIdTrustStepEnv cliIo.rd (runFiles i) peer k := by
    intro peer k; unfold W4BinaryIdTrustStepEnvAllFixed CliRealBinaryKitEnvs.W4BinaryIdTrustStepEnv
    rw [htrustPoll peer.val k .receiving]
  have hsave : ∀ peer k,
      W4BinaryIdSaveStepEnvAllFixed cliIo.rd (runFiles i) peer k =
        CliRealBinaryKitEnvs.W4BinaryIdSaveStepEnv cliIo.rd (runFiles i) peer k := by
    intro peer k; unfold W4BinaryIdSaveStepEnvAllFixed CliRealBinaryKitEnvs.W4BinaryIdSaveStepEnv
    rw [hsavePoll peer.val k]
  have hspk : ∀ id,
      W4BinarySpkGetStepEnvAllFixed cliIo.rd (runFiles i) id =
        CliRealBinaryKitEnvs.W4BinarySpkGetStepEnv cliIo.rd (runFiles i) id := by
    intro id; unfold W4BinarySpkGetStepEnvAllFixed CliRealBinaryKitEnvs.W4BinarySpkGetStepEnv CliSpkGetPollEnv
    dsimp only
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_signed hi _)]
  have hkpk : ∀ id,
      W4BinaryKpkGetStepEnvAllFixed cliIo.rd (runFiles i) id =
        CliRealBinaryKitEnvs.W4BinaryKpkGetStepEnv cliIo.rd (runFiles i) id := by
    intro id; unfold W4BinaryKpkGetStepEnvAllFixed CliRealBinaryKitEnvs.W4BinaryKpkGetStepEnv CliKpkGetPollEnv
      LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.KpkPassEnv
    dsimp only
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_kyberOneTime hi _),
      dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_kyberLastResort_keyName hi id)]
  have hpk : ∀ id,
      W4BinaryPkGetStepEnvAllFixed cliIo.rd (runFiles i) id =
        CliRealBinaryKitEnvs.W4BinaryPkGetStepEnv cliIo.rd (runFiles i) id := by
    intro id; unfold W4BinaryPkGetStepEnvAllFixed CliRealBinaryKitEnvs.W4BinaryPkGetStepEnv CliPkGetPollEnv
    dsimp only
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_oneTime hi _)]
  have hselfKp :
      W4BinarySelfKpStepEnvAllFixed cliIo.rd (runFiles i) =
        CliRealBinaryKitEnvs.W4BinarySelfKpStepEnv cliIo.rd (runFiles i) := by
    unfold W4BinarySelfKpStepEnvAllFixed CliRealBinaryKitEnvs.W4BinarySelfKpStepEnv
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_own_ikp hi)]
  have hselfReg :
      W4BinarySelfRegIdStepEnvAllFixed cliIo.rd (runFiles i) =
        CliRealBinaryKitEnvs.W4BinarySelfRegIdStepEnv cliIo.rd (runFiles i) := by
    unfold W4BinarySelfRegIdStepEnvAllFixed CliRealBinaryKitEnvs.W4BinarySelfRegIdStepEnv
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_own_regId hi)]
  have hpkRem : ∀ id,
      W4BinaryPkRemoveStepEnvAllFixed cliIo.rd (runFiles i) id =
        W4BinaryPkRemoveStepEnv cliIo.rd (runFiles i) id := by
    intro id; unfold W4BinaryPkRemoveStepEnvAllFixed W4BinaryPkRemoveStepEnv CliPkRemovePollEnv
    dsimp only
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_oneTime hi _)]
  have hp1ok : ∀ peer k,
      W4BinaryStageP1OkEnvAllFixed cliIo.rd (runFiles i) peer k =
        W4BinaryStageP1OkEnv cliIo.rd (runFiles i) peer k := by
    intro peer k; funext evs; unfold W4BinaryStageP1OkEnvAllFixed W4BinaryStageP1OkEnv
    rw [hsess, htrust]
  have hp1un : ∀ peer k,
      W4BinaryStageP1UntrustedEnvAllFixed cliIo.rd (runFiles i) peer k =
        W4BinaryStageP1UntrustedEnv cliIo.rd (runFiles i) peer k := by
    intro peer k; funext evs; unfold W4BinaryStageP1UntrustedEnvAllFixed W4BinaryStageP1UntrustedEnv
    rw [hsess, htrust]
  have hp2a : ∀ hasOpk spkId kpkId opkId F x_res x_spqr,
      W4BinaryStageP2PathAWideEnvAllFixed hasOpk cliIo.rd (runFiles i) spkId kpkId opkId F x_res x_spqr =
        W4BinaryStageP2PathAWideEnv hasOpk cliIo.rd (runFiles i) spkId kpkId opkId F x_res x_spqr := by
    intro hasOpk spkId kpkId opkId F x_res x_spqr; funext evs
    unfold W4BinaryStageP2PathAWideEnvAllFixed W4BinaryStageP2PathAWideEnv
    rw [hspk, hkpk, hpk, hselfKp, hselfReg]
  have hp2c : ∀ {α : Type} G_cur st_cur CurTrialFailEnv
      (DecEnv TrialEnv DropEnv : α → List AllocEvent → Prop) xs g_arch r_arch
      hasOpk spkId kpkId opkId F x_res x_spqr,
      W4BinaryStageP2PathCWideEnvAllFixed G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
          g_arch r_arch hasOpk cliIo.rd (runFiles i) spkId kpkId opkId F x_res x_spqr =
        W4BinaryStageP2PathCWideEnv G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs
          g_arch r_arch hasOpk cliIo.rd (runFiles i) spkId kpkId opkId F x_res x_spqr := by
    intro α G_cur st_cur CurTrialFailEnv DecEnv TrialEnv DropEnv xs g_arch r_arch
      hasOpk spkId kpkId opkId F x_res x_spqr; funext evs
    unfold W4BinaryStageP2PathCWideEnvAllFixed W4BinaryStageP2PathCWideEnv
    rw [hspk, hkpk, hpk, hselfKp, hselfReg]
  have hp4m : ∀ peer k g_out0 r_out0,
      W4BinaryStageP4MatchedWideEnvAllFixed cliIo.rd (runFiles i) peer k g_out0 r_out0 =
        W4BinaryStageP4MatchedWideEnv cliIo.rd (runFiles i) peer k g_out0 r_out0 := by
    intro peer k g_out0 r_out0; funext evs
    unfold W4BinaryStageP4MatchedWideEnvAllFixed W4BinaryStageP4MatchedWideEnv
    rw [hsave]
  have hp4a : ∀ hasOpk peer k kpkId spkId opkId bk g_out0 r_out0,
      W4BinaryStageP4PathAWideEnvAllFixed hasOpk cliIo.rd (runFiles i) peer k kpkId spkId opkId bk
          g_out0 r_out0 =
        W4BinaryStageP4PathAWideEnvFixed hasOpk cliIo.rd (runFiles i) peer k kpkId spkId opkId bk
          g_out0 r_out0 := by
    intro hasOpk peer k kpkId spkId opkId bk g_out0 r_out0; funext evs
    unfold W4BinaryStageP4PathAWideEnvAllFixed W4BinaryStageP4PathAWideEnvFixed
    rw [hsave, hpkRem]
  have hp4c : ∀ hasOpk peer k kpkId spkId opkId bk G_out1 sess_out1 enc_prev1,
      W4BinaryStageP4PathCWideEnvAllFixed hasOpk cliIo.rd (runFiles i) peer k kpkId spkId opkId bk
          G_out1 sess_out1 enc_prev1 =
        W4BinaryStageP4PathCWideEnvFixed hasOpk cliIo.rd (runFiles i) peer k kpkId spkId opkId bk
          G_out1 sess_out1 enc_prev1 := by
    intro hasOpk peer k kpkId spkId opkId bk G_out1 sess_out1 enc_prev1; funext evs
    unfold W4BinaryStageP4PathCWideEnvAllFixed W4BinaryStageP4PathCWideEnvFixed
    rw [hsave, hpkRem]
  funext evs
  unfold W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
    W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
    W4BinaryRecvPrekeyPathBWideCmkSrEnvOf W4BinaryRecvPrekeyPathAWideCmkSrEnvFixedOf
    W4BinaryRecvPrekeyPathCWideCmkVerNeSrEnvFixedOf
  dsimp only
  rw [hfiles, hrd, hp1un, hp1ok, hp2a, hp2c, hp4m, hp4a, hp4c]

theorem w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed_of_cliPqOrD3RecvDom {P : PEParams} {i : Inputs}
    (hi : CliPqOrD3RecvDom P i) {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {w : W4BinaryRecvPrekeyParamsCmk}
    (hfiles : w.base.files = runFiles i) (hrd : w.base.rd = cliIo.rd) :
    W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf SR LoopAdvEnv maxOps w =
      W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf SR LoopAdvEnv maxOps w := by
  rcases hi with hPq | ⟨st, ct, rc, hwf, rfl⟩
  · exact w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed hPq hfiles hrd
  · exact w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed (cliPqxdhInputs_pqRecvInputs_nil hwf rc) hfiles hrd

/-! ## `SR`-Parametric `Dom0` (`archivedTrials = []`) Domain Predicates & Top-Level Envelopes -/

/-- `SR`-parametric domain bundle for `W4RecvPrekeyRealParamsCmk` (`0` `DoublingChainLe`). -/
structure W4RecvPrekeyRealDomCmkSrOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps smallFileCap maxCt : Nat)
    (R : W4RecvPrekeyRealParamsCmk) : Prop where
  kpk_dir : R.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            R.kpkDir = StoresGhost.opened.kyber.lastResort
  outer_dom : W4DecryptPrekeyTightDom (mkW4RecvPrekeyWideCmkSrSlotParamsOf SR LoopAdvEnv maxOps R)
    2097152 smallFileCap 286196 286196 2097152 286196 2097152 16384 2097152 2457152 4096
  cur_fail_dom : R.hasCurSession = true → W4FailedTdDomCmkOf R.C.F R.K maxCt R.fc_cur
  trials_dom : ∀ x ∈ R.archivedTrials, W4ArchivedTrialDomCmkOf R.C.F R.K maxCt x
  tdB_dom : R.isPathB = true → W4TryDecryptCallDomCmkOf R.C.F R.K maxCt R.td_B
  tdAC_dom : R.isPathAC = true → W4TryDecryptPathACDomCmkOf R.C.F R.K maxCt R.td_AC

/-- Parametric `(SR, LoopAdvEnv, maxOps, smallFileCap, maxCt)` W4 `recv-prekey` `Dom0` predicate:
`W4RecvPrekeyRealDomCmkSrOf SR LoopAdvEnv maxOps smallFileCap maxCt R ∧ R.archivedTrials = []`
(`0` `DoublingChainLe`, `rc ≤ 5`, `mk ≤ 2000`, `25,000` forward jumps). -/
def W4RecvPrekeyCmkDom0Of (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps smallFileCap maxCt : Nat)
    (R : W4RecvPrekeyRealParamsCmk) : Prop :=
  W4RecvPrekeyRealDomCmkSrOf SR LoopAdvEnv maxOps smallFileCap maxCt R ∧ R.archivedTrials = []

/-- Default `(CmkLoopAdvanceEvs, maxOps, sessionCapBytes, msgCapBytes)` `SR`-parametric W4 `Dom0`
predicate (`maxOps`-parametric: `83` / `109` / `128`). -/
abbrev W4RecvPrekeyCmkDom0 (SR : W4StatesRecvEnv) (maxOps : Nat)
    (R : W4RecvPrekeyRealParamsCmk) : Prop :=
  W4RecvPrekeyCmkDom0Of SR CmkLoopAdvanceEvs maxOps sessionCapBytes msgCapBytes R

/-- Call-site domain guard `W4BinaryCallSiteDomCmk` conjoined with `R.archivedTrials = []`
(independent of `(SR, LoopAdvEnv, maxOps)`). -/
def W4BinaryCallSiteDomCmk0 (C : Crypto) (K : MlKem)
    (maxCt : Nat) (peerVal : AddrVal) (files : FsFiles) (R : W4RecvPrekeyRealParamsCmk) : Prop :=
  W4BinaryCallSiteDomCmk C K maxCt peerVal files R ∧ R.archivedTrials = []

private theorem zb_tryDecryptCallDomCmkOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {td : W4RecvPrekeyCmkSlot.W4TryDecryptCallCmk}
    (h : W4TryDecryptCallDomCmkOf F K c₁ td) :
    W4TryDecryptCallDomCmkOf F K c₂ td :=
  { h with ct_le := Nat.le_trans h.ct_le hc }

private theorem zb_failedTdDomCmkOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {fc : W4RecvPrekeyCmkSlot.W4FailedTryDecryptCallCmk}
    (h : W4FailedTdDomCmkOf F K c₁ fc) :
    W4FailedTdDomCmkOf F K c₂ fc :=
  ⟨zb_tryDecryptCallDomCmkOf_mono hc h.td_dom, h.align_le, h.cancel_live⟩

private theorem zb_archivedTrialDomCmkOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {tr : W4ArchivedTrialCmk}
    (h : W4ArchivedTrialDomCmkOf F K c₁ tr) :
    W4ArchivedTrialDomCmkOf F K c₂ tr :=
  ⟨h.enc_le, h.live_le_peak, h.live_le_drop, h.drop_caps, h.tr_gv, h.tr_dom,
    zb_failedTdDomCmkOf_mono hc h.tr_fail⟩

private theorem zb_tryDecryptPathACDomCmkOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {td : W4RecvPrekeyCmkSlot.W4TryDecryptCallCmk}
    (h : W4TryDecryptPathACDomCmkOf F K c₁ td) :
    W4TryDecryptPathACDomCmkOf F K c₂ td :=
  ⟨zb_tryDecryptCallDomCmkOf_mono hc h.base, h.rc_nil⟩

/-- Call-site lift from `W4BinaryCallSiteDomCmk` to `W4RecvPrekeyRealDomCmkSrOf` for ANY
`(SR, LoopAdvEnv, maxOps)`. -/
theorem W4BinaryCallSiteDomCmk.toRealDomCmkSrOf (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    {C : Crypto} {K : MlKem} {maxCt : Nat}
    {i : Inputs} {peerV : AddrV} {files : FsFiles}
    {R : W4RecvPrekeyRealParamsCmk}
    (hcs : W4BinaryCallSiteDomCmk C K maxCt (addrValOf peerV) files R)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV))
    (hct : maxCt ≤ msgCapBytes) :
    W4RecvPrekeyRealDomCmkSrOf SR LoopAdvEnv maxOps sessionCapBytes msgCapBytes R where
  kpk_dir := hcs.kpk_dir
  outer_dom := by
    have hpeer40 : R.peer.name.bytes.length ≤ 40 := by
      have hp40 := parseArgs_peer_name_length_le hparse
      change R.peer.val.name.length ≤ 40
      rw [hcs.eq_peerVal]
      exact hp40
    have hsess2M : sessionCapBytes ≤ 2097152 := by
      unfold sessionCapBytes
      decide
    have hcur :
        (∀ evs, ¬ (mkW4RecvPrekeyWideCmkSrSlotParamsOf SR LoopAdvEnv maxOps R).CurTrialFailEnv evs) ∨
        ∃ ses_cur : Session (List (BitVec 8)),
          ses_cur.state = R.st_cur ∧ SessionGhostValid R.G_cur ses_cur ∧
            SessionCloneDom 286196 ses_cur := by
      rcases hcs.cur_dom with hfalse | hses
      · refine Or.inl fun evs hev => ?_
        dsimp only [mkW4RecvPrekeyWideCmkSrSlotParamsOf] at hev
        rw [hfalse] at hev
        exact nomatch hev
      · exact Or.inr hses
    refine
      { peer_len := hpeer40
        ownKey_len := hcs.ownKey_len
        ownReg_len := hcs.ownReg_len
        kpkMark_len := hcs.kpkMark_len
        res_old := hcs.res_old
        res_new := hcs.res_new
        ikm_small := by decide
        spqr_key := hcs.spqr_key
        sess_cap := fun bs hr => by
          dsimp only [mkW4RecvPrekeyWideCmkSrSlotParamsOf] at hr
          rw [hcs.eq_rd] at hr
          exact Nat.le_trans (cliIo_rd_ok_length_le_sessionCapBytes R.files _ bs hr) hsess2M
        small_cap := fun d _ n bs hr => by
          dsimp only [mkW4RecvPrekeyWideCmkSrSlotParamsOf] at hr
          rw [hcs.eq_rd] at hr
          exact cliIo_rd_ok_length_le_sessionCapBytes R.files (pathOf d.path n) bs hr
        cur_dom := hcur
        arch_valid := hcs.arch_valid
        arch_enc := hcs.arch_enc
        out0_valid := hcs.out0_valid
        out0_enc := hcs.out0_enc
        out1_freshBob := hcs.out1_freshBob
        trials_len4 := hcs.trials_len4 }
  cur_fail_dom hcur := zb_failedTdDomCmkOf_mono hct (hcs.cur_fail_dom hcur)
  trials_dom y hy := zb_archivedTrialDomCmkOf_mono hct (hcs.trials_dom y hy)
  tdB_dom hb := zb_tryDecryptCallDomCmkOf_mono hct (hcs.tdB_dom hb)
  tdAC_dom hac := zb_tryDecryptPathACDomCmkOf_mono hct (hcs.tdAC_dom hac)

/-- Direct call-site lift from `W4BinaryCallSiteDomCmk0` to
`W4RecvPrekeyCmkDom0Of SR LoopAdvEnv maxOps sessionCapBytes msgCapBytes R` on `.recv peerV`. -/
theorem W4BinaryCallSiteDomCmk0.toCmkDom0Of (SR : W4StatesRecvEnv)
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    {C : Crypto} {K : MlKem} {maxCt : Nat}
    {i : Inputs} {peerV : AddrV} {files : FsFiles}
    {R : W4RecvPrekeyRealParamsCmk}
    (hcs0 : W4BinaryCallSiteDomCmk0 C K maxCt (addrValOf peerV) files R)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV))
    (hct : maxCt ≤ msgCapBytes) :
    W4RecvPrekeyCmkDom0Of SR LoopAdvEnv maxOps sessionCapBytes msgCapBytes R :=
  ⟨W4BinaryCallSiteDomCmk.toRealDomCmkSrOf SR LoopAdvEnv maxOps hcs0.1 hparse hct, hcs0.2⟩

/-- Binary-kit call-dispatched `Dom0` guard on `W4BinaryRecvPrekeyParamsCmk` at
`(SR, LoopAdvEnv, maxOps)`. -/
def W4BinaryRecvPrekeyDomCmk0 (SR : W4StatesRecvEnv) (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (c : CallV) (i : Inputs) (w : W4BinaryRecvPrekeyParamsCmk) : Prop :=
  ∀ peerAddr, c = .recv peerAddr →
    w.base.peer.val = addrValOf peerAddr ∧
    w.base.peer.name.bytes.length ≤ 40 ∧
    w.base.files = runFiles i ∧
    w.base.rd = cliIo.rd ∧
    W4RecvPrekeyCmkDom0Of SR LoopAdvEnv maxOps sessionCapBytes msgCapBytes w.base

/-- `(SR, LoopAdvEnv, maxOps)`-parametric unguarded binary-kit W4 (`decrypt_prekey`) `Dom0` slot
envelope (including `VerNe-prev1` on Path C Stage P3). -/
abbrev realCliDecPkBinaryWideSlotEnvCmkDom0FixedOf [LibsignalPlacement]
    (SR : W4StatesRecvEnv) (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (_X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
    W4BinaryCallSiteDomCmk0 W.C W.Q.K x.msg.message.ciphertext.length x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf SR LoopAdvEnv maxOps w4 evs

/-- Default `(CmkLoopAdvanceEvs, 109)` `SR`-parametric unguarded W4 `Dom0` slot envelope. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkDom0Fixed [LibsignalPlacement]
    (SR : W4StatesRecvEnv) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  realCliDecPkBinaryWideSlotEnvCmkDom0FixedOf SR CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps X W x evs

theorem realCliDecPkBinaryWideSlotEnvCmkDom0FixedOf_ghost_congr [LibsignalPlacement]
    (SR : W4StatesRecvEnv) (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val)
    (_hm : x.me.val = y.me.val)
    (_hs : x.stores = y.stores)
    (_hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F)
    (_hc : x.coins = y.coins)
    (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnvCmkDom0FixedOf SR LoopAdvEnv maxOps X W x =
      realCliDecPkBinaryWideSlotEnvCmkDom0FixedOf SR LoopAdvEnv maxOps X W y := by
  funext evs
  simp only [realCliDecPkBinaryWideSlotEnvCmkDom0FixedOf, hp, hf, hmsg]

theorem realCliDecPkBinaryWideSlotEnvCmkDom0Fixed_ghost_congr [LibsignalPlacement]
    (SR : W4StatesRecvEnv) (X : UnreachedPqxdhPrimitives) (W : CliHooks) (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnvCmkDom0Fixed SR X W x =
      realCliDecPkBinaryWideSlotEnvCmkDom0Fixed SR X W y :=
  realCliDecPkBinaryWideSlotEnvCmkDom0FixedOf_ghost_congr
    SR CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps X W x y hp hm hs hcp hf hc hmsg

/-- `(SR, LoopAdvEnv, maxOps)`-parametric `PeerSpqrStateTight640`-guarded binary-kit W4 `Dom0`
slot envelope. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixedOf [LibsignalPlacement]
    (SR : W4StatesRecvEnv) (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
    realCliDecPkBinaryWideSlotEnvCmkDom0FixedOf SR LoopAdvEnv maxOps X W x evs

/-- Default `(CmkLoopAdvanceEvs, 109)` `SR`-parametric `PeerSpqrStateTight640`-guarded W4 `Dom0`
slot envelope. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed [LibsignalPlacement]
    (SR : W4StatesRecvEnv) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixedOf
    SR CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps X W x evs

theorem realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixedOf_ghost_congr [LibsignalPlacement]
    (SR : W4StatesRecvEnv) (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixedOf SR LoopAdvEnv maxOps X W x =
      realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixedOf SR LoopAdvEnv maxOps X W y := by
  funext evs
  dsimp [realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixedOf]
  rw [hf, hp,
    realCliDecPkBinaryWideSlotEnvCmkDom0FixedOf_ghost_congr
      SR LoopAdvEnv maxOps X W x y hp hm hs hcp hf hc hmsg]

theorem realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed_ghost_congr [LibsignalPlacement]
    (SR : W4StatesRecvEnv) (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed SR X W x =
      realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed SR X W y :=
  realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixedOf_ghost_congr
    SR CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps X W x y hp hm hs hcp hf hc hmsg

/-! ## `Dom0` Producer Lifts (`deserializeTie` & `loadRec_decodeTie`) -/

theorem w4RecvPrekeyCmkDom0Of_of_deserializeTie
    {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps smallFileCap maxCt : Nat}
    {R : W4RecvPrekeyRealParamsCmk} {bs : List (BitVec 8)} {orec : Option RecordStructure}
    (hDom : W4RecvPrekeyRealDomCmkSrOf SR LoopAdvEnv maxOps smallFileCap maxCt R)
    (hget : StoresGhost.opened.sessions.get cliIo.rd R.files (addressText R.peer.val) = .ok bs)
    (hdes : RecordStructure.deserialize bs = .ok orec)
    (hprev0 : (orec.map (·.previousSessions.length)).getD 0 = 0)
    (hTie : ∀ bs' orec',
      StoresGhost.opened.sessions.get cliIo.rd R.files (addressText R.peer.val) = .ok bs' →
      RecordStructure.deserialize bs' = .ok orec' →
      R.archivedTrials.length ≤ (orec'.map (·.previousSessions.length)).getD 0) :
    W4RecvPrekeyCmkDom0Of SR LoopAdvEnv maxOps smallFileCap maxCt R :=
  ⟨hDom, list_eq_nil_of_deserialize_tie hget hdes hprev0 hTie⟩

theorem w4RecvPrekeyCmkDom0Of_of_loadRec_decodeTie
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps smallFileCap maxCt : Nat}
    {R : W4RecvPrekeyRealParamsCmk} {recOpt : Option (SessionRecord (List (BitVec 8)))}
    (hDom : W4RecvPrekeyRealDomCmkSrOf SR LoopAdvEnv maxOps smallFileCap maxCt R)
    (hlr : loadRec Scope R.files R.peer.val = .ok recOpt)
    (hNone : loadRec Scope R.files R.peer.val = .ok none → R.archivedTrials = [])
    (hTie : ∀ r rec, loadRec Scope R.files R.peer.val = .ok (some r) →
      RecordStructure.decode (encodeRecord r) = some rec →
      R.archivedTrials.length ≤ rec.previousSessions.length)
    (hPrev0 : ∀ r, loadRec Scope R.files R.peer.val = .ok (some r) →
      ∃ rec, RecordStructure.decode (encodeRecord r) = some rec ∧ rec.previousSessions = []) :
    W4RecvPrekeyCmkDom0Of SR LoopAdvEnv maxOps smallFileCap maxCt R :=
  ⟨hDom, list_eq_nil_of_loadRec_decode_tie hlr hNone hTie hPrev0⟩

theorem w4RecvPrekeyCmkDom0Of_of_cliPqOrD3RecvDom_deserializeTie {W : PEParams}
    {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps smallFileCap maxCt : Nat}
    {i : Inputs} {peer : AddrV} {R : W4RecvPrekeyRealParamsCmk}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hfiles : R.files = runFiles i) (hpeer : R.peer.val = addrValOf peer)
    (hDom : W4RecvPrekeyRealDomCmkSrOf SR LoopAdvEnv maxOps smallFileCap maxCt R)
    (hTie : ∀ bs orec,
      StoresGhost.opened.sessions.get cliIo.rd R.files (addressText R.peer.val) = .ok bs →
      RecordStructure.deserialize bs = .ok orec →
      R.archivedTrials.length ≤ (orec.map (·.previousSessions.length)).getD 0) :
    W4RecvPrekeyCmkDom0Of SR LoopAdvEnv maxOps smallFileCap maxCt R :=
  ⟨hDom, list_eq_nil_of_cliPqOrD3RecvDom_deserializeTie hi hparse
    (fun bs orec hget hdes => hTie bs orec (hfiles.symm ▸ hpeer.symm ▸ hget) hdes)⟩

theorem w4RecvPrekeyCmkDom0Of_of_cliPqOrD3RecvDom_loadRec_decodeTie {W : PEParams}
    {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps smallFileCap maxCt : Nat}
    {i : Inputs} {peer : AddrV} {R : W4RecvPrekeyRealParamsCmk}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hfiles : R.files = runFiles i) (hpeer : R.peer.val = addrValOf peer)
    (hDom : W4RecvPrekeyRealDomCmkSrOf SR LoopAdvEnv maxOps smallFileCap maxCt R)
    (hNone : loadRec scopeKit R.files R.peer.val = .ok none → R.archivedTrials = [])
    (hTie : ∀ r rec, loadRec scopeKit R.files R.peer.val = .ok (some r) →
      RecordStructure.decode (encodeRecord r) = some rec →
      R.archivedTrials.length ≤ rec.previousSessions.length) :
    W4RecvPrekeyCmkDom0Of SR LoopAdvEnv maxOps smallFileCap maxCt R :=
  ⟨hDom, list_eq_nil_of_cliPqOrD3RecvDom_loadRec_decodeTie hi hparse
    (fun hlr => hNone (hfiles.symm ▸ hpeer.symm ▸ hlr))
    (fun r rec hlr hdec => hTie r rec (hfiles.symm ▸ hpeer.symm ▸ hlr) hdec)⟩

theorem w4BinaryCallSiteDomCmk0_of_cliPqOrD3RecvDom_deserializeTie {W : PEParams}
    {C : Crypto} {K : MlKem} {maxCt : Nat}
    {i : Inputs} {peer : AddrV} {R : W4RecvPrekeyRealParamsCmk}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hcs : W4BinaryCallSiteDomCmk C K maxCt (addrValOf peer) (runFiles i) R)
    (hTie : ∀ bs orec,
      StoresGhost.opened.sessions.get cliIo.rd R.files (addressText R.peer.val) = .ok bs →
      RecordStructure.deserialize bs = .ok orec →
      R.archivedTrials.length ≤ (orec.map (·.previousSessions.length)).getD 0) :
    W4BinaryCallSiteDomCmk0 C K maxCt (addrValOf peer) (runFiles i) R :=
  ⟨hcs, list_eq_nil_of_cliPqOrD3RecvDom_deserializeTie hi hparse
    (fun bs orec hget hdes => hTie bs orec (hcs.eq_files.symm ▸ hcs.eq_peerVal.symm ▸ hget) hdes)⟩

theorem w4BinaryCallSiteDomCmk0_of_cliPqOrD3RecvDom_loadRec_decodeTie {W : PEParams}
    {C : Crypto} {K : MlKem} {maxCt : Nat}
    {i : Inputs} {peer : AddrV} {R : W4RecvPrekeyRealParamsCmk}
    (hi : CliPqOrD3RecvDom W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peer))
    (hcs : W4BinaryCallSiteDomCmk C K maxCt (addrValOf peer) (runFiles i) R)
    (hNone : loadRec scopeKit R.files R.peer.val = .ok none → R.archivedTrials = [])
    (hTie : ∀ r rec, loadRec scopeKit R.files R.peer.val = .ok (some r) →
      RecordStructure.decode (encodeRecord r) = some rec →
      R.archivedTrials.length ≤ rec.previousSessions.length) :
    W4BinaryCallSiteDomCmk0 C K maxCt (addrValOf peer) (runFiles i) R :=
  ⟨hcs, list_eq_nil_of_cliPqOrD3RecvDom_loadRec_decodeTie hi hparse
    (fun hlr => hNone (hcs.eq_files.symm ▸ hcs.eq_peerVal.symm ▸ hlr))
    (fun r rec hlr hdec => hTie r rec (hcs.eq_files.symm ▸ hcs.eq_peerVal.symm ▸ hlr) hdec)⟩

/-! ## Non-Vacuity Witness (`evs ≠ []` Path-B Trace) -/

theorem w4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixed_nonvacuous_alloc
    (SR : W4StatesRecvEnv) (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) :
    ∃ evs : List AllocEvent,
      evs ≠ [] ∧ W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf SR LoopAdvEnv maxOps w evs :=
  ⟨rustAllocEvents 24 8, by decide,
    Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨by decide, rfl⟩)))))⟩

theorem w4BinaryRecvPrekeyCmkDom0_nonvacuous_alloc
    {SR : W4StatesRecvEnv} {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {peerAddr : AddrV} {i : Inputs} {w : W4BinaryRecvPrekeyParamsCmk}
    (_hDom0 : W4BinaryRecvPrekeyDomCmk0 SR LoopAdvEnv maxOps (.recv peerAddr) i w) :
    ∃ evs : List AllocEvent,
      evs ≠ [] ∧ W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf SR LoopAdvEnv maxOps w evs :=
  w4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixed_nonvacuous_alloc SR LoopAdvEnv maxOps w

/-! ## Closed `SingleSlotFineSpec` Constants & Theorems -/

/-- Exact closed decimal-literal cumulative small-pool credit (`138,754,427` B). -/
abbrev w4CmkDom0Cum : Nat := W4RecvPrekeyCmkDom0StageAux.w4CmkDom0Cum

/-- Exact closed decimal-literal post-slot live large-pool credit (`29,203,219` B). -/
abbrev w4CmkDom0Live : Nat := W4RecvPrekeyCmkDom0StageAux.w4CmkDom0Live

/-- Exact closed decimal-literal transient peak large-pool credit (`29,203,219` B). -/
abbrev w4CmkDom0Peak : Nat := W4RecvPrekeyCmkDom0StageAux.w4CmkDom0Peak

/-- Exact closed decimal-literal maximum single allocation request (`4,194,368` B). -/
abbrev w4CmkDom0MaxReq : Nat := W4RecvPrekeyCmkDom0StageAux.w4CmkDom0MaxReq

/-- Parametric `FineScale`-scaled small-group counter `grpS` (`83` / `109` / `128`). -/
abbrev w4CmkDom0GrpSOf (maxOps : Nat) : Nat := W4RecvPrekeyCmkDom0StageAux.w4CmkDom0GrpSOf maxOps

/-- Exact closed decimal-literal `grpS` at `maxOps = 83` (`2,696,470,354`). -/
abbrev w4CmkDom0GrpS83 : Nat := W4RecvPrekeyCmkDom0StageAux.w4CmkDom0GrpS83

/-- Exact closed decimal-literal `grpS` at `maxOps = 109` (`2,703,750,926`). -/
abbrev w4CmkDom0GrpS109 : Nat := W4RecvPrekeyCmkDom0StageAux.w4CmkDom0GrpS109

/-- Exact closed decimal-literal `grpS` at `maxOps = 128` (`2,709,071,344`). -/
abbrev w4CmkDom0GrpS128 : Nat := W4RecvPrekeyCmkDom0StageAux.w4CmkDom0GrpS128

/-- Default `maxOps = 109` (`w4c_defaultDecodeMaxOps`) `grpS` (`2,703,750,926`). -/
abbrev w4CmkDom0GrpS : Nat := w4CmkDom0GrpS109

theorem w4CmkDom0_live_le_peak : w4CmkDom0Live ≤ w4CmkDom0Peak :=
  W4RecvPrekeyCmkDom0StageAux.w4CmkDom0_live_le_peak

theorem w4CmkDom0GrpSOf_83_eq : w4CmkDom0GrpSOf 83 = w4CmkDom0GrpS83 :=
  W4RecvPrekeyCmkDom0StageAux.w4CmkDom0GrpSOf_83_eq

theorem w4CmkDom0GrpSOf_109_eq :
    w4CmkDom0GrpSOf w4c_defaultDecodeMaxOps = w4CmkDom0GrpS109 :=
  W4RecvPrekeyCmkDom0StageAux.w4CmkDom0GrpSOf_109_eq

theorem w4CmkDom0GrpSOf_128_eq : w4CmkDom0GrpSOf 128 = w4CmkDom0GrpS128 :=
  W4RecvPrekeyCmkDom0StageAux.w4CmkDom0GrpSOf_128_eq

/-- `SingleSlotFineSpec` on the `CallV`-dispatched `SR`-parametric `Dom0` `recv-prekey`
binary-kit envelope (with `W4BobSessionBuildEnv9` and `VerNe-prev1` on Path C Stage P3) at
`(SR, CmkLoopAdvanceEvs, maxOps)`. -/
def w4BinaryRecvPrekeyCmkDom0Of_singleSlotFineSpec {P : PEParams} {c : CallV} {i : Inputs}
    (SR : W4StatesRecvEnv) (maxOps : Nat)
    (hSrCred : ∀ F K, StatesRecvTightCreditSpec F (SR F K) 1647247 93776)
    (hSrGrp : ∀ F K, StatesRecvTightGroupSpec F (SR F K) statesRecvTightGroupS_split)
    (hi : CliPqOrD3RecvDom P i) :
    SingleSlotFineSpec
      (fun evs =>
        match c with
        | .recv _ =>
          ∃ w : W4BinaryRecvPrekeyParamsCmk,
            W4BinaryRecvPrekeyDomCmk0 SR CmkLoopAdvanceEvs maxOps c i w ∧
              W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf SR CmkLoopAdvanceEvs maxOps w evs
        | _ => False) where
  cum := w4CmkDom0Cum
  live := w4CmkDom0Live
  peak := w4CmkDom0Peak
  maxReq := w4CmkDom0MaxReq
  grpS := w4CmkDom0GrpSOf maxOps
  credit := by
    cases c with
    | recv peerAddr =>
      have hInp : ∃ i₀ : Inputs, CliPqxdhInputs P i₀ ∧ runFiles i = runFiles i₀ := by
        rcases hi with hPq | ⟨st, ct, rc, hwf, rfl⟩
        · exact ⟨i, hPq, rfl⟩
        · exact ⟨pqRecvInputs P st [] rc, cliPqxdhInputs_pqRecvInputs_nil hwf rc,
            runFiles_pqRecvInputs_eq_nil P st ct rc⟩
      obtain ⟨i₀, hi₀, hfilesEq⟩ := hInp
      let W : CliHooks := {
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
      }
      refine ⟨fun evs ⟨w, hw4, henv⟩ => ?_, fun st0 {evs} ⟨w, hw4, henv⟩ => ?_⟩
      · obtain ⟨hpv, hp40, hfiles, hrd, hd, htr⟩ := hw4 peerAddr rfl
        rw [w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed_of_cliPqOrD3RecvDom hi hfiles hrd] at henv
        have hP2M : ∀ (T₁ T₂ : W4ArchivedTrialCmk → List AllocEvent → Prop),
            W4BinaryStageP2MatchedWideEnv W4TrialDecCmkEnv T₁ W4TrialDropCmkEnv
              w.base.archivedTrials w.base.g_arch w.base.r_arch =
            W4BinaryStageP2MatchedWideEnv W4TrialDecCmkEnv T₂ W4TrialDropCmkEnv
              w.base.archivedTrials w.base.g_arch w.base.r_arch := by
          intro T₁ T₂; rw [htr]; rfl
        have hP2C : ∀ Ccur (T₁ T₂ : W4ArchivedTrialCmk → List AllocEvent → Prop),
            W4BinaryStageP2PathCWideEnv w.base.G_cur w.base.st_cur Ccur W4TrialDecCmkEnv T₁
              W4TrialDropCmkEnv w.base.archivedTrials w.base.g_arch w.base.r_arch w.base.hasOpk
              w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId w.base.C.F
              w.base.x_res w.base.x_spqr =
            W4BinaryStageP2PathCWideEnv w.base.G_cur w.base.st_cur Ccur W4TrialDecCmkEnv T₂
              W4TrialDropCmkEnv w.base.archivedTrials w.base.g_arch w.base.r_arch w.base.hasOpk
              w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId w.base.C.F
              w.base.x_res w.base.x_spqr := by
          intro Ccur T₁ T₂; rw [htr]; rfl
        have hEnvEq :
            W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf SR CmkLoopAdvanceEvs maxOps w =
              W4RecvPrekeyCmkDom0StageAux.W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
                SR CmkLoopAdvanceEvs maxOps w := by
          unfold W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
            W4BinaryRecvPrekeyPathBWideCmkSrEnvOf
            W4BinaryRecvPrekeyPathAWideCmkSrEnvFixedOf
            W4BinaryRecvPrekeyPathCWideCmkVerNeSrEnvFixedOf
            W4RecvPrekeyCmkDom0StageAux.W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
            GateM2rGStatesRecvTwins.m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf'
            GateM2rGStatesRecvTwins.m2rg_W4BinaryRecvPrekeyPathBWideCmkEnvOf'
            GateM2rGStatesRecvTwins.m2rg_W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf'
            GateM2rGStatesRecvTwins.m2rg_W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed'
            GateM2rGStatesRecvTwins.m2rg_verNePrev1P3PathCEnv'
            GateM2rGStatesRecvTwins.m2rg_verNePrev1P3PathCEnvOf'
            mkW4RecvPrekeyWideCmkSrSlotParamsOf
            GateM2rGStatesRecvTwins.m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf'
          dsimp only
          rw [hP2M _ _, hP2C _ _ _]
          rfl
        rw [hEnvEq] at henv
        have hOuter₀ : W4DecryptPrekeyTightDom
            (W4RecvPrekeyCmkDom0StageAux.mkW4RecvPrekeyWideCmkSrSlotParamsOf
              SR CmkLoopAdvanceEvs maxOps w.base)
            2097152 sessionCapBytes 286196 286196 2097152 286196 2097152 16384 2097152 2457152 4096 :=
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
            out1_freshBob := hd.outer_dom.out1_freshBob
            trials_len4 := hd.outer_dom.trials_len4 }
        have hw4₀ : W4RecvPrekeyCmkDom0StageAux.W4BinaryRecvPrekeyDomCmk0
            SR CmkLoopAdvanceEvs maxOps (.recv peerAddr) i₀ w := by
          intro p hp
          cases hp
          exact ⟨hpv, hp40, hfiles.trans hfilesEq, hrd,
            ⟨⟨hd.kpk_dir, hOuter₀, hd.cur_fail_dom, hd.trials_dom, hd.tdB_dom, hd.tdAC_dom⟩, htr⟩⟩
        exact (W4RecvPrekeyCmkDom0StageAux.w4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf_phaseCreditSpec_of_dom
          (fun _ _ _ _ _ hp => hp) hSrCred W i₀ peerAddr hi₀ w hw4₀).req_align evs henv
      · obtain ⟨hpv, hp40, hfiles, hrd, hd, htr⟩ := hw4 peerAddr rfl
        rw [w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed_of_cliPqOrD3RecvDom hi hfiles hrd] at henv
        have hP2M : ∀ (T₁ T₂ : W4ArchivedTrialCmk → List AllocEvent → Prop),
            W4BinaryStageP2MatchedWideEnv W4TrialDecCmkEnv T₁ W4TrialDropCmkEnv
              w.base.archivedTrials w.base.g_arch w.base.r_arch =
            W4BinaryStageP2MatchedWideEnv W4TrialDecCmkEnv T₂ W4TrialDropCmkEnv
              w.base.archivedTrials w.base.g_arch w.base.r_arch := by
          intro T₁ T₂; rw [htr]; rfl
        have hP2C : ∀ Ccur (T₁ T₂ : W4ArchivedTrialCmk → List AllocEvent → Prop),
            W4BinaryStageP2PathCWideEnv w.base.G_cur w.base.st_cur Ccur W4TrialDecCmkEnv T₁
              W4TrialDropCmkEnv w.base.archivedTrials w.base.g_arch w.base.r_arch w.base.hasOpk
              w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId w.base.C.F
              w.base.x_res w.base.x_spqr =
            W4BinaryStageP2PathCWideEnv w.base.G_cur w.base.st_cur Ccur W4TrialDecCmkEnv T₂
              W4TrialDropCmkEnv w.base.archivedTrials w.base.g_arch w.base.r_arch w.base.hasOpk
              w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId w.base.C.F
              w.base.x_res w.base.x_spqr := by
          intro Ccur T₁ T₂; rw [htr]; rfl
        have hEnvEq :
            W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf SR CmkLoopAdvanceEvs maxOps w =
              W4RecvPrekeyCmkDom0StageAux.W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
                SR CmkLoopAdvanceEvs maxOps w := by
          unfold W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
            W4BinaryRecvPrekeyPathBWideCmkSrEnvOf
            W4BinaryRecvPrekeyPathAWideCmkSrEnvFixedOf
            W4BinaryRecvPrekeyPathCWideCmkVerNeSrEnvFixedOf
            W4RecvPrekeyCmkDom0StageAux.W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
            GateM2rGStatesRecvTwins.m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf'
            GateM2rGStatesRecvTwins.m2rg_W4BinaryRecvPrekeyPathBWideCmkEnvOf'
            GateM2rGStatesRecvTwins.m2rg_W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf'
            GateM2rGStatesRecvTwins.m2rg_W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed'
            GateM2rGStatesRecvTwins.m2rg_verNePrev1P3PathCEnv'
            GateM2rGStatesRecvTwins.m2rg_verNePrev1P3PathCEnvOf'
            mkW4RecvPrekeyWideCmkSrSlotParamsOf
            GateM2rGStatesRecvTwins.m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf'
          dsimp only
          rw [hP2M _ _, hP2C _ _ _]
          rfl
        rw [hEnvEq] at henv
        have hOuter₀ : W4DecryptPrekeyTightDom
            (W4RecvPrekeyCmkDom0StageAux.mkW4RecvPrekeyWideCmkSrSlotParamsOf
              SR CmkLoopAdvanceEvs maxOps w.base)
            2097152 sessionCapBytes 286196 286196 2097152 286196 2097152 16384 2097152 2457152 4096 :=
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
            out1_freshBob := hd.outer_dom.out1_freshBob
            trials_len4 := hd.outer_dom.trials_len4 }
        have hw4₀ : W4RecvPrekeyCmkDom0StageAux.W4BinaryRecvPrekeyDomCmk0
            SR CmkLoopAdvanceEvs maxOps (.recv peerAddr) i₀ w := by
          intro p hp
          cases hp
          exact ⟨hpv, hp40, hfiles.trans hfilesEq, hrd,
            ⟨⟨hd.kpk_dir, hOuter₀, hd.cur_fail_dom, hd.trials_dom, hd.tdB_dom, hd.tdAC_dom⟩, htr⟩⟩
        exact (W4RecvPrekeyCmkDom0StageAux.w4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf_phaseCreditSpec_of_dom
          (fun _ _ _ _ _ hp => hp) hSrCred W i₀ peerAddr hi₀ w hw4₀).credit_le st0 henv
    | keygen _ _ => exact ⟨fun _ h => False.elim h, fun _ {_} h => False.elim h⟩
    | init _ _ => exact ⟨fun _ h => False.elim h, fun _ {_} h => False.elim h⟩
    | send _ => exact ⟨fun _ h => False.elim h, fun _ {_} h => False.elim h⟩
  live_le_peak := w4CmkDom0_live_le_peak
  groups := by
    cases c with
    | recv peerAddr =>
      have hInp : ∃ i₀ : Inputs, CliPqxdhInputs P i₀ ∧ runFiles i = runFiles i₀ := by
        rcases hi with hPq | ⟨st, ct, rc, hwf, rfl⟩
        · exact ⟨i, hPq, rfl⟩
        · exact ⟨pqRecvInputs P st [] rc, cliPqxdhInputs_pqRecvInputs_nil hwf rc,
            runFiles_pqRecvInputs_eq_nil P st ct rc⟩
      obtain ⟨i₀, hi₀, hfilesEq⟩ := hInp
      let W : CliHooks := {
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
      }
      refine ⟨fun st0 {evs} ⟨w, hw4, henv⟩ => ?_⟩
      obtain ⟨hpv, hp40, hfiles, hrd, hd, htr⟩ := hw4 peerAddr rfl
      rw [w4c_wideSlotEnvCmkVerNeSrAllFixed_eq_fixed_of_cliPqOrD3RecvDom hi hfiles hrd] at henv
      have hP2M : ∀ (T₁ T₂ : W4ArchivedTrialCmk → List AllocEvent → Prop),
          W4BinaryStageP2MatchedWideEnv W4TrialDecCmkEnv T₁ W4TrialDropCmkEnv
            w.base.archivedTrials w.base.g_arch w.base.r_arch =
          W4BinaryStageP2MatchedWideEnv W4TrialDecCmkEnv T₂ W4TrialDropCmkEnv
            w.base.archivedTrials w.base.g_arch w.base.r_arch := by
        intro T₁ T₂; rw [htr]; rfl
      have hP2C : ∀ Ccur (T₁ T₂ : W4ArchivedTrialCmk → List AllocEvent → Prop),
          W4BinaryStageP2PathCWideEnv w.base.G_cur w.base.st_cur Ccur W4TrialDecCmkEnv T₁
            W4TrialDropCmkEnv w.base.archivedTrials w.base.g_arch w.base.r_arch w.base.hasOpk
            w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId w.base.C.F
            w.base.x_res w.base.x_spqr =
          W4BinaryStageP2PathCWideEnv w.base.G_cur w.base.st_cur Ccur W4TrialDecCmkEnv T₂
            W4TrialDropCmkEnv w.base.archivedTrials w.base.g_arch w.base.r_arch w.base.hasOpk
            w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId w.base.C.F
            w.base.x_res w.base.x_spqr := by
        intro Ccur T₁ T₂; rw [htr]; rfl
      have hEnvEq :
          W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf SR CmkLoopAdvanceEvs maxOps w =
            W4RecvPrekeyCmkDom0StageAux.W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
              SR CmkLoopAdvanceEvs maxOps w := by
        unfold W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
          W4BinaryRecvPrekeyPathBWideCmkSrEnvOf
          W4BinaryRecvPrekeyPathAWideCmkSrEnvFixedOf
          W4BinaryRecvPrekeyPathCWideCmkVerNeSrEnvFixedOf
          W4RecvPrekeyCmkDom0StageAux.W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf
          GateM2rGStatesRecvTwins.m2rg_W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf'
          GateM2rGStatesRecvTwins.m2rg_W4BinaryRecvPrekeyPathBWideCmkEnvOf'
          GateM2rGStatesRecvTwins.m2rg_W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf'
          GateM2rGStatesRecvTwins.m2rg_W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed'
          GateM2rGStatesRecvTwins.m2rg_verNePrev1P3PathCEnv'
          GateM2rGStatesRecvTwins.m2rg_verNePrev1P3PathCEnvOf'
          mkW4RecvPrekeyWideCmkSrSlotParamsOf
          GateM2rGStatesRecvTwins.m2rg_mkW4RecvPrekeyWideCmkSlotParamsOf'
        dsimp only
        rw [hP2M _ _, hP2C _ _ _]
        rfl
      rw [hEnvEq] at henv
      have hOuter₀ : W4DecryptPrekeyTightDom
          (W4RecvPrekeyCmkDom0StageAux.mkW4RecvPrekeyWideCmkSrSlotParamsOf
            SR CmkLoopAdvanceEvs maxOps w.base)
          2097152 sessionCapBytes 286196 286196 2097152 286196 2097152 16384 2097152 2457152 4096 :=
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
          out1_freshBob := hd.outer_dom.out1_freshBob
          trials_len4 := hd.outer_dom.trials_len4 }
      have hw4₀ : W4RecvPrekeyCmkDom0StageAux.W4BinaryRecvPrekeyDomCmk0
          SR CmkLoopAdvanceEvs maxOps (.recv peerAddr) i₀ w := by
        intro p hp
        cases hp
        exact ⟨hpv, hp40, hfiles.trans hfilesEq, hrd,
          ⟨⟨hd.kpk_dir, hOuter₀, hd.cur_fail_dom, hd.trials_dom, hd.tdB_dom, hd.tdAC_dom⟩, htr⟩⟩
      exact (W4RecvPrekeyCmkDom0StageAux.w4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrFixedOf_phaseGroupSpec_of_dom
        (fun _ _ _ _ _ hp => hp) hSrGrp W i₀ peerAddr hi₀ w hw4₀).groups_le st0 henv
    | keygen _ _ => exact ⟨fun _ {_} h => False.elim h⟩
    | init _ _ => exact ⟨fun _ {_} h => False.elim h⟩
    | send _ => exact ⟨fun _ {_} h => False.elim h⟩

/-- Default `maxOps = 109` (`w4c_defaultDecodeMaxOps`) `SR`-parametric `SingleSlotFineSpec`. -/
def w4BinaryRecvPrekeyCmkDom0_singleSlotFineSpec {P : PEParams} {c : CallV} {i : Inputs}
    (SR : W4StatesRecvEnv)
    (hSrCred : ∀ F K, StatesRecvTightCreditSpec F (SR F K) 1647247 93776)
    (hSrGrp : ∀ F K, StatesRecvTightGroupSpec F (SR F K) statesRecvTightGroupS_split)
    (hi : CliPqOrD3RecvDom P i) :
    SingleSlotFineSpec
      (fun evs =>
        match c with
        | .recv _ =>
          ∃ w : W4BinaryRecvPrekeyParamsCmk,
            W4BinaryRecvPrekeyDomCmk0 SR CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps c i w ∧
              W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
                SR CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps w evs
        | _ => False) :=
  w4BinaryRecvPrekeyCmkDom0Of_singleSlotFineSpec SR w4c_defaultDecodeMaxOps hSrCred hSrGrp hi

theorem w4BinaryRecvPrekeyCmkDom0Of_singleSlotFineSpec_caps
    {P : PEParams} {c : CallV} {i : Inputs}
    (SR : W4StatesRecvEnv) (maxOps : Nat)
    (hSrCred : ∀ F K, StatesRecvTightCreditSpec F (SR F K) 1647247 93776)
    (hSrGrp : ∀ F K, StatesRecvTightGroupSpec F (SR F K) statesRecvTightGroupS_split)
    (hi : CliPqOrD3RecvDom P i) :
    let S := w4BinaryRecvPrekeyCmkDom0Of_singleSlotFineSpec (c := c) SR maxOps hSrCred hSrGrp hi
    S.cum = w4CmkDom0Cum ∧
      S.live = w4CmkDom0Live ∧
      S.peak = w4CmkDom0Peak ∧
      S.maxReq = w4CmkDom0MaxReq ∧
      S.grpS = w4CmkDom0GrpSOf maxOps :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem w4BinaryRecvPrekeyCmkDom0_singleSlotFineSpec_caps
    {P : PEParams} {c : CallV} {i : Inputs}
    (SR : W4StatesRecvEnv)
    (hSrCred : ∀ F K, StatesRecvTightCreditSpec F (SR F K) 1647247 93776)
    (hSrGrp : ∀ F K, StatesRecvTightGroupSpec F (SR F K) statesRecvTightGroupS_split)
    (hi : CliPqOrD3RecvDom P i) :
    let S := w4BinaryRecvPrekeyCmkDom0_singleSlotFineSpec (c := c) SR hSrCred hSrGrp hi
    S.cum = w4CmkDom0Cum ∧
      S.live = w4CmkDom0Live ∧
      S.peak = w4CmkDom0Peak ∧
      S.maxReq = w4CmkDom0MaxReq ∧
      S.grpS = w4CmkDom0GrpS109 :=
  ⟨rfl, rfl, rfl, rfl, w4CmkDom0GrpSOf_109_eq⟩

/-! ## `StatesRecvProtoEnv'` (`w4c_repairedStatesRecvEnvFam`) Specializations -/

/-- Sealed `@StatesRecvProtoEnv'` unguarded W4 `Dom0` slot envelope (`maxOps = 109`). -/
abbrev realCliDecPkBinaryWideSlotEnvCmkDom0Fixed' [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  realCliDecPkBinaryWideSlotEnvCmkDom0Fixed w4c_repairedStatesRecvEnvFam X W x evs

/-- Sealed `@StatesRecvProtoEnv'` `PeerSpqrStateTight640`-guarded W4 `Dom0` slot envelope (`maxOps = 109`). -/
abbrev realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed' [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  realCliDecPkBinaryWideSlotEnvCmkDom0GuardedFixed w4c_repairedStatesRecvEnvFam X W x evs

/-- Sealed `@StatesRecvProtoEnv'` `maxOps`-parametric `SingleSlotFineSpec` (`0` `SR` hypotheses). -/
def w4BinaryRecvPrekeyCmkDom0Of_singleSlotFineSpec' {P : PEParams} {c : CallV} {i : Inputs}
    (maxOps : Nat) (hi : CliPqOrD3RecvDom P i) :
    SingleSlotFineSpec
      (fun evs =>
        match c with
        | .recv _ =>
          ∃ w : W4BinaryRecvPrekeyParamsCmk,
            W4BinaryRecvPrekeyDomCmk0 w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs maxOps c i w ∧
              W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
                w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs maxOps w evs
        | _ => False) :=
  w4BinaryRecvPrekeyCmkDom0Of_singleSlotFineSpec
    w4c_repairedStatesRecvEnvFam maxOps
    w4c_repairedStatesRecv_creditSpec w4c_repairedStatesRecv_split_groupSpec hi

/-- Sealed `@StatesRecvProtoEnv'` default `maxOps = 109` `SingleSlotFineSpec` (`0` `SR` hypotheses). -/
def w4BinaryRecvPrekeyCmkDom0_singleSlotFineSpec' {P : PEParams} {c : CallV} {i : Inputs}
    (hi : CliPqOrD3RecvDom P i) :
    SingleSlotFineSpec
      (fun evs =>
        match c with
        | .recv _ =>
          ∃ w : W4BinaryRecvPrekeyParamsCmk,
            W4BinaryRecvPrekeyDomCmk0
              w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps c i w ∧
              W4BinaryRecvPrekeyWideSlotEnvCmkVerNeSrAllFixedOf
                w4c_repairedStatesRecvEnvFam CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps w evs
        | _ => False) :=
  w4BinaryRecvPrekeyCmkDom0_singleSlotFineSpec
    w4c_repairedStatesRecvEnvFam
    w4c_repairedStatesRecv_creditSpec w4c_repairedStatesRecv_split_groupSpec hi

theorem w4BinaryRecvPrekeyCmkDom0_singleSlotFineSpec'_caps
    {P : PEParams} {c : CallV} {i : Inputs} (hi : CliPqOrD3RecvDom P i) :
    let S := w4BinaryRecvPrekeyCmkDom0_singleSlotFineSpec' (c := c) hi
    S.cum = w4CmkDom0Cum ∧
      S.live = w4CmkDom0Live ∧
      S.peak = w4CmkDom0Peak ∧
      S.maxReq = w4CmkDom0MaxReq ∧
      S.grpS = w4CmkDom0GrpS109 :=
  w4BinaryRecvPrekeyCmkDom0_singleSlotFineSpec_caps (c := c)
    w4c_repairedStatesRecvEnvFam
    w4c_repairedStatesRecv_creditSpec w4c_repairedStatesRecv_split_groupSpec hi

end LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkDom0
