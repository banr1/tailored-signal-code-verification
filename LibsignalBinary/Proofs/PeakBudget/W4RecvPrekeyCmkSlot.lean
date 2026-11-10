/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkLinked
public import LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
public import LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak
public import LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
public import LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux
public import LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.DropSsLocal1Budget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
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
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# Widened `(LoopAdvEnv, maxOps)`-Parametric `decrypt_prekey` Slot Envelope

**Checked by Lean.**

Replaces `W4RecvPrekeyRealSlot`'s `DoublingChainLe 2000` (`W2TryDecryptTightEnv` /
`W2TryDecryptSeedsEnv 12`) Stage-P3 and failed-trial `try_decrypt` envelopes with `FromS2GenEnv`
(`TryDecryptCliLinkedEnv` / `CmkLoopAdvanceEvs`, up to `maxForwardJumps = 25000`), parametric in:
1. `LoopAdvEnv : W4LoopAdvEnv` (default `CmkLoopAdvanceEvs`), and
2. `maxOps : Nat` (default `w4c_defaultDecodeMaxOps = 109`, covering both `83` on 4-link stored SPQR
   states and up to `109` when `TopStateTight` decoding encounters an extra link).

Main results:
- At `(CmkLoopAdvanceEvs, 83)`, `w4c_TryDecryptCliLinkedEnvOf CmkLoopAdvanceEvs 83 C K` is
  definitionally (`rfl`) equal to `DecPkD2cSlotOkLinked.TryDecryptCliLinkedEnv C K`, and lifts to any
  `83 ≤ maxOps` via `w4c_tryDecryptCliLinkedEnv_sub`.
- Monotonicity in `(LoopAdvEnv, maxOps)` (`w4c_wideSlotEnvCmkAllFixed_mono`,
  `w4c_wideSlotEnvCmkFixed_mono`, `realCliDecPkBinaryWideSlotEnvCmkFixedOf_mono`,
  `realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf_mono`).
- Collapse of `W4BinaryRecvPrekeyWideSlotEnvCmkAllFixedOf` to `W4BinaryRecvPrekeyWideSlotEnvCmkFixedOf`
  under `CliPqxdhInputs P i` (`w4c_wideSlotEnvCmkAllFixed_eq_fixed`).
- Unguarded and `PeerSpqrStateTight640`-guarded `DecPkGhost → List AllocEvent → Prop` slot envelopes
  with `_ghost_congr` lemmas.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot

open Arm64.Process (bytesOfString)
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession
  (ChainKey Crypto IdentityKey MessageKeyGenerator MessageKeys Mut PublicKey RatchetState
   SessionState ShaCompress SignalMessage TripleRatchet)
open CryptoGames.LibsignalSessionApi (Direction Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams UnreachedPqxdhPrimitives)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Message MlKem PqRatchetState States V1Recv V1State VersionNegotiationPB spqrAuthApi
   spqrPolyApi spqrV1)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall SpqrModel TrGhost TryDecryptGhost reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost SessionGhost UuidParser coinsOf uuidTryParse)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs Inputs stdinCapBytes)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule StoresGhost addressText keyName pathOf)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (DecPkGhost addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps (parseArgs_peer_name_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
  (cliIo_rd_ok_length_le_sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (CliPkDecodeEnv CliSpkDecodeEnv W4BinaryPkRemoveStepEnv W4BinaryStageP1OkEnv
   W4BinaryStageP1UntrustedEnv W4BinaryStageP2MatchedWideEnv W4BinaryStageP2PathAWideEnv
   W4BinaryStageP2PathCWideEnv W4BinaryStageP4MatchedWideEnv W4CloneACDomEnv W4CloneBDomEnv)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
  (SpqrRecvC07C09aBytesEnv TryDecryptCliLinkedEnv spqrRecvC07C09aBytesEnv_nonempty
   tryDecryptEnvArgsToGhost)
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
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv IterSeqEnv)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (dropClonedSessionEvents)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (SpqrTightEvs StatesIntoPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec (DecodeStateTightEnv StatesFromPbTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv (SpqrRecvGhostLink)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches (SpqrRecvTightEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec (StatesRecvProtoEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (TopStateTight)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds (SessionCloneDom)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec (w2CmkChainTightLive)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak (optDeallocListEvs optDeallocListLarge)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak (ArchivedTrialIterEnv)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak (W4BoundedEvs)
open LibsignalBinary.Proofs.PeakBudget.W4OuterPeakSpec
  (OptStageEnv W4DecryptPrekeySlotParams W4StageP3WideEnv W4TryDecryptCloneFailWideEnv)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpec (W4DecryptPrekeyTightDom)
open LibsignalBinary.Proofs.PeakBudget.W4OuterTightSpecAux (FreshBobPrev1Dom)
open LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak (W4AesDecErrEnv)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget (SessionGhostValid)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.DropSsLocal1Budget
  (SessionDropCapsOk dropSessionStructureLocal1Events)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (ssStateLargeLive)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.SessionDeserializeBudget
  (sessDeserLargeLive)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (RecordDeserializeCancelEnv deserCancelFineMaxReq deserCancelFinePeak)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (SessDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv)
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
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget (s8Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget (s9Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (s3DefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
  (FromS2GenEnv FromS3GenEnv FromS4GenEnv FromS5GenEnv FromS6GenEnv FromS7GenEnv FromS8GenEnv
   s1InitTrGhost seqEnv_mono stdAesOpt)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudget (s7Env)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SegCloneEnv TryDecryptEnvArgs)

/-! ## `maxOps`-Parametric `spqr::recv` Linked Byte-Slice Envelope -/

/-- Default `spqr::decode_state` small-op cap (`109`, covering `83` for ≤4 links and up to `109`). -/
def w4c_defaultDecodeMaxOps : Nat := 109

/-- `maxOps`-parametric `DecodeStateTightEnv` (`rfl`-equal to `DecodeStateTightEnv` at `maxOps = 83`). -/
def w4c_DecodeStateTightEnvOf (maxOps : Nat) (_bs : Bytes) (evs : List AllocEvent) : Prop :=
  SpqrTightEvs maxOps 1307216 79236 evs

theorem w4c_decodeStateTightEnvOf_83_eq :
    w4c_DecodeStateTightEnvOf 83 = fun _ => DecodeStateTightEnv :=
  rfl

theorem w4c_decodeStateTightEnvOf_mono {m₁ m₂ : Nat} (hm : m₁ ≤ m₂) (bs : Bytes)
    {evs : List AllocEvent} (h : w4c_DecodeStateTightEnvOf m₁ bs evs) :
    w4c_DecodeStateTightEnvOf m₂ bs evs :=
  SpqrTightEvs.mono hm (Nat.le_refl _) (Nat.le_refl _) h

/-- `maxOps`-parametric `SpqrRecvC07TightEnv` (`rfl`-equal to `SpqrRecvC07TightEnv` at `maxOps = 83`). -/
def w4c_SpqrRecvC07TightEnvOf (F : ShaCompress) (K : MlKem) (maxOps : Nat)
    (StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  SpqrRecvTightEnv F K
    (w4c_DecodeStateTightEnvOf maxOps)
    (fun _ => StatesFromPbTightEnv)
    (fun _ => StatesIntoPbTightEnv)
    StatesRecvEnv' stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

/-- `maxOps`-parametric `SpqrRecvC07TightLinkedEnv`. -/
def w4c_SpqrRecvC07TightLinkedEnvOf (F : ShaCompress) (K : MlKem) (maxOps : Nat)
    (StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  w4c_SpqrRecvC07TightEnvOf F K maxOps StatesRecvEnv'
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs ∧
    SpqrRecvGhostLink F K stBytes sckaMsg xAdd xRk

/-- `maxOps`-parametric `SpqrRecvC07C09aTightLinkedEnv`. -/
def w4c_SpqrRecvC07C09aTightLinkedEnvOf (F : ShaCompress) (K : MlKem) (maxOps : Nat)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (evs : List AllocEvent) : Prop :=
  w4c_SpqrRecvC07TightLinkedEnvOf F K maxOps StatesRecvProtoEnv
    stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

/-- `maxOps`-parametric `∃`-lifted 12-ghost `C07 + C09a` linked `spqr::recv` byte-slice envelope
(`rfl`-equal to `DecPkD2cSlotOkLinked.SpqrRecvC07C09aBytesEnv` at `maxOps = 83`). -/
def w4c_SpqrRecvC07C09aBytesEnvOf (F : ShaCompress) (K : MlKem) (maxOps : Nat)
    (stBs _msgBs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
    w4c_SpqrRecvC07C09aTightLinkedEnvOf F K maxOps
      stBs pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs

theorem w4c_spqrRecvC07C09aBytesEnvOf_83_eq (F : ShaCompress) (K : MlKem) :
    w4c_SpqrRecvC07C09aBytesEnvOf F K 83 = SpqrRecvC07C09aBytesEnv F K :=
  rfl

theorem w4c_spqrRecvC07TightLinkedEnvOf_mono {F : ShaCompress} {K : MlKem} {m₁ m₂ : Nat}
    (hm : m₁ ≤ m₂)
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {stBytes : Bytes}
    {pre_pb : PqRatchetState} {vn : VersionNegotiationPB} {pb : V1State}
    {st0 : States spqrPolyApi (spqrAuthApi F)} {sckaMsg : Message spqrPolyApi}
    {v : V1Recv spqrPolyApi (spqrAuthApi F)}
    {xInit : InitInnerGhost} {xNew : ChainNewGhost}
    {xAdd : ChainAddEpochGhost} {xRk : ChainRecvKeyGhost}
    {xSInto : StatesIntoPbGhost F} {xCInto : ChainIntoPbCall}
    {evs : List AllocEvent}
    (h : w4c_SpqrRecvC07TightLinkedEnvOf F K m₁ StatesRecvEnv'
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs) :
    w4c_SpqrRecvC07TightLinkedEnvOf F K m₂ StatesRecvEnv'
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs := by
  refine ⟨?_, h.2⟩
  rcases h.1 with hfree | hseq
  · exact Or.inl hfree
  · exact Or.inr (seqEnv_mono (fun _ hd => w4c_decodeStateTightEnvOf_mono hm stBytes hd)
      (fun _ ha => ha) hseq)

theorem w4c_spqrRecvC07C09aBytesEnvOf_mono {F : ShaCompress} {K : MlKem} {m₁ m₂ : Nat}
    (hm : m₁ ≤ m₂) (stBs msgBs : List (BitVec 8)) {evs : List AllocEvent}
    (h : w4c_SpqrRecvC07C09aBytesEnvOf F K m₁ stBs msgBs evs) :
    w4c_SpqrRecvC07C09aBytesEnvOf F K m₂ stBs msgBs evs := by
  let _ := msgBs
  obtain ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto, h1⟩ := h
  exact ⟨pre_pb, vn, pb, st0, sckaMsg, v, xInit, xNew, xAdd, xRk, xSInto, xCInto,
    w4c_spqrRecvC07TightLinkedEnvOf_mono hm h1⟩

theorem w4c_spqrRecvC07C09aBytesEnvOf_nonempty (F : ShaCompress) (K : MlKem) (maxOps : Nat)
    (hm : 83 ≤ maxOps) (stBs msgBs : List (BitVec 8)) :
    ∃ evs, w4c_SpqrRecvC07C09aBytesEnvOf F K maxOps stBs msgBs evs := by
  obtain ⟨evs, h⟩ := spqrRecvC07C09aBytesEnv_nonempty F K stBs msgBs
  exact ⟨evs, w4c_spqrRecvC07C09aBytesEnvOf_mono hm stBs msgBs h⟩

/-! ## `(LoopAdvEnv, maxOps)`-Parametric `TryDecryptCliLinkedEnv` & Failed-Trial Envelopes -/

/-- Segment-4 `consume_message_key` advance-loop envelope parameter type (`steps → cap0 → len0 → isAllOnes → evs → Prop`). -/
abbrev W4LoopAdvEnv : Type := Nat → BitVec 64 → Nat → Bool → List AllocEvent → Prop

/-- Pointwise inclusion on `W4LoopAdvEnv`. -/
def W4LoopAdvSub (L₁ L₂ : W4LoopAdvEnv) : Prop :=
  ∀ n cap0 len0 allOnes evs, L₁ n cap0 len0 allOnes evs → L₂ n cap0 len0 allOnes evs

theorem w4c_loopAdvSub_refl (L : W4LoopAdvEnv) : W4LoopAdvSub L L :=
  fun _ _ _ _ _ h => h

/-- `LoopAdvEnv`-parametric Segment-4 `consume_message_key` step envelope (`rfl`-equal to
`DecPkD2cSlotOkLinked.tryDecryptCmkStepEnv` at `LoopAdvEnv := CmkLoopAdvanceEvs`). -/
def w4c_tryDecryptCmkStepEnvOf (LoopAdvEnv : W4LoopAdvEnv)
    (msgCounter : BitVec 32) (senderRatchetKey : PublicKey)
    (trG : TrGhost) (r : RatchetState) (ck : ChainKey) (evs : List AllocEvent) : Prop :=
  if msgCounter < ck.index then
    FreeOnlyEvs evs
  else if (msgCounter - ck.index).toNat ≤ r.maxForwardJumps then
    match r.findReceiverChainIndex senderRatchetKey with
    | none =>
      if ck.index < msgCounter then
        evs = [] ∨ evs = rustAllocEvents 32 1
      else
        evs = []
    | some ci =>
      let cap0 := (trG.ratchet.chains[ci]?.map (·.mkCap)).getD 0#64
      let len0 := (r.receiverChains[ci]?.map (·.messageKeys.length)).getD 0
      LoopAdvEnv (msgCounter - ck.index).toNat cap0 len0
        (msgCounter == BitVec.allOnes 32) evs
  else
    evs = rustAllocEvents 36 1

/-- `LoopAdvEnv`-parametric Segment-4 (`ConsumeMsgKey`) envelope (`rfl`-equal to
`DecPkD2cSlotOkLinked.tryDecryptCmkSeg4Env` at `LoopAdvEnv := CmkLoopAdvanceEvs`). -/
def w4c_tryDecryptCmkSeg4EnvOf (LoopAdvEnv : W4LoopAdvEnv)
    (fmtWriteEnv : List AllocEvent → Prop)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (ck : ChainKey) : List AllocEvent → Prop :=
  SeqEnv fmtWriteEnv
    (SeqEnv (w4c_tryDecryptCmkStepEnvOf LoopAdvEnv x.msg.counter x.msg.senderRatchetKey
      trG tr.ratchet ck) FreeOnlyEvs)

/-- `LoopAdvEnv`-parametric `TryDecryptCliEnvOfPure` (`rfl`-equal to
`DecPkD2cSlotOkLinked.TryDecryptCliEnvOfPure` at `LoopAdvEnv := CmkLoopAdvanceEvs`). -/
def w4c_TryDecryptCliEnvOfPure (LoopAdvEnv : W4LoopAdvEnv)
    (C : Crypto) (S : SpqrModel)
    (fmtWriteEnv : List AllocEvent → Prop)
    (RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop)
    (a : TryDecryptEnvArgs) : List AllocEvent → Prop :=
  match Mut.exec TripleRatchet.fromSessionState a.st with
  | (.error _, _) => FreeOnlyEvs
  | (.ok tr0, st1) =>
    SeqEnv FreeOnlyEvs
      (FromS2GenEnv C uuidTryParse S (stdAesOpt C)
        (s3DefaultEnv C) (w4c_tryDecryptCmkSeg4EnvOf LoopAdvEnv fmtWriteEnv)
        (PqRecvEnv S RecvBytesEnv fmtEnv)
        s6FreeOnlyEnv (s7Env C.F uuidTryParse) s8Env s9Env
        (tryDecryptEnvArgsToGhost a) (s1InitTrGhost a.G) tr0 st1)

/-- `(LoopAdvEnv, maxOps)`-parametric linked Block-`507` `try_decrypt_with_state` CLI envelope
(`rfl`-equal to `DecPkD2cSlotOkLinked.TryDecryptCliLinkedEnv C K` at `(CmkLoopAdvanceEvs, 83)`). -/
abbrev w4c_TryDecryptCliLinkedEnvOf (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem) : TryDecryptEnvArgs → List AllocEvent → Prop :=
  w4c_TryDecryptCliEnvOfPure LoopAdvEnv C (spqrV1 C.F K)
    FmtWriteEnv (w4c_SpqrRecvC07C09aBytesEnvOf C.F K maxOps) FormatInnerEnv

theorem w4c_tryDecryptCliLinkedEnvOf_83_eq (C : Crypto) (K : MlKem) :
    w4c_TryDecryptCliLinkedEnvOf CmkLoopAdvanceEvs 83 C K = TryDecryptCliLinkedEnv C K :=
  rfl

/-- Failed-AES-CBC (`aesOpt = none`) Segment-`S8` envelope where any output buffer is dropped before
returning `.error`, keeping `Δlive = 0` on `S8` so `fc.failDropPairs` cancels the failed trial. -/
def w4c_s8FailEnv (x : TryDecryptGhost) (_mks : MessageKeys) (_newPqr : List (BitVec 8)) :
    List AllocEvent → Prop :=
  SeqEnv (W4AesDecErrEnv x.msg.ciphertext.length) FreeOnlyEvs

/-- Failed-trial `FromS2GenEnv` envelope (`aesOpt := fun _ _ => none`, `s8Env := w4c_s8FailEnv`). -/
def w4c_TryDecryptCliFailEnvOfPure (LoopAdvEnv : W4LoopAdvEnv)
    (C : Crypto) (S : SpqrModel)
    (fmtWriteEnv : List AllocEvent → Prop)
    (RecvBytesEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop)
    (a : TryDecryptEnvArgs) : List AllocEvent → Prop :=
  match Mut.exec TripleRatchet.fromSessionState a.st with
  | (.error _, _) => FreeOnlyEvs
  | (.ok tr0, st1) =>
    SeqEnv FreeOnlyEvs
      (FromS2GenEnv C uuidTryParse S (fun _ _ => none)
        (s3DefaultEnv C) (w4c_tryDecryptCmkSeg4EnvOf LoopAdvEnv fmtWriteEnv)
        (PqRecvEnv S RecvBytesEnv fmtEnv)
        s6FreeOnlyEnv (s7Env C.F uuidTryParse) w4c_s8FailEnv s9Env
        (tryDecryptEnvArgsToGhost a) (s1InitTrGhost a.G) tr0 st1)

/-- `(LoopAdvEnv, maxOps)`-parametric failed-trial linked `try_decrypt_with_state` envelope. -/
abbrev w4c_TryDecryptCliLinkedFailEnvOf (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem) : TryDecryptEnvArgs → List AllocEvent → Prop :=
  w4c_TryDecryptCliFailEnvOfPure LoopAdvEnv C (spqrV1 C.F K)
    FmtWriteEnv (w4c_SpqrRecvC07C09aBytesEnvOf C.F K maxOps) FormatInnerEnv

private theorem w4c_tryDecryptCmkStepEnvOf_mono {L₁ L₂ : W4LoopAdvEnv}
    (hL : W4LoopAdvSub L₁ L₂)
    (msgCounter : BitVec 32) (senderRatchetKey : PublicKey)
    (trG : TrGhost) (r : RatchetState) (ck : ChainKey) {evs : List AllocEvent}
    (h : w4c_tryDecryptCmkStepEnvOf L₁ msgCounter senderRatchetKey trG r ck evs) :
    w4c_tryDecryptCmkStepEnvOf L₂ msgCounter senderRatchetKey trG r ck evs := by
  unfold w4c_tryDecryptCmkStepEnvOf at h ⊢
  by_cases hlt : msgCounter < ck.index
  · simp only [hlt, ↓reduceIte] at h ⊢
    exact h
  · simp only [hlt, ↓reduceIte] at h ⊢
    by_cases hj : (msgCounter - ck.index).toNat ≤ r.maxForwardJumps
    · simp only [hj, ↓reduceIte] at h ⊢
      revert h
      cases r.findReceiverChainIndex senderRatchetKey <;> intro h
      · exact h
      · exact hL _ _ _ _ _ h
    · simp only [hj, ↓reduceIte] at h ⊢
      exact h

private theorem w4c_tryDecryptCmkSeg4EnvOf_mono {L₁ L₂ : W4LoopAdvEnv}
    (hL : W4LoopAdvSub L₁ L₂) (fmtWriteEnv : List AllocEvent → Prop)
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (ck : ChainKey) {evs : List AllocEvent}
    (h : w4c_tryDecryptCmkSeg4EnvOf L₁ fmtWriteEnv x trG tr ck evs) :
    w4c_tryDecryptCmkSeg4EnvOf L₂ fmtWriteEnv x trG tr ck evs :=
  seqEnv_mono (fun _ hf => hf)
    (fun _ hs => seqEnv_mono
      (fun _ hc => w4c_tryDecryptCmkStepEnvOf_mono hL _ _ _ _ _ hc)
      (fun _ hfr => hfr) hs) h

private theorem w4c_pqRecvEnv_mono {S : SpqrModel}
    {R₁ R₂ : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    (hR : ∀ stBs msgBs evs, R₁ stBs msgBs evs → R₂ stBs msgBs evs)
    (fmtEnv : List AllocEvent → Prop)
    (x : TryDecryptGhost) (tr : TripleRatchet (List (BitVec 8))) {evs : List AllocEvent}
    (h : PqRecvEnv S R₁ fmtEnv x tr evs) :
    PqRecvEnv S R₂ fmtEnv x tr evs := by
  unfold PqRecvEnv at h ⊢
  revert h
  cases S.recv tr.pqrState x.msg.pqRatchet <;> intro h
  · exact seqEnv_mono
      (fun _ h1 => seqEnv_mono (fun _ hr => hR _ _ _ hr) (fun _ hf => hf) h1)
      (fun _ hfr => hfr) h
  · exact hR _ _ _ h

private theorem w4c_fromS5GenEnv_mono {C : Crypto} {parse : UuidParser} {S : SpqrModel}
    {aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8))}
    {s5₁ s5₂ : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hs5 : ∀ x tr evs, s5₁ x tr evs → s5₂ x tr evs)
    {s6 : MessageKeyGenerator → List AllocEvent → Prop}
    {s7 : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop}
    {s8 : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9 : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) {evs : List AllocEvent}
    (h : FromS5GenEnv C parse S aesOpt s5₁ s6 s7 s8 s9 x trG tr st1 mkg evs) :
    FromS5GenEnv C parse S aesOpt s5₂ s6 s7 s8 s9 x trG tr st1 mkg evs := by
  unfold FromS5GenEnv at h ⊢
  revert h
  cases S.recv tr.pqrState x.msg.pqRatchet with
  | error e =>
    intro h
    exact seqEnv_mono (fun _ h5 => hs5 x tr _ h5) (fun _ hfr => hfr) h
  | ok pair =>
    rcases pair with ⟨newPqrState, pqrKey⟩
    intro h
    exact seqEnv_mono (fun _ h5 => hs5 x tr _ h5) (fun _ h6 => h6) h

private theorem w4c_fromS4GenEnv_mono {C : Crypto} {parse : UuidParser} {S : SpqrModel}
    {aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8))}
    {s4₁ s4₂ : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop}
    {s5₁ s5₂ : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hs4 : ∀ x trG tr ck evs, s4₁ x trG tr ck evs → s4₂ x trG tr ck evs)
    (hs5 : ∀ x tr evs, s5₁ x tr evs → s5₂ x tr evs)
    {s6 : MessageKeyGenerator → List AllocEvent → Prop}
    {s7 : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop}
    {s8 : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9 : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (ck : ChainKey) {evs : List AllocEvent}
    (h : FromS4GenEnv C parse S aesOpt s4₁ s5₁ s6 s7 s8 s9 x trG tr st1 ck evs) :
    FromS4GenEnv C parse S aesOpt s4₂ s5₂ s6 s7 s8 s9 x trG tr st1 ck evs := by
  unfold FromS4GenEnv at h ⊢
  revert h
  cases Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) tr.ratchet with
  | mk res r2 =>
    cases res with
    | error e =>
      intro h
      exact seqEnv_mono (fun _ h4 => hs4 x trG tr ck _ h4) (fun _ hfr => hfr) h
    | ok mkg =>
      intro h
      exact seqEnv_mono (fun _ h4 => hs4 x trG tr ck _ h4)
        (fun _ h5 => w4c_fromS5GenEnv_mono hs5 x trG { tr with ratchet := r2 } st1 mkg h5) h

private theorem w4c_fromS3GenEnv_mono {C : Crypto} {parse : UuidParser} {S : SpqrModel}
    {aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8))}
    {s3 : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    {s4₁ s4₂ : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop}
    {s5₁ s5₂ : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hs4 : ∀ x trG tr ck evs, s4₁ x trG tr ck evs → s4₂ x trG tr ck evs)
    (hs5 : ∀ x tr evs, s5₁ x tr evs → s5₂ x tr evs)
    {s6 : MessageKeyGenerator → List AllocEvent → Prop}
    {s7 : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop}
    {s8 : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9 : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) {evs : List AllocEvent}
    (h : FromS3GenEnv C parse S aesOpt s3 s4₁ s5₁ s6 s7 s8 s9 x trG tr st1 evs) :
    FromS3GenEnv C parse S aesOpt s3 s4₂ s5₂ s6 s7 s8 s9 x trG tr st1 evs := by
  unfold FromS3GenEnv at h ⊢
  revert h
  cases Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest)) tr.ratchet with
  | mk res r1 =>
    cases res with
    | error e =>
      intro h
      exact h
    | ok ck =>
      intro h
      exact seqEnv_mono (fun _ h3 => h3)
        (fun _ h4 => w4c_fromS4GenEnv_mono hs4 hs5 _ _ _ _ _ h4) h

private theorem w4c_fromS2GenEnv_mono {C : Crypto} {parse : UuidParser} {S : SpqrModel}
    {aesOpt : MessageKeys → SignalMessage → Option (List (BitVec 8))}
    {s3 : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    {s4₁ s4₂ : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) → ChainKey →
      List AllocEvent → Prop}
    {s5₁ s5₂ : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → List AllocEvent → Prop}
    (hs4 : ∀ x trG tr ck evs, s4₁ x trG tr ck evs → s4₂ x trG tr ck evs)
    (hs5 : ∀ x tr evs, s5₁ x tr evs → s5₂ x tr evs)
    {s6 : MessageKeyGenerator → List AllocEvent → Prop}
    {s7 : TryDecryptGhost → TripleRatchet (List (BitVec 8)) → MessageKeys →
      List (BitVec 8) → List AllocEvent → Prop}
    {s8 : TryDecryptGhost → MessageKeys → List (BitVec 8) → List AllocEvent → Prop}
    {s9 : TryDecryptGhost → TrGhost → TripleRatchet (List (BitVec 8)) →
      SessionState (List (BitVec 8)) → List (BitVec 8) → List AllocEvent → Prop}
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) {evs : List AllocEvent}
    (h : FromS2GenEnv C parse S aesOpt s3 s4₁ s5₁ s6 s7 s8 s9 x trG tr st1 evs) :
    FromS2GenEnv C parse S aesOpt s3 s4₂ s5₂ s6 s7 s8 s9 x trG tr st1 evs := by
  unfold FromS2GenEnv at h ⊢
  revert h
  cases tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
  | error e =>
    intro h
    exact h
  | ok ckOpt =>
    cases ckOpt with
    | some ck =>
      intro h
      exact w4c_fromS4GenEnv_mono hs4 hs5 x trG tr st1 ck h
    | none =>
      intro h
      exact w4c_fromS3GenEnv_mono hs4 hs5 x trG tr st1 h

theorem w4c_tryDecryptCliLinkedEnvOf_mono {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    {C : Crypto} {K : MlKem} {a : TryDecryptEnvArgs} {evs : List AllocEvent}
    (h : w4c_TryDecryptCliLinkedEnvOf L₁ m₁ C K a evs) :
    w4c_TryDecryptCliLinkedEnvOf L₂ m₂ C K a evs := by
  unfold w4c_TryDecryptCliLinkedEnvOf w4c_TryDecryptCliEnvOfPure at h ⊢
  revert h
  cases Mut.exec TripleRatchet.fromSessionState a.st with
  | mk res st1 =>
    cases res with
    | error e =>
      intro h
      exact h
    | ok tr0 =>
      intro h
      exact seqEnv_mono (fun _ hf => hf)
        (fun _ h2 => w4c_fromS2GenEnv_mono
          (fun x trG tr ck _ hs4 => w4c_tryDecryptCmkSeg4EnvOf_mono hL FmtWriteEnv x trG tr ck hs4)
          (fun x tr _ hs5 => w4c_pqRecvEnv_mono
            (fun stBs msgBs _ hr => w4c_spqrRecvC07C09aBytesEnvOf_mono hm stBs msgBs hr)
            FormatInnerEnv x tr hs5)
          _ _ tr0 st1 h2) h

theorem w4c_tryDecryptCliLinkedFailEnvOf_mono {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    {C : Crypto} {K : MlKem} {a : TryDecryptEnvArgs} {evs : List AllocEvent}
    (h : w4c_TryDecryptCliLinkedFailEnvOf L₁ m₁ C K a evs) :
    w4c_TryDecryptCliLinkedFailEnvOf L₂ m₂ C K a evs := by
  unfold w4c_TryDecryptCliLinkedFailEnvOf w4c_TryDecryptCliFailEnvOfPure at h ⊢
  revert h
  cases Mut.exec TripleRatchet.fromSessionState a.st with
  | mk res st1 =>
    cases res with
    | error e =>
      intro h
      exact h
    | ok tr0 =>
      intro h
      exact seqEnv_mono (fun _ hf => hf)
        (fun _ h2 => w4c_fromS2GenEnv_mono
          (fun x trG tr ck _ hs4 => w4c_tryDecryptCmkSeg4EnvOf_mono hL FmtWriteEnv x trG tr ck hs4)
          (fun x tr _ hs5 => w4c_pqRecvEnv_mono
            (fun stBs msgBs _ hr => w4c_spqrRecvC07C09aBytesEnvOf_mono hm stBs msgBs hr)
            FormatInnerEnv x tr hs5)
          _ _ tr0 st1 h2) h

/-- Direct containment from `DecPkD2cSlotOkLinked.TryDecryptCliLinkedEnv C K` into
`w4c_TryDecryptCliLinkedEnvOf LoopAdvEnv maxOps C K` whenever `CmkLoopAdvanceEvs ⊆ LoopAdvEnv` and
`83 ≤ maxOps` (in particular at `(CmkLoopAdvanceEvs, 109)`). -/
theorem w4c_tryDecryptCliLinkedEnv_sub {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    (hL : W4LoopAdvSub CmkLoopAdvanceEvs LoopAdvEnv) (hm : 83 ≤ maxOps)
    {C : Crypto} {K : MlKem} {a : TryDecryptEnvArgs} {evs : List AllocEvent}
    (h : TryDecryptCliLinkedEnv C K a evs) :
    w4c_TryDecryptCliLinkedEnvOf LoopAdvEnv maxOps C K a evs :=
  w4c_tryDecryptCliLinkedEnvOf_mono hL hm h

/-! ## Witness-Free `Cmk`-Widened Call Bundles, Parameter Bundles, & Binary Slot Envelopes -/

/-- Bundled call arguments for one linked `try_decrypt_with_state` invocation in W4. -/
structure W4TryDecryptCallCmk : Type where
  a : TryDecryptEnvArgs

/-- Bundled call arguments for one failed cloned-session `try_decrypt` trial plus its receiver-chain
`cmk` / SPQR temporary buffer drop list (`optDeallocListEvs failDropPairs`). -/
structure W4FailedTryDecryptCallCmk : Type where
  td : W4TryDecryptCallCmk
  failDropPairs : List (Nat × Nat)

/-- Bundled call parameters for one archived-session `PrevDec` + `try_decrypt_pq` + drop iteration. -/
structure W4ArchivedTrialCmk : Type where
  r_dec : SessionRecord (List (BitVec 8))
  G_dec : SessionGhost
  st_dec : SessionState (List (BitVec 8))
  G_tr : SessionGhost
  ses_tr : Session (List (BitVec 8))
  fc_tr : W4FailedTryDecryptCallCmk

/-- Failed-trial `try_decrypt` + drop-cancellation envelope (`Δlive = 0`). -/
def W4FailedTdCancelCmkEnvOf (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem) (fc : W4FailedTryDecryptCallCmk)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    ConcatEnv (w4c_TryDecryptCliLinkedFailEnvOf LoopAdvEnv maxOps C K fc.td.a)
      (· = optDeallocListEvs fc.failDropPairs) evs

/-- Archived-trial `PrevDec` deserialization envelope (`SessDeserializeCancelEnv`). -/
def W4TrialDecCmkEnv (x : W4ArchivedTrialCmk) (evs : List AllocEvent) : Prop :=
  SessDeserializeCancelEnv x.r_dec evs

/-- Archived-trial version-mismatch (`FreeOnlyEvs`) or widened cloned-session failed
`try_decrypt_pq` envelope (`W4TryDecryptCloneFailWideEnv`). -/
def W4TrialRunWideCmkEnvOf (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (C : Crypto) (K : MlKem) (x : W4ArchivedTrialCmk)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    W4TryDecryptCloneFailWideEnv (SegCloneEnv x.G_tr x.ses_tr.state)
      (W4FailedTdCancelCmkEnvOf LoopAdvEnv maxOps C K x.fc_tr)
      (· = dropClonedSessionEvents x.G_tr x.ses_tr.state) evs

/-- Archived-trial deterministic `SessionStructure` drop envelope (`Block 6`). -/
def W4TrialDropCmkEnv (x : W4ArchivedTrialCmk) (evs : List AllocEvent) : Prop :=
  evs = dropSessionStructureLocal1Events x.G_dec x.st_dec

/-- Concrete parameter bundle for the `CmkLoopAdvanceEvs`-widened W4 (`recv-prekey`) CLI slot
(independent of `(LoopAdvEnv, maxOps)`, carrying full `C : Crypto` and `K : MlKem`). -/
structure W4RecvPrekeyRealParamsCmk : Type where
  C : Crypto
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
  fc_cur : W4FailedTryDecryptCallCmk
  archivedTrials : List W4ArchivedTrialCmk
  isPathB : Bool
  td_B : W4TryDecryptCallCmk
  isPathAC : Bool
  td_AC : W4TryDecryptCallCmk
  g_arch : RecordGhost
  r_arch : SessionRecord (List (BitVec 8))
  g_out0 : RecordGhost
  r_out0 : SessionRecord (List (BitVec 8))
  G_out1 : SessionGhost
  sess_out1 : Session (List (BitVec 8))
  enc_prev1 : List (BitVec 8)

/-- Parameter bundle for the binary-kit `Cmk`-widened W4 (`recv-prekey`) slot envelope. -/
structure W4BinaryRecvPrekeyParamsCmk : Type where
  base : W4RecvPrekeyRealParamsCmk
  remoteIdKey : IdentityKey
  baseKey : PublicKey

/-- `W4DecryptPrekeySlotParams` wired to `StoresGhost.opened`, `RecordDeserializeCancelEnv`, and
`w4c_TryDecryptCliLinkedEnvOf LoopAdvEnv maxOps R.C R.K`. -/
def mkW4RecvPrekeyWideCmkSlotParamsOf (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
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
    if R.hasCurSession then W4FailedTdCancelCmkEnvOf LoopAdvEnv maxOps R.C R.K R.fc_cur
    else fun _ => False
  DecEnv := W4TrialDecCmkEnv
  TrialEnv := W4TrialRunWideCmkEnvOf LoopAdvEnv maxOps R.C R.K
  DropEnv := W4TrialDropCmkEnv
  archivedTrials := R.archivedTrials
  g_arch := R.g_arch
  r_arch := R.r_arch
  VecPushEnv := W4BoundedEvs 1 192
  TryDecEnv :=
    if R.isPathB then w4c_TryDecryptCliLinkedEnvOf LoopAdvEnv maxOps R.C R.K R.td_B.a
    else fun _ => False
  g_out0 := R.g_out0
  r_out0 := R.r_out0
  G_out1 := R.G_out1
  sess_out1 := R.sess_out1
  enc_prev1 := R.enc_prev1

/-- Path A / Path C Stage-P3 `try_decrypt` envelope at `(LoopAdvEnv, maxOps)`. -/
def W4RecvPrekeyTryDecACCmkEnvOf (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (R : W4RecvPrekeyRealParamsCmk) (evs : List AllocEvent) : Prop :=
  if R.isPathAC then w4c_TryDecryptCliLinkedEnvOf LoopAdvEnv maxOps R.C R.K R.td_AC.a evs
  else False

/-- Binary-kit Path B (`Matched`) Stages P1 → P2 → P3 → P4 envelope at `(LoopAdvEnv, maxOps)`. -/
def W4BinaryRecvPrekeyPathBWideCmkEnvOf (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  let P := mkW4RecvPrekeyWideCmkSlotParamsOf LoopAdvEnv maxOps w.base
  SeqEnv (W4BinaryStageP1OkEnv w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2MatchedWideEnv P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials
          w.base.g_arch w.base.r_arch))
      (SeqEnv (OptStageEnv (W4StageP3WideEnv W4CloneBDomEnv P.TryDecEnv))
        (OptStageEnv
          (W4BinaryStageP4MatchedWideEnv w.base.rd w.base.files w.base.peer w.remoteIdKey
            w.base.g_out0 w.base.r_out0)))) evs

/-- Binary-kit Path A (`0`-prev) Stages P1 → P2 → P3 → P4 envelope at `W4BinaryStageP4PathAWideEnvFixed`
and `(LoopAdvEnv, maxOps)`. -/
def W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  SeqEnv (W4BinaryStageP1OkEnv w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2PathAWideEnv w.base.hasOpk w.base.rd w.base.files
          w.base.spkId w.base.kpkId w.base.opkId w.base.C.F w.base.x_res w.base.x_spqr))
      (SeqEnv
        (OptStageEnv
          (W4StageP3WideEnv W4CloneACDomEnv
            (W4RecvPrekeyTryDecACCmkEnvOf LoopAdvEnv maxOps w.base)))
        (OptStageEnv
          (W4BinaryStageP4PathAWideEnvFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
            w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
            w.base.g_out0 w.base.r_out0)))) evs

/-- Binary-kit Path C (`Over` / `prev1`) Stages P1 → P2 → P3 → P4 envelope at
`W4BinaryStageP4PathCWideEnvFixed` and `(LoopAdvEnv, maxOps)`. -/
def W4BinaryRecvPrekeyPathCWideCmkEnvFixedOf (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  let P := mkW4RecvPrekeyWideCmkSlotParamsOf LoopAdvEnv maxOps w.base
  SeqEnv (W4BinaryStageP1OkEnv w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2PathCWideEnv w.base.G_cur w.base.st_cur P.CurTrialFailEnv
          P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials w.base.g_arch w.base.r_arch
          w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
          w.base.C.F w.base.x_res w.base.x_spqr))
      (SeqEnv
        (OptStageEnv
          (W4StageP3WideEnv W4CloneACDomEnv
            (W4RecvPrekeyTryDecACCmkEnvOf LoopAdvEnv maxOps w.base)))
        (OptStageEnv
          (W4BinaryStageP4PathCWideEnvFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
            w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
            w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) evs

/-- Complete 4-arm binary-kit W4 (`recv-prekey`) slot envelope at `W4BinaryKpkMarkStepEnvFixed` on
Paths A and C (collapsed target of `w4c_wideSlotEnvCmkAllFixed_eq_fixed` under `CliPqxdhInputs`). -/
def W4BinaryRecvPrekeyWideSlotEnvCmkFixedOf (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4BinaryStageP1UntrustedEnv w.base.rd w.base.files w.base.peer w.remoteIdKey e ∨
      W4BinaryRecvPrekeyPathBWideCmkEnvOf LoopAdvEnv maxOps w e ∨
      W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf LoopAdvEnv maxOps w e ∨
      W4BinaryRecvPrekeyPathCWideCmkEnvFixedOf LoopAdvEnv maxOps w e)
    FreeOnlyEvs evs

/-- Complete 4-arm binary-kit W4 (`recv-prekey`) slot envelope with `ReadFileRuleEnvFixed` on all
store-kit `Dir::get` steps at `(LoopAdvEnv, maxOps)`. -/
def W4BinaryRecvPrekeyWideSlotEnvCmkAllFixedOf (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  let P := mkW4RecvPrekeyWideCmkSlotParamsOf LoopAdvEnv maxOps w.base
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
                (W4RecvPrekeyTryDecACCmkEnvOf LoopAdvEnv maxOps w.base)))
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
              (W4StageP3WideEnv W4CloneACDomEnv
                (W4RecvPrekeyTryDecACCmkEnvOf LoopAdvEnv maxOps w.base)))
            (OptStageEnv
              (W4BinaryStageP4PathCWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
                w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) e)
    FreeOnlyEvs evs

/-- Under `CliPqxdhInputs P i` (`w.base.files = runFiles i`, `w.base.rd = cliIo.rd`), all 9
non-`kpkMark` store steps in `W4BinaryRecvPrekeyWideSlotEnvCmkAllFixedOf` satisfy `¬ OverCapFile`,
collapsing `AllFixed` to `W4BinaryRecvPrekeyWideSlotEnvCmkFixedOf`. -/
theorem w4c_wideSlotEnvCmkAllFixed_eq_fixed {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {w : W4BinaryRecvPrekeyParamsCmk}
    (hfiles : w.base.files = runFiles i) (hrd : w.base.rd = cliIo.rd) :
    W4BinaryRecvPrekeyWideSlotEnvCmkAllFixedOf LoopAdvEnv maxOps w =
      W4BinaryRecvPrekeyWideSlotEnvCmkFixedOf LoopAdvEnv maxOps w := by
  have hsessLoad : ∀ a : AddrVal,
      cliSessionKitLoadPollEnv cliIo.rd scopeKit (AddrTextValEnv DecimalEnv)
          (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          (ofBytesEnv RecordDeserializeCancelEnv) (runFiles i) StoresGhost.opened.sessions a =
        cliSessionKitLoadPollEnv cliIo.rd scopeKit (AddrTextValEnv DecimalEnv)
          (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
          (ofBytesEnv RecordDeserializeCancelEnv) (runFiles i) StoresGhost.opened.sessions a := by
    intro a
    unfold cliSessionKitLoadPollEnv
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_sessions hi _)]
  have htrustPoll : ∀ (a : AddrVal) (k : IdentityKey) (d : Direction),
      cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          (runFiles i) StoresGhost.opened.identity a k d =
        cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
          (runFiles i) StoresGhost.opened.identity a k d := by
    intro a k d
    unfold cliIdentityKitTrustPollEnv
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_identities hi _)]
  have hsavePoll : ∀ (a : AddrVal) (k : IdentityKey),
      cliIdentityKitSavePollEnv cliIo.rd (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          DirPutStrEnv (runFiles i) StoresGhost.opened.identity a k =
        cliIdentityKitSavePollEnv cliIo.rd (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
          DirPutStrEnv (runFiles i) StoresGhost.opened.identity a k := by
    intro a k
    unfold cliIdentityKitSavePollEnv
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_identities hi _)]
  have hsess : ∀ peer,
      W4BinarySessLoadStepEnvAllFixed cliIo.rd (runFiles i) peer =
        CliRealBinaryKitEnvs.W4BinarySessLoadStepEnv cliIo.rd (runFiles i) peer := by
    intro peer
    unfold W4BinarySessLoadStepEnvAllFixed CliRealBinaryKitEnvs.W4BinarySessLoadStepEnv
    rw [hsessLoad peer.val]
  have htrust : ∀ peer k,
      W4BinaryIdTrustStepEnvAllFixed cliIo.rd (runFiles i) peer k =
        CliRealBinaryKitEnvs.W4BinaryIdTrustStepEnv cliIo.rd (runFiles i) peer k := by
    intro peer k
    unfold W4BinaryIdTrustStepEnvAllFixed CliRealBinaryKitEnvs.W4BinaryIdTrustStepEnv
    rw [htrustPoll peer.val k .receiving]
  have hsave : ∀ peer k,
      W4BinaryIdSaveStepEnvAllFixed cliIo.rd (runFiles i) peer k =
        CliRealBinaryKitEnvs.W4BinaryIdSaveStepEnv cliIo.rd (runFiles i) peer k := by
    intro peer k
    unfold W4BinaryIdSaveStepEnvAllFixed CliRealBinaryKitEnvs.W4BinaryIdSaveStepEnv
    rw [hsavePoll peer.val k]
  have hspk : ∀ id,
      W4BinarySpkGetStepEnvAllFixed cliIo.rd (runFiles i) id =
        CliRealBinaryKitEnvs.W4BinarySpkGetStepEnv cliIo.rd (runFiles i) id := by
    intro id
    unfold W4BinarySpkGetStepEnvAllFixed CliRealBinaryKitEnvs.W4BinarySpkGetStepEnv CliSpkGetPollEnv
    dsimp only
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_signed hi _)]
  have hkpk : ∀ id,
      W4BinaryKpkGetStepEnvAllFixed cliIo.rd (runFiles i) id =
        CliRealBinaryKitEnvs.W4BinaryKpkGetStepEnv cliIo.rd (runFiles i) id := by
    intro id
    unfold W4BinaryKpkGetStepEnvAllFixed CliRealBinaryKitEnvs.W4BinaryKpkGetStepEnv CliKpkGetPollEnv
      LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkGetPoll.LayoutBudget.KpkPassEnv
    dsimp only
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_kyberOneTime hi _),
      dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_kyberLastResort_keyName hi id)]
  have hpk : ∀ id,
      W4BinaryPkGetStepEnvAllFixed cliIo.rd (runFiles i) id =
        CliRealBinaryKitEnvs.W4BinaryPkGetStepEnv cliIo.rd (runFiles i) id := by
    intro id
    unfold W4BinaryPkGetStepEnvAllFixed CliRealBinaryKitEnvs.W4BinaryPkGetStepEnv CliPkGetPollEnv
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
    intro id
    unfold W4BinaryPkRemoveStepEnvAllFixed W4BinaryPkRemoveStepEnv CliPkRemovePollEnv
    dsimp only
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_oneTime hi _)]
  have hp1ok : ∀ peer k,
      W4BinaryStageP1OkEnvAllFixed cliIo.rd (runFiles i) peer k =
        W4BinaryStageP1OkEnv cliIo.rd (runFiles i) peer k := by
    intro peer k; funext evs
    unfold W4BinaryStageP1OkEnvAllFixed W4BinaryStageP1OkEnv
    rw [hsess, htrust]
  have hp1un : ∀ peer k,
      W4BinaryStageP1UntrustedEnvAllFixed cliIo.rd (runFiles i) peer k =
        W4BinaryStageP1UntrustedEnv cliIo.rd (runFiles i) peer k := by
    intro peer k; funext evs
    unfold W4BinaryStageP1UntrustedEnvAllFixed W4BinaryStageP1UntrustedEnv
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
      W4BinaryStageP4PathAWideEnvAllFixed hasOpk cliIo.rd (runFiles i) peer k kpkId spkId opkId bk g_out0 r_out0 =
        W4BinaryStageP4PathAWideEnvFixed hasOpk cliIo.rd (runFiles i) peer k kpkId spkId opkId bk g_out0 r_out0 := by
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
  unfold W4BinaryRecvPrekeyWideSlotEnvCmkAllFixedOf W4BinaryRecvPrekeyWideSlotEnvCmkFixedOf
    W4BinaryRecvPrekeyPathBWideCmkEnvOf W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf
    W4BinaryRecvPrekeyPathCWideCmkEnvFixedOf
  dsimp only
  rw [hfiles, hrd, hp1un, hp1ok, hp2a, hp2c, hp4m, hp4a, hp4c]

/-! ## Monotonicity in `(LoopAdvEnv, maxOps)` Across All Slot Envelopes -/

private theorem w4c_optStageEnv_mono {E₁ E₂ : List AllocEvent → Prop}
    (hE : ∀ evs, E₁ evs → E₂ evs) (evs : List AllocEvent)
    (h : OptStageEnv E₁ evs) : OptStageEnv E₂ evs :=
  h.elim Or.inl (fun h2 => Or.inr (hE evs h2))

private theorem w4c_iterSeqEnv_mono {α : Type} {S₁ S₂ : α → List AllocEvent → Prop}
    (hS : ∀ x evs, S₁ x evs → S₂ x evs) :
    ∀ (xs : List α) (evs : List AllocEvent),
      IterSeqEnv S₁ xs evs → IterSeqEnv S₂ xs evs
  | [], _, h => h
  | x :: xs, _, h =>
    seqEnv_mono (fun e hx => hS x e hx) (fun e hxs => w4c_iterSeqEnv_mono hS xs e hxs) h

private theorem w4c_archivedTrialIterEnv_mono {α : Type}
    {DecEnv T₁ T₂ DropEnv : α → List AllocEvent → Prop}
    (hT : ∀ x evs, T₁ x evs → T₂ x evs) (x : α) (evs : List AllocEvent)
    (h : ArchivedTrialIterEnv DecEnv T₁ DropEnv x evs) :
    ArchivedTrialIterEnv DecEnv T₂ DropEnv x evs :=
  ConcatEnv.mono
    (fun _ h12 => ConcatEnv.mono (fun _ hd => hd) (fun e ht => hT x e ht) h12)
    (fun _ hdr => hdr) h

private theorem w4c_cloneFailWideEnv_mono {CloneEnv F₁ F₂ DropCloneEnv : List AllocEvent → Prop}
    (hF : ∀ evs, F₁ evs → F₂ evs) (evs : List AllocEvent)
    (h : W4TryDecryptCloneFailWideEnv CloneEnv F₁ DropCloneEnv evs) :
    W4TryDecryptCloneFailWideEnv CloneEnv F₂ DropCloneEnv evs :=
  seqEnv_mono
    (fun _ hc => ConcatEnv.mono
      (fun _ h12 => ConcatEnv.mono (fun _ hcl => hcl) (fun e hf => hF e hf) h12)
      (fun _ hd => hd) hc)
    (fun _ ht => ht) h

private theorem w4c_stageP3WideEnv_mono {CloneEnv T₁ T₂ : List AllocEvent → Prop}
    (hT : ∀ evs, T₁ evs → T₂ evs) (evs : List AllocEvent)
    (h : W4StageP3WideEnv CloneEnv T₁ evs) :
    W4StageP3WideEnv CloneEnv T₂ evs :=
  seqEnv_mono (fun _ hc => hc)
    (fun _ h2 => seqEnv_mono (fun e ho => w4c_optStageEnv_mono hT e ho) (fun _ ht => ht) h2) h

private theorem w4c_failedTdCancelCmkEnvOf_mono {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    {C : Crypto} {K : MlKem} {fc : W4FailedTryDecryptCallCmk} {evs : List AllocEvent}
    (h : W4FailedTdCancelCmkEnvOf L₁ m₁ C K fc evs) :
    W4FailedTdCancelCmkEnvOf L₂ m₂ C K fc evs :=
  h.elim Or.inl fun hc => Or.inr (ConcatEnv.mono
    (fun _ ht => w4c_tryDecryptCliLinkedFailEnvOf_mono hL hm ht)
    (fun _ hd => hd) hc)

private theorem w4c_trialRunWideCmkEnvOf_mono {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    {C : Crypto} {K : MlKem} (x : W4ArchivedTrialCmk) {evs : List AllocEvent}
    (h : W4TrialRunWideCmkEnvOf L₁ m₁ C K x evs) :
    W4TrialRunWideCmkEnvOf L₂ m₂ C K x evs :=
  h.elim Or.inl fun hc => Or.inr (w4c_cloneFailWideEnv_mono
    (fun _ hf => w4c_failedTdCancelCmkEnvOf_mono hL hm hf) evs hc)

private theorem w4c_curTrialFailEnv_mono {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    (R : W4RecvPrekeyRealParamsCmk) {evs : List AllocEvent}
    (h : (mkW4RecvPrekeyWideCmkSlotParamsOf L₁ m₁ R).CurTrialFailEnv evs) :
    (mkW4RecvPrekeyWideCmkSlotParamsOf L₂ m₂ R).CurTrialFailEnv evs := by
  dsimp only [mkW4RecvPrekeyWideCmkSlotParamsOf] at h ⊢
  revert h
  cases R.hasCurSession <;> intro h
  · exact False.elim h
  · exact w4c_failedTdCancelCmkEnvOf_mono hL hm h

private theorem w4c_tryDecBEnv_mono {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    (R : W4RecvPrekeyRealParamsCmk) {evs : List AllocEvent}
    (h : (mkW4RecvPrekeyWideCmkSlotParamsOf L₁ m₁ R).TryDecEnv evs) :
    (mkW4RecvPrekeyWideCmkSlotParamsOf L₂ m₂ R).TryDecEnv evs := by
  dsimp only [mkW4RecvPrekeyWideCmkSlotParamsOf] at h ⊢
  revert h
  cases R.isPathB <;> intro h
  · exact False.elim h
  · exact w4c_tryDecryptCliLinkedEnvOf_mono hL hm h

private theorem w4c_tryDecACEnv_mono {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    (R : W4RecvPrekeyRealParamsCmk) {evs : List AllocEvent}
    (h : W4RecvPrekeyTryDecACCmkEnvOf L₁ m₁ R evs) :
    W4RecvPrekeyTryDecACCmkEnvOf L₂ m₂ R evs := by
  unfold W4RecvPrekeyTryDecACCmkEnvOf at h ⊢
  revert h
  cases R.isPathAC <;> intro h
  · exact False.elim h
  · exact w4c_tryDecryptCliLinkedEnvOf_mono hL hm h

private theorem w4c_stageP2MatchedWideEnv_mono {α : Type}
    {DecEnv T₁ T₂ DropEnv : α → List AllocEvent → Prop}
    (hT : ∀ x evs, T₁ x evs → T₂ x evs) (xs : List α)
    (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8))) (evs : List AllocEvent)
    (h : W4BinaryStageP2MatchedWideEnv DecEnv T₁ DropEnv xs g_arch r_arch evs) :
    W4BinaryStageP2MatchedWideEnv DecEnv T₂ DropEnv xs g_arch r_arch evs :=
  seqEnv_mono (fun _ hc => hc)
    (fun e ho => w4c_optStageEnv_mono
      (fun _ h2 => h2.elim Or.inl fun hs => Or.inr (seqEnv_mono
        (fun e1 hi => w4c_iterSeqEnv_mono (w4c_archivedTrialIterEnv_mono hT) xs e1 hi)
        (fun _ hp => hp) hs)) e ho) h

private theorem w4c_stageP2PathCWideEnv_mono {α : Type}
    {G_cur : SessionGhost} {st_cur : SessionState (List (BitVec 8))}
    {C₁ C₂ : List AllocEvent → Prop}
    {DecEnv T₁ T₂ DropEnv : α → List AllocEvent → Prop}
    (hC : ∀ evs, C₁ evs → C₂ evs) (hT : ∀ x evs, T₁ x evs → T₂ x evs)
    (xs : List α) (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (spkId kpkId opkId : BitVec 32)
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    (evs : List AllocEvent)
    (h : W4BinaryStageP2PathCWideEnv G_cur st_cur C₁ DecEnv T₁ DropEnv xs g_arch r_arch
      hasOpk rd files spkId kpkId opkId F x_res x_spqr evs) :
    W4BinaryStageP2PathCWideEnv G_cur st_cur C₂ DecEnv T₂ DropEnv xs g_arch r_arch
      hasOpk rd files spkId kpkId opkId F x_res x_spqr evs :=
  seqEnv_mono
    (fun e hc => w4c_optStageEnv_mono (w4c_cloneFailWideEnv_mono hC) e hc)
    (fun _ h2 => seqEnv_mono
      (fun e hl => w4c_optStageEnv_mono
        (w4c_iterSeqEnv_mono (w4c_archivedTrialIterEnv_mono hT) xs) e hl)
      (fun _ hrest => hrest) h2) h

private theorem w4c_stageP2PathCWideEnvAllFixed_mono {α : Type}
    {G_cur : SessionGhost} {st_cur : SessionState (List (BitVec 8))}
    {C₁ C₂ : List AllocEvent → Prop}
    {DecEnv T₁ T₂ DropEnv : α → List AllocEvent → Prop}
    (hC : ∀ evs, C₁ evs → C₂ evs) (hT : ∀ x evs, T₁ x evs → T₂ x evs)
    (xs : List α) (g_arch : RecordGhost) (r_arch : SessionRecord (List (BitVec 8)))
    (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (spkId kpkId opkId : BitVec 32)
    (F : ShaCompress) (x_res : DoReserveCall) (x_spqr : InitialStateGhost)
    (evs : List AllocEvent)
    (h : W4BinaryStageP2PathCWideEnvAllFixed G_cur st_cur C₁ DecEnv T₁ DropEnv xs g_arch r_arch
      hasOpk rd files spkId kpkId opkId F x_res x_spqr evs) :
    W4BinaryStageP2PathCWideEnvAllFixed G_cur st_cur C₂ DecEnv T₂ DropEnv xs g_arch r_arch
      hasOpk rd files spkId kpkId opkId F x_res x_spqr evs :=
  seqEnv_mono
    (fun e hc => w4c_optStageEnv_mono (w4c_cloneFailWideEnv_mono hC) e hc)
    (fun _ h2 => seqEnv_mono
      (fun e hl => w4c_optStageEnv_mono
        (w4c_iterSeqEnv_mono (w4c_archivedTrialIterEnv_mono hT) xs) e hl)
      (fun _ hrest => hrest) h2) h

theorem w4c_wideSlotEnvCmkFixed_mono {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    {w : W4BinaryRecvPrekeyParamsCmk} {evs : List AllocEvent}
    (h : W4BinaryRecvPrekeyWideSlotEnvCmkFixedOf L₁ m₁ w evs) :
    W4BinaryRecvPrekeyWideSlotEnvCmkFixedOf L₂ m₂ w evs := by
  rcases h with hfr | hseq
  · exact Or.inl hfr
  · refine Or.inr (seqEnv_mono (fun e harm => ?_) (fun _ hfr => hfr) hseq)
    rcases harm with hun | hb | ha | hc
    · exact Or.inl hun
    · refine Or.inr (Or.inl ?_)
      exact seqEnv_mono (fun _ hp1 => hp1)
        (fun _ h2 => seqEnv_mono
          (fun e2 hp2 => w4c_optStageEnv_mono
            (w4c_stageP2MatchedWideEnv_mono (fun x _ ht => w4c_trialRunWideCmkEnvOf_mono hL hm x ht)
              w.base.archivedTrials w.base.g_arch w.base.r_arch) e2 hp2)
          (fun _ h3 => seqEnv_mono
            (fun e3 hp3 => w4c_optStageEnv_mono
              (w4c_stageP3WideEnv_mono (fun _ ht => w4c_tryDecBEnv_mono hL hm w.base ht)) e3 hp3)
            (fun _ hp4 => hp4) h3) h2) hb
    · refine Or.inr (Or.inr (Or.inl ?_))
      exact seqEnv_mono (fun _ hp1 => hp1)
        (fun _ h2 => seqEnv_mono (fun _ hp2 => hp2)
          (fun _ h3 => seqEnv_mono
            (fun e3 hp3 => w4c_optStageEnv_mono
              (w4c_stageP3WideEnv_mono (fun _ ht => w4c_tryDecACEnv_mono hL hm w.base ht)) e3 hp3)
            (fun _ hp4 => hp4) h3) h2) ha
    · refine Or.inr (Or.inr (Or.inr ?_))
      exact seqEnv_mono (fun _ hp1 => hp1)
        (fun _ h2 => seqEnv_mono
          (fun e2 hp2 => w4c_optStageEnv_mono
            (w4c_stageP2PathCWideEnv_mono
              (fun _ hc => w4c_curTrialFailEnv_mono hL hm w.base hc)
              (fun x _ ht => w4c_trialRunWideCmkEnvOf_mono hL hm x ht)
              w.base.archivedTrials w.base.g_arch w.base.r_arch
              w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
              w.base.C.F w.base.x_res w.base.x_spqr) e2 hp2)
          (fun _ h3 => seqEnv_mono
            (fun e3 hp3 => w4c_optStageEnv_mono
              (w4c_stageP3WideEnv_mono (fun _ ht => w4c_tryDecACEnv_mono hL hm w.base ht)) e3 hp3)
            (fun _ hp4 => hp4) h3) h2) hc

theorem w4c_wideSlotEnvCmkAllFixed_mono {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    {w : W4BinaryRecvPrekeyParamsCmk} {evs : List AllocEvent}
    (h : W4BinaryRecvPrekeyWideSlotEnvCmkAllFixedOf L₁ m₁ w evs) :
    W4BinaryRecvPrekeyWideSlotEnvCmkAllFixedOf L₂ m₂ w evs := by
  rcases h with hfr | hseq
  · exact Or.inl hfr
  · refine Or.inr (seqEnv_mono (fun e harm => ?_) (fun _ hfr => hfr) hseq)
    rcases harm with hun | hb | ha | hc
    · exact Or.inl hun
    · refine Or.inr (Or.inl ?_)
      exact seqEnv_mono (fun _ hp1 => hp1)
        (fun _ h2 => seqEnv_mono
          (fun e2 hp2 => w4c_optStageEnv_mono
            (w4c_stageP2MatchedWideEnv_mono (fun x _ ht => w4c_trialRunWideCmkEnvOf_mono hL hm x ht)
              w.base.archivedTrials w.base.g_arch w.base.r_arch) e2 hp2)
          (fun _ h3 => seqEnv_mono
            (fun e3 hp3 => w4c_optStageEnv_mono
              (w4c_stageP3WideEnv_mono (fun _ ht => w4c_tryDecBEnv_mono hL hm w.base ht)) e3 hp3)
            (fun _ hp4 => hp4) h3) h2) hb
    · refine Or.inr (Or.inr (Or.inl ?_))
      exact seqEnv_mono (fun _ hp1 => hp1)
        (fun _ h2 => seqEnv_mono (fun _ hp2 => hp2)
          (fun _ h3 => seqEnv_mono
            (fun e3 hp3 => w4c_optStageEnv_mono
              (w4c_stageP3WideEnv_mono (fun _ ht => w4c_tryDecACEnv_mono hL hm w.base ht)) e3 hp3)
            (fun _ hp4 => hp4) h3) h2) ha
    · refine Or.inr (Or.inr (Or.inr ?_))
      exact seqEnv_mono (fun _ hp1 => hp1)
        (fun _ h2 => seqEnv_mono
          (fun e2 hp2 => w4c_optStageEnv_mono
            (w4c_stageP2PathCWideEnvAllFixed_mono
              (fun _ hc => w4c_curTrialFailEnv_mono hL hm w.base hc)
              (fun x _ ht => w4c_trialRunWideCmkEnvOf_mono hL hm x ht)
              w.base.archivedTrials w.base.g_arch w.base.r_arch
              w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
              w.base.C.F w.base.x_res w.base.x_spqr) e2 hp2)
          (fun _ h3 => seqEnv_mono
            (fun e3 hp3 => w4c_optStageEnv_mono
              (w4c_stageP3WideEnv_mono (fun _ ht => w4c_tryDecACEnv_mono hL hm w.base ht)) e3 hp3)
            (fun _ hp4 => hp4) h3) h2) hc

/-! ## Witness-Free Domain Predicates -/

/-- Pure model-only domain bounds for one `W4TryDecryptCallCmk`:
- `td.a.st.receiverChains.length ≤ 5` (bounds `DhCommitStep3Budget` `grow_one` to `104 * 8 = 832` B
  in small class regardless of `td.a.G.chainsCap`),
- `∀ c ∈ td.a.st.receiverChains, c.messageKeys.length ≤ 2000` (pre-call skipped-key list bound),
- `TopStateTight F K td.a.st.pqRatchetState`,
- `td.a.msg.ciphertext.length ≤ maxCt`.
Note: `Mut.exec TripleRatchet.fromSessionState td.a.st` fixes `maxForwardJumps = 25000` automatically. -/
structure W4TryDecryptCallDomCmkOf (F : ShaCompress) (K : MlKem) (maxCt : Nat)
    (td : W4TryDecryptCallCmk) : Prop where
  rc_len_le : td.a.st.receiverChains.length ≤ 5
  mk_len_le : ∀ c ∈ td.a.st.receiverChains, c.messageKeys.length ≤ 2000
  top_tight : TopStateTight F K td.a.st.pqRatchetState
  ct_le : td.a.msg.ciphertext.length ≤ maxCt

/-- Pure domain bounds for a fresh-Bob Path A / Path C `try_decrypt` (`pathAInitState` has
`receiverChains = []`). -/
structure W4TryDecryptPathACDomCmkOf (F : ShaCompress) (K : MlKem) (maxCt : Nat)
    (td : W4TryDecryptCallCmk) : Prop where
  base : W4TryDecryptCallDomCmkOf F K maxCt td
  rc_nil : td.a.st.receiverChains = []

/-- Pure domain bounds for a failed `try_decrypt` trial with drop cancellation (`Δlive = 0`). -/
structure W4FailedTdDomCmkOf (F : ShaCompress) (K : MlKem) (maxCt : Nat)
    (fc : W4FailedTryDecryptCallCmk) : Prop where
  td_dom : W4TryDecryptCallDomCmkOf F K maxCt fc.td
  align_le : ∀ p ∈ fc.failDropPairs, p.2 ≤ 16
  cancel_live : w2CmkChainTightLive 2000 + 605066 ≤ optDeallocListLarge fineCostModel fc.failDropPairs

/-- Pure domain bounds for one archived-session trial (`PrevDec` + trial + `SessionStructure` drop). -/
structure W4ArchivedTrialDomCmkOf (F : ShaCompress) (K : MlKem) (maxCt : Nat)
    (x : W4ArchivedTrialCmk) : Prop where
  enc_le : (encodeRecord x.r_dec).length ≤ deserCancelFineMaxReq
  live_le_peak : sessDeserLargeLive fineCostModel x.r_dec ≤ deserCancelFinePeak
  live_le_drop :
    sessDeserLargeLive fineCostModel x.r_dec ≤ ssStateLargeLive fineCostModel x.G_dec x.st_dec
  drop_caps : SessionDropCapsOk x.G_dec x.st_dec
  tr_gv : SessionGhostValid x.G_tr x.ses_tr
  tr_dom : SessionCloneDom 286196 x.ses_tr
  tr_fail : W4FailedTdDomCmkOf F K maxCt x.fc_tr

/-- Parametric `(smallFileCap, maxCt)` domain bundle for `W4RecvPrekeyRealParamsCmk`. -/
structure W4RecvPrekeyRealDomCmkOf (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (smallFileCap maxCt : Nat) (R : W4RecvPrekeyRealParamsCmk) : Prop where
  kpk_dir : R.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            R.kpkDir = StoresGhost.opened.kyber.lastResort
  outer_dom : W4DecryptPrekeyTightDom (mkW4RecvPrekeyWideCmkSlotParamsOf LoopAdvEnv maxOps R)
    2097152 smallFileCap 286196 286196 2097152 286196 2097152 16384 2097152 2457152 4096
  cur_fail_dom : R.hasCurSession = true → W4FailedTdDomCmkOf R.C.F R.K maxCt R.fc_cur
  trials_dom : ∀ x ∈ R.archivedTrials, W4ArchivedTrialDomCmkOf R.C.F R.K maxCt x
  tdB_dom : R.isPathB = true → W4TryDecryptCallDomCmkOf R.C.F R.K maxCt R.td_B
  tdAC_dom : R.isPathAC = true → W4TryDecryptPathACDomCmkOf R.C.F R.K maxCt R.td_AC

/-- Call-site domain guard on `W4RecvPrekeyRealParamsCmk` (independent of `(LoopAdvEnv, maxOps)`).
`cur_dom` uses `R.hasCurSession = false` as its left disjunct, immediately discharging
`∀ evs, ¬ (mkW4RecvPrekeyWideCmkSlotParamsOf LoopAdvEnv maxOps R).CurTrialFailEnv evs` when
`hasCurSession = false`. -/
structure W4BinaryCallSiteDomCmk (C : Crypto) (K : MlKem) (maxCt : Nat)
    (peerVal : AddrVal) (files : FsFiles) (R : W4RecvPrekeyRealParamsCmk) : Prop where
  eq_C : R.C = C
  eq_K : R.K = K
  eq_rd : R.rd = cliIo.rd
  eq_files : R.files = files
  eq_peerVal : R.peer.val = peerVal
  kpk_dir : R.kpkDir = StoresGhost.opened.kyber.oneTime ∨
            R.kpkDir = StoresGhost.opened.kyber.lastResort
  ownKey_len : R.ownKeyName.length ≤ 64
  ownReg_len : R.ownRegName.length ≤ 64
  kpkMark_len : R.kpkMarkName.length ≤ 64
  res_old : R.x_res.cap.toNat ≤ 4096
  res_new : reserveCap R.x_res.cap.toNat R.x_res.bs.length R.x_res.additional ≤ 4096
  spqr_key : R.x_spqr.p.authKey.length ≤ 32
  cur_dom : R.hasCurSession = false ∨
    ∃ ses_cur : Session (List (BitVec 8)),
      ses_cur.state = R.st_cur ∧ SessionGhostValid R.G_cur ses_cur ∧
        SessionCloneDom 286196 ses_cur
  arch_valid : ∀ G ses, R.g_arch.cur = some G → R.r_arch.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom 286196 ses
  arch_enc : (encodeRecord R.r_arch).length ≤ 2097152
  out0_valid : ∀ G ses, R.g_out0.cur = some G → R.r_out0.currentSession = some ses →
    SessionGhostValid G ses ∧ SessionCloneDom 286196 ses
  out0_enc : (encodeRecord R.r_out0).length ≤ 2097152
  out1_freshBob : FreshBobPrev1Dom 16384 2097152 2457152 R.G_out1 R.sess_out1 R.enc_prev1
  trials_len4 : R.archivedTrials.length ≤ 4
  cur_fail_dom : R.hasCurSession = true → W4FailedTdDomCmkOf R.C.F R.K maxCt R.fc_cur
  trials_dom : ∀ y ∈ R.archivedTrials, W4ArchivedTrialDomCmkOf R.C.F R.K maxCt y
  tdB_dom : R.isPathB = true → W4TryDecryptCallDomCmkOf R.C.F R.K maxCt R.td_B
  tdAC_dom : R.isPathAC = true → W4TryDecryptPathACDomCmkOf R.C.F R.K maxCt R.td_AC

private theorem w4c_tryDecryptCallDomCmkOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {td : W4TryDecryptCallCmk}
    (h : W4TryDecryptCallDomCmkOf F K c₁ td) :
    W4TryDecryptCallDomCmkOf F K c₂ td :=
  { h with ct_le := Nat.le_trans h.ct_le hc }

private theorem w4c_failedTdDomCmkOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {fc : W4FailedTryDecryptCallCmk}
    (h : W4FailedTdDomCmkOf F K c₁ fc) :
    W4FailedTdDomCmkOf F K c₂ fc :=
  ⟨w4c_tryDecryptCallDomCmkOf_mono hc h.td_dom, h.align_le, h.cancel_live⟩

private theorem w4c_archivedTrialDomCmkOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {tr : W4ArchivedTrialCmk}
    (h : W4ArchivedTrialDomCmkOf F K c₁ tr) :
    W4ArchivedTrialDomCmkOf F K c₂ tr :=
  ⟨h.enc_le, h.live_le_peak, h.live_le_drop, h.drop_caps, h.tr_gv, h.tr_dom,
    w4c_failedTdDomCmkOf_mono hc h.tr_fail⟩

private theorem w4c_tryDecryptPathACDomCmkOf_mono {F : ShaCompress} {K : MlKem} {c₁ c₂ : Nat}
    (hc : c₁ ≤ c₂) {td : W4TryDecryptCallCmk}
    (h : W4TryDecryptPathACDomCmkOf F K c₁ td) :
    W4TryDecryptPathACDomCmkOf F K c₂ td :=
  ⟨w4c_tryDecryptCallDomCmkOf_mono hc h.base, h.rc_nil⟩

/-- Call-site lift from `W4BinaryCallSiteDomCmk` to `W4RecvPrekeyRealDomCmkOf LoopAdvEnv maxOps
sessionCapBytes msgCapBytes R` on `.recv peerV` for ANY `(LoopAdvEnv, maxOps)`. -/
theorem W4BinaryCallSiteDomCmk.toRealDomCmkOf (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    {C : Crypto} {K : MlKem} {maxCt : Nat}
    {i : Inputs} {peerV : AddrV} {files : FsFiles}
    {R : W4RecvPrekeyRealParamsCmk}
    (hcs : W4BinaryCallSiteDomCmk C K maxCt (addrValOf peerV) files R)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerV))
    (hct : maxCt ≤ msgCapBytes) :
    W4RecvPrekeyRealDomCmkOf LoopAdvEnv maxOps sessionCapBytes msgCapBytes R where
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
        (∀ evs, ¬ (mkW4RecvPrekeyWideCmkSlotParamsOf LoopAdvEnv maxOps R).CurTrialFailEnv evs) ∨
        ∃ ses_cur : Session (List (BitVec 8)),
          ses_cur.state = R.st_cur ∧ SessionGhostValid R.G_cur ses_cur ∧
            SessionCloneDom 286196 ses_cur := by
      rcases hcs.cur_dom with hfalse | hses
      · refine Or.inl fun evs hev => ?_
        dsimp only [mkW4RecvPrekeyWideCmkSlotParamsOf] at hev
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
          dsimp only [mkW4RecvPrekeyWideCmkSlotParamsOf] at hr
          rw [hcs.eq_rd] at hr
          exact Nat.le_trans (cliIo_rd_ok_length_le_sessionCapBytes R.files _ bs hr) hsess2M
        small_cap := fun d _ n bs hr => by
          dsimp only [mkW4RecvPrekeyWideCmkSlotParamsOf] at hr
          rw [hcs.eq_rd] at hr
          exact cliIo_rd_ok_length_le_sessionCapBytes R.files (pathOf d.path n) bs hr
        cur_dom := hcur
        arch_valid := hcs.arch_valid
        arch_enc := hcs.arch_enc
        out0_valid := hcs.out0_valid
        out0_enc := hcs.out0_enc
        out1_freshBob := hcs.out1_freshBob
        trials_len4 := hcs.trials_len4 }
  cur_fail_dom hcur := w4c_failedTdDomCmkOf_mono hct (hcs.cur_fail_dom hcur)
  trials_dom y hy := w4c_archivedTrialDomCmkOf_mono hct (hcs.trials_dom y hy)
  tdB_dom hb := w4c_tryDecryptCallDomCmkOf_mono hct (hcs.tdB_dom hb)
  tdAC_dom hac := w4c_tryDecryptPathACDomCmkOf_mono hct (hcs.tdAC_dom hac)

/-! ## Top-Level `DecPkGhost → List AllocEvent → Prop` Slot Envelopes & `_ghost_congr` -/

/-- `(LoopAdvEnv, maxOps)`-parametric unguarded binary-kit W4 (`decrypt_prekey`) slot envelope. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkFixedOf [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (_X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
    W4BinaryCallSiteDomCmk W.C W.Q.K x.msg.message.ciphertext.length x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      W4BinaryRecvPrekeyWideSlotEnvCmkAllFixedOf LoopAdvEnv maxOps w4 evs

/-- Default `(CmkLoopAdvanceEvs, 109)` unguarded binary-kit W4 (`decrypt_prekey`) slot envelope. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkFixed [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  realCliDecPkBinaryWideSlotEnvCmkFixedOf CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps X W x evs

theorem realCliDecPkBinaryWideSlotEnvCmkFixedOf_ghost_congr [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val)
    (_hm : x.me.val = y.me.val)
    (_hs : x.stores = y.stores)
    (_hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F)
    (_hc : x.coins = y.coins)
    (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnvCmkFixedOf LoopAdvEnv maxOps X W x =
      realCliDecPkBinaryWideSlotEnvCmkFixedOf LoopAdvEnv maxOps X W y := by
  funext evs
  simp only [realCliDecPkBinaryWideSlotEnvCmkFixedOf, hp, hf, hmsg]

theorem realCliDecPkBinaryWideSlotEnvCmkFixed_ghost_congr [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val)
    (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores)
    (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F)
    (hc : x.coins = y.coins)
    (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnvCmkFixed X W x =
      realCliDecPkBinaryWideSlotEnvCmkFixed X W y :=
  realCliDecPkBinaryWideSlotEnvCmkFixedOf_ghost_congr
    CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps X W x y hp hm hs hcp hf hc hmsg

theorem realCliDecPkBinaryWideSlotEnvCmkFixedOf_mono [LibsignalPlacement]
    {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {x : DecPkGhost} {evs : List AllocEvent}
    (h : realCliDecPkBinaryWideSlotEnvCmkFixedOf L₁ m₁ X W x evs) :
    realCliDecPkBinaryWideSlotEnvCmkFixedOf L₂ m₂ X W x evs := by
  obtain ⟨w4, hcs, hik, hbk, henv⟩ := h
  exact ⟨w4, hcs, hik, hbk, w4c_wideSlotEnvCmkAllFixed_mono hL hm henv⟩

/-- `(LoopAdvEnv, maxOps)`-parametric `PeerSpqrStateTight640`-guarded binary-kit `decrypt_prekey`
slot envelope.

When `¬ PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val`, the envelope reduces to `fun _ => True`
(`⊤`), so any slot or `run` specification instantiated at this envelope has an unsatisfiable
precondition `FitsEnv M lim st (fun _ => True)` at finite `lim` (`IfaceBudgetLemmas.lean:378`). -/
abbrev realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
    realCliDecPkBinaryWideSlotEnvCmkFixedOf LoopAdvEnv maxOps X W x evs

/-- Default `(CmkLoopAdvanceEvs, 109)` `PeerSpqrStateTight640`-guarded binary-kit `decrypt_prekey` slot envelope. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkGuardedFixed [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps X W x evs

theorem realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf_ghost_congr [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf LoopAdvEnv maxOps X W x =
      realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf LoopAdvEnv maxOps X W y := by
  funext evs
  dsimp [realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf]
  rw [hf, hp,
    realCliDecPkBinaryWideSlotEnvCmkFixedOf_ghost_congr
      LoopAdvEnv maxOps X W x y hp hm hs hcp hf hc hmsg]

theorem realCliDecPkBinaryWideSlotEnvCmkGuardedFixed_ghost_congr [LibsignalPlacement]
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnvCmkGuardedFixed X W x =
      realCliDecPkBinaryWideSlotEnvCmkGuardedFixed X W y :=
  realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf_ghost_congr
    CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps X W x y hp hm hs hcp hf hc hmsg

theorem realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf_mono [LibsignalPlacement]
    {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {x : DecPkGhost} {evs : List AllocEvent}
    (h : realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf L₁ m₁ X W x evs) :
    realCliDecPkBinaryWideSlotEnvCmkGuardedFixedOf L₂ m₂ X W x evs :=
  fun hp => realCliDecPkBinaryWideSlotEnvCmkFixedOf_mono hL hm (h hp)

/-! ## Path-C Stage-P3-Parametric Variants

Generalizes the Path-C Stage-P3 step to an arbitrary `P3PathCEnv : W4BinaryRecvPrekeyParamsCmk →
List AllocEvent → Prop` so `VerNe-prev1` (`W4StageP3Prev1WideEnvOf` / `VerNeTightTopEnv`) plugs in
directly while retaining `rfl` specialization at `w4c_defaultP3PathCEnvOf`. -/

/-- Default Path-C Stage-P3 step envelope (`rfl`-matching `W4BinaryRecvPrekeyPathCWideCmkEnvFixedOf`). -/
def w4c_defaultP3PathCEnvOf (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (w : W4BinaryRecvPrekeyParamsCmk) : List AllocEvent → Prop :=
  OptStageEnv
    (W4StageP3WideEnv W4CloneACDomEnv
      (W4RecvPrekeyTryDecACCmkEnvOf LoopAdvEnv maxOps w.base))

/-- Binary-kit Path C (`Over` / `prev1`) Stages P1 → P2 → `P3PathCEnv` → P4 envelope at
`W4BinaryStageP4PathCWideEnvFixed` and `(LoopAdvEnv, maxOps, P3PathCEnv)`. -/
def W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  let P := mkW4RecvPrekeyWideCmkSlotParamsOf LoopAdvEnv maxOps w.base
  SeqEnv (W4BinaryStageP1OkEnv w.base.rd w.base.files w.base.peer w.remoteIdKey)
    (SeqEnv
      (OptStageEnv
        (W4BinaryStageP2PathCWideEnv w.base.G_cur w.base.st_cur P.CurTrialFailEnv
          P.DecEnv P.TrialEnv P.DropEnv P.archivedTrials w.base.g_arch w.base.r_arch
          w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
          w.base.C.F w.base.x_res w.base.x_spqr))
      (SeqEnv (P3PathCEnv w)
        (OptStageEnv
          (W4BinaryStageP4PathCWideEnvFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
            w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
            w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) evs

/-- Complete 4-arm binary-kit W4 (`recv-prekey`) slot envelope parameterized over `P3PathCEnv`. -/
def W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  SeqEnv
    (fun e =>
      W4BinaryStageP1UntrustedEnv w.base.rd w.base.files w.base.peer w.remoteIdKey e ∨
      W4BinaryRecvPrekeyPathBWideCmkEnvOf LoopAdvEnv maxOps w e ∨
      W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf LoopAdvEnv maxOps w e ∨
      W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed LoopAdvEnv maxOps P3PathCEnv w e)
    FreeOnlyEvs evs

/-- Complete 4-arm `AllFixed` binary-kit W4 (`recv-prekey`) slot envelope parameterized over
`P3PathCEnv`. -/
def W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (w : W4BinaryRecvPrekeyParamsCmk) (evs : List AllocEvent) : Prop :=
  let P := mkW4RecvPrekeyWideCmkSlotParamsOf LoopAdvEnv maxOps w.base
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
                (W4RecvPrekeyTryDecACCmkEnvOf LoopAdvEnv maxOps w.base)))
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
          (SeqEnv (P3PathCEnv w)
            (OptStageEnv
              (W4BinaryStageP4PathCWideEnvAllFixed w.base.hasOpk w.base.rd w.base.files w.base.peer
                w.remoteIdKey w.base.kpkId w.base.spkId w.base.opkId w.baseKey
                w.base.G_out1 w.base.sess_out1 w.base.enc_prev1)))) e)
    FreeOnlyEvs evs

theorem w4c_wideSlotEnvCmkWithP3CFixedOf_default_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf
        LoopAdvEnv maxOps (w4c_defaultP3PathCEnvOf LoopAdvEnv maxOps) =
      W4BinaryRecvPrekeyWideSlotEnvCmkFixedOf LoopAdvEnv maxOps :=
  rfl

theorem w4c_wideSlotEnvCmkWithP3CAllFixedOf_default_eq
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat) :
    W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf
        LoopAdvEnv maxOps (w4c_defaultP3PathCEnvOf LoopAdvEnv maxOps) =
      W4BinaryRecvPrekeyWideSlotEnvCmkAllFixedOf LoopAdvEnv maxOps :=
  rfl

theorem w4c_wideSlotEnvCmkWithP3CAllFixed_eq_fixed {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) {LoopAdvEnv : W4LoopAdvEnv} {maxOps : Nat}
    {P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop}
    {w : W4BinaryRecvPrekeyParamsCmk}
    (hfiles : w.base.files = runFiles i) (hrd : w.base.rd = cliIo.rd) :
    W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf LoopAdvEnv maxOps P3PathCEnv w =
      W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf LoopAdvEnv maxOps P3PathCEnv w := by
  have hsessLoad : ∀ a : AddrVal,
      cliSessionKitLoadPollEnv cliIo.rd scopeKit (AddrTextValEnv DecimalEnv)
          (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          (ofBytesEnv RecordDeserializeCancelEnv) (runFiles i) StoresGhost.opened.sessions a =
        cliSessionKitLoadPollEnv cliIo.rd scopeKit (AddrTextValEnv DecimalEnv)
          (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
          (ofBytesEnv RecordDeserializeCancelEnv) (runFiles i) StoresGhost.opened.sessions a := by
    intro a; unfold cliSessionKitLoadPollEnv
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_sessions hi _)]
  have htrustPoll : ∀ (a : AddrVal) (k : IdentityKey) (d : Direction),
      cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
          (runFiles i) StoresGhost.opened.identity a k d =
        cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
          (runFiles i) StoresGhost.opened.identity a k d := by
    intro a k d; unfold cliIdentityKitTrustPollEnv
    rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_identities hi _)]
  have hsavePoll : ∀ (a : AddrVal) (k : IdentityKey),
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
  unfold W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf
    W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf
    W4BinaryRecvPrekeyPathBWideCmkEnvOf W4BinaryRecvPrekeyPathAWideCmkEnvFixedOf
    W4BinaryRecvPrekeyPathCWideCmkWithP3EnvFixed
  dsimp only
  rw [hfiles, hrd, hp1un, hp1ok, hp2a, hp2c, hp4m, hp4a, hp4c]

theorem w4c_wideSlotEnvCmkWithP3CFixed_mono {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    {P3₁ P3₂ : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    (hP3 : ∀ w evs, P3₁ w evs → P3₂ w evs)
    {w : W4BinaryRecvPrekeyParamsCmk} {evs : List AllocEvent}
    (h : W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf L₁ m₁ P3₁ w evs) :
    W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CFixedOf L₂ m₂ P3₂ w evs := by
  rcases h with hfr | hseq
  · exact Or.inl hfr
  · refine Or.inr (seqEnv_mono (fun e harm => ?_) (fun _ hfr => hfr) hseq)
    rcases harm with hun | hb | ha | hc
    · exact Or.inl hun
    · refine Or.inr (Or.inl ?_)
      exact seqEnv_mono (fun _ hp1 => hp1)
        (fun _ h2 => seqEnv_mono
          (fun e2 hp2 => w4c_optStageEnv_mono
            (w4c_stageP2MatchedWideEnv_mono (fun x _ ht => w4c_trialRunWideCmkEnvOf_mono hL hm x ht)
              w.base.archivedTrials w.base.g_arch w.base.r_arch) e2 hp2)
          (fun _ h3 => seqEnv_mono
            (fun e3 hp3 => w4c_optStageEnv_mono
              (w4c_stageP3WideEnv_mono (fun _ ht => w4c_tryDecBEnv_mono hL hm w.base ht)) e3 hp3)
            (fun _ hp4 => hp4) h3) h2) hb
    · refine Or.inr (Or.inr (Or.inl ?_))
      exact seqEnv_mono (fun _ hp1 => hp1)
        (fun _ h2 => seqEnv_mono (fun _ hp2 => hp2)
          (fun _ h3 => seqEnv_mono
            (fun e3 hp3 => w4c_optStageEnv_mono
              (w4c_stageP3WideEnv_mono (fun _ ht => w4c_tryDecACEnv_mono hL hm w.base ht)) e3 hp3)
            (fun _ hp4 => hp4) h3) h2) ha
    · refine Or.inr (Or.inr (Or.inr ?_))
      exact seqEnv_mono (fun _ hp1 => hp1)
        (fun _ h2 => seqEnv_mono
          (fun e2 hp2 => w4c_optStageEnv_mono
            (w4c_stageP2PathCWideEnv_mono
              (fun _ hc => w4c_curTrialFailEnv_mono hL hm w.base hc)
              (fun x _ ht => w4c_trialRunWideCmkEnvOf_mono hL hm x ht)
              w.base.archivedTrials w.base.g_arch w.base.r_arch
              w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
              w.base.C.F w.base.x_res w.base.x_spqr) e2 hp2)
          (fun _ h3 => seqEnv_mono (fun e3 hp3 => hP3 w e3 hp3) (fun _ hp4 => hp4) h3) h2) hc

theorem w4c_wideSlotEnvCmkWithP3CAllFixed_mono {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    {P3₁ P3₂ : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    (hP3 : ∀ w evs, P3₁ w evs → P3₂ w evs)
    {w : W4BinaryRecvPrekeyParamsCmk} {evs : List AllocEvent}
    (h : W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf L₁ m₁ P3₁ w evs) :
    W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf L₂ m₂ P3₂ w evs := by
  rcases h with hfr | hseq
  · exact Or.inl hfr
  · refine Or.inr (seqEnv_mono (fun e harm => ?_) (fun _ hfr => hfr) hseq)
    rcases harm with hun | hb | ha | hc
    · exact Or.inl hun
    · refine Or.inr (Or.inl ?_)
      exact seqEnv_mono (fun _ hp1 => hp1)
        (fun _ h2 => seqEnv_mono
          (fun e2 hp2 => w4c_optStageEnv_mono
            (w4c_stageP2MatchedWideEnv_mono (fun x _ ht => w4c_trialRunWideCmkEnvOf_mono hL hm x ht)
              w.base.archivedTrials w.base.g_arch w.base.r_arch) e2 hp2)
          (fun _ h3 => seqEnv_mono
            (fun e3 hp3 => w4c_optStageEnv_mono
              (w4c_stageP3WideEnv_mono (fun _ ht => w4c_tryDecBEnv_mono hL hm w.base ht)) e3 hp3)
            (fun _ hp4 => hp4) h3) h2) hb
    · refine Or.inr (Or.inr (Or.inl ?_))
      exact seqEnv_mono (fun _ hp1 => hp1)
        (fun _ h2 => seqEnv_mono (fun _ hp2 => hp2)
          (fun _ h3 => seqEnv_mono
            (fun e3 hp3 => w4c_optStageEnv_mono
              (w4c_stageP3WideEnv_mono (fun _ ht => w4c_tryDecACEnv_mono hL hm w.base ht)) e3 hp3)
            (fun _ hp4 => hp4) h3) h2) ha
    · refine Or.inr (Or.inr (Or.inr ?_))
      exact seqEnv_mono (fun _ hp1 => hp1)
        (fun _ h2 => seqEnv_mono
          (fun e2 hp2 => w4c_optStageEnv_mono
            (w4c_stageP2PathCWideEnvAllFixed_mono
              (fun _ hc => w4c_curTrialFailEnv_mono hL hm w.base hc)
              (fun x _ ht => w4c_trialRunWideCmkEnvOf_mono hL hm x ht)
              w.base.archivedTrials w.base.g_arch w.base.r_arch
              w.base.hasOpk w.base.rd w.base.files w.base.spkId w.base.kpkId w.base.opkId
              w.base.C.F w.base.x_res w.base.x_spqr) e2 hp2)
          (fun _ h3 => seqEnv_mono (fun e3 hp3 => hP3 w e3 hp3) (fun _ hp4 => hp4) h3) h2) hc

/-- `(LoopAdvEnv, maxOps, P3PathCEnv)`-parametric unguarded binary-kit W4 (`decrypt_prekey`) slot
envelope. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (_X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  ∃ w4 : W4BinaryRecvPrekeyParamsCmk,
    W4BinaryCallSiteDomCmk W.C W.Q.K x.msg.message.ciphertext.length x.peer.val x.F w4.base ∧
      w4.remoteIdKey = x.msg.identityKey ∧
      w4.baseKey = x.msg.baseKey ∧
      W4BinaryRecvPrekeyWideSlotEnvCmkWithP3CAllFixedOf LoopAdvEnv maxOps P3PathCEnv w4 evs

theorem realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf_ghost_congr [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks) (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val)
    (_hm : x.me.val = y.me.val)
    (_hs : x.stores = y.stores)
    (_hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F)
    (_hc : x.coins = y.coins)
    (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf LoopAdvEnv maxOps P3PathCEnv X W x =
      realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf LoopAdvEnv maxOps P3PathCEnv X W y := by
  funext evs
  simp only [realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf, hp, hf, hmsg]

theorem realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf_mono [LibsignalPlacement]
    {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    {P3₁ P3₂ : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    (hP3 : ∀ w evs, P3₁ w evs → P3₂ w evs)
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {x : DecPkGhost} {evs : List AllocEvent}
    (h : realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf L₁ m₁ P3₁ X W x evs) :
    realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf L₂ m₂ P3₂ X W x evs := by
  obtain ⟨w4, hcs, hik, hbk, henv⟩ := h
  exact ⟨w4, hcs, hik, hbk, w4c_wideSlotEnvCmkWithP3CAllFixed_mono hL hm hP3 henv⟩

/-- `(LoopAdvEnv, maxOps, P3PathCEnv)`-parametric `PeerSpqrStateTight640`-guarded binary-kit W4
(`decrypt_prekey`) slot envelope. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  PeerSpqrStateTight640 W.C.F W.Q.K x.F x.peer.val →
    realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf LoopAdvEnv maxOps P3PathCEnv X W x evs

/-- Default `(CmkLoopAdvanceEvs, 109)` `PeerSpqrStateTight640`-guarded binary-kit W4
(`decrypt_prekey`) slot envelope parameterized over `P3PathCEnv`. -/
abbrev realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixed [LibsignalPlacement]
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x : DecPkGhost) (evs : List AllocEvent) : Prop :=
  realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf
    CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps P3PathCEnv X W x evs

theorem realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf_ghost_congr [LibsignalPlacement]
    (LoopAdvEnv : W4LoopAdvEnv) (maxOps : Nat)
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf LoopAdvEnv maxOps P3PathCEnv X W x =
      realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf LoopAdvEnv maxOps P3PathCEnv X W y := by
  funext evs
  dsimp [realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf]
  rw [hf, hp,
    realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf_ghost_congr
      LoopAdvEnv maxOps P3PathCEnv X W x y hp hm hs hcp hf hc hmsg]

theorem realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixed_ghost_congr [LibsignalPlacement]
    (P3PathCEnv : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop)
    (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (x y : DecPkGhost)
    (hp : x.peer.val = y.peer.val) (hm : x.me.val = y.me.val)
    (hs : x.stores = y.stores) (hcp : x.coinsP = y.coinsP)
    (hf : x.F = y.F) (hc : x.coins = y.coins) (hmsg : x.msg = y.msg) :
    realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixed P3PathCEnv X W x =
      realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixed P3PathCEnv X W y :=
  realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf_ghost_congr
    CmkLoopAdvanceEvs w4c_defaultDecodeMaxOps P3PathCEnv X W x y hp hm hs hcp hf hc hmsg

theorem realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf_mono [LibsignalPlacement]
    {L₁ L₂ : W4LoopAdvEnv} {m₁ m₂ : Nat}
    {P3₁ P3₂ : W4BinaryRecvPrekeyParamsCmk → List AllocEvent → Prop}
    (hL : W4LoopAdvSub L₁ L₂) (hm : m₁ ≤ m₂)
    (hP3 : ∀ w evs, P3₁ w evs → P3₂ w evs)
    {X : UnreachedPqxdhPrimitives} {W : CliHooks} {x : DecPkGhost} {evs : List AllocEvent}
    (h : realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf L₁ m₁ P3₁ X W x evs) :
    realCliDecPkBinaryWideSlotEnvCmkWithP3CGuardedFixedOf L₂ m₂ P3₂ X W x evs :=
  fun hp => realCliDecPkBinaryWideSlotEnvCmkWithP3CFixedOf_mono hL hm hP3 (h hp)

end LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
