/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak
public import LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.PqValid
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn
import LibsignalBinary.Proofs.SpqrV1.Top.StateSizeGrow

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

/-!
# Linked `spqr::recv` and `try_decrypt` Slot Credit/Group Wrappers

Discharges `SpqrRecvTightDomain` from `TopStateTight F K stBytes` (or per-peer
`PeerSpqrStateTight640` / `CliPqxdhInputs`) across the tight `spqr::recv` credit and slot-group
specs, `W2TryDecryptEnv` / `W2TryDecryptFailEnv` trial specs, and CLI decrypt slot contracts.
-/

namespace LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWrappers

open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (Crypto IdentityKey ShaCompress)
open CryptoGames.LibsignalSessionApi (Direction Session SessionRecord)
open CryptoVerification.E2E (PEParams)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (decryptRecord recGhostOf)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Message MlKem PqRatchetState States V1Recv V1State VersionNegotiationPB
   spqrAuthApi spqrPolyApi spqrV1)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost UuidParser uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliPqxdhInputs Inputs)
open CryptoVerification.SignalSession.Cli (StoresGhost addressText pathOf)
open CryptoVerification.SignalSession.Cli.KitInst (cliIdentityStoreSpec cliSessionStoreSpec)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.Slots (scopeIn scopeKit)
open CryptoVerification.SignalSession.Cli.Slots.PqValid (PqInV1)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.StateSize (ValidState)
open LibsignalBinary.Heap (AllocCostModel AllocEvent)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (dirDomainCaps_opened_peers dirDomainCaps_opened_sess)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (HasFineGroupCredit PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessLoadPollEnv CliSessStorePollEnv CliSmallStorePollEnv optLargeCost
   sessLoadPollTightDeltaCum sessLoadPollTightDeltaLive sessLoadPollTightDeltaPeak
   sessLoadPollTightMaxReq sessLoadPoll_phaseCredit_tight sessStorePollMaxReq
   sessStorePollTightDeltaCum sessStorePollTightDeltaLive sessStorePollTightDeltaPeak
   smallStorePollTightDeltaCum smallStorePollTightDeltaLive smallStorePollTightDeltaPeak
   smallStorePollTightMaxReq smallStorePoll_phaseCredit_tight)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvC09aWire
  (c09aStatesRecvTightCreditSpec_inst spqrRecvParts_c07_c09a_phaseCreditSpec_tight_uncondHist
   spqrRecvParts_c07_c09a_phaseCreditSpec_tight_uncondHist_rawEnv
   spqrRecvParts_c07_c09a_phaseGroupSpec_tight spqrRecvParts_c07_c09a_phaseGroupSpec_tight_rawEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
  (SpqrRecvC07C09aTightLinkedEnv SpqrRecvC07TightLinkedEnv spqrRecvC07TightLinkedEnv_proto_eq
   spqrRecvTightDomain_of_topStateTight_and_link)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches (StatesRecvTightCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightSpec
  (spqrRecvParts_c07_phaseCreditSpec_tight_uncondHist)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpec (StatesRecvEnv StatesRecvProtoEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
  (ValidChainParams ValidEncoderPts640 ValidStateChainParams)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
  (PeerSpqrStateTight640 RecordSpqrStateTight640 peerSpqrStateTight640_of_cliPqInputs_recv
   peerSpqrStateTight640_of_cliSessionStoreSpec recordSpqrStateTight640_of_cliSessionStoreSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (TopStateTight topStateTight_length_le topStateTight_to_tightValid640)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (RecordGhostValid SessionCloneDom recordDecrypt_dom_phaseCredit_tight)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
  (DoublingChainLe W2TryDecryptEnv W2TryDecryptFailEnv w2CmkChainTightLive
   w2TryDecryptFail_fine_phaseCreditSpec_tight w2TryDecryptMaxReq w2TryDecryptTightCum
   w2TryDecryptTightLive w2TryDecryptTightPeak w2TryDecrypt_fine_phaseCreditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak
  (cliSessStorePoll_exists_dom_phaseCredit_tight decryptRecord_post_caps_of_scopeIn
   opened_scopeAt_encodeRecord_le opened_scopeAt_sessionCloneDom withStoresDec_fine_creditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.W4TryDecryptPqPeak (phaseCredit_exists)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (SessionGhostValid WithStoresDecEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (TryDecryptEnvArgs recordTryDecryptEnvArgs)

/-! ## Existential Witness Combinators and `TopStateTight` Bridges -/

/-- Lifts a uniform `PhaseGroupSpec` bound across an existential ghost witness `∃ a, E a evs`. -/
theorem phaseGroup_exists {α : Sort _} {M : AllocCostModel} [HasFineGroupCredit M]
    {E : α → List AllocEvent → Prop} {g : Nat}
    (h : ∀ a, PhaseGroupSpec M (E a) g) :
    PhaseGroupSpec M (fun evs => ∃ a, E a evs) g where
  groups_le st0 {_} := fun ⟨a, hevs⟩ => (h a).groups_le st0 hevs

private theorem phaseCredit_of_and_right {M : AllocCostModel} [HasFineReallocCredit M]
    {P : List AllocEvent → Prop} {Q : Prop} {c l p r : Nat}
    (h : Q → PhaseCreditSpec M P c l p r) :
    PhaseCreditSpec M (fun evs => P evs ∧ Q) c l p r where
  req_align evs hpq ev hev := (h hpq.2).req_align evs hpq.1 ev hev
  credit_le st0 {_} hpq := (h hpq.2).credit_le st0 hpq.1

private theorem phaseGroup_of_and_right {M : AllocCostModel} [HasFineGroupCredit M]
    {P : List AllocEvent → Prop} {Q : Prop} {g : Nat}
    (h : Q → PhaseGroupSpec M P g) :
    PhaseGroupSpec M (fun evs => P evs ∧ Q) g where
  groups_le st0 {_} hpq := (h hpq.2).groups_le st0 hpq.1

theorem validState_of_validStateChainParams {s : Bytes} (h : ValidStateChainParams s) :
    ValidState s := by
  rcases h with rfl | ⟨st, rfl, hch, hvn⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨st, rfl,
      ⟨fun vn hvnEq p hp => (hvn vn hvnEq p hp).2,
       fun ch hchEq p hp => (hch ch hchEq p hp).2⟩⟩

/-- Every `TopStateTight` byte slice is a `ValidState` of length below `2 ^ 31` (`PqInV1`). -/
theorem pqInV1_of_topStateTight {F : ShaCompress} {K : MlKem} {bytes : Bytes}
    (hTop : TopStateTight F K bytes) : PqInV1 bytes := by
  have hlen : bytes.length < 2 ^ 31 :=
    Nat.lt_of_le_of_lt (topStateTight_length_le hTop) (by decide)
  rcases hTop with ⟨_, _, _, _, _, _, _, _, _, _, hw⟩
  exact ⟨validState_of_validStateChainParams hw.hcp, hlen⟩

/-- Combines `scopeKit rec` and `RecordSpqrStateTight640 F K rec` into `scopeIn rec`. -/
theorem scopeIn_of_scopeKit_and_recordSpqrStateTight640 {F : ShaCompress} {K : MlKem}
    {rec : SessionRecord (List (BitVec 8))}
    (hKit : scopeKit rec)
    (hRec : RecordSpqrStateTight640 F K rec) :
    scopeIn rec :=
  ⟨⟨hKit.1.1, fun s hs => pqInV1_of_topStateTight (hRec s hs), hKit.1.2.2⟩, hKit.2⟩

/-! ## Linked Unconditional-History `spqr::recv` Credit Bounds -/

/-- Linked unconditional-history `PhaseCreditSpec` for `SpqrRecvC07TightLinkedEnv` under `TopStateTight`.
-/
theorem spqrRecvParts_c07_linked_phaseCreditSpec_tight_uncondHist
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv' cRecv rRecv)
    (hcRecv : cRecv ≤ 1900660)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hTop : TopStateTight F K stBytes) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      23313687 605066 621350 (max rRecv 302480) :=
  phaseCredit_of_and_right fun hLink =>
    spqrRecvParts_c07_phaseCreditSpec_tight_uncondHist F K C09a hcRecv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto
      (spqrRecvTightDomain_of_topStateTight_and_link hTop hLink)

theorem spqrRecvParts_c07_linked_exists_phaseCreditSpec_tight_uncondHist
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv' cRecv rRecv)
    (hcRecv : cRecv ≤ 1900660)
    (stBytes : Bytes)
    (hTop : TopStateTight F K stBytes) :
    PhaseCreditSpec fineCostModel
      (fun evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
        SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)
      23313687 605066 621350 (max rRecv 302480) :=
  phaseCredit_exists fun pre_pb =>
  phaseCredit_exists fun vn =>
  phaseCredit_exists fun pb =>
  phaseCredit_exists fun st0 =>
  phaseCredit_exists fun sckaMsg =>
  phaseCredit_exists fun v =>
  phaseCredit_exists fun xInit =>
  phaseCredit_exists fun xNew =>
  phaseCredit_exists fun xAdd =>
  phaseCredit_exists fun xRk =>
  phaseCredit_exists fun xSInto =>
  phaseCredit_exists fun xCInto =>
    spqrRecvParts_c07_linked_phaseCreditSpec_tight_uncondHist F K C09a hcRecv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop

/-! ## Closed Linked `spqr::recv` Credit and Group Bounds -/

/-- Closed linked unconditional-history `PhaseCreditSpec` for `SpqrRecvC07TightLinkedEnv` at `StatesRecvProtoEnv`.
-/
theorem spqrRecvParts_c07_c09a_linked_phaseCreditSpec_tight_uncondHist
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hTop : TopStateTight F K stBytes) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvC07C09aTightLinkedEnv F K
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      23313687 605066 621350 302480 :=
  phaseCredit_of_and_right fun hLink =>
    spqrRecvParts_c07_c09a_phaseCreditSpec_tight_uncondHist F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto
      (spqrRecvTightDomain_of_topStateTight_and_link hTop hLink)

theorem spqrRecvParts_c07_c09a_linked_phaseCreditSpec_tight_uncondHist_rawEnv
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hTop : TopStateTight F K stBytes) :
    PhaseCreditSpec fineCostModel
      (SpqrRecvC07TightLinkedEnv F K StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      23313687 605066 621350 302480 :=
  phaseCredit_of_and_right fun hLink =>
    spqrRecvParts_c07_c09a_phaseCreditSpec_tight_uncondHist_rawEnv F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto
      (spqrRecvTightDomain_of_topStateTight_and_link hTop hLink)

theorem spqrRecvParts_c07_c09a_linked_exists_phaseCreditSpec_tight_uncondHist
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (hTop : TopStateTight F K stBytes) :
    PhaseCreditSpec fineCostModel
      (fun evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
        SpqrRecvC07C09aTightLinkedEnv F K
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)
      23313687 605066 621350 302480 :=
  phaseCredit_exists fun pre_pb =>
  phaseCredit_exists fun vn =>
  phaseCredit_exists fun pb =>
  phaseCredit_exists fun st0 =>
  phaseCredit_exists fun sckaMsg =>
  phaseCredit_exists fun v =>
  phaseCredit_exists fun xInit =>
  phaseCredit_exists fun xNew =>
  phaseCredit_exists fun xAdd =>
  phaseCredit_exists fun xRk =>
  phaseCredit_exists fun xSInto =>
  phaseCredit_exists fun xCInto =>
    spqrRecvParts_c07_c09a_linked_phaseCreditSpec_tight_uncondHist F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop

theorem spqrRecvParts_c07_c09a_linked_exists_phaseCreditSpec_tight_uncondHist_rawEnv
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (hTop : TopStateTight F K stBytes) :
    PhaseCreditSpec fineCostModel
      (fun evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
        SpqrRecvC07TightLinkedEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)
      23313687 605066 621350 302480 :=
  phaseCredit_exists fun pre_pb =>
  phaseCredit_exists fun vn =>
  phaseCredit_exists fun pb =>
  phaseCredit_exists fun st0 =>
  phaseCredit_exists fun sckaMsg =>
  phaseCredit_exists fun v =>
  phaseCredit_exists fun xInit =>
  phaseCredit_exists fun xNew =>
  phaseCredit_exists fun xAdd =>
  phaseCredit_exists fun xRk =>
  phaseCredit_exists fun xSInto =>
  phaseCredit_exists fun xCInto =>
    spqrRecvParts_c07_c09a_linked_phaseCreditSpec_tight_uncondHist_rawEnv F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop

/-- Closed linked `PhaseGroupSpec` (`701,273,904` scaled units = `10,701` groups) for `SpqrRecvC07TightLinkedEnv` at `StatesRecvProtoEnv`.
-/
theorem spqrRecvParts_c07_c09a_linked_phaseGroupSpec_tight
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (SpqrRecvC07C09aTightLinkedEnv F K
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      701273904 :=
  phaseGroup_of_and_right fun hLink =>
    spqrRecvParts_c07_c09a_phaseGroupSpec_tight F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto
      (spqrRecvTightDomain_of_topStateTight_and_link hTop hLink)

theorem spqrRecvParts_c07_c09a_linked_phaseGroupSpec_tight_rawEnv
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (SpqrRecvC07TightLinkedEnv F K StatesRecvEnv
        stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      701273904 :=
  phaseGroup_of_and_right fun hLink =>
    spqrRecvParts_c07_c09a_phaseGroupSpec_tight_rawEnv F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto
      (spqrRecvTightDomain_of_topStateTight_and_link hTop hLink)

theorem spqrRecvParts_c07_c09a_linked_exists_phaseGroupSpec_tight
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (fun evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
        SpqrRecvC07C09aTightLinkedEnv F K
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)
      701273904 :=
  phaseGroup_exists fun pre_pb =>
  phaseGroup_exists fun vn =>
  phaseGroup_exists fun pb =>
  phaseGroup_exists fun st0 =>
  phaseGroup_exists fun sckaMsg =>
  phaseGroup_exists fun v =>
  phaseGroup_exists fun xInit =>
  phaseGroup_exists fun xNew =>
  phaseGroup_exists fun xAdd =>
  phaseGroup_exists fun xRk =>
  phaseGroup_exists fun xSInto =>
  phaseGroup_exists fun xCInto =>
    spqrRecvParts_c07_c09a_linked_phaseGroupSpec_tight F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop

theorem spqrRecvParts_c07_c09a_linked_exists_phaseGroupSpec_tight_rawEnv
    (F : ShaCompress) (K : MlKem)
    (stBytes : Bytes)
    (hTop : TopStateTight F K stBytes) :
    PhaseGroupSpec fineCostModel
      (fun evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
        SpqrRecvC07TightLinkedEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)
      701273904 :=
  phaseGroup_exists fun pre_pb =>
  phaseGroup_exists fun vn =>
  phaseGroup_exists fun pb =>
  phaseGroup_exists fun st0 =>
  phaseGroup_exists fun sckaMsg =>
  phaseGroup_exists fun v =>
  phaseGroup_exists fun xInit =>
  phaseGroup_exists fun xNew =>
  phaseGroup_exists fun xAdd =>
  phaseGroup_exists fun xRk =>
  phaseGroup_exists fun xSInto =>
  phaseGroup_exists fun xCInto =>
    spqrRecvParts_c07_c09a_linked_phaseGroupSpec_tight_rawEnv F K
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop

/-! ## Linked `try_decrypt` Credit Bounds -/

/-- Linked unconditional-history `PhaseCreditSpec` for `W2TryDecryptEnv` under `TopStateTight`. -/
theorem w2TryDecrypt_spqrC07_linked_uncondHist_phaseCreditSpec_tight
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv' cRecv rRecv)
    (hcRecv : cRecv ≤ 1900660)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hTop : TopStateTight F K stBytes)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptEnv dhCap needGrow caps
        (SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptTightCum dhCap needGrow maxSteps 23313687)
      (w2TryDecryptTightLive maxOldCap 605066 maxCt)
      (w2TryDecryptTightPeak maxOldCap 605066 621350 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap (max rRecv 302480) maxCt) :=
  w2TryDecrypt_fine_phaseCreditSpec_tight hDhSmall hlen hchain
    (spqrRecvParts_c07_linked_phaseCreditSpec_tight_uncondHist F K C09a hcRecv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hTop)
    hct

theorem w2TryDecrypt_spqrC07_linked_exists_uncondHist_phaseCreditSpec_tight
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv' : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv' cRecv rRecv)
    (hcRecv : cRecv ≤ 1900660)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hTop : TopStateTight F K stBytes)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptEnv dhCap needGrow caps
        (fun evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvC07TightLinkedEnv F K StatesRecvEnv'
            stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)
        withAddr errAlloc ctLen)
      (w2TryDecryptTightCum dhCap needGrow maxSteps 23313687)
      (w2TryDecryptTightLive maxOldCap 605066 maxCt)
      (w2TryDecryptTightPeak maxOldCap 605066 621350 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap (max rRecv 302480) maxCt) :=
  w2TryDecrypt_fine_phaseCreditSpec_tight hDhSmall hlen hchain
    (spqrRecvParts_c07_linked_exists_phaseCreditSpec_tight_uncondHist F K C09a hcRecv stBytes hTop)
    hct

/-- Closed existentially lifted `PhaseCreditSpec` for `W2TryDecryptEnv` at `StatesRecvProtoEnv` (`maxReq = 302,480`).
-/
theorem w2TryDecrypt_spqrC07_c09a_linked_exists_uncondHist_phaseCreditSpec_tight
    (F : ShaCompress) (K : MlKem)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hTop : TopStateTight F K stBytes)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptEnv dhCap needGrow caps
        (fun evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvC07C09aTightLinkedEnv F K
            stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)
        withAddr errAlloc ctLen)
      (w2TryDecryptTightCum dhCap needGrow maxSteps 23313687)
      (w2TryDecryptTightLive maxOldCap 605066 maxCt)
      (w2TryDecryptTightPeak maxOldCap 605066 621350 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap 302480 maxCt) :=
  w2TryDecrypt_fine_phaseCreditSpec_tight hDhSmall hlen hchain
    (spqrRecvParts_c07_c09a_linked_exists_phaseCreditSpec_tight_uncondHist F K stBytes hTop)
    hct

theorem w2TryDecrypt_spqrC07_c09a_linked_exists_uncondHist_phaseCreditSpec_tight_rawEnv
    (F : ShaCompress) (K : MlKem)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hTop : TopStateTight F K stBytes)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptEnv dhCap needGrow caps
        (fun evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvC07TightLinkedEnv F K StatesRecvEnv
            stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)
        withAddr errAlloc ctLen)
      (w2TryDecryptTightCum dhCap needGrow maxSteps 23313687)
      (w2TryDecryptTightLive maxOldCap 605066 maxCt)
      (w2TryDecryptTightPeak maxOldCap 605066 621350 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap 302480 maxCt) :=
  w2TryDecrypt_fine_phaseCreditSpec_tight hDhSmall hlen hchain
    (spqrRecvParts_c07_c09a_linked_exists_phaseCreditSpec_tight_uncondHist_rawEnv F K stBytes hTop)
    hct

theorem w2TryDecryptFail_spqrC07_c09a_linked_exists_uncondHist_phaseCreditSpec_tight_rawEnv
    (F : ShaCompress) (K : MlKem)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hTop : TopStateTight F K stBytes)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptFailEnv dhCap needGrow caps
        (fun evs => ∃ pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto,
          SpqrRecvC07TightLinkedEnv F K StatesRecvEnv
            stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto evs)
        withAddr errAlloc ctLen)
      (w2TryDecryptTightCum dhCap needGrow maxSteps 23313687)
      (w2CmkChainTightLive maxOldCap + 605066)
      (w2TryDecryptTightPeak maxOldCap 605066 621350 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap 302480 maxCt) :=
  w2TryDecryptFail_fine_phaseCreditSpec_tight hDhSmall hlen hchain
    (spqrRecvParts_c07_c09a_linked_exists_phaseCreditSpec_tight_uncondHist_rawEnv F K stBytes hTop)
    hct

/-! ## `PeerSpqrStateTight640` CLI Decrypt Slot Contracts -/

/-- CLI decrypt slot `PhaseCreditSpec` under `PeerSpqrStateTight640`, deriving `scopeIn rec` from
`scopeKit rec` and `RecordSpqrStateTight640` and supplying `TopStateTight C.F K ses.state.pqRatchetState`
directly to the per-session `try_decrypt` hypothesis. -/
theorem w2CliDecryptSlot_stateTight640_fine_creditSpec {A : RustAlloc}
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
    {fileCap idFileCap deserCum deserLive deserPeak deserMaxReq
     c_td l_td p_td r_td c_st l_st p_st r_st : Nat}
    (hrem : x.rem.val = peer.val)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hremName : x.rem.name.bytes.length ≤ 40)
    (hidKeyLen : peerIdKeyName.length ≤ 64)
    (hStateTight : PeerSpqrStateTight640 C.F K F x.rem.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hIdFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.identity.peers.path peerIdKeyName) = .ok bs →
      bs.length ≤ idFileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hLoadEq : ∀ evs,
      kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv F StoresGhost.opened.sessions peer evs)
    (hTrustEq : ∀ k evs,
      ikitEnv.trustPollEnv StoresGhost.opened.identity x.rem.val k .receiving evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSaveEq : ∀ k evs,
      ikitEnv.savePollEnv StoresGhost.opened.identity x.rem.val k evs →
      CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hTd : ∀ rec ses G G₁,
      scopeIn rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      SessionCloneDom fileCap ses →
      CloneRel G G₁ →
      TopStateTight C.F K ses.state.pqRatchetState →
      ValidEncoderPts640 ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      PhaseCreditSpec fineCostModel
        (tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁))
        c_td l_td p_td r_td)
    (hStore : ∀ rec pt rec' ses' k,
      scopeIn rec →
      decryptRecord C (spqrV1 C.F K) parse x rec = .ok (pt, rec') →
      scopeKit rec' →
      rec'.currentSession = some ses' →
      ses'.state.remoteIdentity = some k →
      ses'.state.pqRatchetState.length ≤ fileCap + 1128000 →
      SessionCloneDom (fileCap + 1128000) ses' →
      (encodeRecord rec').length ≤ fileCap + 3225192 →
      PhaseCreditSpec fineCostModel (kitEnv.storePollEnv StoresGhost.opened.sessions x.rem.val rec')
        c_st l_st p_st r_st) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4
    let c_ld := sessLoadPollTightDeltaCum (max 0 fileCap) deserCum
    let l_ld := sessLoadPollTightDeltaLive (max 0 fileCap) deserLive
    let p_ld := sessLoadPollTightDeltaPeak (max 0 fileCap) deserPeak
    let r_ld := sessLoadPollTightMaxReq (max 0 fileCap) deserMaxReq
    let c_rd := 8286380 + c_td
    let l_rd := 1080975 + optLargeCost fineCostModel fileCap + l_td
    let p_rd := 1080975 + optLargeCost fineCostModel fileCap + max p_td l_td
    let r_rd := max (max 208000 fileCap) (max r_td 192)
    let c_id := smallStorePollTightDeltaCum (max 0 idFileCap) 0
    let l_id := smallStorePollTightDeltaLive (max 0 idFileCap) 0
    let p_id := smallStorePollTightDeltaPeak (max 0 idFileCap) 0
    let r_id := smallStorePollTightMaxReq (max 0 idFileCap) 0
    let c_ld_step := 488 + c_ld
    let c_id_step := 738 + c_id
    let c_st_step := 738 + c_st
    let c_kr := c_id_step + max 738 (c_id_step + c_st_step)
    let l_kr := l_id + (l_id + l_st)
    let p_kr := max p_id (l_id + max p_id (l_id + p_st))
    let r_kr := max (max 32 r_id) (max 40 (max (max 32 r_id) (max 32 r_st)))
    PhaseCreditSpec fineCostModel
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity C (spqrV1 C.F K) parse tdEnv scopeKit x)
      (c_ld_step + max 738 (c_rd + c_kr))
      (l_ld + (l_rd + l_kr))
      (max p_ld (l_ld + max p_rd (l_rd + p_kr)))
      (max (max 24 r_ld) (max (max 40 17) (max r_rd r_kr))) := by
  intro kit ikit c_ld l_ld p_ld r_ld c_rd l_rd p_rd r_rd c_id l_id p_id r_id
    c_ld_step c_id_step c_st_step c_kr l_kr p_kr r_kr
  have hLoadPoll : PhaseCreditSpec fineCostModel
      (kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val) c_ld l_ld p_ld r_ld :=
    PhaseCreditSpec.of_imp hLoadEq
      (sessLoadPoll_phaseCredit_tight dirDomainCaps_opened_sess (by decide) hpeer hSessFileCap hDeser)
  have hSmallId : PhaseCreditSpec fineCostModel
      (CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName)
      c_id l_id p_id r_id :=
    smallStorePoll_phaseCredit_tight dirDomainCaps_opened_peers (by decide) hidKeyLen hIdFileCap
  exact withStoresDec_fine_creditSpec_tight
    (kit := kit) (kitEnv := kitEnv) (st0 := StoresGhost.opened.sessions)
    (ikit := ikit) (ikitEnv := ikitEnv) (ist0 := StoresGhost.opened.identity)
    (nameCap := 40)
    rfl rfl rfl rfl hremName (by decide)
    hLoadPoll
    (fun rec ses G hsc hcur hgv => by
      have hRecTight : RecordSpqrStateTight640 C.F K rec :=
        recordSpqrStateTight640_of_cliSessionStoreSpec hsc hStateTight
      have hIn : scopeIn rec :=
        scopeIn_of_scopeKit_and_recordSpqrStateTight640 hsc.1 hRecTight
      obtain ⟨hPqFile, hDom⟩ := opened_scopeAt_sessionCloneDom hrem hSessFileCap hsc hcur
      have hTop : TopStateTight C.F K ses.state.pqRatchetState :=
        peerSpqrStateTight640_of_cliSessionStoreSpec hsc hcur rfl hStateTight
      obtain ⟨hVe, hVcp, hPqLt31⟩ := topStateTight_to_tightValid640 hTop
      exact recordDecrypt_dom_phaseCredit_tight
        (x := recGhostOf x 0#64 G ses.state) (ses := ses) rfl hgv hDom
        (fun G₁ hRel => hTd rec ses G G₁ hIn hcur hgv hDom hRel hTop hVe hVcp hPqLt31 hPqFile))
    (fun _ _ _ _ k _ _ _ _ => PhaseCreditSpec.of_imp (hTrustEq k) hSmallId)
    (fun _ _ _ _ k _ _ _ _ => PhaseCreditSpec.of_imp (hSaveEq k) hSmallId)
    (fun rec pt rec' ses' k hsc hdec hc' hk => by
      have hRecTight : RecordSpqrStateTight640 C.F K rec :=
        recordSpqrStateTight640_of_cliSessionStoreSpec hsc hStateTight
      have hIn : scopeIn rec :=
        scopeIn_of_scopeKit_and_recordSpqrStateTight640 hsc.1 hRecTight
      have hEncPre : (encodeRecord rec).length ≤ fileCap :=
        opened_scopeAt_encodeRecord_le hrem hSessFileCap hsc
      obtain ⟨hKit', hPostDom, hEncPost⟩ := decryptRecord_post_caps_of_scopeIn hIn hEncPre hdec
      obtain ⟨hPqPost, hDomPost⟩ := hPostDom ses' hc'
      exact hStore rec pt rec' ses' k hIn hdec hKit' hc' hk hPqPost hDomPost hEncPost)

theorem w2CliDecryptSlot_polls_stateTight640_fine_creditSpec {A : RustAlloc}
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
    {fileCap idFileCap deserCum deserLive deserPeak deserMaxReq
     c_td l_td p_td r_td : Nat}
    (hrem : x.rem.val = peer.val)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hremName : x.rem.name.bytes.length ≤ 40)
    (hidKeyLen : peerIdKeyName.length ≤ 64)
    (hStateTight : PeerSpqrStateTight640 C.F K F x.rem.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hIdFileCap : ∀ bs,
      cliIo.rd F (pathOf StoresGhost.opened.identity.peers.path peerIdKeyName) = .ok bs →
      bs.length ≤ idFileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
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
      TopStateTight C.F K ses.state.pqRatchetState →
      ValidEncoderPts640 ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      PhaseCreditSpec fineCostModel
        (tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁))
        c_td l_td p_td r_td) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4
    let pqCap' := fileCap + 1128000
    let encCap' := fileCap + 3225192
    let c_ld := sessLoadPollTightDeltaCum (max 0 fileCap) deserCum
    let l_ld := sessLoadPollTightDeltaLive (max 0 fileCap) deserLive
    let p_ld := sessLoadPollTightDeltaPeak (max 0 fileCap) deserPeak
    let r_ld := sessLoadPollTightMaxReq (max 0 fileCap) deserMaxReq
    let c_rd := 8286380 + c_td
    let l_rd := 1080975 + optLargeCost fineCostModel fileCap + l_td
    let p_rd := 1080975 + optLargeCost fineCostModel fileCap + max p_td l_td
    let r_rd := max (max 208000 fileCap) (max r_td 192)
    let c_id := smallStorePollTightDeltaCum (max 0 idFileCap) 0
    let l_id := smallStorePollTightDeltaLive (max 0 idFileCap) 0
    let p_id := smallStorePollTightDeltaPeak (max 0 idFileCap) 0
    let r_id := smallStorePollTightMaxReq (max 0 idFileCap) 0
    let c_st := sessStorePollTightDeltaCum 8420940 0
    let l_st := sessStorePollTightDeltaLive (optLargeCost fineCostModel encCap') 0
    let p_st := sessStorePollTightDeltaPeak
      (1080975 + optLargeCost fineCostModel pqCap' + optLargeCost fineCostModel encCap') 0
    let r_st := sessStorePollMaxReq (max (max 208000 pqCap') encCap') 0
    let c_ld_step := 488 + c_ld
    let c_id_step := 738 + c_id
    let c_st_step := 738 + c_st
    let c_kr := c_id_step + max 738 (c_id_step + c_st_step)
    let l_kr := l_id + (l_id + l_st)
    let p_kr := max p_id (l_id + max p_id (l_id + p_st))
    let r_kr := max (max 32 r_id) (max 40 (max (max 32 r_id) (max 32 r_st)))
    PhaseCreditSpec fineCostModel
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity C (spqrV1 C.F K) parse tdEnv scopeKit x)
      (c_ld_step + max 738 (c_rd + c_kr))
      (l_ld + (l_rd + l_kr))
      (max p_ld (l_ld + max p_rd (l_rd + p_kr)))
      (max (max 24 r_ld) (max (max 40 17) (max r_rd r_kr))) := by
  intro kit ikit pqCap' encCap' c_ld l_ld p_ld r_ld c_rd l_rd p_rd r_rd
    c_id l_id p_id r_id c_st l_st p_st r_st
    c_ld_step c_id_step c_st_step c_kr l_kr p_kr r_kr
  exact w2CliDecryptSlot_stateTight640_fine_creditSpec F pathOk peer s1 s2 s3 s4 t1 t2 t3 t4
    C K parse x DeserEnv peerIdKeyName kitEnv ikitEnv tdEnv
    hrem hpeer hremName hidKeyLen hStateTight hSessFileCap hIdFileCap hDeser
    hLoadEq hTrustEq hSaveEq hTd
    (fun _ _ rec' ses' _ _ _ hKit' hc' _ _ hDomPost hEncPost =>
      PhaseCreditSpec.of_imp (fun evs h => hStoreEq rec' evs hKit' h)
        (cliSessStorePoll_exists_dom_phaseCredit_tight dirDomainCaps_opened_sess hpeer
          (fun s hs => by rw [hc'] at hs; injection hs with hs; subst hs; exact hDomPost)
          hEncPost))

/-- `CliPqxdhInputs` specialization of `w2CliDecryptSlot_polls_stateTight640_fine_creditSpec` on `.recv peerAddr`.
-/
theorem w2CliDecryptSlot_polls_cliPqInputs_fine_creditSpec {A : RustAlloc}
    {W : PEParams} {i : Inputs} {peerAddr : AddrV}
    (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 t1 t2 t3 t4 : Nat)
    (parse : UuidParser) (x : DecryptGhost)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (peerIdKeyName : List (BitVec 8))
    (kitEnv : SessionStoreBudgetEnv
      (cliSessionStoreSpec A 0#64 cliIo.rd (runFiles i) pathOk scopeKit peer s1 s2 s3 s4))
    (ikitEnv : IdentityStoreBudgetEnv
      (cliIdentityStoreSpec A 0#64 cliIo.rd (runFiles i) pathOk peer t1 t2 t3 t4))
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    {fileCap idFileCap deserCum deserLive deserPeak deserMaxReq
     c_td l_td p_td r_td : Nat}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (hpeerAddr : peer.val = addrValOf peerAddr)
    (hrem : x.rem.val = peer.val)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hremName : x.rem.name.bytes.length ≤ 40)
    (hidKeyLen : peerIdKeyName.length ≤ 64)
    (hSessFileCap : ∀ bs,
      cliIo.rd (runFiles i) (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hIdFileCap : ∀ bs,
      cliIo.rd (runFiles i) (pathOf StoresGhost.opened.identity.peers.path peerIdKeyName) = .ok bs →
      bs.length ≤ idFileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hLoadEq : ∀ evs,
      kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv (runFiles i) StoresGhost.opened.sessions peer evs)
    (hTrustEq : ∀ k evs,
      ikitEnv.trustPollEnv StoresGhost.opened.identity x.rem.val k .receiving evs →
      CliSmallStorePollEnv cliIo.rd (runFiles i) StoresGhost.opened.identity.peers peerIdKeyName evs)
    (hSaveEq : ∀ k evs,
      ikitEnv.savePollEnv StoresGhost.opened.identity x.rem.val k evs →
      CliSmallStorePollEnv cliIo.rd (runFiles i) StoresGhost.opened.identity.peers peerIdKeyName evs)
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
      TopStateTight W.C.F W.Q.K ses.state.pqRatchetState →
      ValidEncoderPts640 ses.state.pqRatchetState →
      ValidChainParams ses.state.pqRatchetState →
      ses.state.pqRatchetState.length < 2 ^ 31 →
      ses.state.pqRatchetState.length ≤ fileCap →
      PhaseCreditSpec fineCostModel
        (tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁))
        c_td l_td p_td r_td) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd (runFiles i) pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd (runFiles i) pathOk peer t1 t2 t3 t4
    let pqCap' := fileCap + 1128000
    let encCap' := fileCap + 3225192
    let c_ld := sessLoadPollTightDeltaCum (max 0 fileCap) deserCum
    let l_ld := sessLoadPollTightDeltaLive (max 0 fileCap) deserLive
    let p_ld := sessLoadPollTightDeltaPeak (max 0 fileCap) deserPeak
    let r_ld := sessLoadPollTightMaxReq (max 0 fileCap) deserMaxReq
    let c_rd := 8286380 + c_td
    let l_rd := 1080975 + optLargeCost fineCostModel fileCap + l_td
    let p_rd := 1080975 + optLargeCost fineCostModel fileCap + max p_td l_td
    let r_rd := max (max 208000 fileCap) (max r_td 192)
    let c_id := smallStorePollTightDeltaCum (max 0 idFileCap) 0
    let l_id := smallStorePollTightDeltaLive (max 0 idFileCap) 0
    let p_id := smallStorePollTightDeltaPeak (max 0 idFileCap) 0
    let r_id := smallStorePollTightMaxReq (max 0 idFileCap) 0
    let c_st := sessStorePollTightDeltaCum 8420940 0
    let l_st := sessStorePollTightDeltaLive (optLargeCost fineCostModel encCap') 0
    let p_st := sessStorePollTightDeltaPeak
      (1080975 + optLargeCost fineCostModel pqCap' + optLargeCost fineCostModel encCap') 0
    let r_st := sessStorePollMaxReq (max (max 208000 pqCap') encCap') 0
    let c_ld_step := 488 + c_ld
    let c_id_step := 738 + c_id
    let c_st_step := 738 + c_st
    let c_kr := c_id_step + max 738 (c_id_step + c_st_step)
    let l_kr := l_id + (l_id + l_st)
    let p_kr := max p_id (l_id + max p_id (l_id + p_st))
    let r_kr := max (max 32 r_id) (max 40 (max (max 32 r_id) (max 32 r_st)))
    PhaseCreditSpec fineCostModel
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity W.C (spqrV1 W.C.F W.Q.K) parse tdEnv scopeKit x)
      (c_ld_step + max 738 (c_rd + c_kr))
      (l_ld + (l_rd + l_kr))
      (max p_ld (l_ld + max p_rd (l_rd + p_kr)))
      (max (max 24 r_ld) (max (max 40 17) (max r_rd r_kr))) := by
  have hStateTight : PeerSpqrStateTight640 W.C.F W.Q.K (runFiles i) x.rem.val := by
    rw [hrem, hpeerAddr]
    exact peerSpqrStateTight640_of_cliPqInputs_recv hi hparse
  exact w2CliDecryptSlot_polls_stateTight640_fine_creditSpec (runFiles i) pathOk peer
    s1 s2 s3 s4 t1 t2 t3 t4 W.C W.Q.K parse x DeserEnv peerIdKeyName kitEnv ikitEnv tdEnv
    hrem hpeer hremName hidKeyLen hStateTight hSessFileCap hIdFileCap hDeser
    hLoadEq hTrustEq hSaveEq hStoreEq hTd

end LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWrappers
