/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process.Semantics
public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliSlotFineSpec
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
public import LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit
public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWrappers
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak
public import LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySpec
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionSpec
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommit
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.KitRelDet
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.Process
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.SignalSession.PqDir
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.FilesOk

@[expose] public section

set_option autoImplicit false

/-!
# Concrete W2 (`recv` Whisper) Real Slot Closure

Instantiates `SingleSlotFineSpec` for the W2 `recv` SignalMessage (`WithStoresDecEnv` on
`StoresGhost.opened`) slot under `CliPqxdhInputs W i` and `.recv peerAddr`, both parametrically in
`DeserEnv` and hard-wired with `RecordDeserializeCancelEnv`, and discharges the
`cliRecvWhisperSlot*Cap` numerical ceilings.
-/

namespace LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot

open Arm64.Process (bytesOfString initFsState)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey ShaCompress)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams wirePrekey wireWhisper)
open CryptoVerification.E2E.Record (encodeRecord)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (recGhostOf)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Message MlKem PqRatchetState States V1Recv V1State VersionNegotiationPB
   spqrAuthApi spqrPolyApi spqrV1)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost UuidParser uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession
  (CliPqxdhInputs Cmd Inputs PqParty bundleDir partyAddress pqInitInputs pqRecvInputs pqSendInputs)
open CryptoVerification.SignalSession.Cli (DirGhost StoresGhost addressText cliInputs pathOf)
open CryptoVerification.SignalSession.Cli.KitInst
  (cliIdentityStoreSpec cliIdentityVtRoSym cliSessionKitSpecPlaced cliSessionStoreSpec
   cliSessionVtRoSym)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV CallV cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunRefine (parseArgs_init parseArgs_send)
open CryptoVerification.SignalSession.Cli.Slots
  (callPeer_of_cmd partyAddr pqIdBytes pqIdGet_recv scopeIn scopeKit)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (FilesBounded parseArgs_peer_name_length_le)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds (W2TryDecryptTightEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRunPeakSpec
  (cliIo_rd_runFiles_length_le_of_filesBounded)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetSpec
  (SingleSlotFineSpec cliRecvWhisperSlotCumCap cliRecvWhisperSlotGrpSCap cliRecvWhisperSlotLiveCap
   cliRecvWhisperSlotPeakCap cliRecvWhisperSlotReqCap)
open LibsignalBinary.Proofs.PeakBudget.DirPeakSpec
  (CliAddrTextEnv CliDirGetEnv CliDirPutEnv)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessLoadPollEnv CliSessStorePollEnv CliSmallStorePollEnv
   sessLoadPollTightDeltaCum sessLoadPollTightDeltaLive sessLoadPollTightDeltaPeak
   sessLoadPollTightMaxReq sessStorePollMaxReq sessStorePollTightDeltaCum
   sessStorePollTightDeltaLive sessStorePollTightDeltaPeak
   smallStorePollTightDeltaCum smallStorePollTightDeltaLive smallStorePollTightDeltaPeak
   smallStorePollTightMaxReq)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (optLargeCost)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit (RecordSerializeCancelEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedEnv (SpqrRecvC07C09aTightLinkedEnv)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedGroupSplit
  (w2TryDecryptTightEnv_c07c09a_linked_fine_groupSpec_split_12
   w2TryDecrypt_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvLinkedWrappers
  (scopeIn_of_scopeKit_and_recordSpqrStateTight640
   w2CliDecryptSlot_polls_cliPqInputs_fine_creditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightGroupSplit (w2TryDecryptTightGroupS_split_12)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps (ValidChainParams ValidEncoderPts640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift
  (PeerSpqrStateTight640 RecordSpqrStateTight640 TopStateTight
   peerSpqrStateTight640_of_cliPqInputs_recv peerSpqrStateTight640_of_cliSessionStoreSpec
   recordSpqrStateTight640_of_cliSessionStoreSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (topStateTight_to_tightValid640)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (RecordGhostValid SessionCloneDom recordDecrypt_dom_phaseGroup)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
  (DoublingChainLe w2TryDecryptMaxReq w2TryDecryptTightLive w2TryDecryptTightPeak)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptSlotPeak
  (cliSessLoadPoll_phaseGroupSpec cliSessStorePoll_exists_dom_phaseGroupSpec
   cliSmallStorePoll_phaseGroupSpec decryptRecord_post_caps_of_scopeIn
   opened_scopeAt_encodeRecord_le opened_scopeAt_sessionCloneDom withStoresDec_phaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738 (w2TryDecryptSeeds738Cum)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (SessionGhostValid WithStoresDecEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (RecordDeserializeCancelEnv deserCancelFineCum deserCancelFineGrpS deserCancelFineLive
   deserCancelFineMaxReq deserCancelFinePeak recordDeserializeCancelEnv_fine_groupSpec
   recordDeserializeCancelEnv_fine_phaseCreditSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (cliSessionKitBudgetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
  (ofBytesEnv w2_hLoadEq_of_cliSessionKitBudgetEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (TryDecryptEnvArgs recordTryDecryptEnvArgs)

/-! ## 1. Linked `PhaseGroupSpec` Companions -/

private theorem phaseGroup_exists {α : Sort _} {P : α → List AllocEvent → Prop} {g : Nat}
    (h : ∀ a, PhaseGroupSpec fineCostModel (P a) g) :
    PhaseGroupSpec fineCostModel (fun evs => ∃ a, P a evs) g where
  groups_le st0 {_} := fun ⟨a, hevs⟩ => (h a).groups_le st0 hevs

private theorem phaseGroup_and_left {Q : Prop} {P : List AllocEvent → Prop} {g : Nat}
    (h : Q → PhaseGroupSpec fineCostModel P g) :
    PhaseGroupSpec fineCostModel (fun evs => Q ∧ P evs) g where
  groups_le st0 {_} hqp := (h hqp.1).groups_le st0 hqp.2

private theorem phaseCredit_exists {α : Sort _} {P : α → List AllocEvent → Prop}
    {c l p r : Nat}
    (h : ∀ a, PhaseCreditSpec fineCostModel (P a) c l p r) :
    PhaseCreditSpec fineCostModel (fun evs => ∃ a, P a evs) c l p r where
  req_align evs := fun ⟨a, hevs⟩ ev hev => (h a).req_align evs hevs ev hev
  credit_le st0 {_} := fun ⟨a, hevs⟩ => (h a).credit_le st0 hevs

private theorem phaseCredit_and_left {Q : Prop} {P : List AllocEvent → Prop}
    {c l p r : Nat}
    (h : Q → PhaseCreditSpec fineCostModel P c l p r) :
    PhaseCreditSpec fineCostModel (fun evs => Q ∧ P evs) c l p r where
  req_align evs hqp ev hev := (h hqp.1).req_align evs hqp.2 ev hev
  credit_le st0 {_} hqp := (h hqp.1).credit_le st0 hqp.2

private theorem w2CliSlot_group_bound {g_deser g_td : Nat} :
    (196608 + (2752512 + g_deser)) +
      max 196608 ((173274672 + g_td) +
        ((196608 + 9437184) + max 196608 ((196608 + 9437184) + (196608 + 173471280)))) ≤
      369159264 + g_deser + g_td := by
  have hkr : (196608 + 9437184) + max 196608 ((196608 + 9437184) + (196608 + 173471280)) =
      192935472 := by decide
  rw [hkr]
  have hld : 196608 + (2752512 + g_deser) = 2949120 + g_deser := by
    rw [← Nat.add_assoc 196608 2752512 g_deser, show 196608 + 2752512 = 2949120 by decide]
  rw [hld]
  have hrd : (173274672 + g_td) + 192935472 = 366210144 + g_td := by
    rw [Nat.add_assoc 173274672 g_td 192935472,
        Nat.add_comm g_td 192935472,
        ← Nat.add_assoc 173274672 192935472 g_td,
        show 173274672 + 192935472 = 366210144 by decide]
  rw [hrd]
  have hmax : max 196608 (366210144 + g_td) = 366210144 + g_td :=
    Nat.max_eq_right (Nat.le_trans (by decide : 196608 ≤ 366210144) (Nat.le_add_right _ g_td))
  rw [hmax]
  have htot : (2949120 + g_deser) + (366210144 + g_td) = 369159264 + g_deser + g_td := by
    rw [Nat.add_assoc 2949120 g_deser (366210144 + g_td),
        ← Nat.add_assoc g_deser 366210144 g_td,
        Nat.add_comm g_deser 366210144,
        Nat.add_assoc 366210144 g_deser g_td,
        ← Nat.add_assoc 2949120 366210144 (g_deser + g_td),
        show 2949120 + 366210144 = 369159264 by decide,
        ← Nat.add_assoc 369159264 g_deser g_td]
  exact Nat.le_of_eq htot

/-- `PeerSpqrStateTight640` group-spec companion to `w2CliDecryptSlot_polls_stateTight640_fine_creditSpec`.
-/
theorem w2CliDecryptSlot_polls_stateTight640_linked_fine_groupSpec {A : RustAlloc}
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
    {fileCap g_deser g_td : Nat}
    (hrem : x.rem.val = peer.val)
    (hStateTight : PeerSpqrStateTight640 C.F K F x.rem.val)
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
      PhaseGroupSpec fineCostModel
        (tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁))
        g_td) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4
    PhaseGroupSpec fineCostModel
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity C (spqrV1 C.F K) parse tdEnv scopeKit x)
      (369159264 + g_deser + g_td) := by
  intro kit ikit
  have hLoadPoll : PhaseGroupSpec fineCostModel
      (kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val) (2752512 + g_deser) :=
    (cliSessLoadPoll_phaseGroupSpec hDeser).of_imp hLoadEq
  have hSmallId : PhaseGroupSpec fineCostModel
      (CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName)
      9437184 :=
    cliSmallStorePoll_phaseGroupSpec cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName
  refine (withStoresDec_phaseGroupSpec
    (kit := kit) (kitEnv := kitEnv) (st0 := StoresGhost.opened.sessions)
    (ikit := ikit) (ikitEnv := ikitEnv) (ist0 := StoresGhost.opened.identity)
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
      exact recordDecrypt_dom_phaseGroup
        (x := recGhostOf x 0#64 G ses.state) (ses := ses) rfl hgv hDom
        (fun G₁ hRel => hTd rec ses G G₁ hIn hcur hgv hDom hRel hTop hVe hVcp hPqLt31 hPqFile))
    (fun _ _ _ _ k _ _ _ _ => hSmallId.of_imp (hTrustEq k))
    (fun _ _ _ _ k _ _ _ _ => hSmallId.of_imp (hSaveEq k))
    (fun rec _ rec' ses' _ hsc hdec hc' _ => by
      have hRecTight : RecordSpqrStateTight640 C.F K rec :=
        recordSpqrStateTight640_of_cliSessionStoreSpec hsc hStateTight
      have hIn : scopeIn rec :=
        scopeIn_of_scopeKit_and_recordSpqrStateTight640 hsc.1 hRecTight
      have hEncPre : (encodeRecord rec).length ≤ fileCap :=
        opened_scopeAt_encodeRecord_le hrem hSessFileCap hsc
      obtain ⟨hKit', hPostDom, _⟩ := decryptRecord_post_caps_of_scopeIn hIn hEncPre hdec
      obtain ⟨_, hDomPost⟩ := hPostDom ses' hc'
      exact (cliSessStorePoll_exists_dom_phaseGroupSpec
        (pqCap := fileCap + 1128000)
        (fun s hs => by rw [hc'] at hs; injection hs with hs; subst hs; exact hDomPost)).of_imp
        (fun evs h => hStoreEq rec' evs hKit' h))).mono w2CliSlot_group_bound

/-- Parametric `hTd` `CliPqxdhInputs W i` group-spec companion. -/
theorem w2CliDecryptSlot_polls_cliPqInputs_fine_groupSpec {A : RustAlloc}
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
    {fileCap g_deser g_td : Nat}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (hpeerAddr : peer.val = addrValOf peerAddr)
    (hrem : x.rem.val = peer.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd (runFiles i) (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (DeserEnv bs) g_deser)
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
      PhaseGroupSpec fineCostModel
        (tdEnv (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁))
        g_td) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd (runFiles i) pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd (runFiles i) pathOk peer t1 t2 t3 t4
    PhaseGroupSpec fineCostModel
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity W.C (spqrV1 W.C.F W.Q.K) parse tdEnv scopeKit x)
      (369159264 + g_deser + g_td) := by
  have hStateTight : PeerSpqrStateTight640 W.C.F W.Q.K (runFiles i) x.rem.val := by
    rw [hrem, hpeerAddr]
    exact peerSpqrStateTight640_of_cliPqInputs_recv hi hparse
  exact w2CliDecryptSlot_polls_stateTight640_linked_fine_groupSpec (runFiles i) pathOk peer
    s1 s2 s3 s4 t1 t2 t3 t4 W.C W.Q.K parse x DeserEnv peerIdKeyName kitEnv ikitEnv tdEnv
    hrem hStateTight hSessFileCap hDeser hLoadEq hTrustEq hSaveEq hStoreEq hTd

/-- Real W2 `try_decrypt` envelope at `dhCap ≤ 16`, `caps.length ≤ 12`, `DoublingChainLe 2000 caps`, and `SpqrRecvC07C09aTightLinkedEnv`.
-/
def W2RealTdEnv (F : ShaCompress) (K : MlKem)
    (a : TryDecryptEnvArgs) (evs : List AllocEvent) : Prop :=
  ∃ (dhCap : Nat) (needGrow withAddr errAlloc : Bool) (caps : List Nat)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall),
    dhCap ≤ 16 ∧ caps.length ≤ 12 ∧ DoublingChainLe 2000 caps ∧
    W2TryDecryptTightEnv dhCap needGrow caps
      (SpqrRecvC07C09aTightLinkedEnv F K a.st.pqRatchetState
        pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
      withAddr errAlloc a.msg.ciphertext.length evs

theorem w2RealTd_fine_groupSpec (F : ShaCompress) (K : MlKem) (a : TryDecryptEnvArgs)
    (hTop : TopStateTight F K a.st.pqRatchetState) :
    PhaseGroupSpec fineCostModel (W2RealTdEnv F K a) w2TryDecryptTightGroupS_split_12 := by
  unfold W2RealTdEnv
  exact
    phaseGroup_exists fun dhCap =>
    phaseGroup_exists fun needGrow =>
    phaseGroup_exists fun withAddr =>
    phaseGroup_exists fun errAlloc =>
    phaseGroup_exists fun caps =>
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
    phaseGroup_and_left fun _ =>
    phaseGroup_and_left fun hcaps =>
    phaseGroup_and_left fun _ =>
      w2TryDecryptTightEnv_c07c09a_linked_fine_groupSpec_split_12 F K
        dhCap needGrow withAddr errAlloc a.msg.ciphertext.length a.st.pqRatchetState
        pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hcaps hTop

/-- Linked `CliPqxdhInputs W i` group-spec companion for the W2 decrypt slot. -/
theorem w2CliDecryptSlot_polls_cliPqInputs_linked_fine_groupSpec {A : RustAlloc}
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
    {fileCap g_deser : Nat}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (hpeerAddr : peer.val = addrValOf peerAddr)
    (hrem : x.rem.val = peer.val)
    (hSessFileCap : ∀ bs,
      cliIo.rd (runFiles i) (pathOf StoresGhost.opened.sessions.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hDeser : ∀ bs, bs.length ≤ 2097152 → PhaseGroupSpec fineCostModel (DeserEnv bs) g_deser)
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
        CliSessStorePollEnv StoresGhost.opened.sessions peer g rec' evs) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd (runFiles i) pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd (runFiles i) pathOk peer t1 t2 t3 t4
    PhaseGroupSpec fineCostModel
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity W.C (spqrV1 W.C.F W.Q.K) parse
        (W2RealTdEnv W.C.F W.Q.K) scopeKit x)
      (369159264 + g_deser + w2TryDecryptTightGroupS_split_12) :=
  w2CliDecryptSlot_polls_cliPqInputs_fine_groupSpec pathOk peer s1 s2 s3 s4 t1 t2 t3 t4
    parse x DeserEnv peerIdKeyName kitEnv ikitEnv (W2RealTdEnv W.C.F W.Q.K)
    hi hparse hpeerAddr hrem hSessFileCap hDeser hLoadEq hTrustEq hSaveEq hStoreEq
    (fun _rec ses G G₁ _hIn _hcur _hgv _hDom _hRel hTop _hVe _hVcp _hPqLt31 _hPqFile =>
      w2RealTd_fine_groupSpec W.C.F W.Q.K (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁)
        hTop)

/-! ## 2. `CliPqxdhInputs` `.recv` Name and Identity-Peers File Bounds -/

private theorem pqRecv_party_idPeers_rd_le_64 {W : PEParams} {st : PqParty}
    {ct : List (BitVec 8)} {rc : BitVec 256} {bs : List (BitVec 8)}
    (hrd : cliIo.rd (runFiles (pqRecvInputs W st ct rc))
      (pathOf StoresGhost.opened.identity.peers.path (partyAddr st.party.other).name) = .ok bs) :
    bs.length ≤ 64 := by
  change StoresGhost.opened.identity.peers.get cliIo.rd
      (runFiles (pqRecvInputs W st ct rc)) (partyAddr st.party.other).name = .ok bs at hrd
  rw [pqIdGet_recv] at hrd
  injection hrd with h
  subst h
  unfold pqIdBytes
  cases st.peerId with
  | none => exact Nat.zero_le 64
  | some k =>
    change k.serialize.length ≤ 64
    have hk : k.serialize.length = 33 := by simp [IdentityKey.serialize, PublicKey.serialize]
    omega

/-- On `.recv peerAddr` under `CliPqxdhInputs W i`, any identity-peers file for `peer.name.bytes` has length `≤ 64`.
-/
theorem idPeers_rd_length_le_64_of_cliPqInputs_recv {W : PEParams} {i : Inputs}
    {peerAddr : AddrV} {peer : AddrGhost}
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (hpeerAddr : peer.val = addrValOf peerAddr) :
    ∀ bs,
      cliIo.rd (runFiles i) (pathOf StoresGhost.opened.identity.peers.path peer.name.bytes) = .ok bs →
      bs.length ≤ 64 := by
  intro bs hrd
  obtain ⟨st, _hwf, hcases⟩ := hi
  have hrecvCase : ∀ (ct : List (BitVec 8)) (rc : BitVec 256),
      parseArgs uuidTryParse ((pqRecvInputs W st ct rc).argv.map bytesOfString) =
        some (.recv peerAddr) →
      cliIo.rd (runFiles (pqRecvInputs W st ct rc))
        (pathOf StoresGhost.opened.identity.peers.path peer.name.bytes) = .ok bs →
      bs.length ≤ 64 := by
    intro ct rc hp hrd'
    have ha : (pqRecvInputs W st ct rc).argv = (Cmd.recv (partyAddress st.party.other)).argv := rfl
    have hpa : addrValOf peerAddr = partyAddr st.party.other :=
      callPeer_of_cmd (.recv (partyAddress st.party.other)) rfl (ha ▸ hp) rfl
    have hpname : peer.name.bytes = (partyAddr st.party.other).name := by
      change peer.val.name = (partyAddr st.party.other).name
      rw [hpeerAddr, hpa]
    rw [hpname] at hrd'
    exact pqRecv_party_idPeers_rd_le_64 hrd'
  rcases hcases with ⟨_, b, t, rfl⟩ | ⟨m, r, _, rfl⟩ | ⟨c, rc, _, rfl⟩ |
      ⟨m, rc, _, rfl⟩ | ⟨c, rc, _, _, _, rfl⟩
  · have ha : (pqInitInputs W st b t).argv = (Cmd.init (partyAddress st.party.other) bundleDir).argv := rfl
    rw [ha, parseArgs_init] at hparse
    cases hparse
  · have ha : (pqSendInputs W st m r).argv = (Cmd.send (partyAddress st.party.other)).argv := rfl
    rw [ha, parseArgs_send] at hparse
    cases hparse
  · exact hrecvCase (wireWhisper :: c) rc hparse hrd
  · exact hrecvCase (wirePrekey :: m.bytes) rc hparse hrd
  · exact hrecvCase c rc hparse hrd

theorem peer_and_rem_name_le_40_of_recv {i : Inputs} {peerAddr : AddrV}
    {peer : AddrGhost} {x : DecryptGhost}
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (hpeerAddr : peer.val = addrValOf peerAddr)
    (hrem : x.rem.val = peer.val) :
    peer.name.bytes.length ≤ 40 ∧
      x.rem.name.bytes.length ≤ 40 ∧
      peer.name.bytes.length ≤ 64 := by
  have hp40 : peerAddr.name.length ≤ 40 := parseArgs_peer_name_length_le hparse
  have hpeer : peer.name.bytes.length ≤ 40 := by
    change peer.val.name.length ≤ 40
    rw [hpeerAddr]
    exact hp40
  have hremName : x.rem.name.bytes.length ≤ 40 := by
    change x.rem.val.name.length ≤ 40
    rw [hrem, hpeerAddr]
    exact hp40
  exact ⟨hpeer, hremName, Nat.le_trans hpeer (by decide)⟩

/-! ## 3. Real W2 Envelopes and `SingleSlotFineSpec` -/

/-- `0`-prev session-record serialize envelope for W2 (`decryptRecord` clears `previousSessions = []`).
-/
def W2RealRecordSerEnv (r : SessionRecord (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  match r.currentSession with
  | none => RecordSerializeCancelEnv ⟨0#64, 0#64, none⟩ r evs
  | some ses =>
    ∃ G : SessionGhost, SessionGhostValid G ses ∧
      RecordSerializeCancelEnv ⟨0#64, 0#64, some G⟩ r evs

/-- `0`-prev `store_session` poll envelope for W2 guarded by `SessionGhostValid G ses`. -/
def W2RealStorePollEnv (peer : AddrGhost) (dir : DirGhost) (_rem : AddrVal)
    (r : SessionRecord (List (BitVec 8))) (evs : List AllocEvent) : Prop :=
  match r.currentSession with
  | none => CliSessStorePollEnv dir peer ⟨0#64, 0#64, none⟩ r evs
  | some ses =>
    ∃ G : SessionGhost, SessionGhostValid G ses ∧
      CliSessStorePollEnv dir peer ⟨0#64, 0#64, some G⟩ r evs

/-- Real W2 `SessionStoreBudgetEnv` on `cliSessionKitSpecPlaced`. -/
def w2RealSessionKitPlacedEnv [LibsignalPlacement] (A : RustAlloc)
    (F : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 : Nat)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (vtSym : String := cliSessionVtRoSym)
    (idVtSym : String := cliIdentityVtRoSym) :
    SessionStoreBudgetEnv
      (cliSessionKitSpecPlaced A cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4 vtSym idVtSym) :=
  cliSessionKitBudgetEnv A cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4
    (fun _ => CliAddrTextEnv peer)
    (CliDirGetEnv (ReadFileRuleEnv cliIo.rd))
    (ofBytesEnv DeserEnv)
    W2RealRecordSerEnv
    (fun d _ _ => SeqEnv (CliDirPutEnv d [] []) FreeOnlyEvs)
    vtSym idVtSym

/-- Real W2 `SessionStoreBudgetEnv` on `cliSessionStoreSpec`. -/
def w2RealSessionKitEnv [LibsignalPlacement] (A : RustAlloc)
    (F : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 : Nat)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop) :
    SessionStoreBudgetEnv
      (cliSessionStoreSpec A 0#64 cliIo.rd F pathOk scopeKit peer s1 s2 s3 s4) where
  loadPollEnv := (w2RealSessionKitPlacedEnv A F pathOk peer s1 s2 s3 s4 DeserEnv).loadPollEnv
  storePollEnv := W2RealStorePollEnv peer

def w2RealIdentityKitEnv {A : RustAlloc}
    (F : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (t1 t2 t3 t4 : Nat) :
    IdentityStoreBudgetEnv
      (cliIdentityStoreSpec A 0#64 cliIo.rd F pathOk peer t1 t2 t3 t4) where
  trustPollEnv ist _ _ _ := CliSmallStorePollEnv cliIo.rd F ist.peers peer.name.bytes
  savePollEnv ist _ _ := CliSmallStorePollEnv cliIo.rd F ist.peers peer.name.bytes

theorem w2Real_hStoreEq [LibsignalPlacement] {A : RustAlloc}
    {F : FsFiles} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {rem : AddrVal} (rec' : SessionRecord (List (BitVec 8))) (evs : List AllocEvent)
    (hst : (w2RealSessionKitEnv A F pathOk peer s1 s2 s3 s4 DeserEnv).storePollEnv
      StoresGhost.opened.sessions rem rec' evs) :
    ∃ g : RecordGhost, RecordGhostValid g rec' ∧
      CliSessStorePollEnv StoresGhost.opened.sessions peer g rec' evs := by
  change W2RealStorePollEnv peer StoresGhost.opened.sessions rem rec' evs at hst
  unfold W2RealStorePollEnv at hst
  rcases hcur : rec'.currentSession with _ | ses
  · rw [hcur] at hst
    have hrgv : RecordGhostValid ⟨0#64, 0#64, none⟩ rec' := by
      simp [RecordGhostValid, hcur]
    exact ⟨⟨0#64, 0#64, none⟩, hrgv, hst⟩
  · rw [hcur] at hst
    obtain ⟨G, hgv, hpoll⟩ := hst
    have hrgv : RecordGhostValid ⟨0#64, 0#64, some G⟩ rec' := by
      simp [RecordGhostValid, hcur]
      exact hgv
    exact ⟨⟨0#64, 0#64, some G⟩, hrgv, hpoll⟩

private theorem dhCap_small_le_16 {dhCap : Nat} (hdh : dhCap ≤ 16) :
    104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
  match dhCap with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 => decide
  | _ + 17 => omega

private theorem w2RealTd_cum_mono {dhCap : Nat} {needGrow : Bool} (hdh : dhCap ≤ 16) :
    w2TryDecryptSeeds738Cum dhCap needGrow 12 23313687 ≤
      w2TryDecryptSeeds738Cum 16 true 12 23313687 := by
  cases needGrow <;> (
    match dhCap with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 => decide
    | _ + 17 => omega)

private theorem w2RealTd_maxReq_mono {dhCap : Nat} (hdh : dhCap ≤ 16) :
    w2TryDecryptMaxReq dhCap 2000 302480 msgCapBytes ≤
      w2TryDecryptMaxReq 16 2000 302480 msgCapBytes := by
  match dhCap with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 => decide
  | _ + 17 => omega

def w2RealTdCum : Nat := w2TryDecryptSeeds738Cum 16 true 12 23313687
def w2RealTdLive : Nat := w2TryDecryptTightLive 2000 605066 msgCapBytes
def w2RealTdPeak : Nat := w2TryDecryptTightPeak 2000 605066 621350 msgCapBytes
def w2RealTdMaxReq : Nat := w2TryDecryptMaxReq 16 2000 302480 msgCapBytes

theorem w2RealTd_phaseCredit (F : ShaCompress) (K : MlKem) (a : TryDecryptEnvArgs)
    (hTop : TopStateTight F K a.st.pqRatchetState)
    (hct : a.msg.ciphertext.length ≤ msgCapBytes) :
    PhaseCreditSpec fineCostModel (W2RealTdEnv F K a)
      w2RealTdCum w2RealTdLive w2RealTdPeak w2RealTdMaxReq := by
  unfold W2RealTdEnv
  exact
    phaseCredit_exists fun dhCap =>
    phaseCredit_exists fun needGrow =>
    phaseCredit_exists fun withAddr =>
    phaseCredit_exists fun errAlloc =>
    phaseCredit_exists fun caps =>
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
    phaseCredit_and_left fun hdh =>
    phaseCredit_and_left fun hcaps =>
    phaseCredit_and_left fun hchain =>
      (w2TryDecrypt_spqrC07_c09a_linked_uncondHist_phaseCreditSpec_seeds738 F K
        a.st.pqRatchetState pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto
        (dhCap_small_le_16 hdh) hcaps hchain hTop hct).mono
        (w2RealTd_cum_mono hdh) (Nat.le_refl _) (Nat.le_refl _) (w2RealTd_maxReq_mono hdh)

def w2RecvWhisperRealCum (deserCum : Nat) : Nat :=
  let fileCap := sessionCapBytes
  let idFileCap := 64
  let c_ld := sessLoadPollTightDeltaCum (max 0 fileCap) deserCum
  let c_rd := 8286380 + w2RealTdCum
  let c_id := smallStorePollTightDeltaCum (max 0 idFileCap) 0
  let c_st := sessStorePollTightDeltaCum 8420940 0
  let c_ld_step := 488 + c_ld
  let c_id_step := 738 + c_id
  let c_st_step := 738 + c_st
  let c_kr := c_id_step + max 738 (c_id_step + c_st_step)
  c_ld_step + max 738 (c_rd + c_kr)

def w2RecvWhisperRealLive (deserLive : Nat) : Nat :=
  let fileCap := sessionCapBytes
  let idFileCap := 64
  let encCap' := fileCap + 3225192
  let l_ld := sessLoadPollTightDeltaLive (max 0 fileCap) deserLive
  let l_rd := 1080975 + optLargeCost fineCostModel fileCap + w2RealTdLive
  let l_id := smallStorePollTightDeltaLive (max 0 idFileCap) 0
  let l_st := sessStorePollTightDeltaLive (optLargeCost fineCostModel encCap') 0
  let l_kr := l_id + (l_id + l_st)
  l_ld + (l_rd + l_kr)

def w2RecvWhisperRealPeak (deserLive deserPeak : Nat) : Nat :=
  let fileCap := sessionCapBytes
  let idFileCap := 64
  let pqCap' := fileCap + 1128000
  let encCap' := fileCap + 3225192
  let l_ld := sessLoadPollTightDeltaLive (max 0 fileCap) deserLive
  let p_ld := sessLoadPollTightDeltaPeak (max 0 fileCap) deserPeak
  let l_rd := 1080975 + optLargeCost fineCostModel fileCap + w2RealTdLive
  let p_rd := 1080975 + optLargeCost fineCostModel fileCap + max w2RealTdPeak w2RealTdLive
  let l_id := smallStorePollTightDeltaLive (max 0 idFileCap) 0
  let p_id := smallStorePollTightDeltaPeak (max 0 idFileCap) 0
  let p_st := sessStorePollTightDeltaPeak
    (1080975 + optLargeCost fineCostModel pqCap' + optLargeCost fineCostModel encCap') 0
  let p_kr := max p_id (l_id + max p_id (l_id + p_st))
  max p_ld (l_ld + max p_rd (l_rd + p_kr))

def w2RecvWhisperRealMaxReq (deserMaxReq : Nat) : Nat :=
  let fileCap := sessionCapBytes
  let idFileCap := 64
  let pqCap' := fileCap + 1128000
  let encCap' := fileCap + 3225192
  let r_ld := sessLoadPollTightMaxReq (max 0 fileCap) deserMaxReq
  let r_rd := max (max 208000 fileCap) (max w2RealTdMaxReq 192)
  let r_id := smallStorePollTightMaxReq (max 0 idFileCap) 0
  let r_st := sessStorePollMaxReq (max (max 208000 pqCap') encCap') 0
  let r_kr := max (max 32 r_id) (max 40 (max (max 32 r_id) (max 32 r_st)))
  max (max 24 r_ld) (max (max 40 17) (max r_rd r_kr))

def w2RecvWhisperRealGrpS (deserGrpS : Nat) : Nat :=
  369159264 + deserGrpS + w2TryDecryptTightGroupS_split_12

theorem w2RecvWhisperReal_live_le_peak (deserLive deserPeak : Nat) :
    w2RecvWhisperRealLive deserLive ≤ w2RecvWhisperRealPeak deserLive deserPeak := by
  unfold w2RecvWhisperRealLive w2RecvWhisperRealPeak
  dsimp only
  set l_ld := sessLoadPollTightDeltaLive (max 0 sessionCapBytes) deserLive
  set p_ld := sessLoadPollTightDeltaPeak (max 0 sessionCapBytes) deserPeak
  have hbody :
      (1080975 + optLargeCost fineCostModel sessionCapBytes + w2RealTdLive) +
        (smallStorePollTightDeltaLive (max 0 64) 0 +
          (smallStorePollTightDeltaLive (max 0 64) 0 +
            sessStorePollTightDeltaLive (optLargeCost fineCostModel (sessionCapBytes + 3225192)) 0)) ≤
      max (1080975 + optLargeCost fineCostModel sessionCapBytes + max w2RealTdPeak w2RealTdLive)
        ((1080975 + optLargeCost fineCostModel sessionCapBytes + w2RealTdLive) +
          max (smallStorePollTightDeltaPeak (max 0 64) 0)
            (smallStorePollTightDeltaLive (max 0 64) 0 +
              max (smallStorePollTightDeltaPeak (max 0 64) 0)
                (smallStorePollTightDeltaLive (max 0 64) 0 +
                  sessStorePollTightDeltaPeak
                    (1080975 + optLargeCost fineCostModel (sessionCapBytes + 1128000) +
                      optLargeCost fineCostModel (sessionCapBytes + 3225192)) 0))) := by
    decide
  exact Nat.le_trans (Nat.add_le_add_left hbody l_ld) (Nat.le_max_right p_ld _)

theorem w2Real_hLoadEq [LibsignalPlacement] {A : RustAlloc}
    {i : Inputs} {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
    {s1 s2 s3 s4 : Nat} {x : DecryptGhost}
    {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    (hrem : x.rem.val = peer.val)
    (hfb : FilesBounded sessionCapBytes (initFsState (cliInputs i))) :
    ∀ evs,
      (w2RealSessionKitEnv A (runFiles i) pathOk peer s1 s2 s3 s4 DeserEnv).loadPollEnv
        StoresGhost.opened.sessions x.rem.val evs →
      CliSessLoadPollEnv cliIo.rd DeserEnv (runFiles i) StoresGhost.opened.sessions peer evs :=
  w2_hLoadEq_of_cliSessionKitBudgetEnv
    (A := A) (F := runFiles i) (pathOk := pathOk) (Scope := scopeKit) (peer := peer)
    (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (fileCap := sessionCapBytes)
    (vtSym := cliSessionVtRoSym) (idVtSym := cliIdentityVtRoSym)
    (AddrValEnv := fun _ => CliAddrTextEnv peer)
    (GetEnv := CliDirGetEnv (ReadFileRuleEnv cliIo.rd))
    (DeserEnv := ofBytesEnv DeserEnv)
    (SerValEnv := W2RealRecordSerEnv)
    (PutEnv := fun d _ _ => SeqEnv (CliDirPutEnv d [] []) FreeOnlyEvs)
    (DeserByBytesEnv := DeserEnv)
    (rem := x.rem.val)
    hrem (by decide : sessionCapBytes ≤ 2097152)
    (cliIo_rd_runFiles_length_le_of_filesBounded hfb
      (pathOf StoresGhost.opened.sessions.path (addressText peer.val)))
    (fun _ h => h) (fun _ h => h) (fun _ _ _ h => h)

/-- Closed W2 `recv`-whisper `SingleSlotFineSpec` on `StoresGhost.opened`, parametric in `(DeserEnv, deserCum, deserLive, deserPeak, deserMaxReq, deserGrpS)`.
-/
def w2RecvWhisperReal_singleSlotFineSpec [LibsignalPlacement] {A : RustAlloc}
    {W : PEParams} {i : Inputs} {peerAddr : AddrV}
    (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 t1 t2 t3 t4 : Nat)
    (parse : UuidParser) (x : DecryptGhost)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (deserCum deserLive deserPeak deserMaxReq deserGrpS : Nat)
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (hpeerAddr : peer.val = addrValOf peerAddr)
    (hrem : x.rem.val = peer.val)
    (hct : x.msg.ciphertext.length ≤ msgCapBytes)
    (hfb : FilesBounded sessionCapBytes (initFsState (cliInputs i)))
    (hDeserCredit : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq)
    (hDeserGrp : ∀ bs, bs.length ≤ 2097152 →
      PhaseGroupSpec fineCostModel (DeserEnv bs) deserGrpS) :
    let kit := cliSessionStoreSpec A 0#64 cliIo.rd (runFiles i) pathOk scopeKit peer s1 s2 s3 s4
    let ikit := cliIdentityStoreSpec A 0#64 cliIo.rd (runFiles i) pathOk peer t1 t2 t3 t4
    let kitEnv := w2RealSessionKitEnv A (runFiles i) pathOk peer s1 s2 s3 s4 DeserEnv
    let ikitEnv := w2RealIdentityKitEnv (A := A) (runFiles i) pathOk peer t1 t2 t3 t4
    SingleSlotFineSpec
      (WithStoresDecEnv kit kitEnv StoresGhost.opened.sessions
        ikit ikitEnv StoresGhost.opened.identity W.C (spqrV1 W.C.F W.Q.K) parse
        (W2RealTdEnv W.C.F W.Q.K) scopeKit x) :=
  { cumB := w2RecvWhisperRealCum deserCum
    liveB := w2RecvWhisperRealLive deserLive
    peakB := w2RecvWhisperRealPeak deserLive deserPeak
    maxReq := w2RecvWhisperRealMaxReq deserMaxReq
    grpS := w2RecvWhisperRealGrpS deserGrpS
    credit_spec := by
      obtain ⟨hpeer, hremName, hidKeyLen⟩ := peer_and_rem_name_le_40_of_recv hparse hpeerAddr hrem
      exact w2CliDecryptSlot_polls_cliPqInputs_fine_creditSpec pathOk peer s1 s2 s3 s4 t1 t2 t3 t4
        parse x DeserEnv peer.name.bytes
        (w2RealSessionKitEnv A (runFiles i) pathOk peer s1 s2 s3 s4 DeserEnv)
        (w2RealIdentityKitEnv (A := A) (runFiles i) pathOk peer t1 t2 t3 t4)
        (W2RealTdEnv W.C.F W.Q.K)
        hi hparse hpeerAddr hrem hpeer hremName hidKeyLen
        (cliIo_rd_runFiles_length_le_of_filesBounded hfb
          (pathOf StoresGhost.opened.sessions.path (addressText peer.val)))
        (idPeers_rd_length_le_64_of_cliPqInputs_recv hi hparse hpeerAddr)
        hDeserCredit (w2Real_hLoadEq hrem hfb) (fun _ _ h => h) (fun _ _ h => h)
        (fun rec' evs _ hst => w2Real_hStoreEq rec' evs hst)
        (fun _rec ses G G₁ _hIn _hcur _hgv _hDom _hRel hTop _hVe _hVcp _hPqLt31 _hPqFile =>
          w2RealTd_phaseCredit W.C.F W.Q.K
            (recordTryDecryptEnvArgs (recGhostOf x 0#64 G ses.state) G₁) hTop hct)
    live_le_peak := w2RecvWhisperReal_live_le_peak deserLive deserPeak
    group_spec :=
      w2CliDecryptSlot_polls_cliPqInputs_linked_fine_groupSpec pathOk peer s1 s2 s3 s4 t1 t2 t3 t4
        parse x DeserEnv peer.name.bytes
        (w2RealSessionKitEnv A (runFiles i) pathOk peer s1 s2 s3 s4 DeserEnv)
        (w2RealIdentityKitEnv (A := A) (runFiles i) pathOk peer t1 t2 t3 t4)
        hi hparse hpeerAddr hrem
        (cliIo_rd_runFiles_length_le_of_filesBounded hfb
          (pathOf StoresGhost.opened.sessions.path (addressText peer.val)))
        hDeserGrp (w2Real_hLoadEq hrem hfb) (fun _ _ h => h) (fun _ _ h => h)
        (fun rec' evs _ hst => w2Real_hStoreEq rec' evs hst) }

/-! ## 4. Kernel `decide` Cap Verification -/

/-- Set A `cliRecvWhisperSlot*Cap` numerical check. -/
theorem w2RecvWhisperReal_bounds_setA_decide :
    w2RecvWhisperRealCum 20638720 ≤ 66500000 ∧
    w2RecvWhisperRealLive 3211282 ≤ 16500000 ∧
    w2RecvWhisperRealPeak 3211282 5316629 ≤ 20500000 ∧
    w2RecvWhisperRealMaxReq 2097152 ≤ 5322344 ∧
    w2RecvWhisperRealGrpS 371994912 ≤ 20000 * FineScale := by
  decide

theorem w2RecvWhisperReal_singleSlotFineSpec_fits_setA [LibsignalPlacement] {A : RustAlloc}
    {W : PEParams} {i : Inputs} {peerAddr : AddrV}
    (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 t1 t2 t3 t4 : Nat)
    (parse : UuidParser) (x : DecryptGhost)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (hpeerAddr : peer.val = addrValOf peerAddr)
    (hrem : x.rem.val = peer.val)
    (hct : x.msg.ciphertext.length ≤ msgCapBytes)
    (hfb : FilesBounded sessionCapBytes (initFsState (cliInputs i)))
    (hDeserCredit : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) 20638720 3211282 5316629 2097152)
    (hDeserGrp : ∀ bs, bs.length ≤ 2097152 →
      PhaseGroupSpec fineCostModel (DeserEnv bs) 371994912) :
    let S := w2RecvWhisperReal_singleSlotFineSpec (A := A) pathOk peer s1 s2 s3 s4 t1 t2 t3 t4
      parse x DeserEnv 20638720 3211282 5316629 2097152 371994912
      hi hparse hpeerAddr hrem hct hfb hDeserCredit hDeserGrp
    S.cumB ≤ 66500000 ∧
    S.liveB ≤ 16500000 ∧
    S.peakB ≤ 20500000 ∧
    S.maxReq ≤ 5322344 ∧
    S.grpS ≤ 20000 * FineScale :=
  w2RecvWhisperReal_bounds_setA_decide

/-- Set B `cliRecvWhisperSlot*Cap` numerical check. -/
theorem w2RecvWhisperReal_bounds_setB_decide :
    w2RecvWhisperRealCum 19417728 ≤ 66500000 ∧
    w2RecvWhisperRealLive 3211282 ≤ 16500000 ∧
    w2RecvWhisperRealPeak 3211282 5316629 ≤ 20500000 ∧
    w2RecvWhisperRealMaxReq 2097152 ≤ 5322344 ∧
    w2RecvWhisperRealGrpS 346829088 ≤ 20000 * FineScale := by
  decide

theorem w2RecvWhisperReal_singleSlotFineSpec_fits_setB [LibsignalPlacement] {A : RustAlloc}
    {W : PEParams} {i : Inputs} {peerAddr : AddrV}
    (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    (s1 s2 s3 s4 t1 t2 t3 t4 : Nat)
    (parse : UuidParser) (x : DecryptGhost)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (hpeerAddr : peer.val = addrValOf peerAddr)
    (hrem : x.rem.val = peer.val)
    (hct : x.msg.ciphertext.length ≤ msgCapBytes)
    (hfb : FilesBounded sessionCapBytes (initFsState (cliInputs i)))
    (hDeserCredit : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec fineCostModel (DeserEnv bs) 19417728 3211282 5316629 2097152)
    (hDeserGrp : ∀ bs, bs.length ≤ 2097152 →
      PhaseGroupSpec fineCostModel (DeserEnv bs) 346829088) :
    let S := w2RecvWhisperReal_singleSlotFineSpec (A := A) pathOk peer s1 s2 s3 s4 t1 t2 t3 t4
      parse x DeserEnv 19417728 3211282 5316629 2097152 346829088
      hi hparse hpeerAddr hrem hct hfb hDeserCredit hDeserGrp
    S.cumB ≤ 66500000 ∧
    S.liveB ≤ 16500000 ∧
    S.peakB ≤ 20500000 ∧
    S.maxReq ≤ 5322344 ∧
    S.grpS ≤ 20000 * FineScale :=
  w2RecvWhisperReal_bounds_setB_decide

/-! ## 5. Hard-Wired `RecordDeserializeCancelEnv` Slot Bundle -/

def w2RecvWhisperRealNoDeserCum : Nat := w2RecvWhisperRealCum 0

def w2RecvWhisperRealDcanCum : Nat := w2RecvWhisperRealCum deserCancelFineCum

def w2RecvWhisperRealDcanLive : Nat := w2RecvWhisperRealLive deserCancelFineLive

def w2RecvWhisperRealDcanPeak : Nat := w2RecvWhisperRealPeak deserCancelFineLive deserCancelFinePeak

def w2RecvWhisperRealDcanMaxReq : Nat := w2RecvWhisperRealMaxReq deserCancelFineMaxReq

def w2RecvWhisperRealDcanGrpS : Nat := w2RecvWhisperRealGrpS deserCancelFineGrpS

theorem w2RecvWhisperRealDcan_live_le_peak :
    w2RecvWhisperRealDcanLive ≤ w2RecvWhisperRealDcanPeak :=
  w2RecvWhisperReal_live_le_peak deserCancelFineLive deserCancelFinePeak

/-- Decomposition and `cliRecvWhisperSlot*Cap` check for the `RecordDeserializeCancelEnv`-wired W2 slot.
-/
theorem w2RecvWhisperReal_dcan_caps_le :
    deserCancelFineCum = 16890453 ∧
    w2RecvWhisperRealDcanCum = w2RecvWhisperRealNoDeserCum + deserCancelFineCum ∧
    w2RecvWhisperRealDcanGrpS = 1222948029 ∧
    w2RecvWhisperRealDcanCum ≤ cliRecvWhisperSlotCumCap ∧
    w2RecvWhisperRealDcanLive ≤ cliRecvWhisperSlotLiveCap ∧
    w2RecvWhisperRealDcanPeak ≤ cliRecvWhisperSlotPeakCap ∧
    w2RecvWhisperRealDcanMaxReq ≤ cliRecvWhisperSlotReqCap ∧
    w2RecvWhisperRealDcanGrpS ≤ cliRecvWhisperSlotGrpSCap := by
  decide

/-- Call-site parameter bundle for the real CLI W2 (`recv` whisper) slot. -/
structure W2RecvWhisperRealParams where
  A : RustAlloc
  pathOk : List (BitVec 8) → Prop
  peer : AddrGhost
  s1 : Nat
  s2 : Nat
  s3 : Nat
  s4 : Nat
  t1 : Nat
  t2 : Nat
  t3 : Nat
  t4 : Nat
  parse : UuidParser
  x : DecryptGhost

/-- Call-site alignment and 1 MiB ciphertext bound for `W2RecvWhisperRealParams` on `.recv peerAddr`.
-/
def W2RecvWhisperRealDom (c : CallV) (R : W2RecvWhisperRealParams) : Prop :=
  ∀ peerAddr, c = .recv peerAddr →
    R.peer.val = addrValOf peerAddr ∧
    R.x.rem.val = R.peer.val ∧
    R.x.msg.ciphertext.length ≤ msgCapBytes

/-- Real CLI W2 (`recv` whisper) slot envelope with `RecordDeserializeCancelEnv` wired into `w2RealSessionKitEnv`.
-/
def W2RecvWhisperRealSlotEnv [LibsignalPlacement]
    (W : PEParams) (i : Inputs) (R : W2RecvWhisperRealParams) (evs : List AllocEvent) : Prop :=
  WithStoresDecEnv
    (cliSessionStoreSpec R.A 0#64 cliIo.rd (runFiles i) R.pathOk scopeKit R.peer
      R.s1 R.s2 R.s3 R.s4)
    (w2RealSessionKitEnv R.A (runFiles i) R.pathOk R.peer R.s1 R.s2 R.s3 R.s4
      RecordDeserializeCancelEnv)
    StoresGhost.opened.sessions
    (cliIdentityStoreSpec R.A 0#64 cliIo.rd (runFiles i) R.pathOk R.peer
      R.t1 R.t2 R.t3 R.t4)
    (w2RealIdentityKitEnv (A := R.A) (runFiles i) R.pathOk R.peer R.t1 R.t2 R.t3 R.t4)
    StoresGhost.opened.identity
    W.C (spqrV1 W.C.F W.Q.K) R.parse
    (W2RealTdEnv W.C.F W.Q.K) scopeKit R.x evs

/-- Closed `SingleSlotFineSpec` for `W2RecvWhisperRealSlotEnv` with `RecordDeserializeCancelEnv` wired in.
-/
def w2RecvWhisperRealSlot_dcan_singleSlotFineSpec [LibsignalPlacement]
    {W : PEParams} {i : Inputs} {peerAddr : AddrV}
    (R : W2RecvWhisperRealParams)
    (hi : CliPqxdhInputs W i)
    (hparse : parseArgs uuidTryParse (i.argv.map bytesOfString) = some (.recv peerAddr))
    (hdom : W2RecvWhisperRealDom (.recv peerAddr) R)
    (hfb : FilesBounded sessionCapBytes (initFsState (cliInputs i))) :
    CliSlotFineSpec.SingleSlotFineSpec (W2RecvWhisperRealSlotEnv W i R) :=
  let h := hdom peerAddr rfl
  let S := w2RecvWhisperReal_singleSlotFineSpec (A := R.A)
    R.pathOk R.peer R.s1 R.s2 R.s3 R.s4 R.t1 R.t2 R.t3 R.t4 R.parse R.x
    RecordDeserializeCancelEnv
    deserCancelFineCum deserCancelFineLive deserCancelFinePeak deserCancelFineMaxReq
    deserCancelFineGrpS
    hi hparse h.1 h.2.1 h.2.2 hfb
    (fun _ hbs => recordDeserializeCancelEnv_fine_phaseCreditSpec hbs)
    (fun bs _ => recordDeserializeCancelEnv_fine_groupSpec bs)
  { cum := w2RecvWhisperRealDcanCum
    live := w2RecvWhisperRealDcanLive
    peak := w2RecvWhisperRealDcanPeak
    maxReq := w2RecvWhisperRealDcanMaxReq
    grpS := w2RecvWhisperRealDcanGrpS
    credit := S.credit_spec
    live_le_peak := S.live_le_peak
    groups := S.group_spec }

end LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot
