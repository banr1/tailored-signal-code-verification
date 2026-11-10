/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactSplit
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
import LibsignalBinary.Proofs.E2E.Epochs
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Defs
import LibsignalBinary.Proofs.E2E.RecordX.ScopeP
import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps
import LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec
import LibsignalBinary.Proofs.PeakBudget.SpqrSendTieLemmas
import LibsignalBinary.Proofs.PeakBudget.SpqrSendTightSpec
import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
import LibsignalBinary.Proofs.PeakBudget.W1EncryptPeakSpec
import LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments
import LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux
import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget

/-!
# Guarded-Tight `W1` (`encrypt` `@109`) Group Core

**Checked by Lean.**

Proves `w1x_groupCore_Stmt W`: under `CliPqxdhInputs ⟨W.C, W.Q⟩ g.i`,
`parseArgs = some (.send peerV)`, `PeerSpqrStateTight640 W.C.F W.Q.K w1R.x.F w1R.x.peer.val`,
`w1R.repAlloc = A.repAlloc`, and `W1BinarySendDom (.send peerV) g.i w1R`, the unguarded `@109`
`CliEncryptSlotEnv` satisfies `PhaseGroupSpec fineCostModel … w1EncExactGrpS`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactGr

open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession
  (Crypto IdentityKey Mut OutgoingTripleRatchet SessionState ShaCompress Spqr)
open CryptoGames.LibsignalSessionApi (Direction Session SessionRecord execOk)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams pqxdhSpqrModel)
open CryptoVerification.E2E.Epochs
  (exec_bind exec_get exec_liftE exec_map exec_modifyGet exec_pure exec_set exec_throw)
open CryptoVerification.E2E.Record (RecordRepr encodeRecord)
open CryptoVerification.E2E.RecordX (RecordInScopeP SessionScopeP)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (WithStoresEncGhost storedRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks CliPqxdhInputs Inputs)
open CryptoVerification.SignalSession.Cli (DirGhost StoresGhost addressText)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (EncGhost runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1EncGhost)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs RustCliAllocBudget SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
  (toTempTwinsIkitEnv toTempTwinsKitEnv)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (otrEncryptStepEnv_groupSpec phaseGroupSpec_exists_guarded recordSerializeDomFineGrpS
   recordSerializeSeqFreeEnv_dom_fine_groupSpec withStoresEncTightEnv_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.CliKitEnvFitsExact (w1EncExactGrpS)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactSplit
  (w1x_groupCore_Stmt w1x_sendEnv109)
open LibsignalBinary.Proofs.PeakBudget.CliKitW1SpqrSendAuxR2
  (ckx2_spqrSendCoins109_phaseGroupSpec_of_stateTight640 ckx2_spqrSendTightGroupSOf)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
  (RecordSerializeSeqFreeValidEnv W1BinarySendDom W1BinarySendParams
   w1BinaryIdKitPlacedBudget w1BinarySessKitPlacedBudget)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit (HasFineGroupCredit PhaseGroupSpec)
open LibsignalBinary.Proofs.PeakBudget.RealCliRunEnvMemFixed
  (dirGetEnv_fixed_eq_of_not_overCap not_overCapFile_runFiles_identities
   not_overCapFile_runFiles_sessions w1BinaryIdKitPlacedBudgetFixed
   w1BinarySessKitPlacedBudgetFixed)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps (spqrStateTightCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendPeakSpec (spqrSendTightMaxReq)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTieLemmas
  (peerSpqrStateTight640_of_cliSessionStoreSpecPlaced)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendTightSpec
  (spqrSendTightGroupS spqrSendTightMaxNonFree)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLift (PeerSpqrStateTight640)
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
  (TopStateTight topStateTight_length_le topStateTight_spqrV1_send)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptPeakSpec (OtrEncryptStepEnv)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments (FromKeySegEnv WithStoresEncSegEnv)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak
  (FromOtrTightEnv WithStoresEncTightEnv otrAfterNone otrAfterSome)
open LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
  (peer_and_rem_name_le_40_of_send w1PostPqCap w1SendRealDcanGrpS w1SendRealGrpS)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCloneBounds
  (RecordGhostValid SessionCloneDom sessionCloneDom_of_scopeKit_pq)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (PreKeyMsgNewRawEnv fineCostModel_wireGroupHyps preKeyMsgNewDeltaGrpS preKeyMsgNewRaw_phaseGroup
   signalMessageNewDeltaGrpS signalMessageNew_phaseGroup)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
  (FromApplyEnv FromCmEnv FromKeyEnv FromOtrEnv FromSaveEnv PreKeyPostEncryptEnv SaveStepEnv
   TrustStepEnv WithStoresEncEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
  (deserCancelFineGrpS recordDeserializeCancelEnv_fine_groupSpec)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (RecordDeserializeCancelEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Decimal.ExecPlacedBudget (DecimalEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.PlacedBudgetAux1a (DirGetEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Path.PlacedBudget (PathEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PlacedBudgetAux (DirPutEnv DirPutTailEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.PutStr.PlacedBudgetAux (DirPutStrEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (ReadFileRuleEnvFixed)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkPlacedBudget
  (cliIdentityKitSavePollEnv cliIdentityKitSaveTailEnv cliIdentityKitTrustPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOkCliPlacedBudget
  (AddrTextValEnv cliSessionKitLoadPollEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Ratchet.EncryptLemmas.SlotOfInnerPlacedBudget
  (CliEncryptSlotEnv w1IdKitPlaced w1SessKitPlaced)
open LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlacedBudget (ReadFileRuleEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.LayoutPlacedBudget (OptLoadDeserEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeser (ofBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPollRecordDeserAux
  (addrTextValEnv_decimal_fine_groupSpec dirGetEnv_path_readFile_groupSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
  (OtrEncryptCoreEnv SpqrSendBudgetEnv otrSignalMsgGhost)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
  (SignalMessageNewEnv SignalMessageNewGhost)

attribute [local simp]
  exec_bind exec_get exec_liftE exec_map exec_modifyGet exec_pure exec_set exec_throw

/-! ## `*BudgetFixed` to `*Budget` Reduction on `runFiles` -/

private theorem w1x_gr_sessLoadPoll_fixed_eq {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (a : AddrVal) :
    cliSessionKitLoadPollEnv cliIo.rd scopeKit (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        (ofBytesEnv RecordDeserializeCancelEnv) (runFiles i) StoresGhost.opened.sessions a =
      cliSessionKitLoadPollEnv cliIo.rd scopeKit (AddrTextValEnv DecimalEnv)
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        (ofBytesEnv RecordDeserializeCancelEnv) (runFiles i) StoresGhost.opened.sessions a := by
  unfold cliSessionKitLoadPollEnv
  rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_sessions hi _)]

private theorem w1x_gr_idTrustPoll_fixed_eq {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (a : AddrVal) (k : IdentityKey) (d : Direction) :
    cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        (runFiles i) StoresGhost.opened.identity a k d =
      cliIdentityKitTrustPollEnv (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        (runFiles i) StoresGhost.opened.identity a k d := by
  unfold cliIdentityKitTrustPollEnv
  rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_identities hi _)]

private theorem w1x_gr_idSavePoll_fixed_eq {P : PEParams} {i : Inputs}
    (hi : CliPqxdhInputs P i) (a : AddrVal) (k : IdentityKey) :
    cliIdentityKitSavePollEnv cliIo.rd (DirGetEnv PathEnv (ReadFileRuleEnvFixed cliIo.rd) cliIo.rd)
        DirPutStrEnv (runFiles i) StoresGhost.opened.identity a k =
      cliIdentityKitSavePollEnv cliIo.rd (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        DirPutStrEnv (runFiles i) StoresGhost.opened.identity a k := by
  unfold cliIdentityKitSavePollEnv
  rw [dirGetEnv_fixed_eq_of_not_overCap (not_overCapFile_runFiles_identities hi _)]

private theorem w1x_gr_cliEncryptSlotEnv_fixed_eq_plain [LibsignalPlacement] {M : AllocCostModel}
    {P : PEParams} {i : Inputs} (hi : CliPqxdhInputs P i)
    (A : RustCliAllocBudget M) (B : RunBudgets) (sendEnv : SpqrSendBudgetEnv)
    {x : EncGhost} (hx : x.F = runFiles i) :
    CliEncryptSlotEnv P A B sendEnv
        (w1BinarySessKitPlacedBudgetFixed A.repAlloc B)
        (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B) x =
      CliEncryptSlotEnv P A B sendEnv
        (w1BinarySessKitPlacedBudget A.repAlloc B)
        (w1BinaryIdKitPlacedBudget A.repAlloc B) x := by
  have hload :
      (toTempTwinsKitEnv
          (w1BinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer)).loadPollEnv
          StoresGhost.opened.sessions (w1EncGhost x).rem.val =
        (toTempTwinsKitEnv
          (w1BinarySessKitPlacedBudget A.repAlloc B x.F x.peer)).loadPollEnv
          StoresGhost.opened.sessions (w1EncGhost x).rem.val := by
    change cliSessionKitLoadPollEnv _ _ _ _ _ x.F _ _ = cliSessionKitLoadPollEnv _ _ _ _ _ x.F _ _
    rw [hx]
    exact w1x_gr_sessLoadPoll_fixed_eq hi _
  have htrust : ∀ k,
      (toTempTwinsIkitEnv
          (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer)).trustPollEnv
          StoresGhost.opened.identity (w1EncGhost x).rem.val k .sending =
        (toTempTwinsIkitEnv
          (w1BinaryIdKitPlacedBudget A.repAlloc B x.F x.peer)).trustPollEnv
          StoresGhost.opened.identity (w1EncGhost x).rem.val k .sending := by
    intro k
    change cliIdentityKitTrustPollEnv _ x.F _ _ k .sending =
      cliIdentityKitTrustPollEnv _ x.F _ _ k .sending
    rw [hx]
    exact w1x_gr_idTrustPoll_fixed_eq hi _ k .sending
  have hsave : ∀ k,
      (toTempTwinsIkitEnv
          (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer)).savePollEnv
          ((w1IdKitPlaced A.repAlloc B x.F x.peer).trustUpdate StoresGhost.opened.identity
            (w1EncGhost x).rem.val k .sending (.ok true))
          (w1EncGhost x).rem.val k =
        (toTempTwinsIkitEnv
          (w1BinaryIdKitPlacedBudget A.repAlloc B x.F x.peer)).savePollEnv
          ((w1IdKitPlaced A.repAlloc B x.F x.peer).trustUpdate StoresGhost.opened.identity
            (w1EncGhost x).rem.val k .sending (.ok true))
          (w1EncGhost x).rem.val k := by
    intro k
    change cliIdentityKitSavePollEnv _ _ _ x.F StoresGhost.opened.identity _ _ =
      cliIdentityKitSavePollEnv _ _ _ x.F StoresGhost.opened.identity _ _
    rw [hx]
    exact w1x_gr_idSavePoll_fixed_eq hi _ k
  have hstore :
      (toTempTwinsKitEnv
          (w1BinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer)).storePollEnv =
        (toTempTwinsKitEnv
          (w1BinarySessKitPlacedBudget A.repAlloc B x.F x.peer)).storePollEnv := rfl
  have hcm : ∀ sess (otr' : OutgoingTripleRatchet (List (BitVec 8))) taken k,
      FromCmEnv (w1SessKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsKitEnv (w1BinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer))
          StoresGhost.opened.sessions
          (w1IdKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsIkitEnv (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer))
          StoresGhost.opened.identity (w1EncGhost x) sess otr' taken k =
        FromCmEnv (w1SessKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsKitEnv (w1BinarySessKitPlacedBudget A.repAlloc B x.F x.peer))
          StoresGhost.opened.sessions
          (w1IdKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsIkitEnv (w1BinaryIdKitPlacedBudget A.repAlloc B x.F x.peer))
          StoresGhost.opened.identity (w1EncGhost x) sess otr' taken k := by
    intro sess otr' taken k
    funext evs
    unfold FromCmEnv TrustStepEnv FromSaveEnv SaveStepEnv FromApplyEnv
    rw [htrust k, hsave k, hstore]
  have hotr : ∀ sess otr taken,
      FromOtrEnv P.C (pqxdhSpqrModel P) sendEnv uuidTryParse
          (w1SessKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsKitEnv (w1BinarySessKitPlacedBudgetFixed A.repAlloc B x.F x.peer))
          StoresGhost.opened.sessions
          (w1IdKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsIkitEnv (w1BinaryIdKitPlacedBudgetFixed A.repAlloc B x.F x.peer))
          StoresGhost.opened.identity (w1EncGhost x) sess otr taken =
        FromOtrEnv P.C (pqxdhSpqrModel P) sendEnv uuidTryParse
          (w1SessKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsKitEnv (w1BinarySessKitPlacedBudget A.repAlloc B x.F x.peer))
          StoresGhost.opened.sessions
          (w1IdKitPlaced A.repAlloc B x.F x.peer)
          (toTempTwinsIkitEnv (w1BinaryIdKitPlacedBudget A.repAlloc B x.F x.peer))
          StoresGhost.opened.identity (w1EncGhost x) sess otr taken := by
    intro sess otr taken
    funext evs
    unfold FromOtrEnv FromKeyEnv PreKeyPostEncryptEnv
    simp only [hcm]
  funext evs
  unfold CliEncryptSlotEnv WithStoresEncEnv
  rw [hload]
  simp only [hotr]

/-! ## `WithStoresEncEnv` to `WithStoresEncTightEnv` Containment -/

private theorem w1x_gr_seqEnv_mono {E₁ E₁' E₂ E₂' : List AllocEvent → Prop}
    (h₁ : ∀ e, E₁ e → E₁' e) (h₂ : ∀ e, E₂ e → E₂' e) :
    ∀ evs, SeqEnv E₁ E₂ evs → SeqEnv E₁' E₂' evs
  | _, Or.inl h => Or.inl (h₁ _ h)
  | _, Or.inr ⟨u, v, rfl, hu, hv⟩ => Or.inr ⟨u, v, rfl, h₁ u hu, h₂ v hv⟩

private theorem w1x_gr_otrEncryptCore_imp_step
    (P : PEParams) (sendEnv : SpqrSendBudgetEnv)
    (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (ptext : List (BitVec 8)) (locOpt : Option AddrGhost)
    (rem : AddrGhost) (rest : List (BitVec 8))
    {evs : List AllocEvent}
    (h : OtrEncryptCoreEnv P.C (pqxdhSpqrModel P) sendEnv uuidTryParse otr ptext locOpt rem rest evs) :
    OtrEncryptStepEnv (sendEnv otr.pqrState rest) ptext.length
      (fun evs' => ∃ g0, SignalMessageNewEnv uuidTryParse g0 evs') evs := by
  unfold OtrEncryptCoreEnv at h
  unfold OtrEncryptStepEnv
  refine w1x_gr_seqEnv_mono (fun _ => id) ?_ evs h
  intro evs' hevs'
  cases hs : (pqxdhSpqrModel P).send otr.pqrState rest with
  | none =>
    rw [hs] at hevs'
    have hnil : evs' = [] := hevs'
    subst hnil
    exact Or.inl FreeOnlyEvs.nil
  | some val =>
    rcases val with ⟨_, pqrKey, pqrMsg⟩
    rw [hs] at hevs'
    exact Or.inr
      (w1x_gr_seqEnv_mono (fun _ => id)
        (w1x_gr_seqEnv_mono (fun _ => id)
          (w1x_gr_seqEnv_mono
            (fun _ hsm => ⟨otrSignalMsgGhost P.C otr pqrKey pqrMsg ptext locOpt rem, hsm⟩)
            (fun _ => id)))
        evs' hevs')

private theorem w1x_gr_withStoresEnc_imp_tight {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (P : PEParams) (sendEnv : SpqrSendBudgetEnv)
    (x : WithStoresEncGhost) {evs : List AllocEvent}
    (h : WithStoresEncEnv kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope P.C (pqxdhSpqrModel P) sendEnv uuidTryParse x evs) :
    WithStoresEncTightEnv Scope kit kitEnv st0 ikit ikitEnv ist0 P.C (pqxdhSpqrModel P) uuidTryParse x
      (fun _ _ otr _ =>
        OtrEncryptStepEnv (sendEnv otr.pqrState x.rest) x.ptext.length
          (fun evs' => ∃ g0, SignalMessageNewEnv uuidTryParse g0 evs'))
      (fun _ _ otr _ =>
        OtrEncryptStepEnv (sendEnv otr.pqrState x.rest) x.ptext.length
          (fun evs' => ∃ g0, SignalMessageNewEnv uuidTryParse g0 evs'))
      (fun _ _ _ _ evs' =>
        ∃ kp smLen outLen, PreKeyMsgNewRawEnv kp smLen outLen evs')
      evs := by
  unfold WithStoresEncEnv at h
  unfold WithStoresEncTightEnv
  dsimp only [WithStoresEncSegEnv]
  refine w1x_gr_seqEnv_mono (fun _ hld => hld) ?_ evs h
  intro evs1 hevs1
  rcases hevs1 with hf | hstr | hcur
  · exact Or.inl hf
  · exact Or.inr (Or.inl hstr)
  · refine Or.inr (Or.inr (w1x_gr_seqEnv_mono (fun _ => id) ?_ evs1 hcur))
    intro evs2 hevs2
    rcases hevs2 with hf2 | ⟨r, sess, otr, taken, hScAt, hcurSess, hfrom, hotr⟩
    · exact Or.inl hf2
    · refine Or.inr ⟨r, sess, otr, taken, hScAt, hcurSess, hfrom, ?_⟩
      unfold FromOtrEnv at hotr
      dsimp only [FromOtrTightEnv]
      rcases hotr with hf3 | ⟨k, hremId, hkey⟩
      · exact Or.inl hf3
      · refine Or.inr ⟨k, hremId, ?_⟩
        unfold FromKeyEnv at hkey
        dsimp only [FromKeySegEnv]
        rcases hkey with ⟨hnone, hseqNone⟩ | ⟨items, hsome, hpkBranch⟩
        · exact Or.inl ⟨hnone, w1x_gr_seqEnv_mono
            (fun _ ho => w1x_gr_otrEncryptCore_imp_step P sendEnv otr x.ptext none x.rem x.rest ho)
            (fun _ htail => htail) _ hseqNone⟩
        · refine Or.inr ⟨by simp [hsome], ?_⟩
          rcases hpkBranch with hstr2 | hkybSeq
          · exact Or.inl hstr2
          · refine Or.inr (w1x_gr_seqEnv_mono (fun _ hk => hk)
              (w1x_gr_seqEnv_mono
                (fun _ ho =>
                  w1x_gr_otrEncryptCore_imp_step P sendEnv otr x.ptext (some x.loc) x.rem x.rest ho)
                (fun _ hpost => ?_))
              _ hkybSeq)
            unfold PreKeyPostEncryptEnv at hpost
            dsimp only at hpost
            rcases hpost with hf5 | hresMatch
            · exact Or.inl hf5
            · refine Or.inr ?_
              split at hresMatch
              · exact False.elim hresMatch
              · exact w1x_gr_seqEnv_mono
                  (fun _ hraw => ⟨_, _, _, hraw⟩)
                  (fun _ htail => htail)
                  _ hresMatch

/-! ## Group Bounds for `loadPollEnv`, `savePollEnv`, and `storePollEnv` -/

private theorem w1x_gr_dirPut_opened_groups (M : AllocCostModel) [HasFineGroupCredit M]
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

private theorem w1x_gr_dirPutStr_opened_groups (M : AllocCostModel) [HasFineGroupCredit M]
    {dir : DirGhost} (hch : dir.changed = []) (name bytes : List (BitVec 8)) :
    PhaseGroupSpec M (DirPutStrEnv dir name bytes) (6 * FineScale) := by
  unfold DirPutStrEnv
  split_ifs
  · exact (w1x_gr_dirPut_opened_groups M hch name bytes).mono (by omega)
  · exact ((PhaseGroupSpec.rustAlloc_any M name.length 1).seq
      (w1x_gr_dirPut_opened_groups M hch name bytes)).mono (by omega)

private theorem w1x_gr_saveTail_groups (M : AllocCostModel) [HasFineGroupCredit M]
    (rem : AddrVal) (k : IdentityKey)
    (gr : Except Unit (List (BitVec 8))) :
    PhaseGroupSpec M
      (cliIdentityKitSaveTailEnv DirPutStrEnv StoresGhost.opened.identity rem k gr)
      (9 * FineScale) := by
  unfold cliIdentityKitSaveTailEnv
  cases gr with
  | error u =>
    cases u
    exact (PhaseGroupSpec.nil M).mono (Nat.zero_le _)
  | ok _ =>
    have hPk : PhaseGroupSpec M PublicKeySerializeEnv (3 * FineScale) := by
      unfold PublicKeySerializeEnv publicKeySerializeEvents
      exact PhaseGroupSpec.rustAlloc_any M 33 1
    have hPut : PhaseGroupSpec M
        (DirPutStrEnv StoresGhost.opened.identity.peers rem.name k.serialize)
        (6 * FineScale) :=
      w1x_gr_dirPutStr_opened_groups M rfl rem.name k.serialize
    exact ((PhaseGroupSpec.freeOnly M).seq (hPk.seq hPut)).mono (by omega)

private theorem w1x_gr_trustPoll_groups
    (F0 : FsFiles) (rem : AddrVal) (k : IdentityKey) (d : Direction) :
    PhaseGroupSpec fineCostModel
      (cliIdentityKitTrustPollEnv
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        F0 StoresGhost.opened.identity rem k d)
      (39 * FineScale) := by
  unfold cliIdentityKitTrustPollEnv
  have hGet :=
    dirGetEnv_path_readFile_groupSpec fineCostModel cliIo.rd
      F0 StoresGhost.opened.identity.peers rem.name
  exact PhaseGroupSpec.mono (hGet.seq (PhaseGroupSpec.freeOnly fineCostModel)) (by omega)

private theorem w1x_gr_savePoll_groups
    (F0 : FsFiles) (rem : AddrVal) (k : IdentityKey) :
    PhaseGroupSpec fineCostModel
      (cliIdentityKitSavePollEnv cliIo.rd
        (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
        DirPutStrEnv F0 StoresGhost.opened.identity rem k)
      (48 * FineScale) := by
  unfold cliIdentityKitSavePollEnv
  have hGet :=
    dirGetEnv_path_readFile_groupSpec fineCostModel cliIo.rd
      F0 StoresGhost.opened.identity.peers rem.name
  have hTail := w1x_gr_saveTail_groups fineCostModel rem k
    (StoresGhost.opened.identity.peers.get cliIo.rd F0 rem.name)
  exact PhaseGroupSpec.mono (hGet.seq hTail) (by omega)

private theorem w1x_gr_fromSessionState_pqr_and_taken
    {st : SessionState (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))}
    (h : execOk OutgoingTripleRatchet.fromSessionState st = .ok (otr, taken)) :
    otr.pqrState = st.pqRatchetState ∧ taken = { st with pqRatchetState := [] } := by
  unfold execOk OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState at h
  rcases hsc : st.senderChain with _ | sc
  · simp [hsc] at h
  · simp only [hsc, exec_bind, exec_get, exec_modifyGet] at h
    split_ifs at h
    · simp at h
    · rcases hrem : st.remoteIdentity with _ | remote
      · simp [hrem] at h
      · simp only [hrem, exec_pure, Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        refine ⟨rfl, ?_⟩
        cases st
        dsimp only at hsc hrem
        subst hsc hrem
        rfl

private theorem w1x_gr_otr_encrypt_pqrState_cases {PQC : Type}
    (C : Crypto) (S : Spqr (List (BitVec 8)) PQC)
    (ptext : List (BitVec 8)) (addrs : Option (List (BitVec 8))) (coins : PQC)
    (otr : OutgoingTripleRatchet (List (BitVec 8))) :
    (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S ptext addrs coins) otr).2.pqrState =
      otr.pqrState ∨
    ∃ newPqr pqrKey pqrMsg,
      S.send otr.pqrState coins = some (newPqr, pqrKey, pqrMsg) ∧
      (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S ptext addrs coins) otr).2.pqrState =
        newPqr := by
  unfold OutgoingTripleRatchet.encrypt
  simp only [exec_bind, exec_get]
  cases S.sendPanics otr.pqrState coins
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases S.send otr.pqrState coins with _ | ⟨newPqr, pqrKey, pqrMsg⟩
    · left; simp
    · dsimp only
      rcases otr.senderChainKey.nextChainKey C.F with _ | _
      · left; simp
      · right; refine ⟨newPqr, pqrKey, pqrMsg, rfl, ?_⟩; simp
  · left; simp

private theorem w1x_gr_otr_encrypt_topStateTight
    {F : ShaCompress} {K : MlKem} (C : Crypto) (hF : C.F = F)
    (ptext : List (BitVec 8)) (addrs : Option (List (BitVec 8))) (coins : List (BitVec 8))
    (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (hTop : TopStateTight F K otr.pqrState) :
    TopStateTight F K
      (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec (spqrV1 F K).spqr
        ptext addrs coins) otr).2.pqrState := by
  subst hF
  rcases w1x_gr_otr_encrypt_pqrState_cases C (spqrV1 C.F K).spqr ptext addrs coins otr with
    heq | ⟨newPqr, _, _, hs, heq⟩
  · rw [heq]; exact hTop
  · rw [heq]; exact topStateTight_spqrV1_send hTop hs

private theorem w1x_gr_storedRecord_cloneDom
    {F : ShaCompress} {K : MlKem}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))}
    (hKit : scopeKit r)
    (hcur : r.currentSession = some sess)
    (htaken : taken = { sess.state with pqRatchetState := [] })
    (hTop' : TopStateTight F K otr'.pqrState) :
    ∀ ses, (storedRecord sess otr' taken).currentSession = some ses →
      SessionCloneDom w1PostPqCap ses := by
  subst htaken
  have hpqCap : otr'.pqrState.length ≤ w1PostPqCap := by
    have hle := topStateTight_length_le hTop'
    have heq : spqrStateTightCapBytes = w1PostPqCap := by
      unfold spqrStateTightCapBytes w1PostPqCap spqrSendTightMaxReq
      decide
    rwa [heq] at hle
  have hotr'_lt32 : otr'.pqrState.length < 2 ^ 32 :=
    Nat.lt_of_le_of_lt hpqCap (by unfold w1PostPqCap spqrSendTightMaxReq; decide)
  obtain ⟨⟨hInP, _, hRepr⟩, s0, hs0, hSessP⟩ := hKit
  have hsess_eq : s0 = sess := Option.some.inj (hs0.symm.trans hcur)
  subst hsess_eq
  have hInSess := hInP s0 hcur
  have hReprSess := hRepr s0 hcur
  have hRecIn' :
      RecordInScopeP (storedRecord s0 otr' { s0.state with pqRatchetState := [] }) := by
    intro s' hs'
    simp only [storedRecord, Option.some.injEq] at hs'
    subst hs'
    unfold OutgoingTripleRatchet.applyToSessionState
    exact ⟨hInSess.1, hInSess.2.1, hInSess.2.2⟩
  have hRepr' :
      RecordRepr (storedRecord s0 otr' { s0.state with pqRatchetState := [] }) := by
    intro s' hs'
    simp only [storedRecord, Option.some.injEq] at hs'
    subst hs'
    refine ⟨hReprSess.1, ?_, ?_, hReprSess.2.2.2⟩
    · intro sc' hsc'
      simp only [OutgoingTripleRatchet.applyToSessionState, Option.map_eq_some_iff] at hsc'
      obtain ⟨sc, hsc, rfl⟩ := hsc'
      exact hReprSess.2.1 sc hsc
    · simpa [Session.Wf, OutgoingTripleRatchet.applyToSessionState] using hReprSess.2.2.1
  have hSessP' :
      SessionScopeP
        { s0 with state := otr'.applyToSessionState { s0.state with pqRatchetState := [] } } :=
    ⟨hSessP.1, hSessP.2.1, hSessP.2.2.1, hSessP.2.2.2⟩
  have hScope' :
      scopeKit (storedRecord s0 otr' { s0.state with pqRatchetState := [] }) := by
    refine ⟨⟨hRecIn', ?_, hRepr'⟩, _, rfl, hSessP'⟩
    intro s' hs'
    simp only [storedRecord, Option.some.injEq] at hs'
    subst hs'
    exact hotr'_lt32
  intro ses hses
  have hpqSes : ses.state.pqRatchetState.length ≤ w1PostPqCap := by
    simp only [storedRecord, Option.some.injEq] at hses
    subst hses
    exact hpqCap
  exact sessionCloneDom_of_scopeKit_pq hScope' hses hpqSes

private theorem w1x_gr_loadPoll_groups [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    {rem : AddrVal} (hremName : rem.name.length ≤ 40) :
    PhaseGroupSpec fineCostModel
      ((w1BinarySessKitPlacedBudget A B F0 peer).loadPollEnv
        StoresGhost.opened.sessions rem)
      (45 * FineScale + deserCancelFineGrpS) := by
  change PhaseGroupSpec fineCostModel
    (cliSessionKitLoadPollEnv cliIo.rd scopeKit (AddrTextValEnv DecimalEnv)
      (DirGetEnv PathEnv (ReadFileRuleEnv cliIo.rd) cliIo.rd)
      (ofBytesEnv RecordDeserializeCancelEnv)
      F0 StoresGhost.opened.sessions rem)
    (45 * FineScale + deserCancelFineGrpS)
  unfold cliSessionKitLoadPollEnv
  have hAddr : PhaseGroupSpec fineCostModel (AddrTextValEnv DecimalEnv rem) (6 * FineScale) :=
    addrTextValEnv_decimal_fine_groupSpec rem hremName
  have hGet :=
    dirGetEnv_path_readFile_groupSpec fineCostModel cliIo.rd
      F0 StoresGhost.opened.sessions (addressText rem)
  have hOpt : PhaseGroupSpec fineCostModel
      (OptLoadDeserEnv scopeKit (ofBytesEnv RecordDeserializeCancelEnv)
        (StoresGhost.opened.sessions.get cliIo.rd F0 (addressText rem)))
      deserCancelFineGrpS := by
    unfold OptLoadDeserEnv
    split
    · exact (phaseGroupSpec_exists_guarded fineCostModel
        (fun (r : SessionRecord (List (BitVec 8))) (_ : True) =>
          recordDeserializeCancelEnv_fine_groupSpec (encodeRecord r))).of_imp
        (fun _ ⟨r, _, _, hd⟩ => ⟨r, trivial, hd⟩)
    · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  exact PhaseGroupSpec.mono
    (hAddr.seq (hGet.seq (hOpt.seq (PhaseGroupSpec.freeOnly fineCostModel)))) (by omega)

private theorem w1x_gr_storePoll_groups [LibsignalPlacement]
    (A : RustAlloc) (B : RunBudgets) (F0 : FsFiles) (peer : AddrGhost)
    {rem : AddrVal} (hremName : rem.name.length ≤ 40)
    {r' : SessionRecord (List (BitVec 8))}
    (hDom : ∀ ses, r'.currentSession = some ses → SessionCloneDom w1PostPqCap ses) :
    PhaseGroupSpec fineCostModel
      ((w1BinarySessKitPlacedBudget A B F0 peer).storePollEnv
        StoresGhost.opened.sessions rem r')
      (9 * FineScale + recordSerializeDomFineGrpS) := by
  change PhaseGroupSpec fineCostModel
    (SeqEnv (AddrTextValEnv DecimalEnv rem)
      (SeqEnv (RecordSerializeSeqFreeValidEnv r')
        (DirPutEnv StoresGhost.opened.sessions (addressText rem) (encodeRecord r'))))
    (9 * FineScale + recordSerializeDomFineGrpS)
  have hAddr : PhaseGroupSpec fineCostModel (AddrTextValEnv DecimalEnv rem) (6 * FineScale) :=
    addrTextValEnv_decimal_fine_groupSpec rem hremName
  have hSer : PhaseGroupSpec fineCostModel
      (RecordSerializeSeqFreeValidEnv r') recordSerializeDomFineGrpS :=
    phaseGroupSpec_exists_guarded fineCostModel
      (fun _ hgv => recordSerializeSeqFreeEnv_dom_fine_groupSpec hgv hDom)
  have hPut : PhaseGroupSpec fineCostModel
      (DirPutEnv StoresGhost.opened.sessions (addressText rem) (encodeRecord r'))
      (3 * FineScale) :=
    w1x_gr_dirPut_opened_groups fineCostModel rfl (addressText rem) (encodeRecord r')
  exact (hAddr.seq (hSer.seq hPut)).mono (by omega)

/-! ## Main Group Theorem -/

/-- Group core `PhaseGroupSpec` for the unguarded `@109` `CliEncryptSlotEnv`. -/
theorem w1x_gr_groupCore [LibsignalPlacement] (W : CliHooks) : w1x_groupCore_Stmt W := by
  intro g peerV M A w1R hi hp hGuard _hrep hdom
  obtain ⟨hpeerVal, hxPeer, hrem, _hptext, hxF⟩ := hdom peerV rfl
  rw [w1x_gr_cliEncryptSlotEnv_fixed_eq_plain hi A w1R.B (w1x_sendEnv109 W) hxF]
  let F0 := runFiles g.i
  let gx := w1EncGhost w1R.x
  have hremName : gx.rem.val.name.length ≤ 40 :=
    (peer_and_rem_name_le_40_of_send hp hpeerVal hrem).2
  have hTopRem : PeerSpqrStateTight640 W.C.F W.Q.K F0 gx.rem.val := by
    have hGuard' : PeerSpqrStateTight640 W.C.F W.Q.K F0 w1R.peer.val := by
      rwa [hxF, hxPeer] at hGuard
    rwa [hrem]
  have hLoadGrp :
      PhaseGroupSpec fineCostModel
        ((w1BinarySessKitPlacedBudget A.repAlloc w1R.B F0 w1R.peer).loadPollEnv
          StoresGhost.opened.sessions gx.rem.val)
        (45 * FineScale + deserCancelFineGrpS) :=
    w1x_gr_loadPoll_groups A.repAlloc w1R.B F0 w1R.peer hremName
  have hSigGrp :
      PhaseGroupSpec fineCostModel
        (fun evs' => ∃ g0 : SignalMessageNewGhost, SignalMessageNewEnv uuidTryParse g0 evs')
        signalMessageNewDeltaGrpS :=
    (phaseGroupSpec_exists_guarded fineCostModel
      (fun (g0 : SignalMessageNewGhost) (_ : True) =>
        signalMessageNew_phaseGroup fineCostModel_wireGroupHyps uuidTryParse g0)).of_imp
      (fun _ ⟨g0, hg0⟩ => ⟨g0, trivial, hg0⟩)
  have hPkGrp :
      PhaseGroupSpec fineCostModel
        (fun evs' => ∃ kp smLen outLen, PreKeyMsgNewRawEnv kp smLen outLen evs')
        preKeyMsgNewDeltaGrpS :=
    (phaseGroupSpec_exists_guarded fineCostModel
      (fun p (_ : True) =>
        preKeyMsgNewRaw_phaseGroup fineCostModel_wireGroupHyps p.1 p.2.1 p.2.2)).of_imp
      (fun _ ⟨kp, smLen, outLen, hraw⟩ => ⟨(kp, smLen, outLen), trivial, hraw⟩)
  have hOtrGrp : ∀ r sess otr taken,
      (w1SessKitPlaced A.repAlloc w1R.B F0 w1R.peer).ScopeAt scopeKit
        StoresGhost.opened.sessions gx.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseGroupSpec fineCostModel
        (OtrEncryptStepEnv (w1x_sendEnv109 W otr.pqrState gx.rest) gx.ptext.length
          (fun evs' => ∃ g0, SignalMessageNewEnv uuidTryParse g0 evs'))
        (ckx2_spqrSendTightGroupSOf 109 + 6 * FineScale + signalMessageNewDeltaGrpS) := by
    intro r sess otr taken hScAt hcur hfrom
    obtain ⟨hpqr, _⟩ := w1x_gr_fromSessionState_pqr_and_taken hfrom
    have hTopOtr : TopStateTight W.C.F W.Q.K otr.pqrState :=
      peerSpqrStateTight640_of_cliSessionStoreSpecPlaced hScAt hcur hpqr hTopRem
    exact otrEncryptStepEnv_groupSpec fineCostModel
      (ckx2_spqrSendCoins109_phaseGroupSpec_of_stateTight640 (Or.inr hTopOtr))
      hSigGrp
  have hStoreNoneGrp : ∀ r sess otr taken (_k : IdentityKey),
      (w1SessKitPlaced A.repAlloc w1R.B F0 w1R.peer).ScopeAt scopeKit
        StoresGhost.opened.sessions gx.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some _k →
      PhaseGroupSpec fineCostModel
        ((w1BinarySessKitPlacedBudget A.repAlloc w1R.B F0 w1R.peer).storePollEnv
          StoresGhost.opened.sessions gx.rem.val
          (storedRecord sess (otrAfterNone W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) gx otr) taken))
        (9 * FineScale + recordSerializeDomFineGrpS) := by
    intro r sess otr taken _ hScAt hcur hfrom _
    obtain ⟨hpqr, htaken⟩ := w1x_gr_fromSessionState_pqr_and_taken hfrom
    have hTopOtr : TopStateTight W.C.F W.Q.K otr.pqrState :=
      peerSpqrStateTight640_of_cliSessionStoreSpecPlaced hScAt hcur hpqr hTopRem
    have hTop' :
        TopStateTight W.C.F W.Q.K
          (otrAfterNone W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) gx otr).pqrState :=
      w1x_gr_otr_encrypt_topStateTight W.C rfl gx.ptext none gx.rest otr hTopOtr
    exact w1x_gr_storePoll_groups A.repAlloc w1R.B F0 w1R.peer hremName
      (w1x_gr_storedRecord_cloneDom hScAt.1 hcur htaken hTop')
  have hStoreSomeGrp : ∀ r sess otr taken (_k : IdentityKey),
      (w1SessKitPlaced A.repAlloc w1R.B F0 w1R.peer).ScopeAt scopeKit
        StoresGhost.opened.sessions gx.rem.val r →
      r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some _k →
      PhaseGroupSpec fineCostModel
        ((w1BinarySessKitPlacedBudget A.repAlloc w1R.B F0 w1R.peer).storePollEnv
          StoresGhost.opened.sessions gx.rem.val
          (storedRecord sess (otrAfterSome W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse gx otr) taken))
        (9 * FineScale + recordSerializeDomFineGrpS) := by
    intro r sess otr taken _ hScAt hcur hfrom _
    obtain ⟨hpqr, htaken⟩ := w1x_gr_fromSessionState_pqr_and_taken hfrom
    have hTopOtr : TopStateTight W.C.F W.Q.K otr.pqrState :=
      peerSpqrStateTight640_of_cliSessionStoreSpecPlaced hScAt hcur hpqr hTopRem
    have hTop' :
        TopStateTight W.C.F W.Q.K
          (otrAfterSome W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse gx otr).pqrState :=
      w1x_gr_otr_encrypt_topStateTight W.C rfl gx.ptext _ gx.rest otr hTopOtr
    exact w1x_gr_storePoll_groups A.repAlloc w1R.B F0 w1R.peer hremName
      (w1x_gr_storedRecord_cloneDom hScAt.1 hcur htaken hTop')
  have hTightGrp :=
    withStoresEncTightEnv_groupSpec fineCostModel scopeKit
      (w1SessKitPlaced A.repAlloc w1R.B F0 w1R.peer)
      (w1BinarySessKitPlacedBudget A.repAlloc w1R.B F0 w1R.peer)
      StoresGhost.opened.sessions
      (w1IdKitPlaced A.repAlloc w1R.B F0 w1R.peer)
      (w1BinaryIdKitPlacedBudget A.repAlloc w1R.B F0 w1R.peer)
      StoresGhost.opened.identity
      W.C (pqxdhSpqrModel ⟨W.C, W.Q⟩) uuidTryParse gx
      hLoadGrp hOtrGrp hOtrGrp
      (fun _ _ _ _ _ _ _ => hPkGrp)
      (fun _ _ _ _ k _ _ _ _ => w1x_gr_trustPoll_groups F0 gx.rem.val k .sending)
      (fun _ _ _ _ k _ _ _ _ => w1x_gr_savePoll_groups F0 gx.rem.val k)
      hStoreNoneGrp hStoreSomeGrp
  have hTightCap :
      18 * FineScale + (45 * FineScale + deserCancelFineGrpS) +
          (ckx2_spqrSendTightGroupSOf 109 + 6 * FineScale + signalMessageNewDeltaGrpS) +
          preKeyMsgNewDeltaGrpS + 39 * FineScale + 48 * FineScale +
          (9 * FineScale + recordSerializeDomFineGrpS) ≤
        w1EncExactGrpS := by
    unfold w1EncExactGrpS w1SendRealDcanGrpS w1SendRealGrpS
      ckx2_spqrSendTightGroupSOf spqrSendTightGroupS spqrSendTightMaxNonFree
    omega
  have hPlain :
      PhaseGroupSpec fineCostModel
        (CliEncryptSlotEnv ⟨W.C, W.Q⟩ A w1R.B (w1x_sendEnv109 W)
          (w1BinarySessKitPlacedBudget A.repAlloc w1R.B)
          (w1BinaryIdKitPlacedBudget A.repAlloc w1R.B) w1R.x)
        w1EncExactGrpS := by
    unfold CliEncryptSlotEnv
    rw [hxF, hxPeer]
    exact (hTightGrp.mono hTightCap).of_imp
      (fun _ hevs =>
        w1x_gr_withStoresEnc_imp_tight
          (w1SessKitPlaced A.repAlloc w1R.B F0 w1R.peer)
          (w1BinarySessKitPlacedBudget A.repAlloc w1R.B F0 w1R.peer)
          StoresGhost.opened.sessions
          (w1IdKitPlaced A.repAlloc w1R.B F0 w1R.peer)
          (w1BinaryIdKitPlacedBudget A.repAlloc w1R.B F0 w1R.peer)
          StoresGhost.opened.identity
          scopeKit ⟨W.C, W.Q⟩ (w1x_sendEnv109 W) gx hevs)
  exact hPlain

end LibsignalBinary.Proofs.PeakBudget.CliKitW1EncExactGr
