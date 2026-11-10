/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
public import LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments
public import LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers

/-!
# W1 `message_encrypt` Callee and CLI Store-Kit Instantiations

Black-box callee instantiations for W1 `message_encrypt`, parametric in `(M : AllocCostModel)
[HasFineReallocCredit M]` under `ModelHyps M` in binary call order: `OutgoingTripleRatchet::encrypt`,
`SignalMessage::new`, `PreKeySignalMessage::new`, CLI `StoreKits` (`load_session`, `store_session`,
`is_trusted_identity`, `save_identity`), and `ScopeAt` SPQR domain-cap bridges.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W1EncryptCalleesPeak

open CryptoGames.LibsignalSession (Mut OutgoingTripleRatchet SessionState)
open CryptoGames.LibsignalSessionApi (Session SessionRecord execOk)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (PreKeyMsgNewCall)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost)
open CryptoVerification.LibsignalSessionRepr (VecGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost UuidParser)
open CryptoVerification.SignalSession.Cli (DirGhost ReadRule StoresGhost addressText pathOf)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1SessKit)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustDeallocEvents)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
  (SignalMessageNewEnv SignalMessageNewGhost)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps (ValidEncoderPts)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
  (PeerSpqrTightValid640 PeerSpqrTightValidAt ValidChainParams ValidEncoderPts640
   ValidEncoderPtsAt peerSpqrTightValidAt_of_w1ScopeAt)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (DirDomainCaps PeerSpqrValid peerSpqrValid_of_scopeAt)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers
  (tryCloneLargeDelta tryCloneSmallDelta)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (PreKeyMsgNewEnv preKeyMsgNewDeltaCum preKeyMsgNewDeltaLive preKeyMsgNewDeltaPeak
   preKeyMsgNewMaxReq preKeyMsgNew_phaseCredit
   signalMessageNewDeltaCum signalMessageNewDeltaLive signalMessageNewDeltaPeak
   signalMessageNewMaxReq signalMessageNew_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessLoadPollEnv CliSessStorePollEnv CliSmallStorePollEnv
   sessLoadPollDeltaCum sessLoadPollDeltaLive sessLoadPollDeltaPeak sessLoadPollMaxReq
   sessLoadPoll_phaseCredit
   sessStorePollDeltaCum sessStorePollDeltaLive sessStorePollDeltaPeak sessStorePollMaxReq
   sessStorePoll_phaseCredit
   smallStorePollDeltaCum smallStorePollDeltaLive smallStorePollDeltaPeak smallStorePollMaxReq
   smallStorePoll_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (recordSerializeCum recordSerializeMaxReq recordSerializeOutLarge recordSerializePeak)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments
  (FromKeySegEnv OtrEncryptStepEnv boxPollDrop_creditSpec_aff boxPollDrop_creditSpec_small
   boxPollDrop_creditSpec_tight fromKeySeg_creditSpec_aff fromKeySeg_creditSpec_tight
   kyberOpt_creditSpec_aff otrEncryptStep_creditSpec otrEncryptStep_creditSpec_small32
   otrEncryptStep_creditSpec_tight stringCloneFree_creditSpec_small)

/-! ## 1. `OutgoingTripleRatchet::encrypt` and `SignalMessage::new` -/

/-- Exact-order `OtrEncryptStepEnv` bound instantiated with `WireMsgPeakSpec.signalMessageNew_phaseCredit` and `E_send`.
-/
theorem otrEncryptWithSigNew_creditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (parse : UuidParser) (sigGhost : SignalMessageNewGhost)
    {E_send : List AllocEvent → Prop} {ptextLen : Nat}
    {c_s l_s p_s r_s : Nat}
    (hSend : PhaseCreditSpec M E_send c_s l_s p_s r_s) :
    let ctLen := (ptextLen / 16 + 1) * 16
    PhaseCreditSpec M (OtrEncryptStepEnv E_send ptextLen (SignalMessageNewEnv parse sigGhost))
      (c_s + (2 * 32 + 9539) + (2 * ctLen + 9539) + signalMessageNewDeltaCum parse sigGhost)
      (l_s + (32 + 8195) + (ctLen + 8195) + signalMessageNewDeltaLive parse sigGhost)
      (max p_s (l_s + (32 + 8195) + (ctLen + 8195) + signalMessageNewDeltaPeak parse sigGhost))
      (max r_s (max 32 (max ctLen (signalMessageNewMaxReq parse sigGhost)))) :=
  otrEncryptStep_creditSpec hM hSend (signalMessageNew_phaseCredit hM parse sigGhost)

/-- Small-regime (`32 ≤ smallMaxReq M`) `OtrEncryptStepEnv` + `SignalMessage::new` bound. -/
theorem otrEncryptWithSigNew_creditSpec_small32 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M)
    (parse : UuidParser) (sigGhost : SignalMessageNewGhost)
    {E_send : List AllocEvent → Prop} {ptextLen : Nat}
    {c_s l_s p_s r_s : Nat}
    (hSend : PhaseCreditSpec M E_send c_s l_s p_s r_s) :
    let ctLen := (ptextLen / 16 + 1) * 16
    PhaseCreditSpec M (OtrEncryptStepEnv E_send ptextLen (SignalMessageNewEnv parse sigGhost))
      (c_s + (2 * 32 + 9539) + (2 * ctLen + 9539) + signalMessageNewDeltaCum parse sigGhost)
      (l_s + (ctLen + 8195) + signalMessageNewDeltaLive parse sigGhost)
      (max p_s (l_s + (ctLen + 8195) + signalMessageNewDeltaPeak parse sigGhost))
      (max r_s (max 32 (max ctLen (signalMessageNewMaxReq parse sigGhost)))) :=
  otrEncryptStep_creditSpec_small32 hM hle32 hSend (signalMessageNew_phaseCredit hM parse sigGhost)

/-- Witness-independent cap wrapper for `otrEncryptWithSigNew_creditSpec_small32`. -/
theorem otrEncryptWithSigNew_capped_small32 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M)
    (parse : UuidParser) (sigGhost : SignalMessageNewGhost)
    {E_send : List AllocEvent → Prop} {ptextLen : Nat}
    {c_s l_s p_s r_s c_n l_n p_n r_n : Nat}
    (hSend : PhaseCreditSpec M E_send c_s l_s p_s r_s)
    (hCum : signalMessageNewDeltaCum parse sigGhost ≤ c_n)
    (hLive : signalMessageNewDeltaLive parse sigGhost ≤ l_n)
    (hPeak : signalMessageNewDeltaPeak parse sigGhost ≤ p_n)
    (hReq : signalMessageNewMaxReq parse sigGhost ≤ r_n) :
    let ctLen := (ptextLen / 16 + 1) * 16
    PhaseCreditSpec M (OtrEncryptStepEnv E_send ptextLen (SignalMessageNewEnv parse sigGhost))
      (c_s + (2 * 32 + 9539) + (2 * ctLen + 9539) + c_n)
      (l_s + (ctLen + 8195) + l_n)
      (max p_s (l_s + (ctLen + 8195) + p_n))
      (max r_s (max 32 (max ctLen r_n))) := by
  intro ctLen
  exact (otrEncryptWithSigNew_creditSpec_small32 hM hle32 parse sigGhost hSend).mono
    (by omega) (by omega) (by omega) (by omega)

/-! ## 2. `FromKeySegEnv` and `PreKeySignalMessage::new` -/

/-- Small-name (`nameCap ≤ smallMaxReq M`) `FromKeySegEnv` bound. -/
theorem fromKeySeg_creditSpec_small {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    {pendingPreKey : Option α} {remName : VecGhost}
    {kyberCt : Option (List (BitVec 8))} {nameCap kyberCap : Nat}
    {E_otrNone E_cmNone E_otrSome E_pksmNew E_cmSome : List AllocEvent → Prop}
    {c_otr l_otr p_otr r_otr c_pk l_pk p_pk r_pk c_cm l_cm p_cm r_cm : Nat}
    (hName : remName.bytes.length ≤ nameCap)
    (hNameSmall : nameCap ≤ HasFineReallocCredit.smallMaxReq M)
    (hKyber : ∀ bs, kyberCt = some bs → bs.length ≤ kyberCap)
    (hOtrNone : PhaseCreditSpec M E_otrNone c_otr l_otr p_otr r_otr)
    (hOtrSome : PhaseCreditSpec M E_otrSome c_otr l_otr p_otr r_otr)
    (hPksmNew : PhaseCreditSpec M E_pksmNew c_pk l_pk p_pk r_pk)
    (hCmNone : PhaseCreditSpec M E_cmNone c_cm l_cm p_cm r_cm)
    (hCmSome : PhaseCreditSpec M E_cmSome c_cm l_cm p_cm r_cm) :
    PhaseCreditSpec M
      (FromKeySegEnv pendingPreKey remName kyberCt E_otrNone E_cmNone E_otrSome E_pksmNew E_cmSome)
      (max (2 * nameCap + 9539) ((2 * kyberCap + 9539) + c_otr + c_pk + c_cm))
      ((kyberCap + 8195) + l_otr + l_pk + l_cm)
      ((kyberCap + 8195) + max p_otr (l_otr + max p_pk (l_pk + p_cm)))
      (max nameCap (max kyberCap (max r_otr (max r_pk r_cm)))) := by
  have hFree := PhaseCreditSpec.freeOnly hM.freeNonInc
  have hNonePath := hOtrNone.seq (PhaseCreditSpec.or hFree hCmNone)
  have hClonePath := stringCloneFree_creditSpec_small hM hName hNameSmall
  have hPkTail := hPksmNew.seq (PhaseCreditSpec.or hFree hCmSome)
  have hOtrTail := hOtrSome.seq (PhaseCreditSpec.or hFree hPkTail)
  have hSomeOk := (kyberOpt_creditSpec_aff hM hKyber).seq hOtrTail
  have hSomePath := PhaseCreditSpec.or hClonePath hSomeOk
  refine (PhaseCreditSpec.or_of_imp
    (himp := fun _ h => h.elim (fun h1 => Or.inl h1.2) (fun h2 => Or.inr h2.2))
    hNonePath hSomePath).mono (by omega) (by omega) (by omega) (by omega)

/-- `FromKeySegEnv` instantiated with `WireMsgPeakSpec.preKeyMsgNew_phaseCredit` under witness-independent caps.
-/
theorem fromKeyWithPksm_capped_aff {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (pkCall : PreKeyMsgNewCall)
    {pendingPreKey : Option α} {remName : VecGhost}
    {kyberCt : Option (List (BitVec 8))} {nameCap kyberCap : Nat}
    {E_otrNone E_cmNone E_otrSome E_cmSome : List AllocEvent → Prop}
    {c_otr l_otr p_otr r_otr c_pk l_pk p_pk r_pk c_cm l_cm p_cm r_cm : Nat}
    (hName : remName.bytes.length ≤ nameCap)
    (hKyber : ∀ bs, kyberCt = some bs → bs.length ≤ kyberCap)
    (hOtrNone : PhaseCreditSpec M E_otrNone c_otr l_otr p_otr r_otr)
    (hOtrSome : PhaseCreditSpec M E_otrSome c_otr l_otr p_otr r_otr)
    (hPkCum : preKeyMsgNewDeltaCum pkCall ≤ c_pk)
    (hPkLive : preKeyMsgNewDeltaLive pkCall ≤ l_pk)
    (hPkPeak : preKeyMsgNewDeltaPeak pkCall ≤ p_pk)
    (hPkReq : preKeyMsgNewMaxReq pkCall ≤ r_pk)
    (hCmNone : PhaseCreditSpec M E_cmNone c_cm l_cm p_cm r_cm)
    (hCmSome : PhaseCreditSpec M E_cmSome c_cm l_cm p_cm r_cm) :
    PhaseCreditSpec M
      (FromKeySegEnv pendingPreKey remName kyberCt
        E_otrNone E_cmNone E_otrSome (PreKeyMsgNewEnv pkCall) E_cmSome)
      (max (2 * nameCap + 9539) ((2 * kyberCap + 9539) + c_otr + c_pk + c_cm))
      (max (nameCap + 8195) ((kyberCap + 8195) + l_otr + l_pk + l_cm))
      (max (nameCap + 8195)
        ((kyberCap + 8195) + max p_otr (l_otr + max p_pk (l_pk + p_cm))))
      (max nameCap (max kyberCap (max r_otr (max r_pk r_cm)))) :=
  fromKeySeg_creditSpec_aff hM hName hKyber hOtrNone hOtrSome
    ((preKeyMsgNew_phaseCredit hM pkCall).mono hPkCum hPkLive hPkPeak hPkReq)
    hCmNone hCmSome

/-- Small-name (`nameCap ≤ smallMaxReq M`) `FromKeySegEnv` instantiated with `WireMsgPeakSpec.preKeyMsgNew_phaseCredit`.
-/
theorem fromKeyWithPksm_capped_small {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (pkCall : PreKeyMsgNewCall)
    {pendingPreKey : Option α} {remName : VecGhost}
    {kyberCt : Option (List (BitVec 8))} {nameCap kyberCap : Nat}
    {E_otrNone E_cmNone E_otrSome E_cmSome : List AllocEvent → Prop}
    {c_otr l_otr p_otr r_otr c_pk l_pk p_pk r_pk c_cm l_cm p_cm r_cm : Nat}
    (hName : remName.bytes.length ≤ nameCap)
    (hNameSmall : nameCap ≤ HasFineReallocCredit.smallMaxReq M)
    (hKyber : ∀ bs, kyberCt = some bs → bs.length ≤ kyberCap)
    (hOtrNone : PhaseCreditSpec M E_otrNone c_otr l_otr p_otr r_otr)
    (hOtrSome : PhaseCreditSpec M E_otrSome c_otr l_otr p_otr r_otr)
    (hPkCum : preKeyMsgNewDeltaCum pkCall ≤ c_pk)
    (hPkLive : preKeyMsgNewDeltaLive pkCall ≤ l_pk)
    (hPkPeak : preKeyMsgNewDeltaPeak pkCall ≤ p_pk)
    (hPkReq : preKeyMsgNewMaxReq pkCall ≤ r_pk)
    (hCmNone : PhaseCreditSpec M E_cmNone c_cm l_cm p_cm r_cm)
    (hCmSome : PhaseCreditSpec M E_cmSome c_cm l_cm p_cm r_cm) :
    PhaseCreditSpec M
      (FromKeySegEnv pendingPreKey remName kyberCt
        E_otrNone E_cmNone E_otrSome (PreKeyMsgNewEnv pkCall) E_cmSome)
      (max (2 * nameCap + 9539) ((2 * kyberCap + 9539) + c_otr + c_pk + c_cm))
      ((kyberCap + 8195) + l_otr + l_pk + l_cm)
      ((kyberCap + 8195) + max p_otr (l_otr + max p_pk (l_pk + p_cm)))
      (max nameCap (max kyberCap (max r_otr (max r_pk r_cm)))) :=
  fromKeySeg_creditSpec_small hM hName hNameSmall hKyber hOtrNone hOtrSome
    ((preKeyMsgNew_phaseCredit hM pkCall).mono hPkCum hPkLive hPkPeak hPkReq)
    hCmNone hCmSome

/-! ## 3. CLI `StoreKits` Boxed-Future Steps -/

/-- Small-box (`32 ≤ smallMaxReq M`) CLI `load_session` step (`shim ++ CliSessLoadPollEnv ++ Box::drop`).
-/
theorem cliSessLoadStep_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M)
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {dir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd files (pathOf dir.path (addressText peer.val)) = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    PhaseCreditSpec M
      (SeqEnv (BoxAllocEnv 32)
        (SeqEnv (CliSessLoadPollEnv rd DeserEnv files dir peer) (· = rustDeallocEvents 32 8)))
      (2 * 32 + 9539 + sessLoadPollDeltaCum (max maxVal fileCap) deserCum)
      (sessLoadPollDeltaLive (max maxVal fileCap) deserLive)
      (sessLoadPollDeltaPeak (max maxVal fileCap) deserPeak)
      (max 32 (sessLoadPollMaxReq (max maxVal fileCap) deserMaxReq)) :=
  boxPollDrop_creditSpec_small hM hle32
    (sessLoadPoll_phaseCredit hM hdc hdir hpeer hcap hdeser)

theorem cliSessLoadStep_creditSpec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {dir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd files (pathOf dir.path (addressText peer.val)) = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    PhaseCreditSpec M
      (SeqEnv (BoxAllocEnv 32)
        (SeqEnv (CliSessLoadPollEnv rd DeserEnv files dir peer) (· = rustDeallocEvents 32 8)))
      (2 * 32 + 9539 + sessLoadPollDeltaCum (max maxVal fileCap) deserCum)
      (32 + 8195 + sessLoadPollDeltaLive (max maxVal fileCap) deserLive)
      (32 + 8195 + sessLoadPollDeltaPeak (max maxVal fileCap) deserPeak)
      (max 32 (sessLoadPollMaxReq (max maxVal fileCap) deserMaxReq)) :=
  boxPollDrop_creditSpec_aff hM
    (sessLoadPoll_phaseCredit hM hdc hdir hpeer hcap hdeser)

/-- Small-box (`40 ≤ smallMaxReq M`) CLI `store_session` step (`0`-prev). -/
theorem cliSessStoreStep_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle40 : 40 ≤ HasFineReallocCredit.smallMaxReq M)
    {dir : DirGhost} {peer : AddrGhost}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    {maxDir maxEntries maxVal : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec M
      (SeqEnv (BoxAllocEnv 40)
        (SeqEnv (CliSessStorePollEnv dir peer g r) (· = rustDeallocEvents 40 8)))
      (2 * 40 + 9539 + sessStorePollDeltaCum (recordSerializeCum g r) maxEntries)
      (sessStorePollDeltaLive (recordSerializeOutLarge M g r) maxEntries)
      (sessStorePollDeltaPeak (recordSerializePeak M g r) maxEntries)
      (max 40 (sessStorePollMaxReq (recordSerializeMaxReq g r) maxEntries)) :=
  boxPollDrop_creditSpec_small hM hle40
    (sessStorePoll_phaseCredit hM hdc hpeer)

/-- Small-box (`40 ≤ smallMaxReq M`) CLI small-record (`is_trusted_identity` / `save_identity`) step.
-/
theorem cliSmallStoreStep_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle40 : 40 ≤ HasFineReallocCredit.smallMaxReq M)
    {rd : ReadRule} {files : FsFiles} {dir : DirGhost}
    {name : List (BitVec 8)} {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hname : name.length ≤ 64)
    (hcap : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M
      (SeqEnv (BoxAllocEnv 40)
        (SeqEnv (CliSmallStorePollEnv rd files dir name) (· = rustDeallocEvents 40 8)))
      (2 * 40 + 9539 + smallStorePollDeltaCum (max maxVal fileCap) maxEntries)
      (smallStorePollDeltaLive (max maxVal fileCap) maxEntries)
      (smallStorePollDeltaPeak (max maxVal fileCap) maxEntries)
      (max 40 (smallStorePollMaxReq (max maxVal fileCap) maxEntries)) :=
  boxPollDrop_creditSpec_small hM hle40
    (smallStorePoll_phaseCredit hM hdc hdir hname hcap)

/-! ## 4. CLI `ScopeAt` to `OutgoingTripleRatchet` SPQR Domain-Cap Bridge -/

theorem fromSessionState_pqrState {s taken : SessionState (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))}
    (h : execOk OutgoingTripleRatchet.fromSessionState s = .ok (otr, taken)) :
    otr.pqrState = s.pqRatchetState := by
  unfold execOk Mut.exec OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hs : s.senderChain with _ | sc <;> rcases hr : s.remoteIdentity with _ | k <;>
    simp only [hs, hr, modifyGet, MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure,
      StateT.pure, StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, reduceCtorEq] at h
  all_goals (try split_ifs at h) <;>
    simp only [ExceptT.bindCont, StateT.bind, StateT.pure, pure, bind, reduceCtorEq,
      Except.ok.injEq, Prod.mk.injEq] at h
  exact (congrArg OutgoingTripleRatchet.pqrState h.1).symm

/-- Transfers `PeerSpqrValid F rem` across `OutgoingTripleRatchet.fromSessionState` at any `w1SessKit.ScopeAt` record.
-/
theorem peerSpqrValid_of_fromSessionState {B : RunBudgets} {img : Arm64.Obj.Image}
    {F : FsFiles} {peer : AddrGhost} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    (hScAt : (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions rem r)
    (hcur : r.currentSession = some sess)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hValid : PeerSpqrValid F rem) :
    ValidEncoderPts otr.pqrState ∧ otr.pqrState.length < 2 ^ 31 :=
  peerSpqrValid_of_scopeAt hScAt hcur (fromSessionState_pqrState hfrom) hValid

/-! ## 5. Tight `smallAllocCost` and `PeerSpqrTightValid640` Instantiations -/

/-- Tight `OtrEncryptStepEnv` + `SignalMessage::new` bound using `smallAllocCost M 32` and `tryCloneSmallDelta` / `tryCloneLargeDelta`.
-/
theorem otrEncryptWithSigNew_creditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M)
    (parse : UuidParser) (sigGhost : SignalMessageNewGhost)
    {E_send : List AllocEvent → Prop} {ptextLen : Nat}
    {c_s l_s p_s r_s : Nat}
    (hSend : PhaseCreditSpec M E_send c_s l_s p_s r_s) :
    let ctLen := (ptextLen / 16 + 1) * 16
    PhaseCreditSpec M (OtrEncryptStepEnv E_send ptextLen (SignalMessageNewEnv parse sigGhost))
      (c_s + HasFineReallocCredit.smallAllocCost M 32 + tryCloneSmallDelta M ctLen +
        signalMessageNewDeltaCum parse sigGhost)
      (l_s + tryCloneLargeDelta M ctLen + signalMessageNewDeltaLive parse sigGhost)
      (max p_s (l_s + tryCloneLargeDelta M ctLen + signalMessageNewDeltaPeak parse sigGhost))
      (max r_s (max 32 (max ctLen (signalMessageNewMaxReq parse sigGhost)))) :=
  otrEncryptStep_creditSpec_tight hM hle32 hSend (signalMessageNew_phaseCredit hM parse sigGhost)

theorem otrEncryptWithSigNew_capped_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M)
    (parse : UuidParser) (sigGhost : SignalMessageNewGhost)
    {E_send : List AllocEvent → Prop} {ptextLen : Nat}
    {c_s l_s p_s r_s c_n l_n p_n r_n : Nat}
    (hSend : PhaseCreditSpec M E_send c_s l_s p_s r_s)
    (hCum : signalMessageNewDeltaCum parse sigGhost ≤ c_n)
    (hLive : signalMessageNewDeltaLive parse sigGhost ≤ l_n)
    (hPeak : signalMessageNewDeltaPeak parse sigGhost ≤ p_n)
    (hReq : signalMessageNewMaxReq parse sigGhost ≤ r_n) :
    let ctLen := (ptextLen / 16 + 1) * 16
    PhaseCreditSpec M (OtrEncryptStepEnv E_send ptextLen (SignalMessageNewEnv parse sigGhost))
      (c_s + HasFineReallocCredit.smallAllocCost M 32 + tryCloneSmallDelta M ctLen + c_n)
      (l_s + tryCloneLargeDelta M ctLen + l_n)
      (max p_s (l_s + tryCloneLargeDelta M ctLen + p_n))
      (max r_s (max 32 (max ctLen r_n))) :=
  otrEncryptStep_creditSpec_tight hM hle32 hSend
    ((signalMessageNew_phaseCredit hM parse sigGhost).mono hCum hLive hPeak hReq)

/-- Tight `FromKeySegEnv` + `PreKeySignalMessage::new` bound under exact Kyber ciphertext length `kyberLen ≤ smallMaxReq M`.
-/
theorem fromKeyWithPksm_capped_tight {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (pkCall : PreKeyMsgNewCall)
    {pendingPreKey : Option α} {remName : VecGhost}
    {kyberCt : Option (List (BitVec 8))} {nameCap nameCum kyberLen : Nat}
    {E_otrNone E_cmNone E_otrSome E_cmSome : List AllocEvent → Prop}
    {c_otr l_otr p_otr r_otr c_pk l_pk p_pk r_pk c_cm l_cm p_cm r_cm : Nat}
    (hName : remName.bytes.length ≤ nameCap)
    (hNameSmall : nameCap ≤ HasFineReallocCredit.smallMaxReq M)
    (hNameCum : ∀ n, 0 < n → n ≤ nameCap → HasFineReallocCredit.smallAllocCost M n ≤ nameCum)
    (hKyberEq : ∀ bs, kyberCt = some bs → bs.length = kyberLen)
    (hKyberSmall : kyberLen ≤ HasFineReallocCredit.smallMaxReq M)
    (hOtrNone : PhaseCreditSpec M E_otrNone c_otr l_otr p_otr r_otr)
    (hOtrSome : PhaseCreditSpec M E_otrSome c_otr l_otr p_otr r_otr)
    (hPkCum : preKeyMsgNewDeltaCum pkCall ≤ c_pk)
    (hPkLive : preKeyMsgNewDeltaLive pkCall ≤ l_pk)
    (hPkPeak : preKeyMsgNewDeltaPeak pkCall ≤ p_pk)
    (hPkReq : preKeyMsgNewMaxReq pkCall ≤ r_pk)
    (hCmNone : PhaseCreditSpec M E_cmNone c_cm l_cm p_cm r_cm)
    (hCmSome : PhaseCreditSpec M E_cmSome c_cm l_cm p_cm r_cm) :
    PhaseCreditSpec M
      (FromKeySegEnv pendingPreKey remName kyberCt
        E_otrNone E_cmNone E_otrSome (PreKeyMsgNewEnv pkCall) E_cmSome)
      (max nameCum (HasFineReallocCredit.smallAllocCost M kyberLen + c_otr + c_pk + c_cm))
      (l_otr + l_pk + l_cm)
      (max p_otr (l_otr + max p_pk (l_pk + p_cm)))
      (max nameCap (max kyberLen (max r_otr (max r_pk r_cm)))) :=
  fromKeySeg_creditSpec_tight hM hName hNameSmall hNameCum hKyberEq hKyberSmall
    hOtrNone hOtrSome
    ((preKeyMsgNew_phaseCredit hM pkCall).mono hPkCum hPkLive hPkPeak hPkReq)
    hCmNone hCmSome

theorem cliSessLoadStep_creditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M)
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {dir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd files (pathOf dir.path (addressText peer.val)) = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    PhaseCreditSpec M
      (SeqEnv (BoxAllocEnv 32)
        (SeqEnv (CliSessLoadPollEnv rd DeserEnv files dir peer) (· = rustDeallocEvents 32 8)))
      (HasFineReallocCredit.smallAllocCost M 32 +
        sessLoadPollDeltaCum (max maxVal fileCap) deserCum)
      (sessLoadPollDeltaLive (max maxVal fileCap) deserLive)
      (sessLoadPollDeltaPeak (max maxVal fileCap) deserPeak)
      (max 32 (sessLoadPollMaxReq (max maxVal fileCap) deserMaxReq)) :=
  boxPollDrop_creditSpec_tight hM hle32
    (sessLoadPoll_phaseCredit hM hdc hdir hpeer hcap hdeser)

theorem cliSessStoreStep_creditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle40 : 40 ≤ HasFineReallocCredit.smallMaxReq M)
    {dir : DirGhost} {peer : AddrGhost}
    {g : RecordGhost} {r : SessionRecord (List (BitVec 8))}
    {maxDir maxEntries maxVal : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec M
      (SeqEnv (BoxAllocEnv 40)
        (SeqEnv (CliSessStorePollEnv dir peer g r) (· = rustDeallocEvents 40 8)))
      (HasFineReallocCredit.smallAllocCost M 40 +
        sessStorePollDeltaCum (recordSerializeCum g r) maxEntries)
      (sessStorePollDeltaLive (recordSerializeOutLarge M g r) maxEntries)
      (sessStorePollDeltaPeak (recordSerializePeak M g r) maxEntries)
      (max 40 (sessStorePollMaxReq (recordSerializeMaxReq g r) maxEntries)) :=
  boxPollDrop_creditSpec_tight hM hle40
    (sessStorePoll_phaseCredit hM hdc hpeer)

theorem cliSmallStoreStep_creditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle40 : 40 ≤ HasFineReallocCredit.smallMaxReq M)
    {rd : ReadRule} {files : FsFiles} {dir : DirGhost}
    {name : List (BitVec 8)} {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hname : name.length ≤ 64)
    (hcap : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M
      (SeqEnv (BoxAllocEnv 40)
        (SeqEnv (CliSmallStorePollEnv rd files dir name) (· = rustDeallocEvents 40 8)))
      (HasFineReallocCredit.smallAllocCost M 40 +
        smallStorePollDeltaCum (max maxVal fileCap) maxEntries)
      (smallStorePollDeltaLive (max maxVal fileCap) maxEntries)
      (smallStorePollDeltaPeak (max maxVal fileCap) maxEntries)
      (max 40 (smallStorePollMaxReq (max maxVal fileCap) maxEntries)) :=
  boxPollDrop_creditSpec_tight hM hle40
    (smallStorePoll_phaseCredit hM hdc hdir hname hcap)

/-- Transfers `PeerSpqrTightValidAt K F rem` across `OutgoingTripleRatchet.fromSessionState` at any `w1SessKit.ScopeAt` record.
-/
theorem peerSpqrTightValidAt_of_fromSessionState {B : RunBudgets} {img : Arm64.Obj.Image}
    {F : FsFiles} {peer : AddrGhost} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    {K : Nat}
    (hScAt : (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions rem r)
    (hcur : r.currentSession = some sess)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hValid : PeerSpqrTightValidAt K F rem) :
    ValidEncoderPtsAt K otr.pqrState ∧ ValidChainParams otr.pqrState ∧
      otr.pqrState.length < 2 ^ 31 :=
  peerSpqrTightValidAt_of_w1ScopeAt hScAt hcur (fromSessionState_pqrState hfrom) hValid

theorem peerSpqrTightValid640_of_fromSessionState {B : RunBudgets} {img : Arm64.Obj.Image}
    {F : FsFiles} {peer : AddrGhost} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    (hScAt : (w1SessKit B img F peer).ScopeAt scopeKit StoresGhost.opened.sessions rem r)
    (hcur : r.currentSession = some sess)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hValid : PeerSpqrTightValid640 F rem) :
    ValidEncoderPts640 otr.pqrState ∧ ValidChainParams otr.pqrState ∧
      otr.pqrState.length < 2 ^ 31 :=
  peerSpqrTightValidAt_of_fromSessionState hScAt hcur hfrom hValid

end LibsignalBinary.Proofs.PeakBudget.W1EncryptCalleesPeak
