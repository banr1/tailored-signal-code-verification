/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.W1EncryptCalleesPeak

/-!
# End-to-End `WithStoresEnc` and CLI W1 `message_encrypt` Slot Peak Bounds

Composes the post-encryption store tail (`is_trusted_identity` → `save_identity` →
`apply_to_session_state` → `store_session`), guarded `WithStoresEncTightEnv`, and CLI W1
(`StoresGhost.opened`) domain bridges into end-to-end `PhaseCreditSpec` slot bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak

open CryptoGames.LibsignalSession
  (Crypto IdentityKey Mut OutgoingTripleRatchet SessionState)
open CryptoGames.LibsignalSessionApi (Direction Session SessionRecord execOk)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (PreKeyMsgNewCall WithStoresEncGhost storedRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles IdentityStoreSpec SessionStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost)
open CryptoVerification.LibsignalSessionRepr (VecGhost)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost UuidParser serializeAddresses serviceIdParse uuidTryParse)
open CryptoVerification.SignalSession.Cli
  (DirGhost IdGhost ReadRule StoresGhost addressText pathOf)
open CryptoVerification.SignalSession.Cli.MainHops (cliIo)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1IdKit w1SessKit)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SignalSession.Cli.Slots (scopeKit)
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FreeOnlyEvs)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
  (SignalMessageNewEnv SignalMessageNewGhost)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCaps (ValidEncoderPts)
open LibsignalBinary.Proofs.PeakBudget.SpqrTightCaps
  (PeerSpqrTightValid640 ValidChainParams ValidEncoderPts640)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (DirDomainCaps PeerSpqrValid addressText_length_le dirDomainCaps_opened_peers
   dirDomainCaps_opened_sess)
open LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers
  (tryCloneLargeDelta tryCloneSmallDelta)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (recordSerializeCum recordSerializeMaxReq recordSerializeOutLarge recordSerializePeak)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessLoadPollEnv CliSessStorePollEnv CliSmallStorePollEnv
   sessLoadPollDeltaCum sessLoadPollDeltaLive sessLoadPollDeltaPeak sessLoadPollMaxReq
   sessLoadPoll_phaseCredit
   sessStorePollDeltaCum sessStorePollDeltaLive sessStorePollDeltaPeak sessStorePollMaxReq
   sessStorePoll_phaseCredit
   smallStorePollDeltaCum smallStorePollDeltaLive smallStorePollDeltaPeak smallStorePollMaxReq
   smallStorePoll_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.WireMsgPeakSpec
  (PreKeyMsgNewEnv preKeyMsgNewDeltaCum preKeyMsgNewDeltaLive preKeyMsgNewDeltaPeak
   preKeyMsgNewMaxReq preKeyMsgNew_phaseCredit
   signalMessageNewDeltaCum signalMessageNewDeltaLive signalMessageNewDeltaPeak
   signalMessageNewMaxReq)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptSegments
  (FromApplySegEnv FromCmSegEnv FromKeySegEnv FromSaveSegEnv OtrEncryptStepEnv
   WithStoresEncSegEnv fromApplySeg_creditSpec_aff fromApplySeg_creditSpec_small
   fromApplySeg_creditSpec_tight fromCmSeg_creditSpec_aff fromCmSeg_creditSpec_small
   fromCmSeg_creditSpec_tight fromKeySeg_creditSpec_aff fromKeySeg_creditSpec_tight
   fromSaveSeg_creditSpec_aff fromSaveSeg_creditSpec_small fromSaveSeg_creditSpec_tight
   otrEncryptStep_creditSpec_tight phaseCreditSpec_exists
   withStoresEncSeg_creditSpec_aff withStoresEncSeg_creditSpec_small
   withStoresEncSeg_creditSpec_tight)
open LibsignalBinary.Proofs.PeakBudget.W1EncryptCalleesPeak
  (fromKeySeg_creditSpec_small otrEncryptWithSigNew_capped_small32
   peerSpqrTightValid640_of_fromSessionState peerSpqrValid_of_fromSessionState)

/-! ## 1. Tight Store-Tail Envelopes and `PhaseCreditSpec` -/

/-- Tight `FromApply` envelope (`OtrApplyEnvTight` + `store_session` step + exit drops). -/
def FromApplyTightEnv {A : RustAlloc} {bs : BitVec 64}
    (kit : SessionStoreSpec A bs) (kitEnv : SessionStoreBudgetEnv kit)
    (st0 : kit.StoreState) (rem : AddrVal)
    (sess : Session (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) : List AllocEvent → Prop :=
  FromApplySegEnv kit.storeBoxSize (kitEnv.storePollEnv st0 rem (storedRecord sess otr' taken))

def FromSaveTightEnv {A : RustAlloc} {bs bi : BitVec 64}
    (kit : SessionStoreSpec A bs) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A bi) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist1 : ikit.IdState)
    (rem : AddrVal) (sess : Session (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) : List AllocEvent → Prop :=
  FromSaveSegEnv ikit.saveBoxSize (ikitEnv.savePollEnv ist1 rem k)
    (FromApplyTightEnv kit kitEnv st0 rem sess otr' taken)

def FromCmTightEnv {A : RustAlloc} {bs bi : BitVec 64}
    (kit : SessionStoreSpec A bs) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A bi) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (rem : AddrVal) (remName : VecGhost)
    (sess : Session (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) : List AllocEvent → Prop :=
  FromCmSegEnv ikit.trustBoxSize (ikitEnv.trustPollEnv ist0 rem k .sending) remName
    (FromSaveTightEnv kit kitEnv st0 ikit ikitEnv
      (ikit.trustUpdate ist0 rem k .sending (.ok true)) rem sess otr' taken k)

/-- Affine `PhaseCreditSpec` for `FromCmTightEnv` in binary call order. -/
theorem fromCmTight_creditSpec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} {bs bi : BitVec 64} (hM : ModelHyps M)
    (kit : SessionStoreSpec A bs) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A bi) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    {rem : AddrVal} {remName : VecGhost} {nameCap : Nat}
    {sess : Session (List (BitVec 8))} {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey}
    {c_tr l_tr p_tr r_tr c_sv l_sv p_sv r_sv c_st l_st p_st r_st : Nat}
    (hName : remName.bytes.length ≤ nameCap)
    (hTrust : PhaseCreditSpec M (ikitEnv.trustPollEnv ist0 rem k .sending) c_tr l_tr p_tr r_tr)
    (hSave : PhaseCreditSpec M
      (ikitEnv.savePollEnv (ikit.trustUpdate ist0 rem k .sending (.ok true)) rem k)
      c_sv l_sv p_sv r_sv)
    (hStore : PhaseCreditSpec M
      (kitEnv.storePollEnv st0 rem (storedRecord sess otr' taken)) c_st l_st p_st r_st) :
    let c_ap := (2 * 32 + 9539) + (2 * kit.storeBoxSize + 9539) + c_st
    let l_ap := (32 + 8195) + (kit.storeBoxSize + 8195) + l_st
    let p_ap := (32 + 8195) + (kit.storeBoxSize + 8195) + p_st
    let r_ap := max 32 (max kit.storeBoxSize r_st)
    let c_save := (2 * ikit.saveBoxSize + 9539 + c_sv) + c_ap
    let l_save := (ikit.saveBoxSize + 8195 + l_sv) + l_ap
    let p_save := max (ikit.saveBoxSize + 8195 + p_sv) ((ikit.saveBoxSize + 8195 + l_sv) + p_ap)
    let r_save := max (max ikit.saveBoxSize r_sv) r_ap
    PhaseCreditSpec M
      (FromCmTightEnv kit kitEnv st0 ikit ikitEnv ist0 rem remName sess otr' taken k)
      ((2 * ikit.trustBoxSize + 9539 + c_tr) + max (2 * nameCap + 9539) c_save)
      ((ikit.trustBoxSize + 8195 + l_tr) + max (nameCap + 8195) l_save)
      (max (ikit.trustBoxSize + 8195 + p_tr)
        ((ikit.trustBoxSize + 8195 + l_tr) + max (nameCap + 8195) p_save))
      (max (max ikit.trustBoxSize r_tr) (max nameCap r_save)) := by
  intro c_ap l_ap p_ap r_ap c_save l_save p_save r_save
  exact fromCmSeg_creditSpec_aff hM hName hTrust
    (fromSaveSeg_creditSpec_aff hM hSave (fromApplySeg_creditSpec_aff hM hStore))

/-- Small-box / small-name `PhaseCreditSpec` for `FromCmTightEnv`. -/
theorem fromCmTight_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} {bs bi : BitVec 64} (hM : ModelHyps M)
    (kit : SessionStoreSpec A bs) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A bi) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    {rem : AddrVal} {remName : VecGhost} {nameCap : Nat}
    {sess : Session (List (BitVec 8))} {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey}
    {c_tr l_tr p_tr r_tr c_sv l_sv p_sv r_sv c_st l_st p_st r_st : Nat}
    (hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxSt : kit.storeBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxSv : ikit.saveBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxTr : ikit.trustBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hName : remName.bytes.length ≤ nameCap)
    (hNameSm : nameCap ≤ HasFineReallocCredit.smallMaxReq M)
    (hTrust : PhaseCreditSpec M (ikitEnv.trustPollEnv ist0 rem k .sending) c_tr l_tr p_tr r_tr)
    (hSave : PhaseCreditSpec M
      (ikitEnv.savePollEnv (ikit.trustUpdate ist0 rem k .sending (.ok true)) rem k)
      c_sv l_sv p_sv r_sv)
    (hStore : PhaseCreditSpec M
      (kitEnv.storePollEnv st0 rem (storedRecord sess otr' taken)) c_st l_st p_st r_st) :
    let c_ap := (2 * 32 + 9539) + (2 * kit.storeBoxSize + 9539) + c_st
    let c_save := (2 * ikit.saveBoxSize + 9539 + c_sv) + c_ap
    PhaseCreditSpec M
      (FromCmTightEnv kit kitEnv st0 ikit ikitEnv ist0 rem remName sess otr' taken k)
      ((2 * ikit.trustBoxSize + 9539 + c_tr) + max (2 * nameCap + 9539) c_save)
      (l_tr + (l_sv + l_st))
      (max p_tr (l_tr + max p_sv (l_sv + p_st)))
      (max (max ikit.trustBoxSize r_tr)
        (max nameCap (max (max ikit.saveBoxSize r_sv) (max 32 (max kit.storeBoxSize r_st))))) := by
  intro c_ap c_save
  exact fromCmSeg_creditSpec_small hM hBoxTr hName hNameSm hTrust
    (fromSaveSeg_creditSpec_small hM hBoxSv hSave
      (fromApplySeg_creditSpec_small hM hle32 hBoxSt hStore))

/-! ## 2. Guarded `FromOtrTightEnv` and `WithStoresEncTightEnv` Composers -/

def otrAfterNone (C : Crypto) (S : SpqrModel) (x : WithStoresEncGhost)
    (otr : OutgoingTripleRatchet (List (BitVec 8))) : OutgoingTripleRatchet (List (BitVec 8)) :=
  (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext none x.rest) otr).2

def otrAfterSome (C : Crypto) (S : SpqrModel) (parse : UuidParser) (x : WithStoresEncGhost)
    (otr : OutgoingTripleRatchet (List (BitVec 8))) : OutgoingTripleRatchet (List (BitVec 8)) :=
  (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
    (serializeAddresses (serviceIdParse parse) x.loc x.rem) x.rest) otr).2

/-- Tight `FromOtr` envelope joining `FromKey` with `FromCmTightEnv`. -/
def FromOtrTightEnv {A : RustAlloc} {bs bi : BitVec 64}
    (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (kit : SessionStoreSpec A bs) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A bi) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (x : WithStoresEncGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8)))
    (E_otrNone E_otrSome E_pksmNew : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  ∃ k : IdentityKey, taken.remoteIdentity = some k ∧
    FromKeySegEnv sess.pendingPreKey x.rem.name (sess.pendingKyberPreKey.map (·.ciphertext))
      E_otrNone
      (FromCmTightEnv kit kitEnv st0 ikit ikitEnv ist0 x.rem.val x.rem.name
        sess (otrAfterNone C S x otr) taken k)
      E_otrSome
      E_pksmNew
      (FromCmTightEnv kit kitEnv st0 ikit ikitEnv ist0 x.rem.val x.rem.name
        sess (otrAfterSome C S parse x otr) taken k)
      evs

/-- End-to-end `session_message_encrypt_with_stores` envelope (`WithStoresEncTightEnv`) guarded by `ScopeAt`, `currentSession`, and `fromSessionState`.
-/
def WithStoresEncTightEnv {A : RustAlloc} {bs bi : BitVec 64}
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (kit : SessionStoreSpec A bs) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A bi) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (C : Crypto) (S : SpqrModel) (parse : UuidParser) (x : WithStoresEncGhost)
    (E_otrNone E_otrSome E_pksmNew :
      SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      OutgoingTripleRatchet (List (BitVec 8)) → SessionState (List (BitVec 8)) →
      List AllocEvent → Prop) : List AllocEvent → Prop :=
  WithStoresEncSegEnv kit.loadBoxSize (kitEnv.loadPollEnv st0 x.rem.val) x.rem.name
    (fun evs' =>
      ∃ (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
        (otr : OutgoingTripleRatchet (List (BitVec 8)))
        (taken : SessionState (List (BitVec 8))),
        kit.ScopeAt Scope st0 x.rem.val r ∧
        r.currentSession = some sess ∧
        execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
        FromOtrTightEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken
          (E_otrNone r sess otr taken) (E_otrSome r sess otr taken)
          (E_pksmNew r sess otr taken) evs')

/-- Affine end-to-end `PhaseCreditSpec` for `WithStoresEncTightEnv`. -/
theorem withStoresEncTight_creditSpec_aff {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} {bs bi : BitVec 64} (hM : ModelHyps M)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (kit : SessionStoreSpec A bs) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A bi) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (C : Crypto) (S : SpqrModel) (parse : UuidParser) (x : WithStoresEncGhost)
    {E_otrNone E_otrSome E_pksmNew :
      SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      OutgoingTripleRatchet (List (BitVec 8)) → SessionState (List (BitVec 8)) →
      List AllocEvent → Prop}
    {nameCap kyberCap : Nat}
    {c_ld l_ld p_ld r_ld : Nat}
    {c_otr l_otr p_otr r_otr c_pk l_pk p_pk r_pk : Nat}
    {c_tr l_tr p_tr r_tr c_sv l_sv p_sv r_sv c_st l_st p_st r_st : Nat}
    (hName : x.rem.name.bytes.length ≤ nameCap)
    (hLoad : PhaseCreditSpec M (kitEnv.loadPollEnv st0 x.rem.val) c_ld l_ld p_ld r_ld)
    (hKyber : ∀ r sess otr taken,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      ∀ ct, sess.pendingKyberPreKey.map (·.ciphertext) = some ct → ct.length ≤ kyberCap)
    (hOtrNone : ∀ r sess otr taken,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseCreditSpec M (E_otrNone r sess otr taken) c_otr l_otr p_otr r_otr)
    (hOtrSome : ∀ r sess otr taken,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseCreditSpec M (E_otrSome r sess otr taken) c_otr l_otr p_otr r_otr)
    (hPksmNew : ∀ r sess otr taken,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseCreditSpec M (E_pksmNew r sess otr taken) c_pk l_pk p_pk r_pk)
    (hTrust : ∀ r sess otr taken k,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M (ikitEnv.trustPollEnv ist0 x.rem.val k .sending) c_tr l_tr p_tr r_tr)
    (hSave : ∀ r sess otr taken k,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M
        (ikitEnv.savePollEnv (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k)
        c_sv l_sv p_sv r_sv)
    (hStoreNone : ∀ r sess otr taken k,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M
        (kitEnv.storePollEnv st0 x.rem.val (storedRecord sess (otrAfterNone C S x otr) taken))
        c_st l_st p_st r_st)
    (hStoreSome : ∀ r sess otr taken k,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M
        (kitEnv.storePollEnv st0 x.rem.val
          (storedRecord sess (otrAfterSome C S parse x otr) taken))
        c_st l_st p_st r_st) :
    let c_ap := (2 * 32 + 9539) + (2 * kit.storeBoxSize + 9539) + c_st
    let l_ap := (32 + 8195) + (kit.storeBoxSize + 8195) + l_st
    let p_ap := (32 + 8195) + (kit.storeBoxSize + 8195) + p_st
    let r_ap := max 32 (max kit.storeBoxSize r_st)
    let c_save := (2 * ikit.saveBoxSize + 9539 + c_sv) + c_ap
    let l_save := (ikit.saveBoxSize + 8195 + l_sv) + l_ap
    let p_save := max (ikit.saveBoxSize + 8195 + p_sv) ((ikit.saveBoxSize + 8195 + l_sv) + p_ap)
    let r_save := max (max ikit.saveBoxSize r_sv) r_ap
    let c_cm := (2 * ikit.trustBoxSize + 9539 + c_tr) + max (2 * nameCap + 9539) c_save
    let l_cm := (ikit.trustBoxSize + 8195 + l_tr) + max (nameCap + 8195) l_save
    let p_cm := max (ikit.trustBoxSize + 8195 + p_tr)
      ((ikit.trustBoxSize + 8195 + l_tr) + max (nameCap + 8195) p_save)
    let r_cm := max (max ikit.trustBoxSize r_tr) (max nameCap r_save)
    let c_fo := max (2 * nameCap + 9539) ((2 * kyberCap + 9539) + c_otr + c_pk + c_cm)
    let l_fo := max (nameCap + 8195) ((kyberCap + 8195) + l_otr + l_pk + l_cm)
    let p_fo := max (nameCap + 8195)
      ((kyberCap + 8195) + max p_otr (l_otr + max p_pk (l_pk + p_cm)))
    let r_fo := max nameCap (max kyberCap (max r_otr (max r_pk r_cm)))
    PhaseCreditSpec M
      (WithStoresEncTightEnv Scope kit kitEnv st0 ikit ikitEnv ist0 C S parse x
        E_otrNone E_otrSome E_pksmNew)
      ((2 * kit.loadBoxSize + 9539 + c_ld) + max (2 * nameCap + 9539) c_fo)
      ((kit.loadBoxSize + 8195 + l_ld) + max (nameCap + 8195) l_fo)
      (max (kit.loadBoxSize + 8195 + p_ld)
        ((kit.loadBoxSize + 8195 + l_ld) + max (nameCap + 8195) p_fo))
      (max (max kit.loadBoxSize r_ld) (max nameCap r_fo)) := by
  intro c_ap l_ap p_ap r_ap c_save l_save p_save r_save c_cm l_cm p_cm r_cm c_fo l_fo p_fo r_fo
  refine withStoresEncSeg_creditSpec_aff hM hName hLoad ?_
  have hEx :
      PhaseCreditSpec M
        (fun evs' =>
          ∃ w : SessionRecord (List (BitVec 8)) × Session (List (BitVec 8)) ×
              OutgoingTripleRatchet (List (BitVec 8)) × SessionState (List (BitVec 8)),
            (kit.ScopeAt Scope st0 x.rem.val w.1 ∧
              w.1.currentSession = some w.2.1 ∧
              execOk OutgoingTripleRatchet.fromSessionState w.2.1.state =
                .ok (w.2.2.1, w.2.2.2)) ∧
            FromOtrTightEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x
              w.2.1 w.2.2.1 w.2.2.2
              (E_otrNone w.1 w.2.1 w.2.2.1 w.2.2.2)
              (E_otrSome w.1 w.2.1 w.2.2.1 w.2.2.2)
              (E_pksmNew w.1 w.2.1 w.2.2.1 w.2.2.2) evs')
        c_fo l_fo p_fo r_fo := by
    refine phaseCreditSpec_exists fun ⟨r, sess, otr, taken⟩ ⟨hsc, hcur, hfrom⟩ => ?_
    have hK : PhaseCreditSpec M
        (fun evs => ∃ k : IdentityKey, taken.remoteIdentity = some k ∧
          FromKeySegEnv sess.pendingPreKey x.rem.name
            (sess.pendingKyberPreKey.map (·.ciphertext))
            (E_otrNone r sess otr taken)
            (FromCmTightEnv kit kitEnv st0 ikit ikitEnv ist0 x.rem.val x.rem.name
              sess (otrAfterNone C S x otr) taken k)
            (E_otrSome r sess otr taken)
            (E_pksmNew r sess otr taken)
            (FromCmTightEnv kit kitEnv st0 ikit ikitEnv ist0 x.rem.val x.rem.name
              sess (otrAfterSome C S parse x otr) taken k) evs)
        c_fo l_fo p_fo r_fo :=
      phaseCreditSpec_exists fun k hk =>
        fromKeySeg_creditSpec_aff hM hName (hKyber r sess otr taken hsc hcur hfrom)
          (hOtrNone r sess otr taken hsc hcur hfrom)
          (hOtrSome r sess otr taken hsc hcur hfrom)
          (hPksmNew r sess otr taken hsc hcur hfrom)
          (fromCmTight_creditSpec_aff hM kit kitEnv st0 ikit ikitEnv ist0 hName
            (hTrust r sess otr taken k hsc hcur hfrom hk)
            (hSave r sess otr taken k hsc hcur hfrom hk)
            (hStoreNone r sess otr taken k hsc hcur hfrom hk))
          (fromCmTight_creditSpec_aff hM kit kitEnv st0 ikit ikitEnv ist0 hName
            (hTrust r sess otr taken k hsc hcur hfrom hk)
            (hSave r sess otr taken k hsc hcur hfrom hk)
            (hStoreSome r sess otr taken k hsc hcur hfrom hk))
    exact (PhaseCreditSpec.or (PhaseCreditSpec.freeOnly hM.freeNonInc) hK).mono
      (by omega) (by omega) (by omega) (by omega)
  refine PhaseCreditSpec.of_imp (fun evs ⟨r, sess, otr, taken, hsc, hcur, hfrom, hfo⟩ =>
    ⟨(r, sess, otr, taken), ⟨hsc, hcur, hfrom⟩, hfo⟩) hEx

/-- Small-box / small-name end-to-end `PhaseCreditSpec` for `WithStoresEncTightEnv`. -/
theorem withStoresEncTight_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} {bs bi : BitVec 64} (hM : ModelHyps M)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (kit : SessionStoreSpec A bs) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A bi) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (C : Crypto) (S : SpqrModel) (parse : UuidParser) (x : WithStoresEncGhost)
    {E_otrNone E_otrSome E_pksmNew :
      SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      OutgoingTripleRatchet (List (BitVec 8)) → SessionState (List (BitVec 8)) →
      List AllocEvent → Prop}
    {nameCap kyberCap : Nat}
    {c_ld l_ld p_ld r_ld : Nat}
    {c_otr l_otr p_otr r_otr c_pk l_pk p_pk r_pk : Nat}
    {c_tr l_tr p_tr r_tr c_sv l_sv p_sv r_sv c_st l_st p_st r_st : Nat}
    (hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxLd : kit.loadBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxSt : kit.storeBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxSv : ikit.saveBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxTr : ikit.trustBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hName : x.rem.name.bytes.length ≤ nameCap)
    (hNameSm : nameCap ≤ HasFineReallocCredit.smallMaxReq M)
    (hLoad : PhaseCreditSpec M (kitEnv.loadPollEnv st0 x.rem.val) c_ld l_ld p_ld r_ld)
    (hKyber : ∀ r sess otr taken,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      ∀ ct, sess.pendingKyberPreKey.map (·.ciphertext) = some ct → ct.length ≤ kyberCap)
    (hOtrNone : ∀ r sess otr taken,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseCreditSpec M (E_otrNone r sess otr taken) c_otr l_otr p_otr r_otr)
    (hOtrSome : ∀ r sess otr taken,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseCreditSpec M (E_otrSome r sess otr taken) c_otr l_otr p_otr r_otr)
    (hPksmNew : ∀ r sess otr taken,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseCreditSpec M (E_pksmNew r sess otr taken) c_pk l_pk p_pk r_pk)
    (hTrust : ∀ r sess otr taken k,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M (ikitEnv.trustPollEnv ist0 x.rem.val k .sending) c_tr l_tr p_tr r_tr)
    (hSave : ∀ r sess otr taken k,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M
        (ikitEnv.savePollEnv (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k)
        c_sv l_sv p_sv r_sv)
    (hStoreNone : ∀ r sess otr taken k,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M
        (kitEnv.storePollEnv st0 x.rem.val (storedRecord sess (otrAfterNone C S x otr) taken))
        c_st l_st p_st r_st)
    (hStoreSome : ∀ r sess otr taken k,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M
        (kitEnv.storePollEnv st0 x.rem.val
          (storedRecord sess (otrAfterSome C S parse x otr) taken))
        c_st l_st p_st r_st) :
    let c_ap := (2 * 32 + 9539) + (2 * kit.storeBoxSize + 9539) + c_st
    let c_save := (2 * ikit.saveBoxSize + 9539 + c_sv) + c_ap
    let c_cm := (2 * ikit.trustBoxSize + 9539 + c_tr) + max (2 * nameCap + 9539) c_save
    let l_cm := l_tr + (l_sv + l_st)
    let p_cm := max p_tr (l_tr + max p_sv (l_sv + p_st))
    let r_cm := max (max ikit.trustBoxSize r_tr)
      (max nameCap (max (max ikit.saveBoxSize r_sv) (max 32 (max kit.storeBoxSize r_st))))
    let c_fo := max (2 * nameCap + 9539) ((2 * kyberCap + 9539) + c_otr + c_pk + c_cm)
    let l_fo := (kyberCap + 8195) + l_otr + l_pk + l_cm
    let p_fo := (kyberCap + 8195) + max p_otr (l_otr + max p_pk (l_pk + p_cm))
    let r_fo := max nameCap (max kyberCap (max r_otr (max r_pk r_cm)))
    PhaseCreditSpec M
      (WithStoresEncTightEnv Scope kit kitEnv st0 ikit ikitEnv ist0 C S parse x
        E_otrNone E_otrSome E_pksmNew)
      ((2 * kit.loadBoxSize + 9539 + c_ld) + max (2 * nameCap + 9539) c_fo)
      (l_ld + l_fo)
      (max p_ld (l_ld + p_fo))
      (max (max kit.loadBoxSize r_ld) (max nameCap r_fo)) := by
  intro c_ap c_save c_cm l_cm p_cm r_cm c_fo l_fo p_fo r_fo
  refine withStoresEncSeg_creditSpec_small hM hBoxLd hName hNameSm hLoad ?_
  have hEx :
      PhaseCreditSpec M
        (fun evs' =>
          ∃ w : SessionRecord (List (BitVec 8)) × Session (List (BitVec 8)) ×
              OutgoingTripleRatchet (List (BitVec 8)) × SessionState (List (BitVec 8)),
            (kit.ScopeAt Scope st0 x.rem.val w.1 ∧
              w.1.currentSession = some w.2.1 ∧
              execOk OutgoingTripleRatchet.fromSessionState w.2.1.state =
                .ok (w.2.2.1, w.2.2.2)) ∧
            FromOtrTightEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x
              w.2.1 w.2.2.1 w.2.2.2
              (E_otrNone w.1 w.2.1 w.2.2.1 w.2.2.2)
              (E_otrSome w.1 w.2.1 w.2.2.1 w.2.2.2)
              (E_pksmNew w.1 w.2.1 w.2.2.1 w.2.2.2) evs')
        c_fo l_fo p_fo r_fo := by
    refine phaseCreditSpec_exists fun ⟨r, sess, otr, taken⟩ ⟨hsc, hcur, hfrom⟩ => ?_
    have hK : PhaseCreditSpec M
        (fun evs => ∃ k : IdentityKey, taken.remoteIdentity = some k ∧
          FromKeySegEnv sess.pendingPreKey x.rem.name
            (sess.pendingKyberPreKey.map (·.ciphertext))
            (E_otrNone r sess otr taken)
            (FromCmTightEnv kit kitEnv st0 ikit ikitEnv ist0 x.rem.val x.rem.name
              sess (otrAfterNone C S x otr) taken k)
            (E_otrSome r sess otr taken)
            (E_pksmNew r sess otr taken)
            (FromCmTightEnv kit kitEnv st0 ikit ikitEnv ist0 x.rem.val x.rem.name
              sess (otrAfterSome C S parse x otr) taken k) evs)
        c_fo l_fo p_fo r_fo :=
      phaseCreditSpec_exists fun k hk =>
        fromKeySeg_creditSpec_small hM hName hNameSm (hKyber r sess otr taken hsc hcur hfrom)
          (hOtrNone r sess otr taken hsc hcur hfrom)
          (hOtrSome r sess otr taken hsc hcur hfrom)
          (hPksmNew r sess otr taken hsc hcur hfrom)
          (fromCmTight_creditSpec_small hM kit kitEnv st0 ikit ikitEnv ist0
            hle32 hBoxSt hBoxSv hBoxTr hName hNameSm
            (hTrust r sess otr taken k hsc hcur hfrom hk)
            (hSave r sess otr taken k hsc hcur hfrom hk)
            (hStoreNone r sess otr taken k hsc hcur hfrom hk))
          (fromCmTight_creditSpec_small hM kit kitEnv st0 ikit ikitEnv ist0
            hle32 hBoxSt hBoxSv hBoxTr hName hNameSm
            (hTrust r sess otr taken k hsc hcur hfrom hk)
            (hSave r sess otr taken k hsc hcur hfrom hk)
            (hStoreSome r sess otr taken k hsc hcur hfrom hk))
    exact (PhaseCreditSpec.or (PhaseCreditSpec.freeOnly hM.freeNonInc) hK).mono
      (by omega) (by omega) (by omega) (by omega)
  refine PhaseCreditSpec.of_imp (fun evs ⟨r, sess, otr, taken, hsc, hcur, hfrom, hfo⟩ =>
    ⟨(r, sess, otr, taken), ⟨hsc, hcur, hfrom⟩, hfo⟩) hEx

/-! ## 3. CLI W1 (`StoresGhost.opened`) Domain Bridges and Slot Theorem -/

/-- Any pending Kyber pre-key ciphertext in a `w1SessKit.ScopeAt` session has length `≤ 1569`. -/
theorem w1_scopeKit_kyber_ciphertext_le_1569 {B : RunBudgets} {img : Arm64.Obj.Image}
    {F : FsFiles} {peer : AddrGhost} {st0 : DirGhost} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    (hsc : (w1SessKit B img F peer).ScopeAt scopeKit st0 rem r)
    (hs : r.currentSession = some sess) :
    ∀ ct, sess.pendingKyberPreKey.map (·.ciphertext) = some ct → ct.length ≤ 1569 := by
  obtain ⟨s', hs', hsp⟩ := hsc.1.2
  cases hs.symm.trans hs'
  intro ct hct
  rcases hky : sess.pendingKyberPreKey with _ | k
  · simp [hky] at hct
  · simp only [hky, Option.map_some, Option.some.injEq] at hct
    subst hct
    exact Nat.le_of_eq (hsp.2.2.1 k hky)

theorem w1_peer_addressText_le_64 {peer : AddrGhost} (hpeer : peer.name.bytes.length ≤ 40) :
    (addressText peer.val).length ≤ 64 := by
  have hat : (addressText peer.val).length ≤ peer.name.bytes.length + 4 :=
    addressText_length_le peer.val
  omega

/-- Witness-independent cap wrapper for `CliSessStorePollEnv` over a guarded `RecordGhost` existential.
-/
theorem cliSessStorePoll_exists_capped {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {dir : DirGhost} {peer : AddrGhost}
    {r : SessionRecord (List (BitVec 8))} {P : RecordGhost → Prop}
    {maxDir maxEntries maxVal c_st l_st p_st r_st : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hCum : ∀ g, P g → sessStorePollDeltaCum (recordSerializeCum g r) maxEntries ≤ c_st)
    (hLive : ∀ g, P g → sessStorePollDeltaLive (recordSerializeOutLarge M g r) maxEntries ≤ l_st)
    (hPeak : ∀ g, P g → sessStorePollDeltaPeak (recordSerializePeak M g r) maxEntries ≤ p_st)
    (hReq : ∀ g, P g → sessStorePollMaxReq (recordSerializeMaxReq g r) maxEntries ≤ r_st) :
    PhaseCreditSpec M
      (fun evs => ∃ g : RecordGhost, P g ∧ CliSessStorePollEnv dir peer g r evs)
      c_st l_st p_st r_st :=
  phaseCreditSpec_exists fun g hg =>
    (sessStorePoll_phaseCredit hM hdc hpeer).mono
      (hCum g hg) (hLive g hg) (hPeak g hg) (hReq g hg)

/-- CLI W1 (`StoresGhost.opened`) `PhaseCreditSpec` for `WithStoresEncTightEnv` under `40 ≤ smallMaxReq M`, `peer.name.bytes.length ≤ 40`, and `PeerSpqrValid`.
-/
theorem w1CliEncryptSlot_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle40 : 40 ≤ HasFineReallocCredit.smallMaxReq M)
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
    {fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    {c_s l_s p_s r_s c_sig l_sig p_sig r_sig c_pk l_pk p_pk r_pk c_st l_st p_st r_st : Nat}
    (hpeer : peer.name.bytes.length ≤ 40)
    (hremName : x.rem.name.bytes.length ≤ 40)
    (hidKeyLen : peerIdKeyName.length ≤ 64)
    (hValid : PeerSpqrValid F x.rem.val)
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
    (hSend : ∀ pqrState, ValidEncoderPts pqrState → pqrState.length < 2 ^ 31 →
      PhaseCreditSpec M (E_send pqrState x.rest) c_s l_s p_s r_s)
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
    let ctLen := (x.ptext.length / 16 + 1) * 16
    let c_otr := c_s + (2 * 32 + 9539) + (2 * ctLen + 9539) + c_sig
    let l_otr := l_s + (ctLen + 8195) + l_sig
    let p_otr := max p_s (l_s + (ctLen + 8195) + p_sig)
    let r_otr := max r_s (max 32 (max ctLen r_sig))
    let c_ld := sessLoadPollDeltaCum (max 0 fileCap) deserCum
    let l_ld := sessLoadPollDeltaLive (max 0 fileCap) deserLive
    let p_ld := sessLoadPollDeltaPeak (max 0 fileCap) deserPeak
    let r_ld := sessLoadPollMaxReq (max 0 fileCap) deserMaxReq
    let c_id := smallStorePollDeltaCum (max 0 fileCap) 0
    let l_id := smallStorePollDeltaLive (max 0 fileCap) 0
    let p_id := smallStorePollDeltaPeak (max 0 fileCap) 0
    let r_id := smallStorePollMaxReq (max 0 fileCap) 0
    let c_ap := (2 * 32 + 9539) + (2 * 32 + 9539) + c_st
    let c_save := (2 * 32 + 9539 + c_id) + c_ap
    let c_cm := (2 * 32 + 9539 + c_id) + max (2 * 40 + 9539) c_save
    let l_cm := l_id + (l_id + l_st)
    let p_cm := max p_id (l_id + max p_id (l_id + p_st))
    let r_cm := max (max 32 r_id) (max 40 (max (max 32 r_id) (max 32 (max 32 r_st))))
    let c_fo := max (2 * 40 + 9539) ((2 * 1569 + 9539) + c_otr + c_pk + c_cm)
    let l_fo := (1569 + 8195) + l_otr + l_pk + l_cm
    let p_fo := (1569 + 8195) + max p_otr (l_otr + max p_pk (l_pk + p_cm))
    let r_fo := max 40 (max 1569 (max r_otr (max r_pk r_cm)))
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
      ((2 * 24 + 9539 + c_ld) + max (2 * 40 + 9539) c_fo)
      (l_ld + l_fo)
      (max p_ld (l_ld + p_fo))
      (max (max 24 r_ld) (max 40 r_fo)) := by
  intro ctLen c_otr l_otr p_otr r_otr c_ld l_ld p_ld r_ld c_id l_id p_id r_id
    c_ap c_save c_cm l_cm p_cm r_cm c_fo l_fo p_fo r_fo
  have hle24 : 24 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hle40
  have hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hle40
  have hLoadPoll : PhaseCreditSpec M
      (kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val) c_ld l_ld p_ld r_ld :=
    PhaseCreditSpec.of_imp hLoadEq
      (sessLoadPoll_phaseCredit hM dirDomainCaps_opened_sess (by decide) hpeer hSessFileCap hDeser)
  have hSmallId : PhaseCreditSpec M
      (CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName)
      c_id l_id p_id r_id :=
    smallStorePoll_phaseCredit hM dirDomainCaps_opened_peers (by decide) hidKeyLen hIdFileCap
  exact withStoresEncTight_creditSpec_small hM scopeKit
    (w1SessKit B img F peer) kitEnv StoresGhost.opened.sessions
    (w1IdKit B img F peer) ikitEnv StoresGhost.opened.identity
    C S uuidTryParse x
    (nameCap := 40) (kyberCap := 1569)
    hle32 hle24 hle32 hle32 hle32 hremName hle40
    hLoadPoll
    (fun _ _ _ _ hsc hcur _ => w1_scopeKit_kyber_ciphertext_le_1569 hsc hcur)
    (fun r sess otr taken hsc hcur hfrom => by
      obtain ⟨hve, hpq⟩ := peerSpqrValid_of_fromSessionState hsc hcur hfrom hValid
      have hSigEx : PhaseCreditSpec M
          (fun evs => ∃ g, SigNoneGuard r sess otr taken g ∧ SignalMessageNewEnv uuidTryParse g evs)
          c_sig l_sig p_sig r_sig :=
        phaseCreditSpec_exists fun g hg =>
          let ⟨hc, hl, hp, hr⟩ := hSigNone r sess otr taken g hg
          (WireMsgPeakSpec.signalMessageNew_phaseCredit hM uuidTryParse g).mono hc hl hp hr
      exact W1EncryptSegments.otrEncryptStep_creditSpec_small32 hM hle32
        (ptextLen := x.ptext.length) (hSend otr.pqrState hve hpq) hSigEx)
    (fun r sess otr taken hsc hcur hfrom => by
      obtain ⟨hve, hpq⟩ := peerSpqrValid_of_fromSessionState hsc hcur hfrom hValid
      have hSigEx : PhaseCreditSpec M
          (fun evs => ∃ g, SigSomeGuard r sess otr taken g ∧ SignalMessageNewEnv uuidTryParse g evs)
          c_sig l_sig p_sig r_sig :=
        phaseCreditSpec_exists fun g hg =>
          let ⟨hc, hl, hp, hr⟩ := hSigSome r sess otr taken g hg
          (WireMsgPeakSpec.signalMessageNew_phaseCredit hM uuidTryParse g).mono hc hl hp hr
      exact W1EncryptSegments.otrEncryptStep_creditSpec_small32 hM hle32
        (ptextLen := x.ptext.length) (hSend otr.pqrState hve hpq) hSigEx)
    (fun r sess otr taken _ _ _ =>
      phaseCreditSpec_exists fun call hcall =>
        let ⟨hc, hl, hp, hr⟩ := hPkCap r sess otr taken call hcall
        (preKeyMsgNew_phaseCredit hM call).mono hc hl hp hr)
    (fun _ _ _ _ k _ _ _ _ => PhaseCreditSpec.of_imp (hTrustEq k) hSmallId)
    (fun _ _ _ _ k _ _ _ _ => PhaseCreditSpec.of_imp (hSaveEq k) hSmallId)
    hStoreNone
    hStoreSome

/-! ## 4. Tight and `PeerSpqrTightValid640` End-to-End Slot Bounds -/

/-- Exact ML-KEM-1024 ciphertext byte length (`ct.length = 1569`) on any `w1SessKit.ScopeAt` session.
-/
theorem w1_scopeKit_kyber_ciphertext_eq_1569 {B : RunBudgets} {img : Arm64.Obj.Image}
    {F : FsFiles} {peer : AddrGhost} {st0 : DirGhost} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    (hsc : (w1SessKit B img F peer).ScopeAt scopeKit st0 rem r)
    (hs : r.currentSession = some sess) :
    ∀ ct, sess.pendingKyberPreKey.map (·.ciphertext) = some ct → ct.length = 1569 := by
  obtain ⟨s', hs', hsp⟩ := hsc.1.2
  cases hs.symm.trans hs'
  intro ct hct
  rcases hky : sess.pendingKyberPreKey with _ | k
  · simp [hky] at hct
  · simp only [hky, Option.map_some, Option.some.injEq] at hct
    subst hct
    exact hsp.2.2.1 k hky

theorem fromCmTight_creditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} {bs bi : BitVec 64} (hM : ModelHyps M)
    (kit : SessionStoreSpec A bs) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A bi) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    {rem : AddrVal} {remName : VecGhost} {nameCap nameCum : Nat}
    {sess : Session (List (BitVec 8))} {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey}
    {c_tr l_tr p_tr r_tr c_sv l_sv p_sv r_sv c_st l_st p_st r_st : Nat}
    (hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxSt : kit.storeBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxSv : ikit.saveBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxTr : ikit.trustBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hName : remName.bytes.length ≤ nameCap)
    (hNameSm : nameCap ≤ HasFineReallocCredit.smallMaxReq M)
    (hNameCum : ∀ n, 0 < n → n ≤ nameCap → HasFineReallocCredit.smallAllocCost M n ≤ nameCum)
    (hTrust : PhaseCreditSpec M (ikitEnv.trustPollEnv ist0 rem k .sending) c_tr l_tr p_tr r_tr)
    (hSave : PhaseCreditSpec M
      (ikitEnv.savePollEnv (ikit.trustUpdate ist0 rem k .sending (.ok true)) rem k)
      c_sv l_sv p_sv r_sv)
    (hStore : PhaseCreditSpec M
      (kitEnv.storePollEnv st0 rem (storedRecord sess otr' taken)) c_st l_st p_st r_st) :
    let c_ap :=
      HasFineReallocCredit.smallAllocCost M 32 +
        HasFineReallocCredit.smallAllocCost M kit.storeBoxSize + c_st
    let c_save := (HasFineReallocCredit.smallAllocCost M ikit.saveBoxSize + c_sv) + c_ap
    PhaseCreditSpec M
      (FromCmTightEnv kit kitEnv st0 ikit ikitEnv ist0 rem remName sess otr' taken k)
      ((HasFineReallocCredit.smallAllocCost M ikit.trustBoxSize + c_tr) + max nameCum c_save)
      (l_tr + (l_sv + l_st))
      (max p_tr (l_tr + max p_sv (l_sv + p_st)))
      (max (max ikit.trustBoxSize r_tr)
        (max nameCap (max (max ikit.saveBoxSize r_sv) (max 32 (max kit.storeBoxSize r_st))))) := by
  intro c_ap c_save
  exact fromCmSeg_creditSpec_tight hM hBoxTr hName hNameSm hNameCum hTrust
    (fromSaveSeg_creditSpec_tight hM hBoxSv hSave
      (fromApplySeg_creditSpec_tight hM hle32 hBoxSt hStore))

/-- Tight end-to-end `PhaseCreditSpec` for `WithStoresEncTightEnv` under exact Kyber ciphertext length `kyberLen ≤ smallMaxReq M`.
-/
theorem withStoresEncTight_creditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} {bs bi : BitVec 64} (hM : ModelHyps M)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (kit : SessionStoreSpec A bs) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A bi) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (C : Crypto) (S : SpqrModel) (parse : UuidParser) (x : WithStoresEncGhost)
    {E_otrNone E_otrSome E_pksmNew :
      SessionRecord (List (BitVec 8)) → Session (List (BitVec 8)) →
      OutgoingTripleRatchet (List (BitVec 8)) → SessionState (List (BitVec 8)) →
      List AllocEvent → Prop}
    {nameCap nameCum kyberLen : Nat}
    {c_ld l_ld p_ld r_ld : Nat}
    {c_otr l_otr p_otr r_otr c_pk l_pk p_pk r_pk : Nat}
    {c_tr l_tr p_tr r_tr c_sv l_sv p_sv r_sv c_st l_st p_st r_st : Nat}
    (hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxLd : kit.loadBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxSt : kit.storeBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxSv : ikit.saveBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hBoxTr : ikit.trustBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hName : x.rem.name.bytes.length ≤ nameCap)
    (hNameSm : nameCap ≤ HasFineReallocCredit.smallMaxReq M)
    (hNameCum : ∀ n, 0 < n → n ≤ nameCap → HasFineReallocCredit.smallAllocCost M n ≤ nameCum)
    (hKyberSm : kyberLen ≤ HasFineReallocCredit.smallMaxReq M)
    (hLoad : PhaseCreditSpec M (kitEnv.loadPollEnv st0 x.rem.val) c_ld l_ld p_ld r_ld)
    (hKyberEq : ∀ r sess otr taken,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      ∀ ct, sess.pendingKyberPreKey.map (·.ciphertext) = some ct → ct.length = kyberLen)
    (hOtrNone : ∀ r sess otr taken,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseCreditSpec M (E_otrNone r sess otr taken) c_otr l_otr p_otr r_otr)
    (hOtrSome : ∀ r sess otr taken,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseCreditSpec M (E_otrSome r sess otr taken) c_otr l_otr p_otr r_otr)
    (hPksmNew : ∀ r sess otr taken,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      PhaseCreditSpec M (E_pksmNew r sess otr taken) c_pk l_pk p_pk r_pk)
    (hTrust : ∀ r sess otr taken k,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M (ikitEnv.trustPollEnv ist0 x.rem.val k .sending) c_tr l_tr p_tr r_tr)
    (hSave : ∀ r sess otr taken k,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M
        (ikitEnv.savePollEnv (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k)
        c_sv l_sv p_sv r_sv)
    (hStoreNone : ∀ r sess otr taken k,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M
        (kitEnv.storePollEnv st0 x.rem.val (storedRecord sess (otrAfterNone C S x otr) taken))
        c_st l_st p_st r_st)
    (hStoreSome : ∀ r sess otr taken k,
      kit.ScopeAt Scope st0 x.rem.val r → r.currentSession = some sess →
      execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) →
      taken.remoteIdentity = some k →
      PhaseCreditSpec M
        (kitEnv.storePollEnv st0 x.rem.val
          (storedRecord sess (otrAfterSome C S parse x otr) taken))
        c_st l_st p_st r_st) :
    let c_ap :=
      HasFineReallocCredit.smallAllocCost M 32 +
        HasFineReallocCredit.smallAllocCost M kit.storeBoxSize + c_st
    let c_save := (HasFineReallocCredit.smallAllocCost M ikit.saveBoxSize + c_sv) + c_ap
    let c_cm := (HasFineReallocCredit.smallAllocCost M ikit.trustBoxSize + c_tr) + max nameCum c_save
    let l_cm := l_tr + (l_sv + l_st)
    let p_cm := max p_tr (l_tr + max p_sv (l_sv + p_st))
    let r_cm := max (max ikit.trustBoxSize r_tr)
      (max nameCap (max (max ikit.saveBoxSize r_sv) (max 32 (max kit.storeBoxSize r_st))))
    let c_fo := max nameCum (HasFineReallocCredit.smallAllocCost M kyberLen + c_otr + c_pk + c_cm)
    let l_fo := l_otr + l_pk + l_cm
    let p_fo := max p_otr (l_otr + max p_pk (l_pk + p_cm))
    let r_fo := max nameCap (max kyberLen (max r_otr (max r_pk r_cm)))
    PhaseCreditSpec M
      (WithStoresEncTightEnv Scope kit kitEnv st0 ikit ikitEnv ist0 C S parse x
        E_otrNone E_otrSome E_pksmNew)
      ((HasFineReallocCredit.smallAllocCost M kit.loadBoxSize + c_ld) + max nameCum c_fo)
      (l_ld + l_fo)
      (max p_ld (l_ld + p_fo))
      (max (max kit.loadBoxSize r_ld) (max nameCap r_fo)) := by
  intro c_ap c_save c_cm l_cm p_cm r_cm c_fo l_fo p_fo r_fo
  refine withStoresEncSeg_creditSpec_tight hM hBoxLd hName hNameSm hNameCum hLoad ?_
  have hEx :
      PhaseCreditSpec M
        (fun evs' =>
          ∃ w : SessionRecord (List (BitVec 8)) × Session (List (BitVec 8)) ×
              OutgoingTripleRatchet (List (BitVec 8)) × SessionState (List (BitVec 8)),
            (kit.ScopeAt Scope st0 x.rem.val w.1 ∧
              w.1.currentSession = some w.2.1 ∧
              execOk OutgoingTripleRatchet.fromSessionState w.2.1.state =
                .ok (w.2.2.1, w.2.2.2)) ∧
            FromOtrTightEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x
              w.2.1 w.2.2.1 w.2.2.2
              (E_otrNone w.1 w.2.1 w.2.2.1 w.2.2.2)
              (E_otrSome w.1 w.2.1 w.2.2.1 w.2.2.2)
              (E_pksmNew w.1 w.2.1 w.2.2.1 w.2.2.2) evs')
        c_fo l_fo p_fo r_fo := by
    refine phaseCreditSpec_exists fun ⟨r, sess, otr, taken⟩ ⟨hsc, hcur, hfrom⟩ => ?_
    have hK : PhaseCreditSpec M
        (fun evs => ∃ k : IdentityKey, taken.remoteIdentity = some k ∧
          FromKeySegEnv sess.pendingPreKey x.rem.name
            (sess.pendingKyberPreKey.map (·.ciphertext))
            (E_otrNone r sess otr taken)
            (FromCmTightEnv kit kitEnv st0 ikit ikitEnv ist0 x.rem.val x.rem.name
              sess (otrAfterNone C S x otr) taken k)
            (E_otrSome r sess otr taken)
            (E_pksmNew r sess otr taken)
            (FromCmTightEnv kit kitEnv st0 ikit ikitEnv ist0 x.rem.val x.rem.name
              sess (otrAfterSome C S parse x otr) taken k) evs)
        c_fo l_fo p_fo r_fo :=
      phaseCreditSpec_exists fun k hk =>
        fromKeySeg_creditSpec_tight hM hName hNameSm hNameCum
          (hKyberEq r sess otr taken hsc hcur hfrom) hKyberSm
          (hOtrNone r sess otr taken hsc hcur hfrom)
          (hOtrSome r sess otr taken hsc hcur hfrom)
          (hPksmNew r sess otr taken hsc hcur hfrom)
          (fromCmTight_creditSpec_tight hM kit kitEnv st0 ikit ikitEnv ist0
            hle32 hBoxSt hBoxSv hBoxTr hName hNameSm hNameCum
            (hTrust r sess otr taken k hsc hcur hfrom hk)
            (hSave r sess otr taken k hsc hcur hfrom hk)
            (hStoreNone r sess otr taken k hsc hcur hfrom hk))
          (fromCmTight_creditSpec_tight hM kit kitEnv st0 ikit ikitEnv ist0
            hle32 hBoxSt hBoxSv hBoxTr hName hNameSm hNameCum
            (hTrust r sess otr taken k hsc hcur hfrom hk)
            (hSave r sess otr taken k hsc hcur hfrom hk)
            (hStoreSome r sess otr taken k hsc hcur hfrom hk))
    exact (PhaseCreditSpec.or (PhaseCreditSpec.freeOnly hM.freeNonInc) hK).mono
      (by omega) (by omega) (by omega) (by omega)
  refine PhaseCreditSpec.of_imp (fun evs ⟨r, sess, otr, taken, hsc, hcur, hfrom, hfo⟩ =>
    ⟨(r, sess, otr, taken), ⟨hsc, hcur, hfrom⟩, hfo⟩) hEx

/-- `PeerSpqrTightValid640` companion to `w1CliEncryptSlot_creditSpec_small`. -/
theorem w1CliEncryptSlot_tight640_creditSpec_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hle40 : 40 ≤ HasFineReallocCredit.smallMaxReq M)
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
    {fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    {c_s l_s p_s r_s c_sig l_sig p_sig r_sig c_pk l_pk p_pk r_pk c_st l_st p_st r_st : Nat}
    (hpeer : peer.name.bytes.length ≤ 40)
    (hremName : x.rem.name.bytes.length ≤ 40)
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
    (hSend : ∀ pqrState, ValidEncoderPts640 pqrState → ValidChainParams pqrState →
      pqrState.length < 2 ^ 31 → PhaseCreditSpec M (E_send pqrState x.rest) c_s l_s p_s r_s)
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
    let ctLen := (x.ptext.length / 16 + 1) * 16
    let c_otr := c_s + (2 * 32 + 9539) + (2 * ctLen + 9539) + c_sig
    let l_otr := l_s + (ctLen + 8195) + l_sig
    let p_otr := max p_s (l_s + (ctLen + 8195) + p_sig)
    let r_otr := max r_s (max 32 (max ctLen r_sig))
    let c_ld := sessLoadPollDeltaCum (max 0 fileCap) deserCum
    let l_ld := sessLoadPollDeltaLive (max 0 fileCap) deserLive
    let p_ld := sessLoadPollDeltaPeak (max 0 fileCap) deserPeak
    let r_ld := sessLoadPollMaxReq (max 0 fileCap) deserMaxReq
    let c_id := smallStorePollDeltaCum (max 0 fileCap) 0
    let l_id := smallStorePollDeltaLive (max 0 fileCap) 0
    let p_id := smallStorePollDeltaPeak (max 0 fileCap) 0
    let r_id := smallStorePollMaxReq (max 0 fileCap) 0
    let c_ap := (2 * 32 + 9539) + (2 * 32 + 9539) + c_st
    let c_save := (2 * 32 + 9539 + c_id) + c_ap
    let c_cm := (2 * 32 + 9539 + c_id) + max (2 * 40 + 9539) c_save
    let l_cm := l_id + (l_id + l_st)
    let p_cm := max p_id (l_id + max p_id (l_id + p_st))
    let r_cm := max (max 32 r_id) (max 40 (max (max 32 r_id) (max 32 (max 32 r_st))))
    let c_fo := max (2 * 40 + 9539) ((2 * 1569 + 9539) + c_otr + c_pk + c_cm)
    let l_fo := (1569 + 8195) + l_otr + l_pk + l_cm
    let p_fo := (1569 + 8195) + max p_otr (l_otr + max p_pk (l_pk + p_cm))
    let r_fo := max 40 (max 1569 (max r_otr (max r_pk r_cm)))
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
      ((2 * 24 + 9539 + c_ld) + max (2 * 40 + 9539) c_fo)
      (l_ld + l_fo)
      (max p_ld (l_ld + p_fo))
      (max (max 24 r_ld) (max 40 r_fo)) := by
  intro ctLen c_otr l_otr p_otr r_otr c_ld l_ld p_ld r_ld c_id l_id p_id r_id
    c_ap c_save c_cm l_cm p_cm r_cm c_fo l_fo p_fo r_fo
  have hle24 : 24 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hle40
  have hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hle40
  have hLoadPoll : PhaseCreditSpec M
      (kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val) c_ld l_ld p_ld r_ld :=
    PhaseCreditSpec.of_imp hLoadEq
      (sessLoadPoll_phaseCredit hM dirDomainCaps_opened_sess (by decide) hpeer hSessFileCap hDeser)
  have hSmallId : PhaseCreditSpec M
      (CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName)
      c_id l_id p_id r_id :=
    smallStorePoll_phaseCredit hM dirDomainCaps_opened_peers (by decide) hidKeyLen hIdFileCap
  exact withStoresEncTight_creditSpec_small hM scopeKit
    (w1SessKit B img F peer) kitEnv StoresGhost.opened.sessions
    (w1IdKit B img F peer) ikitEnv StoresGhost.opened.identity
    C S uuidTryParse x
    (nameCap := 40) (kyberCap := 1569)
    hle32 hle24 hle32 hle32 hle32 hremName hle40
    hLoadPoll
    (fun _ _ _ _ hsc hcur _ => w1_scopeKit_kyber_ciphertext_le_1569 hsc hcur)
    (fun r sess otr taken hsc hcur hfrom => by
      obtain ⟨hve, hcp, hpq⟩ := peerSpqrTightValid640_of_fromSessionState hsc hcur hfrom hValid
      have hSigEx : PhaseCreditSpec M
          (fun evs => ∃ g, SigNoneGuard r sess otr taken g ∧ SignalMessageNewEnv uuidTryParse g evs)
          c_sig l_sig p_sig r_sig :=
        phaseCreditSpec_exists fun g hg =>
          let ⟨hc, hl, hp, hr⟩ := hSigNone r sess otr taken g hg
          (WireMsgPeakSpec.signalMessageNew_phaseCredit hM uuidTryParse g).mono hc hl hp hr
      exact W1EncryptSegments.otrEncryptStep_creditSpec_small32 hM hle32
        (ptextLen := x.ptext.length) (hSend otr.pqrState hve hcp hpq) hSigEx)
    (fun r sess otr taken hsc hcur hfrom => by
      obtain ⟨hve, hcp, hpq⟩ := peerSpqrTightValid640_of_fromSessionState hsc hcur hfrom hValid
      have hSigEx : PhaseCreditSpec M
          (fun evs => ∃ g, SigSomeGuard r sess otr taken g ∧ SignalMessageNewEnv uuidTryParse g evs)
          c_sig l_sig p_sig r_sig :=
        phaseCreditSpec_exists fun g hg =>
          let ⟨hc, hl, hp, hr⟩ := hSigSome r sess otr taken g hg
          (WireMsgPeakSpec.signalMessageNew_phaseCredit hM uuidTryParse g).mono hc hl hp hr
      exact W1EncryptSegments.otrEncryptStep_creditSpec_small32 hM hle32
        (ptextLen := x.ptext.length) (hSend otr.pqrState hve hcp hpq) hSigEx)
    (fun r sess otr taken _ _ _ =>
      phaseCreditSpec_exists fun call hcall =>
        let ⟨hc, hl, hp, hr⟩ := hPkCap r sess otr taken call hcall
        (preKeyMsgNew_phaseCredit hM call).mono hc hl hp hr)
    (fun _ _ _ _ k _ _ _ _ => PhaseCreditSpec.of_imp (hTrustEq k) hSmallId)
    (fun _ _ _ _ k _ _ _ _ => PhaseCreditSpec.of_imp (hSaveEq k) hSmallId)
    hStoreNone
    hStoreSome

/-- `ScopeAt`-aware tight CLI W1 (`StoresGhost.opened`) `PhaseCreditSpec` under `1569 ≤ smallMaxReq M`.
-/
theorem w1CliEncryptSlot_scopedSend_creditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
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
    let ctLen := (x.ptext.length / 16 + 1) * 16
    let c_otr :=
      c_s + HasFineReallocCredit.smallAllocCost M 32 + tryCloneSmallDelta M ctLen + c_sig
    let l_otr := l_s + tryCloneLargeDelta M ctLen + l_sig
    let p_otr := max p_s (l_s + tryCloneLargeDelta M ctLen + p_sig)
    let r_otr := max r_s (max 32 (max ctLen r_sig))
    let c_ld := sessLoadPollDeltaCum (max 0 fileCap) deserCum
    let l_ld := sessLoadPollDeltaLive (max 0 fileCap) deserLive
    let p_ld := sessLoadPollDeltaPeak (max 0 fileCap) deserPeak
    let r_ld := sessLoadPollMaxReq (max 0 fileCap) deserMaxReq
    let c_id := smallStorePollDeltaCum (max 0 fileCap) 0
    let l_id := smallStorePollDeltaLive (max 0 fileCap) 0
    let p_id := smallStorePollDeltaPeak (max 0 fileCap) 0
    let r_id := smallStorePollMaxReq (max 0 fileCap) 0
    let c_ap :=
      HasFineReallocCredit.smallAllocCost M 32 +
        HasFineReallocCredit.smallAllocCost M 32 + c_st
    let c_save := (HasFineReallocCredit.smallAllocCost M 32 + c_id) + c_ap
    let c_cm := (HasFineReallocCredit.smallAllocCost M 32 + c_id) + max nameCum c_save
    let l_cm := l_id + (l_id + l_st)
    let p_cm := max p_id (l_id + max p_id (l_id + p_st))
    let r_cm := max (max 32 r_id) (max 40 (max (max 32 r_id) (max 32 (max 32 r_st))))
    let c_fo := max nameCum (HasFineReallocCredit.smallAllocCost M 1569 + c_otr + c_pk + c_cm)
    let l_fo := l_otr + l_pk + l_cm
    let p_fo := max p_otr (l_otr + max p_pk (l_pk + p_cm))
    let r_fo := max 40 (max 1569 (max r_otr (max r_pk r_cm)))
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
      ((HasFineReallocCredit.smallAllocCost M 24 + c_ld) + max nameCum c_fo)
      (l_ld + l_fo)
      (max p_ld (l_ld + p_fo))
      (max (max 24 r_ld) (max 40 r_fo)) := by
  intro ctLen c_otr l_otr p_otr r_otr c_ld l_ld p_ld r_ld c_id l_id p_id r_id
    c_ap c_save c_cm l_cm p_cm r_cm c_fo l_fo p_fo r_fo
  have hle24 : 24 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hle1569
  have hle32 : 32 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hle1569
  have hle40 : 40 ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans (by decide) hle1569
  have hLoadPoll : PhaseCreditSpec M
      (kitEnv.loadPollEnv StoresGhost.opened.sessions x.rem.val) c_ld l_ld p_ld r_ld :=
    PhaseCreditSpec.of_imp hLoadEq
      (sessLoadPoll_phaseCredit hM dirDomainCaps_opened_sess (by decide) hpeer hSessFileCap hDeser)
  have hSmallId : PhaseCreditSpec M
      (CliSmallStorePollEnv cliIo.rd F StoresGhost.opened.identity.peers peerIdKeyName)
      c_id l_id p_id r_id :=
    smallStorePoll_phaseCredit hM dirDomainCaps_opened_peers (by decide) hidKeyLen hIdFileCap
  exact withStoresEncTight_creditSpec_tight hM scopeKit
    (w1SessKit B img F peer) kitEnv StoresGhost.opened.sessions
    (w1IdKit B img F peer) ikitEnv StoresGhost.opened.identity
    C S uuidTryParse x
    (nameCap := 40) (nameCum := nameCum) (kyberLen := 1569)
    hle32 hle24 hle32 hle32 hle32 hremName hle40 hNameCum hle1569
    hLoadPoll
    (fun _ _ _ _ hsc hcur _ => w1_scopeKit_kyber_ciphertext_eq_1569 hsc hcur)
    (fun r sess otr taken hsc hcur hfrom => by
      have hSigEx : PhaseCreditSpec M
          (fun evs => ∃ g, SigNoneGuard r sess otr taken g ∧ SignalMessageNewEnv uuidTryParse g evs)
          c_sig l_sig p_sig r_sig :=
        phaseCreditSpec_exists fun g hg =>
          let ⟨hc, hl, hp, hr⟩ := hSigNone r sess otr taken g hg
          (WireMsgPeakSpec.signalMessageNew_phaseCredit hM uuidTryParse g).mono hc hl hp hr
      exact otrEncryptStep_creditSpec_tight hM hle32
        (ptextLen := x.ptext.length) (hSend r sess otr taken hsc hcur hfrom) hSigEx)
    (fun r sess otr taken hsc hcur hfrom => by
      have hSigEx : PhaseCreditSpec M
          (fun evs => ∃ g, SigSomeGuard r sess otr taken g ∧ SignalMessageNewEnv uuidTryParse g evs)
          c_sig l_sig p_sig r_sig :=
        phaseCreditSpec_exists fun g hg =>
          let ⟨hc, hl, hp, hr⟩ := hSigSome r sess otr taken g hg
          (WireMsgPeakSpec.signalMessageNew_phaseCredit hM uuidTryParse g).mono hc hl hp hr
      exact otrEncryptStep_creditSpec_tight hM hle32
        (ptextLen := x.ptext.length) (hSend r sess otr taken hsc hcur hfrom) hSigEx)
    (fun r sess otr taken _ _ _ =>
      phaseCreditSpec_exists fun call hcall =>
        let ⟨hc, hl, hp, hr⟩ := hPkCap r sess otr taken call hcall
        (preKeyMsgNew_phaseCredit hM call).mono hc hl hp hr)
    (fun _ _ _ _ k _ _ _ _ => PhaseCreditSpec.of_imp (hTrustEq k) hSmallId)
    (fun _ _ _ _ k _ _ _ _ => PhaseCreditSpec.of_imp (hSaveEq k) hSmallId)
    hStoreNone
    hStoreSome

theorem w1CliEncryptSlot_creditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
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
    (hValid : PeerSpqrValid F x.rem.val)
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
    (hSend : ∀ pqrState, ValidEncoderPts pqrState → pqrState.length < 2 ^ 31 →
      PhaseCreditSpec M (E_send pqrState x.rest) c_s l_s p_s r_s)
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
    let ctLen := (x.ptext.length / 16 + 1) * 16
    let c_otr :=
      c_s + HasFineReallocCredit.smallAllocCost M 32 + tryCloneSmallDelta M ctLen + c_sig
    let l_otr := l_s + tryCloneLargeDelta M ctLen + l_sig
    let p_otr := max p_s (l_s + tryCloneLargeDelta M ctLen + p_sig)
    let r_otr := max r_s (max 32 (max ctLen r_sig))
    let c_ld := sessLoadPollDeltaCum (max 0 fileCap) deserCum
    let l_ld := sessLoadPollDeltaLive (max 0 fileCap) deserLive
    let p_ld := sessLoadPollDeltaPeak (max 0 fileCap) deserPeak
    let r_ld := sessLoadPollMaxReq (max 0 fileCap) deserMaxReq
    let c_id := smallStorePollDeltaCum (max 0 fileCap) 0
    let l_id := smallStorePollDeltaLive (max 0 fileCap) 0
    let p_id := smallStorePollDeltaPeak (max 0 fileCap) 0
    let r_id := smallStorePollMaxReq (max 0 fileCap) 0
    let c_ap :=
      HasFineReallocCredit.smallAllocCost M 32 +
        HasFineReallocCredit.smallAllocCost M 32 + c_st
    let c_save := (HasFineReallocCredit.smallAllocCost M 32 + c_id) + c_ap
    let c_cm := (HasFineReallocCredit.smallAllocCost M 32 + c_id) + max nameCum c_save
    let l_cm := l_id + (l_id + l_st)
    let p_cm := max p_id (l_id + max p_id (l_id + p_st))
    let r_cm := max (max 32 r_id) (max 40 (max (max 32 r_id) (max 32 (max 32 r_st))))
    let c_fo := max nameCum (HasFineReallocCredit.smallAllocCost M 1569 + c_otr + c_pk + c_cm)
    let l_fo := l_otr + l_pk + l_cm
    let p_fo := max p_otr (l_otr + max p_pk (l_pk + p_cm))
    let r_fo := max 40 (max 1569 (max r_otr (max r_pk r_cm)))
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
      ((HasFineReallocCredit.smallAllocCost M 24 + c_ld) + max nameCum c_fo)
      (l_ld + l_fo)
      (max p_ld (l_ld + p_fo))
      (max (max 24 r_ld) (max 40 r_fo)) :=
  w1CliEncryptSlot_scopedSend_creditSpec_tight hM hle1569 B img F peer C S x DeserEnv
    peerIdKeyName kitEnv ikitEnv E_send SigNoneGuard SigSomeGuard PkCallGuard
    hpeer hremName hNameCum hidKeyLen hSessFileCap hIdFileCap hDeser
    hLoadEq hTrustEq hSaveEq
    (fun _ _ otr _ hsc hcur hfrom =>
      let ⟨hve, hpq⟩ := peerSpqrValid_of_fromSessionState hsc hcur hfrom hValid
      hSend otr.pqrState hve hpq)
    hSigNone hSigSome hPkCap hStoreNone hStoreSome

/-- Combined tight wrapper-delta and `PeerSpqrTightValid640` CLI W1 (`StoresGhost.opened`) `PhaseCreditSpec`.
-/
theorem w1CliEncryptSlot_tight640_creditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
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
    (hSend : ∀ pqrState, ValidEncoderPts640 pqrState → ValidChainParams pqrState →
      pqrState.length < 2 ^ 31 → PhaseCreditSpec M (E_send pqrState x.rest) c_s l_s p_s r_s)
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
    let ctLen := (x.ptext.length / 16 + 1) * 16
    let c_otr :=
      c_s + HasFineReallocCredit.smallAllocCost M 32 + tryCloneSmallDelta M ctLen + c_sig
    let l_otr := l_s + tryCloneLargeDelta M ctLen + l_sig
    let p_otr := max p_s (l_s + tryCloneLargeDelta M ctLen + p_sig)
    let r_otr := max r_s (max 32 (max ctLen r_sig))
    let c_ld := sessLoadPollDeltaCum (max 0 fileCap) deserCum
    let l_ld := sessLoadPollDeltaLive (max 0 fileCap) deserLive
    let p_ld := sessLoadPollDeltaPeak (max 0 fileCap) deserPeak
    let r_ld := sessLoadPollMaxReq (max 0 fileCap) deserMaxReq
    let c_id := smallStorePollDeltaCum (max 0 fileCap) 0
    let l_id := smallStorePollDeltaLive (max 0 fileCap) 0
    let p_id := smallStorePollDeltaPeak (max 0 fileCap) 0
    let r_id := smallStorePollMaxReq (max 0 fileCap) 0
    let c_ap :=
      HasFineReallocCredit.smallAllocCost M 32 +
        HasFineReallocCredit.smallAllocCost M 32 + c_st
    let c_save := (HasFineReallocCredit.smallAllocCost M 32 + c_id) + c_ap
    let c_cm := (HasFineReallocCredit.smallAllocCost M 32 + c_id) + max nameCum c_save
    let l_cm := l_id + (l_id + l_st)
    let p_cm := max p_id (l_id + max p_id (l_id + p_st))
    let r_cm := max (max 32 r_id) (max 40 (max (max 32 r_id) (max 32 (max 32 r_st))))
    let c_fo := max nameCum (HasFineReallocCredit.smallAllocCost M 1569 + c_otr + c_pk + c_cm)
    let l_fo := l_otr + l_pk + l_cm
    let p_fo := max p_otr (l_otr + max p_pk (l_pk + p_cm))
    let r_fo := max 40 (max 1569 (max r_otr (max r_pk r_cm)))
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
      ((HasFineReallocCredit.smallAllocCost M 24 + c_ld) + max nameCum c_fo)
      (l_ld + l_fo)
      (max p_ld (l_ld + p_fo))
      (max (max 24 r_ld) (max 40 r_fo)) :=
  w1CliEncryptSlot_scopedSend_creditSpec_tight hM hle1569 B img F peer C S x DeserEnv
    peerIdKeyName kitEnv ikitEnv E_send SigNoneGuard SigSomeGuard PkCallGuard
    hpeer hremName hNameCum hidKeyLen hSessFileCap hIdFileCap hDeser
    hLoadEq hTrustEq hSaveEq
    (fun _ _ otr _ hsc hcur hfrom =>
      let ⟨hve, hcp, hpq⟩ := peerSpqrTightValid640_of_fromSessionState hsc hcur hfrom hValid
      hSend otr.pqrState hve hcp hpq)
    hSigNone hSigSome hPkCap hStoreNone hStoreSome

end LibsignalBinary.Proofs.PeakBudget.W1EncryptSlotPeak
