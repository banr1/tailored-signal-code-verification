/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
public import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPure

/-!
# Budget-Threaded Relocatable `MessageEncrypt` Envelopes and Seam States

Defines per-seam and end-to-end allocation envelopes (`FromApplyEnv` through `WithStoresEncEnv`),
the budget-threaded `withStoresEncPlacedSpecV` contract (`onOom = ⌜False⌝`), budget-threaded seam
states (`CurStateVPlaced` through `StoredStateVPlaced`), and `FitsEnv` witnesses for
`session_message_encrypt_with_stores` (block `198`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefsBudgetAux

open Arm64 ProofLib
open LibsignalBinary.Heap
open LibsignalBinary.Heap.Fine (FineStepBound fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (fineDynIvsOfCum fineMaxGroupsOfCum fineMaxMetaAreasOfCum fineStepReserveOfCum)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (LoadStepEnv SessionStoreBudgetEnv retagSessionStore)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv SaveStepEnv TrustStepEnv retagIdentityStore)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
  (KyberOptEnv PreKeyMsgNewRawEnv kyberOptEnv_phaseCreditSpec kyberPayloadLen
   preKeyMsgNewRawEnv_phaseCreditSpec preKeySignalMessage_new_small_length_le)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget
  (OtrEncryptCoreEnv SpqrSendBudgetEnv otrEncryptCoreEnv_phaseCreditSpec_bounded
   otrSignalMsgGhost witnessAddrGhost witnessCrypto witnessIdentityKey witnessKeyPair
   witnessOtr witnessPublicKey witnessSendEnv witnessSpqrModel witnessUuidParse)
open LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.DefsBudget
  (OtrApplyEnv otrApplyEnv_phaseCreditSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SeamBudget)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.Placed
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (WithStoresEncGhost encStoreExtraPlaced nowAt storedRecord withStoresEncStackV)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## 1. Per-Seam and End-to-End Allocation Envelopes -/

/-- Remaining allocation envelope from `Apply` (`+0xd9c`) to return (`segApplyStore` + exit). -/
def FromApplyEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) : List AllocEvent → Prop :=
  SeqEnv OtrApplyEnv
    (SeqEnv (BoxAllocEnv kit.storeBoxSize)
      (SeqEnv (kitEnv.storePollEnv st0 x.rem.val (storedRecord sess otr' taken))
        (SeqEnv (· = rustDeallocEvents kit.storeBoxSize 8) FreeOnlyEvs)))

/-- Remaining allocation envelope from `Save` (`+0xbd4`) to return. -/
def FromSaveEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist1 : ikit.IdState) (x : WithStoresEncGhost)
    (sess : Session (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) : List AllocEvent → Prop :=
  SeqEnv (SaveStepEnv ikit ikitEnv ist1 x.rem.val k)
    (fun evs => FreeOnlyEvs evs ∨ FromApplyEnv kit kitEnv st0 x sess otr' taken evs)

/-- Remaining allocation envelope from `Cm` (`+0xa70`) to return. -/
def FromCmEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (x : WithStoresEncGhost)
    (sess : Session (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) : List AllocEvent → Prop :=
  SeqEnv (TrustStepEnv ikit ikitEnv ist0 x.rem.val k .sending)
    (fun evs =>
      FreeOnlyEvs evs ∨
      SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs evs ∨
      FromSaveEnv kit kitEnv st0 ikit ikitEnv
        (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x sess otr' taken k evs)

/-- Pending Kyber payload extracted from `sess.pendingKyberPreKey`. -/
def pendingKyberPayload (sess : Session (List (BitVec 8))) : Option KyberPayload :=
  sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)

/-- Model `PreKeySignalMessage` assembled in `segPreKey` from `(sess, items, otr', sm)`. -/
def preKeyMsgFromItems (sess : Session (List (BitVec 8))) (items : PendingPreKey)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (sm : SignalMessage) : PreKeySignalMessage :=
  PreKeySignalMessage.new otr'.sessionVersion sess.localRegistrationId items.preKeyId
    items.signedPreKeyId (pendingKyberPayload sess) items.baseKey otr'.localIdentityKey sm

/-- Remaining allocation envelope on the `pendingPreKey = some items` path right after
    `OTR::encrypt` returns. -/
def PreKeyPostEncryptEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (items : PendingPreKey) (evs' : List AllocEvent) : Prop :=
  let res := Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext
    (serializeAddresses (serviceIdParse parse) x.loc x.rem) x.rest) otr
  FreeOnlyEvs evs' ∨
  match res.1 with
  | .error _ => False
  | .ok sm =>
    SeqEnv
      (PreKeyMsgNewRawEnv (pendingKyberPayload sess) sm.serialized.length
        (preKeyMsgFromItems sess items res.2 sm).serialized.length)
      (fun evs'' =>
        FreeOnlyEvs evs'' ∨
        FromCmEnv kit kitEnv st0 ikit ikitEnv ist0 x sess res.2 taken k evs'') evs'

/-- Remaining allocation envelope from `Key` (`+0x344`) to return. -/
def FromKeyEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (parse : UuidParser)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (x : WithStoresEncGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (evs : List AllocEvent) : Prop :=
  (sess.pendingPreKey = none ∧
    SeqEnv (OtrEncryptCoreEnv C S sendEnv parse otr x.ptext none x.rem x.rest)
      (fun evs' =>
        FreeOnlyEvs evs' ∨
        FromCmEnv kit kitEnv st0 ikit ikitEnv ist0 x sess
          (Mut.exec (OutgoingTripleRatchet.encrypt C protoSignalCodec S.spqr x.ptext none x.rest) otr).2
          taken k evs') evs) ∨
  (∃ items, sess.pendingPreKey = some items ∧
    (SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs evs ∨
      SeqEnv (KyberOptEnv (sess.pendingKyberPreKey.map (·.ciphertext)))
        (SeqEnv (OtrEncryptCoreEnv C S sendEnv parse otr x.ptext (some x.loc) x.rem x.rest)
          (PreKeyPostEncryptEnv C S parse kit kitEnv st0 ikit ikitEnv ist0
            x sess otr taken k items)) evs))

/-- Remaining allocation envelope from `Otr` (`+0x2c8`) to return. -/
def FromOtrEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (parse : UuidParser)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (x : WithStoresEncGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
  ∃ k, taken.remoteIdentity = some k ∧
    FromKeyEnv C S sendEnv parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken k evs

/-- Remaining allocation envelope from `Cur` (`+0x20c`) to return (`segFrom` + rest). -/
def FromCurEnv {A : RustAlloc} (C : Crypto) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (parse : UuidParser)
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : WithStoresEncGhost) (evs : List AllocEvent) : Prop :=
  SeqEnv FreeOnlyEvs
    (fun evs' =>
      FreeOnlyEvs evs' ∨
      ∃ r sess otr taken,
        kit.ScopeAt Scope st0 x.rem.val r ∧
        r.currentSession = some sess ∧
        execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
        FromOtrEnv C S sendEnv parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken evs') evs

/-- Full end-to-end allocation envelope of `session_message_encrypt_with_stores`. -/
def WithStoresEncEnv {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) (parse : UuidParser)
    (x : WithStoresEncGhost) : List AllocEvent → Prop :=
  SeqEnv (LoadStepEnv kit kitEnv st0 x.rem.val)
    (fun evs =>
      FreeOnlyEvs evs ∨
      SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs evs ∨
      FromCurEnv C S sendEnv parse kit kitEnv st0 ikit ikitEnv ist0 Scope x evs)

/-! ## 2. Retag Lemmas and `withStoresEncPlacedSpecV` -/

@[simp]
theorem storeFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (answers : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ calls : List (StoreCall AddrVal (List (BitVec 8))),
      (retagSessionStore (A' := A') kit).storeFinal st0 answers calls =
        kit.storeFinal st0 answers calls
  | [] => rfl
  | c :: cs => by cases c <;> exact storeFinal_retag kit _ answers cs

@[simp]
theorem idFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ist0 : ikit.IdState)
    (answers : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ calls : List (StoreCall AddrVal (List (BitVec 8))),
      (retagIdentityStore (A' := A') ikit).idFinal ist0 answers calls =
        ikit.idFinal ist0 answers calls
  | [] => rfl
  | c :: cs => by cases c <;> exact idFinal_retag ikit _ answers cs

@[simp]
theorem encStoreExtraPlaced_retag {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (s0 : State) :
    encStoreExtraPlaced (retagSessionStore (A' := A') kit) st
      (retagIdentityStore (A' := A') ikit) ist x s0 =
    encStoreExtraPlaced kit st ikit ist x s0 := rfl

/-- Budget-threaded relocatable `session_message_encrypt_with_stores` (Block `198`) contract
    (`onOom := ⌜False⌝`, `allocFailedIn` eliminated from `onPanic`). -/
def withStoresEncPlacedSpecV [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec (WithStoresEncGhost × M.σ) :=
  StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun (x, st_init) s =>
        ⌜FitsEnv M lim st_init
            (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidParse x) ∧
          s.readReg64 .x0 = x.ptA ∧ (s.readReg64 .x1).toNat = x.ptext.length ∧
          x.ptext.length < 2 ^ 32 ∧ s.readReg64 .x2 = x.remA ∧ s.readReg64 .x3 = x.locA ∧
          x.locA ≠ 0#64 ∧
          s.readReg64 .x4 = x.ssA ∧ s.readReg64 .x5 = kit.ss_vt ∧
          s.readReg64 .x6 = x.idA ∧ s.readReg64 .x7 = ikit.id_vt ∧
          x.now.tvNsec.toNat < 10 ^ 9 ∧ s.readReg64 .x8 = x.ret ∧
          withStoresEncStackV kit ikit ≤ s.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0 ∗
        nowAt s.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗ memRegion x.ret 248 ∗ tapeAt ctl x.cur x.rest ∗
        FromRecordCallees.lsLogOff ∗ stackAt s.sp (withStoresEncStackV kit ikit) ∗
        A.pool lim st_init s
      post := fun (x, st_init) s0 sf =>
        ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit, ∃∗ evs : List AllocEvent,
          ⌜(x.model C S uuidParse answers).1 ≠ .error .panic ∧
            kit.callsRel st0 answers (x.model C S uuidParse answers).2 ∧
            ikit.idCallsRel ist0 answers (x.model C S uuidParse answers).2 ∧
            sf.trace = s0.trace ++
              ikit.traceOfWith kit encRecord answers (x.model C S uuidParse answers).2 ∧
            WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidParse x evs⌝ ∗
          kit.storeAt x.ssA (kit.storeFinal st0 answers (x.model C S uuidParse answers).2) ∗
          ikit.identityAt x.idA (ikit.idFinal ist0 answers (x.model C S uuidParse answers).2) ∗
          apiEncResultAt A.repAlloc x.ret (x.model C S uuidParse answers).1 ∗
          nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
          protocolAddressAt A.repAlloc x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
          FromRecordCallees.lsLogOff ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗
          A.pool lim (M.stepEvents evs st_init) sf
      onPanic := fun (x, _) s0 sf =>
        ⌜s0.trace <+: sf.trace ∧
          ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
            kit.loadRel st0 x.rem.val answers.loadSession ∧
            s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
            ((x.model C S uuidParse answers).1 = .error .panic ∨ x.sendPanics S answers)⌝ ∗
          anyHeap }

abbrev withStoresEncBudgetSpecV := @withStoresEncPlacedSpecV

theorem withStoresEncPlacedSpecV_pre_addrOk [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨
      (withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl uuidTryParse S sendEnv encRecord).pre (x, st_init) s0 ∗ R) :
    kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val := by
  have ⟨_, hp⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## 3. Budget-Threaded Seam States -/

def CurStateVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st
    (FromCurEnv C S sendEnv parse kit kitEnv st0 ikit ikitEnv ist0 Scope x) ∧
  CryptoVerification.LibsignalPublicApi.MessageEncrypt.CurStateVPlaced
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope ctl encRecord
    x r g sess R s0 s

abbrev CurStateVBudget := @CurStateVPlaced

def OtrStateVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st
    (FromOtrEnv C S sendEnv parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken) ∧
  CryptoVerification.LibsignalPublicApi.MessageEncrypt.OtrStateVPlaced
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope ctl encRecord
    x r sess otr taken pqCap pqPtr R s0 s

abbrev OtrStateVBudget := @OtrStateVPlaced

def KeyStateVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st
    (FromKeyEnv C S sendEnv parse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken k) ∧
  CryptoVerification.LibsignalPublicApi.MessageEncrypt.KeyStateVPlaced
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope ctl encRecord
    x r sess otr taken pqCap pqPtr k R s0 s

abbrev KeyStateVBudget := @KeyStateVPlaced

def CmStateVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (m : CiphertextMessage) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st
    (FromCmEnv kit kitEnv st0 ikit ikitEnv ist0 x sess otr' taken k) ∧
  CryptoVerification.LibsignalPublicApi.MessageEncrypt.CmStateVPlaced
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope C ctl parse S encRecord
    x r sess otr taken k m otr' pqCap' pqPtr' R s0 s

abbrev CmStateVBudget := @CmStateVPlaced

def SaveStateVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (m : CiphertextMessage) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st
    (FromSaveEnv kit kitEnv st0 ikit ikitEnv
      (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x sess otr' taken k) ∧
  CryptoVerification.LibsignalPublicApi.MessageEncrypt.SaveStateVPlaced
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope C ctl parse S encRecord
    x r sess otr taken k m otr' pqCap' pqPtr' R s0 s

abbrev SaveStateVBudget := @SaveStateVPlaced

def ApplyStateVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (m : CiphertextMessage) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (c : IdentityChange) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st
    (FromApplyEnv kit kitEnv st0 x sess otr' taken) ∧
  CryptoVerification.LibsignalPublicApi.MessageEncrypt.ApplyStateVPlaced
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope C ctl parse S encRecord
    x r sess otr taken k m otr' pqCap' pqPtr' c R s0 s

abbrev ApplyStateVBudget := @ApplyStateVPlaced

/-- Budget-threaded `Stored` (`+0xe88`) seam state (`FreeOnlyEvs` remaining to exit). -/
def StoredStateVPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init st : M.σ)
    (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (m : CiphertextMessage) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (c : IdentityChange) (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x) st_init st
    FreeOnlyEvs ∧
  CryptoVerification.LibsignalPublicApi.MessageEncrypt.StoredStateVPlaced
    (retagSessionStore (A' := A.atState lim st s) kit) st0
    (retagIdentityStore (A' := A.atState lim st s) ikit) ist0 Scope C ctl parse S encRecord
    x r sess otr taken k m otr' c R s0 s

abbrev StoredStateVBudget := @StoredStateVPlaced

/-! ## 4. `PhaseCreditSpec` Bounds and Non-Vacuity Witnesses -/

def witnessRustAlloc : RustAlloc := ⟨.emp, fun _ _ _ => .emp⟩
def witnessKit : SessionStoreSpec witnessRustAlloc 0#64 := hookSessionStoreSpec witnessRustAlloc 0#64
def witnessKitEnv : SessionStoreBudgetEnv witnessKit :=
  ⟨fun _ _ evs => evs = rustAllocEvents 16 1, fun _ _ _ evs => evs = rustAllocEvents 16 1⟩
def witnessIkit : IdentityStoreSpec witnessRustAlloc 0#64 := hookIdentityStoreSpec witnessRustAlloc 0#64
def witnessIkitEnv : IdentityStoreBudgetEnv witnessIkit :=
  ⟨fun _ _ _ _ evs => evs = rustAllocEvents 16 1, fun _ _ _ evs => evs = rustAllocEvents 16 1⟩
def witnessPendingPreKey : PendingPreKey := ⟨some 2#32, 3#32, witnessPublicKey, 0#64⟩
def witnessEncSession : Session (List (BitVec 8)) :=
  { state := ⟨4#32, witnessIdentityKey, some witnessIdentityKey, 0#256, 0#32,
      some ⟨witnessKeyPair, ⟨0#256, 0#32⟩⟩, [], true, [1#8]⟩
    pendingPreKey := some witnessPendingPreKey, pendingKyberPreKey := some ⟨4#32, [0x44#8]⟩
    localRegistrationId := 1#32, remoteRegistrationId := 2#32, aliceBaseKey := [0x45#8] }
def witnessEncRecord : SessionRecord (List (BitVec 8)) := ⟨some witnessEncSession⟩
def witnessWithStoresGhost : WithStoresEncGhost :=
  ⟨⟨0#64, 0#64, [0x41#8], 0#64, witnessAddrGhost, 0#64, witnessAddrGhost,
    SystemTime.unixEpoch, 0#64, [0x42#8]⟩, 0#64, 0#64⟩

private theorem encode_protoMsg_small_length_le (parse : UuidParser) (x : SignalMessageNewGhost) :
    (encode (x.protoMsg parse)).length ≤ 117 + x.ciphertext.length + x.pqRatchet.length := by
  unfold encode
  have hf1 : encodeBytesField 1 (x.protoMsg parse).ratchetKey =
      [0x0a#8, 0x21#8] ++ x.senderRatchetKey.serialize := by
    simp [SignalMessageNewGhost.protoMsg, encodeBytesField, publicKey_serialize_length,
      encodeKey_1_ld, encodeVarint_33]
  have hf2 : encodeUint32Field 2 (x.protoMsg parse).counter =
      [0x10#8] ++ encodeVarint (x.counter.zeroExtend 64) := by
    simp [SignalMessageNewGhost.protoMsg, encodeUint32Field, encodeKey_2_varint]
  have hf3 : encodeUint32Field 3 (x.protoMsg parse).previousCounter =
      [0x18#8] ++ encodeVarint (x.previousCounter.zeroExtend 64) := by
    simp [SignalMessageNewGhost.protoMsg, encodeUint32Field, encodeKey_3_varint]
  have hf4 : encodeBytesField 4 (x.protoMsg parse).ciphertext =
      [0x22#8] ++ encodeVarint (BitVec.ofNat 64 x.ciphertext.length) ++ x.ciphertext := by
    simp [SignalMessageNewGhost.protoMsg, encodeBytesField, encodeKey_4_ld]
  rw [hf1, hf2, hf3, hf4]
  have hrk := publicKey_serialize_length x.senderRatchetKey
  have ⟨_, hv2⟩ := signalMessageNew_encodeVarint_length_bounds (x.counter.zeroExtend 64)
  have ⟨_, hv3⟩ := signalMessageNew_encodeVarint_length_bounds (x.previousCounter.zeroExtend 64)
  have ⟨_, hv4⟩ := signalMessageNew_encodeVarint_length_bounds (BitVec.ofNat 64 x.ciphertext.length)
  have hpq_len : (encodeBytesField 5 (x.protoMsg parse).pqRatchet).length ≤ 11 + x.pqRatchet.length := by
    by_cases hpq0 : x.pqRatchet = []
    · simp [SignalMessageNewGhost.protoMsg, hpq0, encodeBytesField]
    · have hemp : x.pqRatchet.isEmpty = false := List.isEmpty_eq_false_iff.mpr hpq0
      have ⟨_, hv5⟩ := signalMessageNew_encodeVarint_length_bounds (BitVec.ofNat 64 x.pqRatchet.length)
      have hf5 : encodeBytesField 5 (x.protoMsg parse).pqRatchet =
          [0x2a#8] ++ encodeVarint (BitVec.ofNat 64 x.pqRatchet.length) ++ x.pqRatchet := by
        simp [SignalMessageNewGhost.protoMsg, hemp, encodeBytesField, encodeKey_5_ld]
      rw [hf5]
      simp only [List.length_append, List.length_singleton]
      omega
  have had_len : (encodeBytesField 6 (x.protoMsg parse).addresses).length ≤ 38 := by
    cases had : x.addresses parse with
    | none => simp [SignalMessageNewGhost.protoMsg, had, encodeBytesField]
    | some ad =>
      have hlen : ad.length = 36 := by
        simp only [SignalMessageNewGhost.addresses] at had
        cases hx : x.loc with
        | none => simp [hx] at had
        | some l => simp only [hx, Option.bind_some] at had; exact serializeAddresses_length had
      simp [SignalMessageNewGhost.protoMsg, had, hlen, encodeBytesField, encodeKey_6_ld, encodeVarint_36]
  simp only [List.length_append, List.length_cons, List.length_nil, hrk]
  omega

private theorem boxAllocEnv_phaseCreditSpec {sz : Nat} (hsz : sz ≤ 32) :
    PhaseCreditSpec fineCostModel (BoxAllocEnv sz) 9603 8227 8227 32 :=
  (PhaseCreditSpec.or_of_imp (fun _ h => h)
    ((PhaseCreditSpec.nil fineCostModel).of_imp fun _ h => h.2)
    ((PhaseCreditSpec.rustAlloc_aff fineCostModel_modelHyps (req := sz) (al := 8) (by decide)).of_imp
      fun _ h => h.2)).mono (by omega) (by omega) (by omega) (by omega)

theorem fromCurEnv_phaseCreditSpec :
    PhaseCreditSpec fineCostModel
      (FromCurEnv witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
        witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
        (· = witnessEncRecord) witnessWithStoresGhost)
      320000 270000 270000 512 := by
  have hfr := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hp16 := PhaseCreditSpec.rustAlloc_aff fineCostModel_modelHyps (req := 16) (al := 1) (by decide)
  have hd32 := PhaseCreditSpec.rustDealloc fineCostModel_modelHyps.freeNonInc 32 8
  have hb32 := boxAllocEnv_phaseCreditSpec (sz := 32) (by decide)
  have hsc : PhaseCreditSpec fineCostModel (StringCloneEnv witnessWithStoresGhost.rem.name)
      9541 8196 8196 1 :=
    (PhaseCreditSpec.or_of_imp (fun _ h => h)
      ((PhaseCreditSpec.nil fineCostModel).of_imp fun _ h => h.2)
      ((PhaseCreditSpec.rustAlloc_aff fineCostModel_modelHyps
        (req := witnessWithStoresGhost.rem.name.bytes.length) (al := 1) (by decide)).of_imp
        fun _ h => h.2)).mono (by decide) (by decide) (by decide) (by decide)
  have hscFr := hsc.seq hfr
  have hcm (otr' : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8))) :
      PhaseCreditSpec fineCostModel
        (FromCmEnv witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
          witnessWithStoresGhost witnessEncSession otr' taken witnessIdentityKey)
        70000 60000 60000 32 := by
    have hap : PhaseCreditSpec fineCostModel
        (FromApplyEnv witnessKit witnessKitEnv () witnessWithStoresGhost witnessEncSession otr' taken)
        29000 25000 25000 32 :=
      ((otrApplyEnv_phaseCreditSpec fineCostModel_modelHyps).seq
        (hb32.seq (hp16.seq (hd32.seq hfr)))).mono (by decide) (by decide) (by decide) (by decide)
    have hsv : PhaseCreditSpec fineCostModel
        (FromSaveEnv witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
          witnessWithStoresGhost witnessEncSession otr' taken witnessIdentityKey)
        49000 42000 42000 32 :=
      ((hb32.seq (hp16.seq hd32)).seq (hfr.or hap)).mono (by decide) (by decide) (by decide) (by decide)
    exact ((hb32.seq (hp16.seq hd32)).seq (hfr.or (hscFr.or hsv))).mono
      (by decide) (by decide) (by decide) (by decide)
  let g0 := otrSignalMsgGhost witnessCrypto witnessOtr none [2#8]
    witnessWithStoresGhost.ptext (some witnessWithStoresGhost.loc) witnessWithStoresGhost.rem
  have hg0_ct : g0.ciphertext.length ≤ 16 := by decide
  have hg0_pq : g0.pqRatchet.length ≤ 1 := by decide
  have hg0_enc : (encode (g0.protoMsg witnessUuidParse)).length + 9 ≤ 160 := by
    have h := encode_protoMsg_small_length_le witnessUuidParse g0
    omega
  have henc : PhaseCreditSpec fineCostModel
      (OtrEncryptCoreEnv witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
        witnessOtr witnessWithStoresGhost.ptext (some witnessWithStoresGhost.loc)
        witnessWithStoresGhost.rem witnessWithStoresGhost.rest)
      118000 101000 101000 256 := by
    refine (otrEncryptCoreEnv_phaseCreditSpec_bounded fineCostModel_modelHyps
      witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
      witnessOtr witnessWithStoresGhost.ptext (some witnessWithStoresGhost.loc)
      witnessWithStoresGhost.rem witnessWithStoresGhost.rest 256
      hp16 (by decide) (fun st' pqrKey pqrMsg hS => ?_)).mono
      (by decide) (by decide) (by decide) (by decide)
    change some ([1#8], none, [2#8]) = some (st', pqrKey, pqrMsg) at hS
    injection hS with ht; injection ht with h1 h23; injection h23 with h2 h3
    subst h1 h2 h3
    change g0.ciphertext.length ≤ 256 ∧ g0.pqRatchet.length ≤ 256 ∧
      (encode (g0.protoMsg witnessUuidParse)).length + 9 ≤ 256
    exact ⟨by omega, by omega, by omega⟩
  have hprePost (taken : SessionState (List (BitVec 8))) :
      PhaseCreditSpec fineCostModel
        (PreKeyPostEncryptEnv witnessCrypto witnessSpqrModel witnessUuidParse
          witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
          witnessWithStoresGhost witnessEncSession witnessOtr taken witnessIdentityKey witnessPendingPreKey)
        130000 110000 110000 512 := by
    let res := Mut.exec (OutgoingTripleRatchet.encrypt witnessCrypto protoSignalCodec
      witnessSpqrModel.spqr witnessWithStoresGhost.ptext
      (serializeAddresses (serviceIdParse witnessUuidParse)
        witnessWithStoresGhost.loc witnessWithStoresGhost.rem)
      witnessWithStoresGhost.rest) witnessOtr
    have hpreBody : PhaseCreditSpec fineCostModel
        (fun evs' => match res.1 with
          | .error _ => False
          | .ok sm => SeqEnv (PreKeyMsgNewRawEnv (pendingKyberPayload witnessEncSession)
              sm.serialized.length (preKeyMsgFromItems witnessEncSession witnessPendingPreKey res.2 sm).serialized.length)
              (fun evs'' => FreeOnlyEvs evs'' ∨
                FromCmEnv witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
                  witnessWithStoresGhost witnessEncSession res.2 taken witnessIdentityKey evs'') evs')
        130000 110000 110000 512 := by
      cases hres : res.1 with
      | error _ =>
        exact ((PhaseCreditSpec.nil fineCostModel).of_imp fun _ h => False.elim h).mono
          (by decide) (by decide) (by decide) (by decide)
      | ok sm =>
        have hsm : sm.serialized.length ≤ 160 := by
          have hresEq : res =
              (match witnessOtr.senderChainKey.nextChainKey witnessCrypto.F with
               | .error e => (.error e, witnessOtr)
               | .ok next =>
                 (.ok (SignalMessage.new witnessCrypto.F protoSignalCodec witnessOtr.sessionVersion
                   ((witnessOtr.senderChainKey.messageKeys witnessCrypto.F).generateKeys witnessCrypto.F none).macKey
                   (serializeAddresses (serviceIdParse witnessUuidParse)
                     witnessWithStoresGhost.loc witnessWithStoresGhost.rem)
                   witnessOtr.senderRatchetKey.publicKey witnessOtr.senderChainKey.index
                   witnessOtr.previousCounter g0.ciphertext
                   witnessOtr.localIdentityKey witnessOtr.remoteIdentityKey [2#8]),
                  { witnessOtr with senderChainKey := next, pqrState := [1#8] })) := rfl
          have hres1 := congrArg Prod.fst hresEq
          rw [hres] at hres1
          cases hnk : witnessOtr.senderChainKey.nextChainKey witnessCrypto.F with
          | error e => rw [hnk] at hres1; cases hres1
          | ok next =>
            rw [hnk] at hres1; injection hres1 with hsmEq; subst hsmEq
            dsimp only [SignalMessage.new]
            rw [List.length_append, signalMessageNew_computeMac_length]
            have hser : (serializeContent protoSignalCodec witnessOtr.sessionVersion
                witnessOtr.senderRatchetKey.publicKey witnessOtr.senderChainKey.index
                witnessOtr.previousCounter g0.ciphertext [2#8]
                (serializeAddresses (serviceIdParse witnessUuidParse)
                  witnessWithStoresGhost.loc witnessWithStoresGhost.rem)).length =
                1 + (encode (g0.protoMsg witnessUuidParse)).length := by
              simp [serializeContent, protoSignalCodec, SignalMessageNewGhost.protoMsg,
                SignalMessageNewGhost.addresses, otrSignalMsgGhost, g0]
              omega
            omega
        have hout : (preKeyMsgFromItems witnessEncSession witnessPendingPreKey res.2 sm).serialized.length ≤ 512 := by
          have h := preKeySignalMessage_new_small_length_le
            res.2.sessionVersion witnessEncSession.localRegistrationId
            witnessPendingPreKey.preKeyId witnessPendingPreKey.signedPreKeyId
            (pendingKyberPayload witnessEncSession) witnessPendingPreKey.baseKey
            res.2.localIdentityKey sm
            (by decide) (by rintro _ ⟨⟩; decide) (by decide) (by rintro _ ⟨⟩; decide)
          have hky1 : kyberPayloadLen (pendingKyberPayload witnessEncSession) = 1 := rfl
          change (PreKeySignalMessage.new res.2.sessionVersion witnessEncSession.localRegistrationId
            witnessPendingPreKey.preKeyId witnessPendingPreKey.signedPreKeyId
            (pendingKyberPayload witnessEncSession) witnessPendingPreKey.baseKey
            res.2.localIdentityKey sm).serialized.length ≤ 512
          omega
        have hmono : ∀ sL oL : Nat, sL ≤ 160 → oL ≤ 512 →
            (2 * 1 + 2 * sL + 2 * oL + 47827) + 70000 ≤ 130000 ∧
            (1 + sL + oL + 41041) + 60000 ≤ 110000 ∧
            max (1 + sL + oL + 41041) (1 + sL + oL + 41041 + 60000) ≤ 110000 ∧
            max (max (max 1 33) (max sL oL)) 32 ≤ 512 := by omega
        obtain ⟨hm1, hm2, hm3, hm4⟩ := hmono sm.serialized.length
          (preKeyMsgFromItems witnessEncSession witnessPendingPreKey res.2 sm).serialized.length hsm hout
        exact ((preKeyMsgNewRawEnv_phaseCreditSpec fineCostModel_modelHyps
          (pendingKyberPayload witnessEncSession) sm.serialized.length
          (preKeyMsgFromItems witnessEncSession witnessPendingPreKey res.2 sm).serialized.length).seq
          (hfr.or (hcm res.2 taken))).mono hm1 hm2 hm3 hm4
    unfold PreKeyPostEncryptEnv
    exact (hfr.or hpreBody).mono (by decide) (by decide) (by decide) (by decide)
  have hky := kyberOptEnv_phaseCreditSpec fineCostModel_modelHyps
    (witnessEncSession.pendingKyberPreKey.map (·.ciphertext))
  let htaken := { witnessEncSession.state with pqRatchetState := ([] : List (BitVec 8)) }
  have hex : PhaseCreditSpec fineCostModel
      (fun evs' => ∃ r sess otr taken,
        witnessKit.ScopeAt (· = witnessEncRecord) () witnessWithStoresGhost.rem.val r ∧
        r.currentSession = some sess ∧
        execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
        FromOtrEnv witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
          witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
          witnessWithStoresGhost sess otr taken evs')
      320000 270000 270000 512 := by
    refine ((hfr.or (hscFr.or (hky.seq (henc.seq (hprePost htaken))))).of_imp ?_).mono
      (by decide) (by decide) (by decide) (by decide)
    rintro evs' ⟨r, sess, otr, taken, ⟨rfl, -⟩, hcur, hexec, hotr⟩
    injection hcur with hcur'; subst hcur'
    have hexec0 : execOk OutgoingTripleRatchet.fromSessionState witnessEncSession.state =
        .ok (witnessOtr, htaken) := rfl
    rw [hexec0] at hexec; injection hexec with hp; injection hp with ho ht; subst ho ht
    rcases hotr with hfree | ⟨k, hk, hkey⟩
    · exact Or.inl hfree
    · injection hk with hk'; subst hk'
      rcases hkey with ⟨hnone, _⟩ | ⟨items, hsome, hbody⟩
      · cases hnone
      · injection hsome with hi; subst hi; exact Or.inr hbody
  exact (hfr.seq (hfr.or hex)).mono (by decide) (by decide) (by decide) (by decide)

/-- Non-vacuity `FitsEnv` witness for `WithStoresEncEnv` exercising all allocating paths. -/
theorem withStoresEncEnv_fitsEnv_witness :
    FitsEnv fineCostModel
      { staticCount := 16, staticBytes := 16 * 1024 * 1024,
        physCap := 2 ^ 30, enforced := true }
      fineCostModel.init
      (WithStoresEncEnv witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
        (· = witnessEncRecord) witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
        witnessWithStoresGhost) := by
  have hfr := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hp16 := PhaseCreditSpec.rustAlloc_aff fineCostModel_modelHyps (req := 16) (al := 1) (by decide)
  have hd24 := PhaseCreditSpec.rustDealloc fineCostModel_modelHyps.freeNonInc 24 8
  have hload := (boxAllocEnv_phaseCreditSpec (sz := 24) (by decide)).seq (hp16.seq hd24)
  have hsc : PhaseCreditSpec fineCostModel (StringCloneEnv witnessWithStoresGhost.rem.name)
      9541 8196 8196 1 :=
    (PhaseCreditSpec.or_of_imp (fun _ h => h)
      ((PhaseCreditSpec.nil fineCostModel).of_imp fun _ h => h.2)
      ((PhaseCreditSpec.rustAlloc_aff fineCostModel_modelHyps
        (req := witnessWithStoresGhost.rem.name.bytes.length) (al := 1) (by decide)).of_imp
        fun _ h => h.2)).mono (by decide) (by decide) (by decide) (by decide)
  have hSpec : PhaseCreditSpec fineCostModel
      (WithStoresEncEnv witnessKit witnessKitEnv () witnessIkit witnessIkitEnv ()
        (· = witnessEncRecord) witnessCrypto witnessSpqrModel witnessSendEnv witnessUuidParse
        witnessWithStoresGhost)
      340000 287000 287000 512 :=
    (hload.seq (hfr.or ((hsc.seq hfr).or fromCurEnv_phaseCreditSpec))).mono
      (by decide) (by decide) (by decide) (by decide)
  refine fitsEnv_fineCostModel_of_phaseCredit hSpec (by decide) rfl ?_ ?_
  · unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum pageAlignUp PAGE_SIZE
    decide
  · unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum fineDynIvsOfCum
      fineMaxGroupsOfCum pageAlignUp MMAP_MIN_ADDR PAGE_SIZE
    decide

end LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PlacedDefsBudgetAux
