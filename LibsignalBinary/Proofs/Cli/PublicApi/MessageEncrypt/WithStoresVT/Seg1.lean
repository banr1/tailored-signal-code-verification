/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tails
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.ExtDefs
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromFetch
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegIdentity
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegIdentityFetch
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommon
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustFrame
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustSteps
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustTrap
import ProofLib.RegChain

/-!
# CLI MessageEncrypt `WithStoresVT` (Part 1): `EncEnvT_trap`, `withStoresEncSpecVT_trap`, and
segments `SegIdentity`, `SegFrom`, `SegTrust`, `SegSave` on `trTrapProgAt`
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (SessionOnlyKitOkSE SessionOnlyVtablesOk)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreKitOkIE)
open CryptoVerification.LibsignalSpqrV1 (TokenInit)
open CryptoVerification.Cli.LibsignalPublicApi (encryptWithStoresName)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-- `OTR::encrypt` on `trTrapProgAt` meets `Cli.LibsignalSpqrV1.otrEncryptSpecT`. -/
def OtrEncryptOkT_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  subroutine_ok (trTrapProgAt img.base C abs)
    ((trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
    (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl parse S img)

/-- `OtrEncryptOkT_trap` from an `entryOf`-addressed `subroutine_ok` on `trTrapProgAt`. -/
theorem otrEncryptOkT_of_run_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (h : subroutine_ok (trTrapProgAt img.base C abs)
      (entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse S img)) :
    OtrEncryptOkT_trap img C A ctl uuidTryParse S abs := by
  unfold OtrEncryptOkT_trap
  rwa [entryOf_eq_trTrapProgAt C abs himg] at h

/-- `EncCallees_trap` with `OTR::encrypt` specialized to `OtrEncryptOkT_trap`. -/
structure EncCalleesT_trap (img : Obj.Image) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) :
    Prop where
  otrFrom : OutgoingRatchet.OtrFromExtOk img A (trTrapExterns C abs)
  otrApply : OutgoingRatchet.OtrApplyExtOk img A (trTrapExterns C abs)
  remoteIk : OutgoingRatchet.RemoteIdentityKeyExtOk img A (trTrapExterns C abs)
  otrEnc : OtrEncryptOkT_trap img C A ctl parse S abs
  unack : UnackItemsOk_trap img C A abs
  kyber : KyberMapOk_trap img C A abs
  psmNew : PreKeyMsgNewOk_trap img C A abs
  cmDrop : CmDropOk_trap img C A abs
  dropSs : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt
    img.base A (trTrapExterns C abs)

/-- `EncEnv_trap` at `Q := (·.length < 2^32)` with `callees : EncCalleesT_trap`. -/
structure EncEnvT_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (_ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) : Prop where
  loads : Obj.Loads libsignalSessionImage img
  hooks : CliEncHooks C A S (trTrapExterns C abs)
  kitOk : SessionOnlyKitOkSE kit Scope encRecord (trTrapExterns C abs)
  ikitOk : IdentityStoreKitOkIE img ikit (trTrapExterns C abs)
  callees : EncCalleesT_trap img C A ctl parse S abs
  vtables : SessionOnlyVtablesOk img kit
  idVtables : IdentityVtablesOk img ikit
  scopeIn : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r
  scopeQ : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → r.currentSession = some s → s.state.pqRatchetState.length < 2 ^ 32
  recOk : ∀ {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))},
    kit.addrOk x.rem.val →
    StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S parse x r sess otr taken k m otr' →
    kit.RecOk (storedRecord sess otr' taken)

/-- CLI `withStoresEncSpecV` with `64 ≤ x.rest.length` in `pre` and `TokenInit img` framed. -/
def withStoresEncSpecVT_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) : Spec WithStoresEncGhost :=
  { CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
      kit st0 ikit ist0 C ctl uuidParse S encRecord with
    pre := fun x s =>
      ⌜64 ≤ x.rest.length⌝ ∗ TokenInit img ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
          kit st0 ikit ist0 C ctl uuidParse S encRecord).pre x s
    post := fun x s0 sf =>
      TokenInit img ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
          kit st0 ikit ist0 C ctl uuidParse S encRecord).post x s0 sf }

theorem h45_otrEncryptOkQ_false_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {abs : String → Option (State → State)} :
    OtrEncryptOkQ_trap (fun _ => False) img C A ctl parse S abs := by
  refine subroutine_ok_outcome_intro fun x R s0 _ _ hpre _ => ?_
  change s0.mem ⊨ (⌜False⌝ ∗
    (CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec C A ctl parse S img).pre x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact False.elim hpre.1

@[reducible] def h45_kitF {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) :
    SessionStoreSpec A b :=
  { kit with addrOk := fun _ => False }

theorem h45_storeFinal_kitF {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (h45_kitF kit).storeFinal st0 ans calls = kit.storeFinal st0 ans calls := by
  induction calls generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [SessionStoreSpec.storeFinal, h45_kitF, ih]

theorem h45_callsRel_kitF {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (h45_kitF kit).callsRel st0 ans calls = kit.callsRel st0 ans calls := by
  induction calls generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [SessionStoreSpec.callsRel, h45_kitF, ih]

theorem h45_traceOfWith_kitF {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    ikit.traceOfWith (h45_kitF kit) encRecord ans calls = ikit.traceOfWith kit encRecord ans calls :=
  rfl

theorem h45_subroutineOutcome_kitF {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 sf : State) :
    SubroutineOutcome
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
        (h45_kitF kit) st0 ikit ist0 C ctl parse S encRecord) x R0 s0 sf =
    SubroutineOutcome
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
        kit st0 ikit ist0 C ctl parse S encRecord) x R0 s0 sf := by
  have hpost :
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
        (h45_kitF kit) st0 ikit ist0 C ctl parse S encRecord).post =
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
        kit st0 ikit ist0 C ctl parse S encRecord).post := by
    simp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV,
      Spec.inImage, withStoresEncStackV, h45_kitF,
      h45_storeFinal_kitF, h45_callsRel_kitF, h45_traceOfWith_kitF]
  unfold SubroutineOutcome
  rw [hpost]
  rfl

theorem h45_segExit_kitF_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State)) (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (next : State → Prop) :
    SegExit_trap (h45_kitF kit) st0 ikit ist0 C ctl parse S encRecord abs x R0 s0 s next =
      SegExit_trap kit st0 ikit ist0 C ctl parse S encRecord abs x R0 s0 s next := by
  simp only [SegExit_trap, h45_subroutineOutcome_kitF]

theorem h45_tailModel_kitF {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (res : Except (ApiError AddrVal Unit) CiphertextMessage) (s0 s : State) :
    Tails.TailModel (h45_kitF kit) st0 ikit ist0 C S parse encRecord x ans res s0 s =
      Tails.TailModel kit st0 ikit ist0 C S parse encRecord x ans res s0 s := by
  simp only [Tails.TailModel, h45_kitF, h45_callsRel_kitF, h45_traceOfWith_kitF]

theorem h45_encTailV_kitF {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (x : WithStoresEncGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (pc : BitVec 64)
    (regs : BitVec 64 → State → Prop) (slots : BitVec 64 → SepProp) (R0 : SepProp) (s0 s : State) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.EncTailV
      (h45_kitF kit) st0 ikit ist0 C ctl parse S x ans pc regs slots R0 s0 s =
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.EncTailV
      kit st0 ikit ist0 C ctl parse S x ans pc regs slots R0 s0 s := by
  simp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.EncTailV,
    encStoreExtra, encSubStackV, h45_kitF, h45_storeFinal_kitF]

theorem h45_envF {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs) :
    EncEnv_trap (h45_kitF kit) st0 ikit ist0 (fun _ => False) (fun _ => False)
      C ctl uuidTryParse S encRecord abs where
  loads := hEnv.loads
  hooks := hEnv.hooks
  kitOk := {
    loadShim := hEnv.kitOk.loadShim
    loadPoll := by
      refine subroutine_ok_outcome_intro fun ⟨x, self, st⟩ R s0 _ _ hpre _ => ?_
      dsimp only [kitLoadPollSpecSE, withEnvPre] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      replace hpre := hpre.2
      have hpre' : s0.mem ⊨ ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab ∧
          s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧ False⌝ ∗
          (kit.loadBoxAt x.fut self x.addrA 0#8 ∗ kit.storeAt self st ∗ memRegion x.out 368 ∗
            protocolAddressAt A x.addr x.addrA ∗ A.pool ∗ stackAt s0.sp kit.loadPollStack ∗ R) := by
        simpa only [kitLoadPollSpecS, h45_kitF, sepConj_assoc] using hpre
      rw [satisfies_pure_sepConj] at hpre'
      exact False.elim hpre'.1.2.2.2.2
    loadFutDrop := hEnv.kitOk.loadFutDrop
    storeShim := hEnv.kitOk.storeShim
    storePoll := by
      refine subroutine_ok_outcome_intro fun ⟨x, self, st⟩ R s0 _ _ hpre _ => ?_
      dsimp only [Spec.inImage, kitStorePollSpecE, withEnvPre] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      replace hpre := hpre.2
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      replace hpre := hpre.2
      have hpre' : s0.mem ⊨ ⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
          kit.RecOk x.call.record ∧ False⌝ ∗
          (kit.storeBoxAt x.fut self x.call.addrA x.call.recA 0#8 ∗
            kit.storeAt self st ∗ memRegion x.out 48 ∗
            protocolAddressAt A x.call.addr x.call.addrA ∗
            sessionRecordAt A x.call.recA x.call.g x.call.record ∗
            A.pool ∗ stackAt s0.sp kit.storePollStack ∗ R) := by
        simpa only [kitStorePollSpec, h45_kitF, sepConj_assoc] using hpre
      rw [satisfies_pure_sepConj] at hpre'
      exact False.elim hpre'.1.2.2.2
    storeFutDrop := hEnv.kitOk.storeFutDrop
  }
  ikitOk := hEnv.ikitOk
  callees := {
    otrFrom := hEnv.callees.otrFrom
    otrApply := hEnv.callees.otrApply
    remoteIk := hEnv.callees.remoteIk
    otrEnc := h45_otrEncryptOkQ_false_trap
    unack := hEnv.callees.unack
    kyber := hEnv.callees.kyber
    psmNew := hEnv.callees.psmNew
    cmDrop := hEnv.callees.cmDrop
    dropSs := hEnv.callees.dropSs
  }
  vtables := {
    loadSlot := hEnv.vtables.loadSlot
    storeSlot := hEnv.vtables.storeSlot
    loadFutDrop := hEnv.vtables.loadFutDrop
    loadFutSize := hEnv.vtables.loadFutSize
    loadFutAlign := hEnv.vtables.loadFutAlign
    loadFutPoll := hEnv.vtables.loadFutPoll
    storeFutDrop := hEnv.vtables.storeFutDrop
    storeFutSize := hEnv.vtables.storeFutSize
    storeFutAlign := hEnv.vtables.storeFutAlign
    storeFutPoll := hEnv.vtables.storeFutPoll
  }
  idVtables := hEnv.idVtables
  scopeIn := fun _ h => False.elim h.1
  scopeQ := fun _ _ h _ => False.elim h.1
  recOk := fun haddr _ => False.elim haddr

theorem h45_subroutineOutcome_vt_of_v {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {uuidParse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome
      (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV
        kit st0 ikit ist0 C ctl uuidParse S encRecord)
      x (TokenInit img ∗ R) s0 sf) :
    SubroutineOutcome (withStoresEncSpecVT_trap kit st0 ikit ist0 C ctl uuidParse S encRecord)
      x R s0 sf := by
  rcases h with ⟨h1, hcs, hpost⟩ | ⟨hpan, honp⟩ | ⟨code, hexit, honex⟩ | ⟨_hoom, honoom⟩
  · refine Or.inl ⟨h1, hcs, ?_⟩
    dsimp only [withStoresEncSpecVT_trap]
    refine Satisfies.mono ?_ hpost
    exact Entails.of_eq (by ac_rfl)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withStoresEncSpecVT_trap,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV, Spec.inImage] at honp ⊢
    refine Satisfies.mono ?_ honp
    rw [← sepConj_assoc, sepConj_assoc ⌜_⌝ anyHeap (TokenInit img)]
    refine sepConj_mono_left (sepConj_mono_right ?_)
    exact entails_anyHeap (anyHeap ∗ TokenInit img)
  · refine Or.inr (Or.inr (Or.inl ⟨code, hexit, ?_⟩))
    change sf.mem ⊨ ⌜False⌝ ∗ (TokenInit img ∗ R) at honex
    rw [satisfies_pure_sepConj] at honex
    exact False.elim honex.1
  · change sf.mem ⊨ ⌜False⌝ ∗ (TokenInit img ∗ R) at honoom
    rw [satisfies_pure_sepConj] at honoom
    exact False.elim honoom.1

def h45_ScopeNone (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (r : SessionRecord (List (BitVec 8))) : Prop :=
  Scope r ∧ r.currentSession = none

theorem h45_envNone {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs) :
    EncEnv_trap (h45_kitF kit) st0 ikit ist0 (h45_ScopeNone Scope) (fun _ => False)
      C ctl uuidTryParse S encRecord abs :=
  { h45_envF hEnv with
    kitOk := {
      (h45_envF hEnv).kitOk with
      loadPoll := by
        refine subroutine_ok_outcome_intro fun ⟨x, self, st⟩ R s0 _ _ hpre _ => ?_
        dsimp only [kitLoadPollSpecSE, withEnvPre] at hpre
        rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
        replace hpre := hpre.2
        have hpre' : s0.mem ⊨ ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab ∧
            s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧ False⌝ ∗
            (kit.loadBoxAt x.fut self x.addrA 0#8 ∗ kit.storeAt self st ∗ memRegion x.out 368 ∗
              protocolAddressAt A x.addr x.addrA ∗ A.pool ∗ stackAt s0.sp kit.loadPollStack ∗ R) := by
          simpa only [kitLoadPollSpecS, h45_kitF, sepConj_assoc] using hpre
        rw [satisfies_pure_sepConj] at hpre'
        exact False.elim hpre'.1.2.2.2.2
    }
    scopeIn := fun r h => hEnv.scopeIn r ⟨h.1.1, h.2⟩
    scopeQ := fun _ _ h hs => by rw [h.1.2] at hs; cases hs
    recOk := fun haddr _ => False.elim haddr }

@[reducible] def h45_kitL {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) :
    SessionStoreSpec A b :=
  { kit with addrOk := fun _ => False, loadRel := fun _ _ _ => False }

theorem h45_envL {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs) :
    EncEnv_trap (h45_kitL kit) st0 ikit ist0 Scope (fun _ => False)
      C ctl uuidTryParse S encRecord abs where
  loads := hEnv.loads
  hooks := hEnv.hooks
  kitOk := {
    loadShim := hEnv.kitOk.loadShim
    loadPoll := by
      refine subroutine_ok_outcome_intro fun ⟨x, self, st⟩ R s0 _ _ hpre _ => ?_
      dsimp only [kitLoadPollSpecSE, withEnvPre] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      replace hpre := hpre.2
      have hpre' : s0.mem ⊨ ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab ∧
          s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧ False⌝ ∗
          (kit.loadBoxAt x.fut self x.addrA 0#8 ∗ kit.storeAt self st ∗ memRegion x.out 368 ∗
            protocolAddressAt A x.addr x.addrA ∗ A.pool ∗ stackAt s0.sp kit.loadPollStack ∗ R) := by
        simpa only [kitLoadPollSpecS, h45_kitL, sepConj_assoc] using hpre
      rw [satisfies_pure_sepConj] at hpre'
      exact False.elim hpre'.1.2.2.2.2
    loadFutDrop := hEnv.kitOk.loadFutDrop
    storeShim := hEnv.kitOk.storeShim
    storePoll := by
      refine subroutine_ok_outcome_intro fun ⟨x, self, st⟩ R s0 _ _ hpre _ => ?_
      dsimp only [Spec.inImage, kitStorePollSpecE, withEnvPre] at hpre
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      replace hpre := hpre.2
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
      replace hpre := hpre.2
      have hpre' : s0.mem ⊨ ⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
          kit.RecOk x.call.record ∧ False⌝ ∗
          (kit.storeBoxAt x.fut self x.call.addrA x.call.recA 0#8 ∗
            kit.storeAt self st ∗ memRegion x.out 48 ∗
            protocolAddressAt A x.call.addr x.call.addrA ∗
            sessionRecordAt A x.call.recA x.call.g x.call.record ∗
            A.pool ∗ stackAt s0.sp kit.storePollStack ∗ R) := by
        simpa only [kitStorePollSpec, h45_kitL, sepConj_assoc] using hpre
      rw [satisfies_pure_sepConj] at hpre'
      exact False.elim hpre'.1.2.2.2
    storeFutDrop := hEnv.kitOk.storeFutDrop
  }
  ikitOk := hEnv.ikitOk
  callees := (h45_envF hEnv).callees
  vtables := {
    loadSlot := hEnv.vtables.loadSlot
    storeSlot := hEnv.vtables.storeSlot
    loadFutDrop := hEnv.vtables.loadFutDrop
    loadFutSize := hEnv.vtables.loadFutSize
    loadFutAlign := hEnv.vtables.loadFutAlign
    loadFutPoll := hEnv.vtables.loadFutPoll
    storeFutDrop := hEnv.vtables.storeFutDrop
    storeFutSize := hEnv.vtables.storeFutSize
    storeFutAlign := hEnv.vtables.storeFutAlign
    storeFutPoll := hEnv.vtables.storeFutPoll
  }
  idVtables := hEnv.idVtables
  scopeIn := fun _ h => False.elim h.2
  scopeQ := fun _ _ h _ => False.elim h.2
  recOk := fun haddr _ => False.elim haddr

section SegIdentity
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity
  (SegExit.next_trap SegExit.of_sepWP_trap SegExit.call_trap
   segIdentity_step_pre_trap remoteIk_addr_eq_trap segIdentity_step_ok_trap)
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

theorem h45_segIdentity_okVT_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (R0 : SepProp)
    (s0 s : State)
    (hotrState : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrStateV
      kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr R0 s0 s) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => ∃ k,
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KeyStateV
          kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R0 s0 s') := by
  let R := encStoreExtra kit st0 ikit ist0 x s0 ∗ R0
  rcases hotrState with ⟨hcur, hsc, hfrom, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, ⟨hx0, hx8, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have hsp_x29 : s0.sp - 0x60#64 = sp + 0xb80#64 := by
    rw [← hsp0]; bv_omega
  have hentry : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img =
      (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName :=
    entryOf_eq_trTrapProgAt C abs hEnv.loads encryptWithStoresName
  have hs_pc' : s.pc = (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName + 712#64 := by
    simpa only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrPC, hentry] using hs_pc
  have htaken_rem : taken.remoteIdentity = some otr.remoteIdentityKey :=
    taken_remoteIdentity_eq_some hfrom
  obtain ⟨g, G, hgcur, hrem, hm_unp⟩ :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.otrState_mem_unpack
      A ctl img x sess otr taken pqCap pqPtr sp R s0 hsp0 hm
  refine SegExit.of_sepWP_trap hm_unp
    (segIdentity_step_pre_trap hs_pc' hrun hsp) ?_
  intro s1 Pm1 hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x0, hs1_x8, hs1_x19, hs1_x20, hs1_x22, hs1_x23, hs1_x24, hs1_x25,
      hs1_x26, hs1_x27, hs1_x28, hs1_x29, hs1_lr, hs1_vregs, hPm1⟩
  have ⟨hfl1, hsym1⟩ := callInv_steps hfl hsym hsteps01 hL0
  have hs1_al : s1.spAligned = true := spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hs1_pc' : s1.pc = (trTrapProgAt img.base C abs).fnAddr remoteIdentityKeyName := by
    rw [hs1_pc, remoteIk_addr_eq_trap]
  have hm1_pre :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.remoteIk_pre_frame
      A ctl img x g G sess taken pqCap pqPtr otr sp R Pm1 s0 s1
      hrem hs1_sp (hs1_x0.trans hx0) (hs1_x8.trans hx8) hPm1 hm1
  refine SegExit.call_trap hEnv.callees.remoteIk
    ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩
    hs1_pc' hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (remoteIdentityKeySpec A img).onExit
            ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩ code s1 _ = ⌜False⌝
            from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun _ _ _ hpan => by
      rw [show (remoteIdentityKeySpec A img).onPanic
            ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩ s1 _ = ⌜False⌝
            from rfl,
          sepConj_assoc, satisfies_pure_sepConj] at hpan
      exact hpan.1.elim)
    ?_
  intro s2 hL1 hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have ⟨hfl2, hsym2⟩ := callInv_steps hfl1 hsym1 hsteps12 hL1
  have hs2_sp' : s2.sp = sp := hs2_sp.trans hs1_sp
  have hs2_al : s2.spAligned = true := spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x23 : s2.readReg64 .x23 = sp + 0x58#64 := by reg_chain
  have hs2_x24 : s2.readReg64 .x24 = sp + 0x58#64 := by reg_chain
  have hs2_x25 : s2.readReg64 .x25 = sp + 0x580#64 := by reg_chain
  have hs2_x29 : s2.readReg64 .x29 = sp + 0xb80#64 := by reg_chain
  obtain ⟨hs2_tr, hm2⟩ :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.remoteIk_post_repack
      A ctl img x g G sess taken pqCap pqPtr otr sp R s0 s1 s2 hgcur htaken_rem hsp0 hs1_sp hpost2
  obtain ⟨c0, d0, u868, c4, c30, d4, d30, u86c, ub08, c6, c14, c22, d6, d14, d22, ub00,
    hpack, hm2_unp⟩ :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.remoteIk_ok_unpack
      A ctl img x sess taken pqCap pqPtr otr sp R s0 s2 hm2
  refine SegExit.of_sepWP_trap hm2_unp
    (segIdentity_step_ok_trap hs2_pc hs2_run hs2_sp' hs2_al hs2_x23 hs2_x24 hs2_x25 hs2_x29) ?_
  intro s3 Pm3 hL2 hsteps23 hs3_pc hs3_run hm3
    ⟨hs3_sp, hs3_tr, hs3_x0, hs3_x8, hs3_x19, hs3_x20, hs3_x22, hs3_x23, hs3_x25, hs3_x26,
      hs3_x27, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
  have ⟨hfl3, hsym3⟩ := callInv_steps hfl2 hsym2 hsteps23 hL2
  have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
  have hm3_ok :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity.remoteIk_ok_pack
      A ctl img x sess taken pqCap pqPtr otr c0 c4 c30 c6 c14 c22 sp R Pm3 s0 s3 hpack hPm3 hm3
  refine SegExit.next_trap ⟨otr.remoteIdentityKey, hcur, hsc, hfrom, htaken_rem, ?_⟩
  refine ⟨?_, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hfl3, hsym3,
    by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩, by reg_chain,
    ⟨hs3_x0, hs3_x8, by reg_chain, by reg_chain, hs3_x23, hs3_x25,
      by reg_chain, by reg_chain, by reg_chain⟩,
    hpt, hrest, hloc, hnow, hstk, hm3_ok⟩
  rw [hs3_pc, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.keyPC, hentry]

end SegIdentity

section SegFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
  (SegExit.next_trap SegExit.of_false_trap SegExit.of_sepWP_trap SegExit.call_trap
   segFrom_step_pre_trap otrFrom_addr_eq_trap segFrom_step_err_trap segFrom_step_ok_trap)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails (tailFromSessionStateErr_ok_trap)
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

private theorem h45_fromSessionState_error_ne_invalidState
    {st : SessionState (List (BitVec 8))} {e : SignalProtocolError}
    (h : (Mut.exec OutgoingTripleRatchet.fromSessionState st).1 = .error e) :
    e ≠ .invalidState ∧ e ≠ .panic := by
  unfold Mut.exec OutgoingTripleRatchet.fromSessionState SessionState.takePqRatchetState at h
  rcases hs : st.senderChain with _ | sc <;> rcases hr : st.remoteIdentity with _ | k <;>
    simp only [hs, hr, modifyGet, MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont, StateT.bind, pure, ExceptT.pure,
      StateT.pure, StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, liftM, monadLift,
      MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, Except.error.injEq] at h
  all_goals
    (try split_ifs at h) <;>
    (try simp only [ExceptT.bindCont, StateT.bind, StateT.pure, pure, bind, reduceCtorEq,
      Except.error.injEq] at h) <;>
    (subst h; decide)

private theorem h45_execOk_fromSessionState_of_error
    {st : SessionState (List (BitVec 8))} {e : SignalProtocolError}
    (h : (Mut.exec OutgoingTripleRatchet.fromSessionState st).1 = .error e) :
    execOk OutgoingTripleRatchet.fromSessionState st = .error e := by
  unfold execOk
  rcases hm : Mut.exec OutgoingTripleRatchet.fromSessionState st with ⟨res, st'⟩
  rw [hm] at h
  dsimp only at h ⊢
  subst h
  rfl

private theorem h45_execOk_fromSessionState_of_ok
    {st : SessionState (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    (h : (Mut.exec OutgoingTripleRatchet.fromSessionState st).1 = .ok otr) :
    execOk OutgoingTripleRatchet.fromSessionState st =
      .ok (otr, (Mut.exec OutgoingTripleRatchet.fromSessionState st).2) := by
  unfold execOk
  rcases hm : Mut.exec OutgoingTripleRatchet.fromSessionState st with ⟨res, st'⟩
  rw [hm] at h
  dsimp only at h ⊢
  subst h
  rfl

private theorem h45_model_of_fromSessionState_error
    {C : Crypto} {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {e : SignalProtocolError}
    (hcur : r.currentSession = some sess)
    (herr : (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 = .error e) :
    x.model C S uuidTryParse (okAnswers r .newOrUnchanged) =
      (.error (.protocol e), [.loadSession x.rem.val]) ∧
    x.draws S (okAnswers r .newOrUnchanged) = 0 := by
  have hex : execOk OutgoingTripleRatchet.fromSessionState sess.state = .error e :=
    h45_execOk_fromSessionState_of_error herr
  have hprot : (ApiError.ofProtocol e : ApiError AddrVal Unit) = .protocol e := by
    cases e <;> first | rfl | exact absurd rfl (h45_fromSessionState_error_ne_invalidState herr).2
  have hmod : x.model C S uuidTryParse (okAnswers r .newOrUnchanged) =
      (.error (ApiError.ofProtocol e), [.loadSession x.rem.val]) := by
    unfold EncryptGhost.model messageEncrypt Api.run storeCall liftProtocol okAnswers
    simp only [hcur, hex, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      ExceptT.run, StateT.run, bind, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift,
      StateT.bind, StateT.map, Functor.map, monadLift, MonadLift.monadLift,
      MonadLiftT.monadLift, pure, ExceptT.pure, StateT.pure, throw, throwThe,
      MonadExceptOf.throw, List.nil_append]
  refine ⟨by rw [hmod, hprot], ?_⟩
  unfold EncryptGhost.draws EncryptGhost.sendState loadedSession okAnswers
  simp only [hcur, hex]

theorem h45_segFrom_okVT_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (R0 : SepProp) (s0 s : State)
    (hcurState : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CurStateV
      kit st0 ikit ist0 Scope ctl encRecord x r g sess R0 s0 s) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => ∃ otr taken pqCap pqPtr,
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.OtrStateV
          kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr R0 s0 s') := by
  let R := encStoreExtra kit st0 ikit ist0 x s0 ∗ R0
  rcases hcurState with ⟨hcur, hsc, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, ⟨hx20, hx21, hx25, hx26, hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have hentry : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img =
      (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName :=
    entryOf_eq_trTrapProgAt C abs hEnv.loads encryptWithStoresName
  have hs_pc' : s.pc = (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName + 524#64 := by
    simpa only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.curPC, hentry] using hs_pc
  obtain ⟨G, u280, _, hpure, hm_unp⟩ :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.curState_mem_unpack
      A ctl img x r g sess sp R s0 hsp0 hcur hm
  refine SegExit.of_sepWP_trap hm_unp
    (segFrom_step_pre_trap hs_pc' hrun hsp hal hx20 hx21 hx25 hx26 hx28) ?_
  intro s1 Pm1 hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x0, hs1_x8, hs1_x19, hs1_x20, hs1_x21, hs1_x24, hs1_x25, hs1_x26,
      hs1_x27, hs1_x28, hs1_x29, hs1_lr, hs1_vregs, hPm1⟩
  have ⟨hfl1, hsym1⟩ := callInv_steps hfl hsym hsteps01 hL0
  have hs1_al : s1.spAligned = true := spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hs1_pc' : s1.pc = (trTrapProgAt img.base C abs).fnAddr otrFromName := by
    rw [hs1_pc, otrFrom_addr_eq_trap]
  have hm1_pre :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_pre_frame
      A ctl img x g G sess sp R Pm1 s0 s1 hfl1 hsym1 hs1_sp hs1_x0 hs1_x8 hPm1 hm1
  refine SegExit.call_trap hEnv.callees.otrFrom ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩
    hs1_pc' hs1_run hs1_al hs1_lr hm1_pre
    (fun sf _ _ _ hex => by
      change sf.mem ⊨ ⌜False⌝ ∗ _ at hex
      rw [satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost =>
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_panic_bridge
        kit st0 ikit ist0 C ctl S encRecord x r sess
        ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩ _ _ R0 s0 s1 sf rfl hcur (hs1_tr.trans htr) hpost)
    ?_
  intro s2 hL1 hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have ⟨hfl2, hsym2⟩ := callInv_steps hfl1 hsym1 hsteps12 hL1
  have hs2_sp' : s2.sp = sp := hs2_sp.trans hs1_sp
  have hs2_al : s2.spAligned = true := spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x20 : s2.readReg64 .x20 = sp + 0x58#64 := by reg_chain
  have hs2_x24 : s2.readReg64 .x24 = sp + 0x58#64 := by reg_chain
  have hs2_x25 : s2.readReg64 .x25 = sp + 0x580#64 := by reg_chain
  have hs2_x26 : s2.readReg64 .x26 = sp + 0x9d0#64 := by reg_chain
  have hs2_x27 : s2.readReg64 .x27 = sp + 0xc0#64 := by reg_chain
  have hs2_x28 : s2.readReg64 .x28 = sp + 0x4a0#64 := by reg_chain
  obtain ⟨G', _, hs2_tr, hm2⟩ :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_post_unpack
      A ctl img x g G sess ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩
      sp R s0 s1 s2 rfl hsp0 hs1_sp hpure hpost2
  have hs2_tr' : s2.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) :=
    hs2_tr.trans (hs1_tr.trans htr)
  rcases hres : (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 with p | otr
  · change s2.mem ⊨ otrResultAt A (sp + 0x580#64) G.pq
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 ∗ _ at hm2
    rw [hres] at hm2
    obtain ⟨w0, w1, w2, w3, w4, w5, H, hst, hm2_err⟩ :=
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_err_unpack
        A ctl img x { g with cur := some G' } G.pq sess
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 p sp R s0 s2 hres hm2
    refine SegExit.of_sepWP_trap hm2_err (segFrom_step_err_trap hs2_pc hs2_run hs2_sp' hs2_al) ?_
    intro s3 Pm3 hL2 hsteps23 hs3_pc hs3_run hm3
      ⟨hs3_sp, hs3_tr, hs3_x19, hs3_x21, hs3_x25, hs3_x26, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
    have ⟨hfl3, hsym3⟩ := callInv_steps hfl2 hsym2 hsteps23 hL2
    have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
    have ⟨hmod_res, hdraws0⟩ := h45_model_of_fromSessionState_error (C := C) (S := S)
      (x := x) hcur hres
    have hm3_tail :=
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_err_tail_mem
        A ctl img x { g with cur := some G' } sess
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 w0 w1 w2 w3 w4 w5 sp H R Pm3
        s0 s3 hPm3 hm3
    rw [← h45_segExit_kitF_trap]
    refine SegExit.of_false_trap (tailFromSessionStateErr_ok_trap (h45_envF hEnv) x R0 s0 s3
      (okAnswers r .newOrUnchanged)
      (.protocol p) w0 w1 w2 w3 w4 w5 H { g with cur := some G' }
      (takenRecord sess (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2)
      ?_ hst ?_)
    · refine ⟨⟨by rw [hmod_res], by rw [hmod_res]; exact ⟨hsc.2, trivial⟩, by rw [hmod_res]; trivial⟩, ?_⟩
      rw [hs3_tr, hs2_tr', hmod_res]
      dsimp only [okAnswers]
      rw [ikit.traceOfWith_load]
    · refine ⟨?_, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hfl3, hsym3,
        by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩,
        ⟨by reg_chain, by reg_chain, by reg_chain, by reg_chain⟩, hstk, ?_⟩
      · rw [hs3_pc, hentry]
      · rw [hdraws0, hmod_res]
        exact hm3_tail
  · change s2.mem ⊨ otrResultAt A (sp + 0x580#64) G.pq
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 ∗ _ at hm2
    rw [hres] at hm2
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18,
      w19, w20, w21, w22, w23, w24,
      d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18,
      d19, d20, d21, d22, d23, d24,
      u850, u858, u860, u950, u958, u960, H, hpq, hpack, hm2_ok⟩ :=
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_ok_unpack
        A ctl img x { g with cur := some G' } G.pq sess
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 otr sp R s0 s2 hm2
    refine SegExit.of_sepWP_trap hm2_ok
      (segFrom_step_ok_trap hs2_pc hs2_run hs2_sp' hs2_al hs2_x20 hs2_x24 hs2_x25 hs2_x26 hs2_x27
        hs2_x28 hpq) ?_
    intro s3 Pm3 hL2 hsteps23 hs3_pc hs3_run hm3
      ⟨hs3_sp, hs3_tr, hs3_x0, hs3_x8, hs3_x19, hs3_x20, hs3_x22, hs3_x23, hs3_x24, hs3_x25,
        hs3_x26, hs3_x27, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
    have ⟨hfl3, hsym3⟩ := callInv_steps hfl2 hsym2 hsteps23 hL2
    have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
    have hm3_ok :=
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.otrFrom_ok_pack
        A ctl img x { g with cur := some G' } G.pq sess
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 otr
        w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24
        sp H R Pm3 s0 s3 hpack hPm3 hm3
    refine SegExit.next_trap ⟨otr, (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2,
      G.pq.cap, G.pq.ptr, hcur, hsc, h45_execOk_fromSessionState_of_ok hres, ?_⟩
    refine ⟨?_, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hfl3, hsym3,
      by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩,
      hs3_tr.trans hs2_tr',
      ⟨hs3_x0, hs3_x8, hs3_x20, hs3_x22, hs3_x23, hs3_x24, hs3_x25, hs3_x26, hs3_x27, hs3_x28⟩,
      hpt, hrest, hloc, hnow, hstk, hm3_ok⟩
    rw [hs3_pc, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrPC, hentry]

end SegFrom

section SegTrust
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
  (SegExit.of_false_trap SegExit.of_sepWP_trap encEntry_eq_fnAddr_trap
   trust_to_bc4_trap trust_false_to_d40_trap step_bc4_err_trap step_bc4_ok_true_trap)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
  (tailStoreHookErr_ok_trap tailCmDrop_ok_trap)
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

theorem h45_segTrust_okVT_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R0 : SepProp)
    (s0 s : State)
    (haddr : ikit.addrOk x.rem.val)
    (hfs : EncFsCtx_trap kit ikit C abs s0 s)
    (hcm : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmStateV
      kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr' R0 s0 s) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SaveStateV
        kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr' R0 s0 s') := by
  let env := h45_envF hEnv
  let R : SepProp := kit.storeAt x.ssA st0 ∗ R0
  obtain ⟨h15, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, ⟨hx20, hx25, hx26, hx28⟩, hpt, hrest, hloc, hnow, hstk, hm⟩ := hcm
  set sp := s0.sp - 0xbe0#64
  set draws := S.draws otr.pqrState x.rest
  set F := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.trustPassive
    kit.ss_vt ikit.id_vt A img.base x sess taken otr' pqCap' pqPtr' m draws s0
  have hpref0 : s0.trace <+: s.trace := ⟨_, htr.symm⟩
  have hm_pre : s.mem ⊨
      (trustBaseActive ikit.id_vt A img s.sp x k ∗ encStoreExtra kit st0 ikit ist0 x s0) ∗
      ((memRegion (s.sp + 0x470#64) 16 ∗
        memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x970#64) 24 ∗
        memRegion (s.sp + 0x9d0#64) 24) ∗ F ∗ R0) := by
    have hm1 : s.mem ⊨
        (cmSlots A s.sp sess taken otr' pqCap' pqPtr' k m ∗ cmScratch s.sp ∗
          encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗ memRegion (s.sp + 0x46a#64) 0x716 ∗
          memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0) ∗
        (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0) := by
      rw [hsp]
      exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
    rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.seam_mem_split
      kit.ss_vt ikit.id_vt A ctl img x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp] at hm1
    dsimp only [F]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm1
  have hm_join := Satisfies.mono (sepConj_mono_left
    (trustBaseActive_join_extra kit st0 ikit ist0 x k s0 s.sp hsp)) hm_pre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_join
  obtain ⟨hbound, hm_join⟩ := hm_join
  have hm_split : s.mem ⊨ (trustVtablesAt ikit ∗
      trustActive img ikit ist0 s.sp (encSubStackV kit ikit) x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗
      memRegion (s.sp + 0x580#64) 48 ∗
      memRegion (s.sp + 0x970#64) 24 ∗
      memRegion (s.sp + 0x9d0#64) 24) ∗ (F ∗ R) := by
    have hm' := trustVtablesAt_intro env.idVtables hfl hm_join
    dsimp only [R]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm'
  have hx25' : s.readReg64 .x25 = s.sp + 0x580#64 := by rw [hsp]; exact hx25
  have hpc_a70 : s.pc = (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName + 0xa70#64 := by
    rw [hpc, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.cmPC, encEntry_eq_fnAddr_trap env]
  rw [← h45_segExit_kitF_trap]
  refine trust_to_bc4_trap env haddr
    (fun s' hst' htr' =>
      ((hfs.of_steps hst').envOk_at (htr'.trans htr) fun hq => by
        obtain ⟨⟨hl, -⟩, -⟩ := hq
        simp only [hl]).2)
    hbound hpc_a70 hrun hsp_al hx25' hpref0 hfl hsym hm_split ?_
  intro sm ans w0 w1 w2 w3 w4 w5 H hsteps_bc4 hpcm hrunm hspm hspm_al htrustRel htrm
    hx19m hx20m hx25m hx26m hx28m hx29m hvregsm hx27m hx21m hx23m hans hmm_act
  let R' : SepProp := encStoreExtra kit st0 ikit (ikit.trustUpdate ist0 x.rem.val k .sending ans) x s0 ∗ R0
  have hmm : sm.mem ⊨ (trustBaseActive ikit.id_vt A img s.sp x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗
      memRegion (s.sp + 0x580#64) 48 ∗
      (((s.sp + 0x970#64) ↦₆₄ w3) ∗
        ((s.sp + 0x978#64) ↦₆₄ w4) ∗
        ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
      memRegion (s.sp + 0x9d0#64) 24 ∗ H) ∗ (F ∗ R') := by
    have hmm1 : sm.mem ⊨
        (trustActive img ikit (ikit.trustUpdate ist0 x.rem.val k .sending ans) s.sp (encSubStackV kit ikit) x k ∗
          kit.storeAt x.ssA st0) ∗
        ((memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x970#64) ↦₆₄ w3) ∗
            ((s.sp + 0x978#64) ↦₆₄ w4) ∗
            ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
          memRegion (s.sp + 0x9d0#64) 24 ∗ H) ∗ F ∗ R0) := by
      dsimp only [R] at hmm_act
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm_act
    have hmm2 := Satisfies.mono (sepConj_mono_left
      (trustActive_split_extra kit st0 ikit (ikit.trustUpdate ist0 x.rem.val k .sending ans) x k s0 s.sp hsp hbound)) hmm1
    dsimp only [R']
    exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm2
  have ⟨hflm, hsymm⟩ := callInv_steps hfl hsym hsteps_bc4
  have hspm' : sm.sp = sp := hspm.trans hsp
  have htrm' : sm.trace = s0.trace ++
      (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++ ikit.trustEvs x.rem.val k .sending ans) := by
    rw [htrm, htr, List.append_assoc]
  have hpref_m : s0.trace <+: sm.trace := ⟨_, htrm'.symm⟩
  rcases ans with ⟨⟨⟩⟩ | (_ | _)
  · obtain ⟨rfl, hw1, rfl, rfl, hw4, hH⟩ := hans
    have hmm_emp : sm.mem ⊨ emp ∗
        (((trustBaseActive ikit.id_vt A img s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x970#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x978#64) ↦₆₄ w4) ∗
            ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
          memRegion (s.sp + 0x9d0#64) 24 ∗
          H) ∗ F) ∗ R') := by
      rw [emp_sepConj]
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm
    refine SegExit.of_sepWP_trap hmm_emp (step_bc4_err_trap hpcm hrunm hx27m) ?_
    rintro s_err _ _ hsteps_err hpc_err hrun_err hm_err
      ⟨rfl, hsp_err, htr_err, hx19_err, hx21_err, hx23_err, hx26_err, hx27_err, hx28_err, hx29_err, hvregs_err⟩
    rw [emp_sepConj] at hm_err
    have ⟨hfl_err, hsym_err⟩ := callInv_steps hflm hsymm hsteps_err
    have hm_ro' : s_err.mem ⊨
        ((trustBaseActive ikit.id_vt A img s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x970#64) ↦₆₄ 1#64) ∗
            ((s.sp + 0x978#64) ↦₆₄ w4) ∗
            ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
          memRegion (s.sp + 0x9d0#64) 24 ∗
          H) ∗ F) ∗ R' :=
      Eq.mp (congrArg (s_err.mem ⊨ ·) (by ac_rfl)) hm_err
    have htail_ent :=
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.seam_mem_to_tail
        kit.ss_vt ikit.id_vt A ctl img x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp
        (((s.sp + 0x970#64) ↦₆₄ 1#64) ∗
          ((s.sp + 0x978#64) ↦₆₄ w4) ∗
          ((s.sp + 0x980#64) ↦₆₄ w5))
        (memRegion (s.sp + 0x9d0#64) 24)
        (pollWith s.sp 0x970 [1#64, w4, w5])
        H
        (trustPoll_merge_970 s.sp 1#64 w4 w5)
    have hm_tail := Satisfies.mono (sepConj_mono_left htail_ent) hm_ro'
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_tail
    obtain ⟨g, hm_tail⟩ := hm_tail
    have htm : Tails.TailModel (h45_kitF kit) st0 ikit ist0 C S uuidTryParse encRecord x
        (answersOfTrust r (.error ())) (.error (.store ())) s0 s_err := by
      rw [h45_tailModel_kitF]
      exact StepsThroughEncrypt.tailModel_trust_err (encRecord := encRecord) (s0 := s0) (s := s_err)
        h15 htrustRel (htr_err.trans htrm')
    have hdraws : x.draws S (answersOfTrust r (.error ())) = draws :=
      StepsThroughEncrypt.draws_eq h15 (answersOfTrust r (.error ())) rfl
    refine SegExit.of_false_trap
      (tailStoreHookErr_ok_trap env x R0 s0 s_err (answersOfTrust r (.error ())) (.store ())
        0x800000000000001A#64 w1 10#64 1#64 w4 w5
        H cmScratch (Or.inr rfl)
        g (takenRecord sess taken) (some (pqCap', pqPtr', otr')) m 0xc20 0x970 (Or.inl rfl)
        htm (by subst hH hw1 hw4; exact speStaged_storeErr A img.base x.ret w5) ?_)
    refine ⟨by rw [hpc_err, encEntry_eq_fnAddr_trap env],
      ⟨hrun_err, hsp_err.trans hspm', hsp0_al,
      spAligned_of_sp_eq hspm_al hsp_err,
      by rw [hx29_err, hx29m, hx29], by rw [hx19_err, hx19m, hx19], hfl_err, hsym_err,
      by rw [hvregs_err, hvregsm, hvregs]⟩,
      ⟨by rw [hx26_err, hx26m, hx26], by rw [hx28_err, hx28m, hx28],
       by rw [hx27_err, hx27m], by rw [hx21_err, hx21m], by rw [hx23_err, hx23m]⟩,
      hstk, ?_⟩
    rw [hdraws, (StepsThroughEncrypt.model_trust_err h15)]
    rw [hsp] at hm_tail
    dsimp only [sp, draws, SessionStoreSpec.storeFinal,
      StoreKit.Identity.IdentityStoreSpec.idFinal, answersOfTrust, R'] at hm_tail ⊢
    exact Eq.mp (congrArg (s_err.mem ⊨ ·) (by ac_rfl)) hm_tail
  · obtain ⟨rfl, hw1, rfl⟩ := hans
    have hmm_970 : sm.mem ⊨
        (((sm.sp + 0x970#64) ↦₆₄ w3) ∗
          ((sm.sp + 0x970#64 + 8#64) ↦₆₄ w4) ∗
          ((sm.sp + 0x970#64 + 16#64) ↦₆₄ w5)) ∗
        ((trustBaseActive ikit.id_vt A img sm.sp x k ∗
          memRegion (sm.sp + 0x470#64) 16 ∗
          memRegion (sm.sp + 0x580#64) 48 ∗
          memRegion (sm.sp + 0x9d0#64) 24) ∗ (F ∗ R')) := by
      rw [hspm]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hmm ⊢
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm
    have hmm_fold := Satisfies.mono (sepConj_mono_left
      (words3_entails_memRegion24 (sm.sp + 0x970#64) w3 w4 w5)) hmm_970
    have hmm_in : sm.mem ⊨ (trustBaseActive ikit.id_vt A img sm.sp x k ∗
        memRegion (sm.sp + 0x470#64) 16 ∗
        memRegion (sm.sp + 0x580#64) 48 ∗
        memRegion (sm.sp + 0x970#64) 24 ∗
        memRegion (sm.sp + 0x9d0#64) 24) ∗ (F ∗ R') :=
      Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm_fold
    refine trust_false_to_d40_trap env hpcm hrunm hspm_al hx27m hx21m hw1
      (by rw [hspm, hx25m, hx25']) (by rw [hspm, hx26m, hsp, hx26]) hpref_m hmm_in ?_
    intro s_d40 cap ptr devWord u9e0 hsteps_d40 hpc_d40 hrun_d40 hsp_d40 hsp_d40_al htr_d40
      hx19_d40 hx26_d40 hx28_d40 hx29_d40 hvregs_d40 hx27_d40 hx21_d40 hx23_d40 hdev hm_d40
    have ⟨hfl_d40, hsym_d40⟩ := callInv_steps hflm hsymm hsteps_d40
    rw [hspm] at hm_d40
    have hm_d40' : s_d40.mem ⊨
        ((trustBaseActive ikit.id_vt A img s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          memRegion (s.sp + 0x970#64) 24 ∗
          (((s.sp + 0x9d0#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
            ((s.sp + 0x9d8#64) ↦₆₄ devWord) ∗
            ((s.sp + 0x9e0#64) ↦₆₄ u9e0)) ∗
          vecU8Body A cap ptr x.rem.name.bytes) ∗ F) ∗ R' :=
      Eq.mp (congrArg (s_d40.mem ⊨ ·) (by ac_rfl)) hm_d40
    have htail_ent :=
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.seam_mem_to_tail
        kit.ss_vt ikit.id_vt A ctl img x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp
        (memRegion (s.sp + 0x970#64) 24)
        (((s.sp + 0x9d0#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
          ((s.sp + 0x9d8#64) ↦₆₄ devWord) ∗
          ((s.sp + 0x9e0#64) ↦₆₄ u9e0))
        (pollWith s.sp 0x9d0 [BitVec.ofNat 64 x.rem.name.bytes.length, devWord, u9e0])
        (vecU8Body A cap ptr x.rem.name.bytes)
        (trustPoll_merge_9d0 s.sp (BitVec.ofNat 64 x.rem.name.bytes.length) devWord u9e0)
    have hm_tail := Satisfies.mono (sepConj_mono_left htail_ent) hm_d40'
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_tail
    obtain ⟨g, hm_tail⟩ := hm_tail
    have htm : Tails.TailModel (h45_kitF kit) st0 ikit ist0 C S uuidTryParse encRecord x
        (answersOfTrust r (.ok false)) (.error (.untrustedIdentity x.rem.val)) s0 s_d40 := by
      rw [h45_tailModel_kitF]
      exact StepsThroughEncrypt.tailModel_trust_false (encRecord := encRecord) (s0 := s0) (s := s_d40)
        h15 htrustRel (htr_d40.trans htrm')
    have hdraws : x.draws S (answersOfTrust r (.ok false)) = draws :=
      StepsThroughEncrypt.draws_eq h15 (answersOfTrust r (.ok false)) rfl
    refine SegExit.of_false_trap
      (tailCmDrop_ok_trap env x R0 s0 s_d40 (answersOfTrust r (.ok false)) (.untrustedIdentity x.rem.val)
        (speWord 12) cap ptr (BitVec.ofNat 64 x.rem.name.bytes.length) devWord u9e0
        (vecU8Body A cap ptr x.rem.name.bytes) cmScratch (Or.inr rfl)
        g (takenRecord sess taken) (some (pqCap', pqPtr', otr')) m
        htm
        (speStaged_untrusted A x.ret x.rem.val cap ptr
          (BitVec.ofNat 64 x.rem.name.bytes.length) devWord u9e0 rfl hdev) ?_)
    refine ⟨by rw [hpc_d40, encEntry_eq_fnAddr_trap env],
      ⟨hrun_d40, hsp_d40.trans hspm', hsp0_al, hsp_d40_al,
      by rw [hx29_d40, hx29m, hx29], by rw [hx19_d40, hx19m, hx19], hfl_d40, hsym_d40,
      by rw [hvregs_d40, hvregsm, hvregs]⟩,
      ⟨by rw [hx26_d40, hx26m, hx26], by rw [hx28_d40, hx28m, hx28],
       hx27_d40, hx21_d40, hx23_d40⟩,
      hstk, ?_⟩
    rw [hdraws, (StepsThroughEncrypt.model_trust_false h15)]
    rw [hsp] at hm_tail
    dsimp only [sp, draws, SessionStoreSpec.storeFinal,
      StoreKit.Identity.IdentityStoreSpec.idFinal, answersOfTrust, R'] at hm_tail ⊢
    exact Eq.mp (congrArg (s_d40.mem ⊨ ·) (by ac_rfl)) hm_tail
  · obtain ⟨rfl, hw1, rfl⟩ := hans
    have hmm_emp : sm.mem ⊨ emp ∗
        (((trustBaseActive ikit.id_vt A img s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x970#64) ↦₆₄ w3) ∗
            ((s.sp + 0x978#64) ↦₆₄ w4) ∗
            ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
          memRegion (s.sp + 0x9d0#64) 24) ∗ F) ∗ R') := by
      simp only [sepConj_emp, emp_sepConj] at hmm ⊢
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm
    refine SegExit.of_sepWP_trap hmm_emp (step_bc4_ok_true_trap hpcm hrunm hx27m hx21m hw1) ?_
    rintro s_ok _ _ hsteps_ok hpc_ok hrun_ok hm_ok
      ⟨rfl, hsp_ok, htr_ok, hx19_ok, hx20_ok, hx22_ok, hx25_ok, hx26_ok, hx28_ok, hx29_ok, hvregs_ok⟩
    rw [emp_sepConj] at hm_ok
    have ⟨hfl_ok, hsym_ok⟩ := callInv_steps hflm hsymm hsteps_ok
    have hm_ok_970 : s_ok.mem ⊨
        (((s.sp + 0x970#64) ↦₆₄ w3) ∗
          ((s.sp + 0x970#64 + 8#64) ↦₆₄ w4) ∗
          ((s.sp + 0x970#64 + 16#64) ↦₆₄ w5)) ∗
        ((trustBaseActive ikit.id_vt A img s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          memRegion (s.sp + 0x9d0#64) 24) ∗ F ∗ R') := by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok
    have hm_ok_fold := Satisfies.mono (sepConj_mono_left
      (words3_entails_memRegion24 (s.sp + 0x970#64) w3 w4 w5)) hm_ok_970
    have hm_ok_seam : s_ok.mem ⊨
        ((trustBaseActive ikit.id_vt A img s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗
          memRegion (s.sp + 0x580#64) 48 ∗
          memRegion (s.sp + 0x970#64) 24 ∗
          memRegion (s.sp + 0x9d0#64) 24) ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.trustPassive
            kit.ss_vt ikit.id_vt A img.base x sess taken otr' pqCap' pqPtr' m draws s0) ∗ R' := by
      dsimp only [F] at hm_ok_fold
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok_fold
    rw [← CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust.seam_mem_split
      kit.ss_vt ikit.id_vt A ctl img x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp] at hm_ok_seam
    rw [hsp] at hm_ok_seam
    intro _
    refine ⟨s_ok, Steps.refl s_ok, Or.inl ⟨⟨h15, htrustRel⟩,
      by rw [hpc_ok, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.savePC,
             encEntry_eq_fnAddr_trap env],
      ⟨hrun_ok, hsp_ok.trans hspm', hsp0_al, spAligned_of_sp_eq hspm_al hsp_ok,
        by rw [hx29_ok, hx29m, hx29], by rw [hx19_ok, hx19m, hx19], hfl_ok, hsym_ok,
        by rw [hvregs_ok, hvregsm, hvregs]⟩,
      htr_ok.trans htrm',
      ⟨by rw [hx20_ok, hx20m, hx20], by rw [hx22_ok, hspm'],
       by rw [hx25_ok, hx25m, hx25], by rw [hx26_ok, hx26m, hx26],
       by rw [hx28_ok, hx28m, hx28]⟩,
      hpt, hrest, hloc, hnow, hstk, ?_⟩⟩
    dsimp only [sp, draws, R'] at hm_ok_seam ⊢
    exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok_seam

end SegTrust

/-! ## Ext Bridges (`CliEncHooksExt` / `CliExternsOk` / `EncCallees_ext` → `WithStoresVT.*Ext`) -/

theorem encHooksExt_of_cliEncHooksExt {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (h : CliEncHooksExt C A S ext) : WithStoresVT.EncHooksExt C A S ext where
  toTripleRatchetHooks := h.toTripleRatchetHooks
  shim := h.shim
  memcpy := h.memcpy
  memcpyRO := h.memcpyRO
  timeAdd := h.timeAdd
  durationSinceEpoch := h.durationSinceEpoch

theorem WithStoresVT.encHooksExt_of_externsOk
    {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (S : SpqrModel)
    (hOk : CryptoVerification.SignalSession.CliExternsOk P A ext) :
    WithStoresVT.EncHooksExt P.C A S ext :=
  encHooksExt_of_cliEncHooksExt (cliEncHooksExt_of_externsOk S hOk)

theorem encCalleesQExt_of_encCallees_ext {Q : List (BitVec 8) → Prop} {img : Obj.Image}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (h : EncCallees_ext Q img C A ctl parse S ext) :
    WithStoresVT.EncCalleesQExt Q img C A ctl parse S ext :=
  ⟨h.otrFrom, h.otrApply, h.remoteIk, h.otrEnc, h.unack, h.kyber, h.psmNew, h.cmDrop, h.dropSs⟩

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
