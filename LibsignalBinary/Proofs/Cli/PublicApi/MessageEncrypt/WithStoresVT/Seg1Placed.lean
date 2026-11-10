/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.TailsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegIdentityPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustPlaced
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

@[expose] public section

set_option autoImplicit false

/-!
# Relocatable CLI `MessageEncrypt` `WithStoresVT` (Part 1): `EncEnvTPlaced` and Segments `SegIdentity`, `SegFrom`, `SegTrust`
-/

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSpqrV1 (TokenInit)

/-- Relocatable `withStoresEncPlacedSpecV` with `64 ≤ x.rest.length` and `F` (e.g. `TokenInit img`)
framed in `pre` and `post`. -/
def withStoresEncPlacedSpecVT [LibsignalPlacement] {A : RustAlloc}
    (F : SepProp)
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) : Spec WithStoresEncGhost :=
  let base := withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidParse S encRecord
  { base with
    pre := fun x s =>
      ⌜64 ≤ x.rest.length⌝ ∗ F ∗ base.pre x s
    post := fun x s0 sf =>
      F ∗ base.post x s0 sf }

/-- Relocatable `OTR::encrypt::<Coins>` spec at `Q := (pq.length < 2^32 ∧ 64 ≤ rest.length)` with `F` framed. -/
def otrEncryptPlacedSpecQT [LibsignalPlacement] (F : SepProp) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Spec OtrEncryptGhost :=
  otrEncryptPlacedSpecQF (fun pq rest => pq.length < 2 ^ 32 ∧ 64 ≤ rest.length)
    F C A ctl parse S

/-- Relocatable `EncCalleesPlaced` bundle with `otrEnc` using `otrEncryptPlacedSpecQT F`. -/
structure EncCalleesTPlaced [LibsignalPlacement] (F : SepProp) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (H : LibsignalHooks) : Prop where
  otrFrom : subroutine_ok (lsProg_464 H) (lsmpl.base 19)
    (StoreKit.withLsRoCl lsmpl (OutgoingRatchet.otrFromRawPlacedSpec A))
  otrApply : subroutine_ok (lsProg_464 H) (lsmpl.base 20)
    (StoreKit.withLsRoCl lsmpl (OutgoingRatchet.otrApplyPlacedSpec A))
  remoteIk : subroutine_ok (lsProg_464 H) (lsmpl.base 29)
    (StoreKit.withLsRoCl lsmpl (Getters.remoteIdentityKeyPlacedSpec A))
  otrEnc : subroutine_ok (lsProg_464 H)
    (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
    (StoreKit.withLsRoCl lsmpl (otrEncryptPlacedSpecQT F C A ctl parse S))
  unack : subroutine_ok (lsProg_464 H) (lsmpl.base 36)
    (StoreKit.withLsRoCl lsmpl (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec A))
  kyber : subroutine_ok (lsProg_464 H) (lsmpl.base 430)
    (StoreKit.withLsRoCl lsmpl (kyberMapSpec A))
  psmNew : subroutine_ok (lsProg_464 H) (lsmpl.base 41)
    (StoreKit.withLsRoCl lsmpl (preKeyMsgNewSpec A))
  cmDrop : subroutine_ok (lsProg_464 H) (lsmpl.base 438)
    (StoreKit.withLsRoCl lsmpl (cmDropSpec A))
  dropSs : subroutine_ok (lsProg_464 H) (lsmpl.base 442)
    (StoreKit.withLsRoCl lsmpl (FromRecordCallees.dropSessionStructureLocal2Spec A))

/-- Discharge all 8 proved in-library callees of `EncCalleesTPlaced` from `PublicApiEncHooksPlaced A H`,
leaving only `otrEnc` as an assumption. -/
theorem EncCalleesTPlaced.of_otrEnc [LibsignalPlacement] {F : SepProp}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {H : LibsignalHooks}
    (hhooks : PublicApiEncHooksPlaced A H)
    (hotrEnc : subroutine_ok (lsProg_464 H)
      (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (StoreKit.withLsRoCl lsmpl (otrEncryptPlacedSpecQT F C A ctl parse S))) :
    EncCalleesTPlaced F C A ctl parse S H := by
  have hFalse : subroutine_ok (lsProg_464 H)
      (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (StoreKit.withLsRoCl lsmpl (otrEncryptPlacedSpecQ (fun _ => False) C A ctl parse S)) := by
    intro x R s0 _ _ hpre _ _
    have ⟨_, hp⟩ := StoreKit.extract_withLsRoCl hpre
    dsimp only [otrEncryptPlacedSpecQ] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    exact False.elim hp.1
  have hC := EncCalleesPlaced.of_otrEnc hhooks hFalse
  exact ⟨hC.otrFrom, hC.otrApply, hC.remoteIk, hotrEnc, hC.unack, hC.kyber, hC.psmNew, hC.cmDrop, hC.dropSs⟩

/-- Relocatable `EncEnvPlaced` with `callees : EncCalleesTPlaced F` (`otrEncryptPlacedSpecQT F`) and
`scopeQ` specialized to `s.state.pqRatchetState.length < 2 ^ 32`. -/
structure EncEnvTPlaced [LibsignalPlacement] {A : RustAlloc}
    (F : SepProp)
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (_ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop where
  hooks : PublicApiEncHooksPlaced A H
  kitOk : SessionOnlyKitPlacedOkSE kit Scope encRecord H
  ikitOk : IdentityStoreKitPlacedOkI ikit H
  callees : EncCalleesTPlaced F C A ctl parse S H
  vtables : SessionOnlyVtablesPlacedOk kit
  idVtables : IdentityVtablesPlacedOk ikit
  scopeIn : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r
  scopeQ : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → r.currentSession = some s →
    s.state.pqRatchetState.length < 2 ^ 32
  recOk : ∀ {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))},
    kit.addrOk x.rem.val →
    StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S parse x r sess otr taken k m otr' →
    kit.RecOk (storedRecord sess otr' taken)

theorem h45_otrEncryptPlacedOkQ_false [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {H : LibsignalHooks} :
    subroutine_ok (lsProg_464 H)
      (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (StoreKit.withLsRoCl lsmpl (otrEncryptPlacedSpecQ (fun _ => False) C A ctl parse S)) := by
  intro x R s0 _ _ hpre _ _
  have ⟨_, hp⟩ := StoreKit.extract_withLsRoCl hpre
  dsimp only [otrEncryptPlacedSpecQ] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact False.elim hp.1

@[reducible] def h45_kitF_placed {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) :
    SessionStoreSpec A b :=
  { kit with addrOk := fun _ => False }

theorem h45_storeFinal_kitF_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (h45_kitF_placed kit).storeFinal st0 ans calls = kit.storeFinal st0 ans calls := by
  induction calls generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [SessionStoreSpec.storeFinal, h45_kitF_placed, ih]

theorem h45_callsRel_kitF_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (h45_kitF_placed kit).callsRel st0 ans calls = kit.callsRel st0 ans calls := by
  induction calls generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [SessionStoreSpec.callsRel, h45_kitF_placed, ih]

theorem h45_traceOfWith_kitF_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    ikit.traceOfWith (h45_kitF_placed kit) encRecord ans calls = ikit.traceOfWith kit encRecord ans calls :=
  rfl

theorem h45_subroutineOutcome_kitF_placed [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 sf : State) :
    SubroutineOutcome
      (withStoresEncPlacedSpecV (h45_kitF_placed kit) st0 ikit ist0 C ctl parse S encRecord) x R0 s0 sf =
    SubroutineOutcome
      (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl parse S encRecord) x R0 s0 sf := by
  have hpost :
      (withStoresEncPlacedSpecV (h45_kitF_placed kit) st0 ikit ist0 C ctl parse S encRecord).post =
      (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl parse S encRecord).post := by
    simp only [withStoresEncPlacedSpecV, StoreKit.withLsCodeRoLoaded, withStoresEncStackV,
      h45_kitF_placed, h45_storeFinal_kitF_placed, h45_callsRel_kitF_placed, h45_traceOfWith_kitF_placed]
  unfold SubroutineOutcome
  rw [hpost]
  rfl

theorem h45_segExit_kitF_placed [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (next : State → Prop) :
    SegExitPlaced (h45_kitF_placed kit) st0 ikit ist0 C ctl parse S encRecord H x R0 s0 s next =
      SegExitPlaced kit st0 ikit ist0 C ctl parse S encRecord H x R0 s0 s next := by
  simp only [SegExitPlaced, h45_subroutineOutcome_kitF_placed]

theorem h45_tailModel_kitF_placed {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (res : Except (ApiError AddrVal Unit) CiphertextMessage) (s0 s : State) :
    Tails.TailModel (h45_kitF_placed kit) st0 ikit ist0 C S parse encRecord x ans res s0 s =
      Tails.TailModel kit st0 ikit ist0 C S parse encRecord x ans res s0 s := by
  simp only [Tails.TailModel, h45_kitF_placed, h45_callsRel_kitF_placed, h45_traceOfWith_kitF_placed]

theorem h45_encTailV_kitF_placed [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (x : WithStoresEncGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (pc : BitVec 64)
    (regs : BitVec 64 → State → Prop) (slots : BitVec 64 → SepProp) (R0 : SepProp) (s0 s : State) :
    Tails.EncTailVPlaced (h45_kitF_placed kit) st0 ikit ist0 C ctl parse S x ans pc regs slots R0 s0 s =
    Tails.EncTailVPlaced kit st0 ikit ist0 C ctl parse S x ans pc regs slots R0 s0 s := by
  simp only [Tails.EncTailVPlaced, Pf.TailCommon.EncTailVPlaced,
    encStoreExtraPlaced, encSubStackV, h45_kitF_placed, h45_storeFinal_kitF_placed]

theorem h45_envF_placed [LibsignalPlacement] {F : SepProp} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvTPlaced F kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord H) :
    EncEnvPlaced (h45_kitF_placed kit) st0 ikit ist0 (fun _ => False) (fun _ => False)
      C ctl uuidTryParse S encRecord H where
  hooks := hEnv.hooks
  kitOk := {
    loadShim := hEnv.kitOk.loadShim
    loadPoll := by
      intro callerProg callerBlk _ hblk ⟨x, self, st⟩ R s0 _ _ hpre _ _
      have ⟨_, hp⟩ := StoreKit.extract_withLsRoCl hpre
      obtain ⟨_, hp2⟩ := withEnvPre_pre_elim hp
      have hp3 : s0.mem ⊨ ⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧ False⌝ ∗
          (kit.loadBoxAt x.fut self x.addrA 0#8 ∗ kit.storeAt self st ∗ memRegion x.out 368 ∗
            protocolAddressAt A x.addr x.addrA ∗ A.pool ∗ stackAt s0.sp kit.loadPollStack ∗ R) := by
        simpa only [kitLoadPollPlacedSpecS, h45_kitF_placed, sepConj_assoc] using hp2
      rw [satisfies_pure_sepConj] at hp3
      exact False.elim hp3.1.2.2
    loadFutDrop := hEnv.kitOk.loadFutDrop
    storeShim := hEnv.kitOk.storeShim
    storePoll := by
      intro callerProg callerBlk _ hblk ⟨x, self, st⟩ R s0 _ _ hpre _ _
      have ⟨_, hp⟩ := StoreKit.extract_withLsRoCl hpre
      obtain ⟨_, hp2⟩ := withEnvPre_pre_elim hp
      have hp3 : s0.mem ⊨ ⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
          kit.RecOk x.call.record ∧ False⌝ ∗
          (kit.storeBoxAt x.fut self x.call.addrA x.call.recA 0#8 ∗
            kit.storeAt self st ∗ memRegion x.out 48 ∗
            protocolAddressAt A x.call.addr x.call.addrA ∗
            sessionRecordAt A x.call.recA x.call.g x.call.record ∗
            A.pool ∗ stackAt s0.sp kit.storePollStack ∗ R) := by
        simpa only [kitStorePollPlacedSpec, h45_kitF_placed, sepConj_assoc] using hp2
      rw [satisfies_pure_sepConj] at hp3
      exact False.elim hp3.1.2.2.2
    storeFutDrop := hEnv.kitOk.storeFutDrop
  }
  ikitOk := hEnv.ikitOk
  callees := {
    otrFrom := hEnv.callees.otrFrom
    otrApply := hEnv.callees.otrApply
    remoteIk := hEnv.callees.remoteIk
    otrEnc := h45_otrEncryptPlacedOkQ_false
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
  recOk := fun h => False.elim h.2.1.1

theorem h45_subroutineOutcome_vt_of_v_placed [LibsignalPlacement] {A : RustAlloc}
    {F : SepProp}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {uuidParse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome
      (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidParse S encRecord)
      x (F ∗ R) s0 sf) :
    SubroutineOutcome (withStoresEncPlacedSpecVT F kit st0 ikit ist0 C ctl uuidParse S encRecord)
      x R s0 sf := by
  rcases h with ⟨h1, hcs, hpost⟩ | ⟨hpan, honp⟩ | ⟨code, hexit, honex⟩ | ⟨_hoom, honoom⟩
  · refine Or.inl ⟨h1, hcs, ?_⟩
    dsimp only [withStoresEncPlacedSpecVT]
    refine Satisfies.mono ?_ hpost
    exact Entails.of_eq (by ac_rfl)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withStoresEncPlacedSpecVT, withStoresEncPlacedSpecV, StoreKit.withLsCodeRoLoaded] at honp ⊢
    refine Satisfies.mono ?_ honp
    rw [← sepConj_assoc, sepConj_assoc ⌜_⌝ anyHeap F]
    refine sepConj_mono_left (sepConj_mono_right ?_)
    exact entails_anyHeap (anyHeap ∗ F)
  · refine Or.inr (Or.inr (Or.inl ⟨code, hexit, ?_⟩))
    change sf.mem ⊨ ⌜False⌝ ∗ (F ∗ R) at honex
    rw [satisfies_pure_sepConj] at honex
    exact False.elim honex.1
  · change sf.mem ⊨ ⌜False⌝ ∗ (F ∗ R) at honoom
    rw [satisfies_pure_sepConj] at honoom
    exact False.elim honoom.1

def h45_ScopeNone_placed (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (r : SessionRecord (List (BitVec 8))) : Prop :=
  Scope r ∧ r.currentSession = none

theorem h45_envNone_placed [LibsignalPlacement] {F : SepProp} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvTPlaced F kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord H) :
    EncEnvPlaced (h45_kitF_placed kit) st0 ikit ist0 (h45_ScopeNone_placed Scope) (fun _ => False)
      C ctl uuidTryParse S encRecord H :=
  { h45_envF_placed hEnv with
    kitOk := {
      (h45_envF_placed hEnv).kitOk with
      loadPoll := by
        intro callerProg callerBlk _ hblk ⟨x, self, st⟩ R s0 _ _ hpre _ _
        have ⟨_, hp⟩ := StoreKit.extract_withLsRoCl hpre
        obtain ⟨_, hp2⟩ := withEnvPre_pre_elim hp
        have hp3 : s0.mem ⊨ ⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧ False⌝ ∗
            (kit.loadBoxAt x.fut self x.addrA 0#8 ∗ kit.storeAt self st ∗ memRegion x.out 368 ∗
              protocolAddressAt A x.addr x.addrA ∗ A.pool ∗ stackAt s0.sp kit.loadPollStack ∗ R) := by
          simpa only [kitLoadPollPlacedSpecS, h45_kitF_placed, sepConj_assoc] using hp2
        rw [satisfies_pure_sepConj] at hp3
        exact False.elim hp3.1.2.2
    }
    scopeIn := fun r h => hEnv.scopeIn r ⟨h.1.1, h.2⟩
    scopeQ := fun _ _ h hs => by rw [h.1.2] at hs; cases hs
    recOk := fun h => by have hnone := h.2.1.1.2; rw [h.1] at hnone; cases hnone }

@[reducible] def h45_kitL_placed {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) :
    SessionStoreSpec A b :=
  { kit with addrOk := fun _ => False, loadRel := fun _ _ _ => False }

theorem h45_envL_placed [LibsignalPlacement] {F : SepProp} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvTPlaced F kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord H) :
    EncEnvPlaced (h45_kitL_placed kit) st0 ikit ist0 Scope (fun _ => False)
      C ctl uuidTryParse S encRecord H where
  hooks := hEnv.hooks
  kitOk := {
    loadShim := hEnv.kitOk.loadShim
    loadPoll := by
      intro callerProg callerBlk _ hblk ⟨x, self, st⟩ R s0 _ _ hpre _ _
      have ⟨_, hp⟩ := StoreKit.extract_withLsRoCl hpre
      obtain ⟨_, hp2⟩ := withEnvPre_pre_elim hp
      have hp3 : s0.mem ⊨ ⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧ False⌝ ∗
          (kit.loadBoxAt x.fut self x.addrA 0#8 ∗ kit.storeAt self st ∗ memRegion x.out 368 ∗
            protocolAddressAt A x.addr x.addrA ∗ A.pool ∗ stackAt s0.sp kit.loadPollStack ∗ R) := by
        simpa only [kitLoadPollPlacedSpecS, h45_kitL_placed, sepConj_assoc] using hp2
      rw [satisfies_pure_sepConj] at hp3
      exact False.elim hp3.1.2.2
    loadFutDrop := hEnv.kitOk.loadFutDrop
    storeShim := hEnv.kitOk.storeShim
    storePoll := by
      intro callerProg callerBlk _ hblk ⟨x, self, st⟩ R s0 _ _ hpre _ _
      have ⟨_, hp⟩ := StoreKit.extract_withLsRoCl hpre
      obtain ⟨_, hp2⟩ := withEnvPre_pre_elim hp
      have hp3 : s0.mem ⊨ ⌜s0.readReg64 .x0 = x.fut ∧ s0.readReg64 .x8 = x.out ∧
          kit.RecOk x.call.record ∧ False⌝ ∗
          (kit.storeBoxAt x.fut self x.call.addrA x.call.recA 0#8 ∗
            kit.storeAt self st ∗ memRegion x.out 48 ∗
            protocolAddressAt A x.call.addr x.call.addrA ∗
            sessionRecordAt A x.call.recA x.call.g x.call.record ∗
            A.pool ∗ stackAt s0.sp kit.storePollStack ∗ R) := by
        simpa only [kitStorePollPlacedSpec, h45_kitL_placed, sepConj_assoc] using hp2
      rw [satisfies_pure_sepConj] at hp3
      exact False.elim hp3.1.2.2.2
    storeFutDrop := hEnv.kitOk.storeFutDrop
  }
  ikitOk := hEnv.ikitOk
  callees := (h45_envF_placed hEnv).callees
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
  recOk := fun h => False.elim h.2.1.2

section SegFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails (tailFromSessionStateErr_placed_ok)
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

private theorem model_of_fromSessionState_error_placed
    {C : Crypto} {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {e : SignalProtocolError}
    (hcur : r.currentSession = some sess)
    (herr : (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 = .error e) :
    x.model C S uuidTryParse (okAnswers r .newOrUnchanged) =
      (.error (.protocol e), [.loadSession x.rem.val]) ∧
    x.draws S (okAnswers r .newOrUnchanged) = 0 := by
  have hex : execOk OutgoingTripleRatchet.fromSessionState sess.state = .error e :=
    execOk_fromSessionState_of_error_shared_lb herr
  have hprot : (ApiError.ofProtocol e : ApiError AddrVal Unit) = .protocol e := by
    cases e <;> first | rfl | exact absurd rfl (fromSessionState_error_ne_invalidState_shared_lb herr).2
  have hmod : x.model C S uuidTryParse (okAnswers r .newOrUnchanged) =
      (.error (ApiError.ofProtocol e), [.loadSession x.rem.val]) := by
    unfold EncryptGhost.model messageEncrypt Api.run storeCall liftProtocol okAnswers
    simp [hcur, hex, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      ExceptT.run, StateT.run, bind, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift,
      StateT.bind, StateT.map, Functor.map, monadLift, MonadLift.monadLift,
      MonadLiftT.monadLift, pure, ExceptT.pure, StateT.pure, throw, throwThe,
      MonadExceptOf.throw]
  refine ⟨by rw [hmod, hprot], ?_⟩
  unfold EncryptGhost.draws EncryptGhost.sendState loadedSession okAnswers
  simp only [hcur, hex]

theorem h45_segFrom_placed_okVT [LibsignalPlacement] {F : SepProp}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (R0 : SepProp) (s0 s : State)
    (hcurState : CurStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r g sess R0 s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s
      (fun s' => ∃ otr taken pqCap pqPtr,
        OtrStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr R0 s0 s') := by
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0
  rcases hcurState with ⟨hcur, hsc, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, ⟨hx20, hx21, hx25, hx26, hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have hs_pc' : s.pc = encEntryPlaced + 0x20c#64 := hs_pc
  obtain ⟨G, u280, _, hpure, hm_unp⟩ :=
    curState_placed_mem_unpack A ctl x r g sess sp R s0 hsp0 hcur hm
  refine SegExitPlaced.of_sepWP hm_unp
    (segFrom_placed_step_pre hs_pc' hrun hsp hal hx20 hx21 hx25 hx26 hx28) ?_
  intro s1 Pm1 _hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x0, hs1_x8, hs1_x19, hs1_x20, hs1_x21, hs1_x24, hs1_x25, hs1_x26,
      hs1_x27, hs1_x28, hs1_x29, hs1_lr, hs1_vregs, hPm1⟩
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem := hcrl.of_keepsFrozen hsteps01.keepsFrozen
  have hs1_al : s1.spAligned = true := spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hm1_pre := otrFrom_placed_pre_frame A ctl x g G sess sp R Pm1 s0 s1
    hcrl1 hs1_sp hs1_x0 hs1_x8 hPm1 hm1
  refine SegExitPlaced.call hEnv.callees.otrFrom ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩
    hs1_pc hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (StoreKit.withLsRoCl lsmpl (OutgoingRatchet.otrFromRawPlacedSpec A)).onExit
          ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩ code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpan_post => by
      rw [show (StoreKit.withLsRoCl lsmpl (OutgoingRatchet.otrFromRawPlacedSpec A)).onPanic
          ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩ s1 sf = ⌜False⌝ from rfl,
          sepConj_assoc, satisfies_pure_sepConj] at hpan_post
      exact hpan_post.1.elim)
    ?_
  intro s2 _hL1 _hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have hs2_sp' : s2.sp = sp := hs2_sp.trans hs1_sp
  have hs2_al : s2.spAligned = true := spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x20 : s2.readReg64 .x20 = sp + 0x58#64 := by reg_chain
  have hs2_x24 : s2.readReg64 .x24 = sp + 0x58#64 := by reg_chain
  have hs2_x25 : s2.readReg64 .x25 = sp + 0x580#64 := by reg_chain
  have hs2_x26 : s2.readReg64 .x26 = sp + 0x9d0#64 := by reg_chain
  have hs2_x27 : s2.readReg64 .x27 = sp + 0xc0#64 := by reg_chain
  have hs2_x28 : s2.readReg64 .x28 = sp + 0x4a0#64 := by reg_chain
  obtain ⟨hcrl2, G', _, hs2_tr, hm2⟩ :=
    otrFrom_placed_post_unpack A ctl x g G sess ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩
      sp R s0 s1 s2 rfl hsp0 hs1_sp hpure hpost2
  have hs2_tr' : s2.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) :=
    hs2_tr.trans (hs1_tr.trans htr)
  rcases hres : (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 with p | otr
  · change s2.mem ⊨ otrResultAt A (sp + 0x580#64) G.pq
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 ∗ _ at hm2
    rw [hres] at hm2
    obtain ⟨w0, w1, w2, w3, w4, w5, H, hst, hm2_err⟩ :=
      otrFrom_placed_err_unpack A ctl x { g with cur := some G' } G.pq sess
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 p sp R s0 s2 hres hm2
    refine SegExitPlaced.of_sepWP hm2_err (segFrom_placed_step_err hs2_pc hs2_run hs2_sp' hs2_al) ?_
    intro s3 Pm3 _hL2 hsteps23 hs3_pc hs3_run hm3
      ⟨hs3_sp, hs3_tr, hs3_x19, hs3_x21, hs3_x25, hs3_x26, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
    have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl2.of_keepsFrozen hsteps23.keepsFrozen
    have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
    have ⟨hmod_res, hdraws0⟩ := model_of_fromSessionState_error_placed (C := C) (S := S)
      (x := x) hcur hres
    have hm3_tail := otrFrom_placed_err_tail_mem A ctl x { g with cur := some G' } sess
      (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 w0 w1 w2 w3 w4 w5 sp H R Pm3
      s0 s3 hPm3 hm3
    rw [← h45_segExit_kitF_placed]
    refine SegExitPlaced.of_false (tailFromSessionStateErr_placed_ok (h45_envF_placed hEnv) x R0 s0 s3
      (okAnswers r .newOrUnchanged)
      (.protocol p) w0 w1 w2 w3 w4 w5 H { g with cur := some G' }
      (takenRecord sess (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2)
      ?_ hst ?_)
    · refine ⟨⟨by rw [hmod_res], by rw [hmod_res]; exact ⟨hsc.2, trivial⟩, by rw [hmod_res]; trivial⟩, ?_⟩
      rw [hs3_tr, hs2_tr', hmod_res]
      dsimp only [okAnswers]
      rw [ikit.traceOfWith_load]
    · refine ⟨hs3_pc, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hcrl3,
        by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩,
        ⟨by reg_chain, by reg_chain, by reg_chain, by reg_chain⟩, hstk, ?_⟩
      rw [hdraws0, hmod_res]
      exact hm3_tail
  · change s2.mem ⊨ otrResultAt A (sp + 0x580#64) G.pq
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 ∗ _ at hm2
    rw [hres] at hm2
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18,
      w19, w20, w21, w22, w23, w24,
      d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18,
      d19, d20, d21, d22, d23, d24,
      u850, u858, u860, u950, u958, u960, H, hpq, hpack, hm2_ok⟩ :=
      otrFrom_placed_ok_unpack A ctl x { g with cur := some G' } G.pq sess
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 otr sp R s0 s2 hm2
    refine SegExitPlaced.of_sepWP hm2_ok
      (segFrom_placed_step_ok hs2_pc hs2_run hs2_sp' hs2_al hs2_x20 hs2_x24 hs2_x25 hs2_x26 hs2_x27
        hs2_x28 hpq) ?_
    intro s3 Pm3 _hL2 hsteps23 hs3_pc hs3_run hm3
      ⟨hs3_sp, hs3_tr, hs3_x0, hs3_x8, hs3_x19, hs3_x20, hs3_x22, hs3_x23, hs3_x24, hs3_x25,
        hs3_x26, hs3_x27, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
    have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl2.of_keepsFrozen hsteps23.keepsFrozen
    have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
    have hm3_ok := otrFrom_placed_ok_pack A ctl x { g with cur := some G' } G.pq sess
      (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 otr
      w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24
      sp H R Pm3 s0 s3 hpack hPm3 hm3
    refine SegExitPlaced.next ⟨otr, (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2,
      G.pq.cap, G.pq.ptr, hcur, hsc, execOk_fromSessionState_of_ok_shared_lb hres, ?_⟩
    exact ⟨hs3_pc, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hcrl3,
      by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩,
      hs3_tr.trans hs2_tr',
      ⟨hs3_x0, hs3_x8, hs3_x20, hs3_x22, hs3_x23, hs3_x24, hs3_x25, hs3_x26, hs3_x27, hs3_x28⟩,
      hpt, hrest, hloc, hnow, hstk, hm3_ok⟩

end SegFrom

section SegTrust
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegTrust
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom (SegExitPlaced.next SegExitPlaced.of_false SegExitPlaced.of_sepWP)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
  (tailStoreHookErr_placed_ok tailCmDrop_placed_ok)
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

theorem h45_segTrust_placed_okVT [LibsignalPlacement] {F0 : SepProp}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R0 : SepProp)
    (s0 s : State)
    (haddr : ikit.addrOk x.rem.val)
    (hfs : EncFsCtxPlaced kit ikit Hk s0 s)
    (hcm : CmStateVPlaced kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr' R0 s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s
      (fun s' => SaveStateVPlaced kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr' R0 s0 s') := by
  let env := h45_envF_placed hEnv
  let R : SepProp := kit.storeAt x.ssA st0 ∗ R0
  obtain ⟨h15, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    htr, ⟨hx20, hx25, hx26, hx28⟩, hpt, hrest, hloc, hnow, hstk, hm⟩ := hcm
  set sp := s0.sp - 0xbe0#64
  set draws := S.draws otr.pqrState x.rest
  set F := cliTrustPassive kit.ss_vt ikit.id_vt A ctl x sess taken otr' pqCap' pqPtr' m draws s0
  have hpref0 : s0.trace <+: s.trace := ⟨_, htr.symm⟩
  have hm_pre : s.mem ⊨
      (trustBaseActivePlaced ikit.id_vt A s.sp x k ∗ encStoreExtraPlaced kit st0 ikit ist0 x s0) ∗
      ((memRegion (s.sp + 0x470#64) 16 ∗
        memRegion (s.sp + 0x580#64) 48 ∗
        memRegion (s.sp + 0x970#64) 24 ∗
        memRegion (s.sp + 0x9d0#64) 24) ∗ F ∗ R0) := by
    have hm1 : s.mem ⊨
        (cmSlots A s.sp sess taken otr' pqCap' pqPtr' k m ∗ cmScratch s.sp ∗
          encSpillsAtV kit.ss_vt ikit.id_vt s.sp x ∗ memRegion (s.sp + 0x46a#64) 0x716 ∗
          memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0) ∗
        (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0) := by
      rw [hsp]
      exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
    rw [seam_mem_split_placed kit.ss_vt ikit.id_vt A ctl x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp] at hm1
    dsimp only [F]
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm1
  have hm_join := Satisfies.mono (sepConj_mono_left
    (trustBaseActive_join_extra_placed kit st0 ikit ist0 x k s0 s.sp hsp)) hm_pre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm_join
  obtain ⟨hbound, hm_join⟩ := hm_join
  have hm_split : s.mem ⊨ (trustVtablesAt ikit ∗
      trustActivePlaced ikit ist0 s.sp (encSubStackV kit ikit) x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
      memRegion (s.sp + 0x970#64) 24 ∗ memRegion (s.sp + 0x9d0#64) 24) ∗ (F ∗ R) := by
    have hm' := trustVtablesAt_placed_intro env.idVtables hcrl.2 hm_join
    dsimp only [R]; exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm'
  have hx25' : s.readReg64 .x25 = s.sp + 0x580#64 := by rw [hsp]; exact hx25
  rw [← h45_segExit_kitF_placed]
  refine trust_to_bc4_placed env haddr
    (fun s' hst' htr' =>
      ((hfs.of_steps hst').envOk_at (htr'.trans htr) fun hq => by
        obtain ⟨⟨hl, -⟩, -⟩ := hq; simp only [hl]).2)
    hbound hpc hrun hsp_al hx25' hpref0 hcrl hm_split ?_
  intro sm ans w0 w1 w2 w3 w4 w5 H _hsteps_bc4 hpcm hrunm hspm hspm_al hcrlm htrustRel htrm
    hx19m hx20m hx25m hx26m hx28m hx29m hvregsm hx27m hx21m hx23m hans hmm_act
  let R' : SepProp := encStoreExtraPlaced kit st0 ikit (ikit.trustUpdate ist0 x.rem.val k .sending ans) x s0 ∗ R0
  have hmm : sm.mem ⊨ (trustBaseActivePlaced ikit.id_vt A s.sp x k ∗
      memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
      (((s.sp + 0x970#64) ↦₆₄ w3) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
      memRegion (s.sp + 0x9d0#64) 24 ∗ H) ∗ (F ∗ R') := by
    have hmm1 : sm.mem ⊨
        (trustActivePlaced ikit (ikit.trustUpdate ist0 x.rem.val k .sending ans) s.sp (encSubStackV kit ikit) x k ∗
          kit.storeAt x.ssA st0) ∗
        ((memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x970#64) ↦₆₄ w3) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
          memRegion (s.sp + 0x9d0#64) 24 ∗ H) ∗ F ∗ R0) := by
      dsimp only [R] at hmm_act; exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm_act
    have hmm2 := Satisfies.mono (sepConj_mono_left
      (trustActive_split_extra_placed kit st0 ikit (ikit.trustUpdate ist0 x.rem.val k .sending ans) x k s0 s.sp hsp hbound)) hmm1
    dsimp only [R']; exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm2
  have hspm' : sm.sp = sp := hspm.trans hsp
  have htrm' : sm.trace = s0.trace ++
      (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++ ikit.trustEvs x.rem.val k .sending ans) := by
    rw [htrm, htr, List.append_assoc]
  have hpref_m : s0.trace <+: sm.trace := ⟨_, htrm'.symm⟩
  rcases ans with ⟨⟨⟩⟩ | (_ | _)
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hans
    have hmm_emp : sm.mem ⊨ emp ∗
        (((trustBaseActivePlaced ikit.id_vt A s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x970#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
          memRegion (s.sp + 0x9d0#64) 24 ∗ (w1 ↦ᵣ storeHookStr)) ∗ F) ∗ R') := by
      rw [emp_sepConj]; exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm
    refine SegExitPlaced.of_sepWP hmm_emp (step_bc4_err_placed hpcm hrunm hx27m) ?_
    rintro s_err _ _ hsteps_err hpc_err hrun_err hm_err
      ⟨rfl, hsp_err, htr_err, hx19_err, hx21_err, hx23_err, hx26_err, hx27_err, hx28_err, hx29_err, hvregs_err⟩
    rw [emp_sepConj] at hm_err
    have hcrl_err : StoreKit.LibsignalCodeRoLoaded lsmpl s_err.mem := hcrlm.of_keepsFrozen hsteps_err.keepsFrozen
    have hm_ro' : s_err.mem ⊨
        ((trustBaseActivePlaced ikit.id_vt A s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x970#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
          memRegion (s.sp + 0x9d0#64) 24 ∗ (w1 ↦ᵣ storeHookStr)) ∗ F) ∗ R' :=
      Eq.mp (congrArg (s_err.mem ⊨ ·) (by ac_rfl)) hm_err
    have htail_ent := seam_mem_to_tail_placed kit.ss_vt ikit.id_vt A ctl x sess taken otr' pqCap' pqPtr' k m draws s0
      s.sp hsp
      (((s.sp + 0x970#64) ↦₆₄ 1#64) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5))
      (memRegion (s.sp + 0x9d0#64) 24) (pollWith s.sp 0x970 [1#64, w4, w5]) (w1 ↦ᵣ storeHookStr)
      (trustPoll_merge_970 s.sp 1#64 w4 w5)
    have hm_tail := Satisfies.mono (sepConj_mono_left htail_ent) hm_ro'
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_tail
    obtain ⟨g, hm_tail⟩ := hm_tail
    have htm : Tails.TailModel (h45_kitF_placed kit) st0 ikit ist0 C S uuidTryParse encRecord x
        (answersOfTrust r (.error ())) (.error (.store ())) s0 s_err := by
      rw [h45_tailModel_kitF_placed]
      exact StepsThroughEncrypt.tailModel_trust_err (encRecord := encRecord) (s0 := s0) (s := s_err)
        h15 htrustRel (htr_err.trans htrm')
    have hdraws : x.draws S (answersOfTrust r (.error ())) = draws :=
      StepsThroughEncrypt.draws_eq h15 (answersOfTrust r (.error ())) rfl
    refine SegExitPlaced.of_false
      (tailStoreHookErr_placed_ok env x R0 s0 s_err (answersOfTrust r (.error ())) (.store ())
        0x800000000000001A#64 w1 10#64 1#64 w4 w5
        (w1 ↦ᵣ storeHookStr) cmScratch (Or.inr rfl)
        g (takenRecord sess taken) (some (pqCap', pqPtr', otr')) m 0xc20 0x970 (Or.inl rfl)
        htm (speStaged_storeErr_placed A x.ret w1 w4 w5) ?_)
    refine ⟨hpc_err,
      ⟨hrun_err, hsp_err.trans hspm', hsp0_al,
      CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hspm_al hsp_err,
      by rw [hx29_err, hx29m, hx29], by rw [hx19_err, hx19m, hx19], hcrl_err,
      by rw [hvregs_err, hvregsm, hvregs]⟩,
      ⟨by rw [hx26_err, hx26m, hx26], by rw [hx28_err, hx28m, hx28],
       by rw [hx27_err, hx27m], by rw [hx21_err, hx21m], by rw [hx23_err, hx23m]⟩,
      hstk, ?_⟩
    rw [hdraws, (StepsThroughEncrypt.model_trust_err h15)]; rw [hsp] at hm_tail
    dsimp only [sp, draws, SessionStoreSpec.storeFinal, StoreKit.Identity.IdentityStoreSpec.idFinal, answersOfTrust, R'] at hm_tail ⊢
    exact Eq.mp (congrArg (s_err.mem ⊨ ·) (by ac_rfl)) hm_tail
  · obtain ⟨rfl, hw1, rfl⟩ := hans
    have hmm_970 : sm.mem ⊨
        (((sm.sp + 0x970#64) ↦₆₄ w3) ∗ ((sm.sp + 0x970#64 + 8#64) ↦₆₄ w4) ∗ ((sm.sp + 0x970#64 + 16#64) ↦₆₄ w5)) ∗
        ((trustBaseActivePlaced ikit.id_vt A sm.sp x k ∗
          memRegion (sm.sp + 0x470#64) 16 ∗ memRegion (sm.sp + 0x580#64) 48 ∗
          memRegion (sm.sp + 0x9d0#64) 24) ∗ (F ∗ R')) := by
      rw [hspm]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp] at hmm ⊢
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm
    have hmm_fold := Satisfies.mono (sepConj_mono_left
      (words3_entails_memRegion24 (sm.sp + 0x970#64) w3 w4 w5)) hmm_970
    have hmm_in : sm.mem ⊨ (trustBaseActivePlaced ikit.id_vt A sm.sp x k ∗
        memRegion (sm.sp + 0x470#64) 16 ∗ memRegion (sm.sp + 0x580#64) 48 ∗
        memRegion (sm.sp + 0x970#64) 24 ∗ memRegion (sm.sp + 0x9d0#64) 24) ∗ (F ∗ R') :=
      Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm_fold
    refine trust_false_to_d40_placed env hpcm hrunm hspm_al hx27m hx21m hw1
      (by rw [hspm, hx25m, hx25']) (by rw [hspm, hx26m, hsp, hx26]) hpref_m hcrlm hmm_in ?_
    intro s_d40 cap ptr devWord u9e0 hsteps_d40 hpc_d40 hrun_d40 hsp_d40 hsp_d40_al htr_d40
      hx19_d40 hx26_d40 hx28_d40 hx29_d40 hvregs_d40 hx27_d40 hx21_d40 hx23_d40 hdev hm_d40
    have hcrl_d40 : StoreKit.LibsignalCodeRoLoaded lsmpl s_d40.mem := hcrlm.of_keepsFrozen hsteps_d40.keepsFrozen
    rw [hspm] at hm_d40
    have hm_d40' : s_d40.mem ⊨
        ((trustBaseActivePlaced ikit.id_vt A s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗ memRegion (s.sp + 0x970#64) 24 ∗
          (((s.sp + 0x9d0#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
            ((s.sp + 0x9d8#64) ↦₆₄ devWord) ∗ ((s.sp + 0x9e0#64) ↦₆₄ u9e0)) ∗
          vecU8Body A cap ptr x.rem.name.bytes) ∗ F) ∗ R' :=
      Eq.mp (congrArg (s_d40.mem ⊨ ·) (by ac_rfl)) hm_d40
    have htail_ent := seam_mem_to_tail_placed kit.ss_vt ikit.id_vt A ctl x sess taken otr' pqCap' pqPtr' k m draws s0
      s.sp hsp (memRegion (s.sp + 0x970#64) 24)
      (((s.sp + 0x9d0#64) ↦₆₄ BitVec.ofNat 64 x.rem.name.bytes.length) ∗
        ((s.sp + 0x9d8#64) ↦₆₄ devWord) ∗ ((s.sp + 0x9e0#64) ↦₆₄ u9e0))
      (pollWith s.sp 0x9d0 [BitVec.ofNat 64 x.rem.name.bytes.length, devWord, u9e0])
      (vecU8Body A cap ptr x.rem.name.bytes)
      (trustPoll_merge_9d0 s.sp (BitVec.ofNat 64 x.rem.name.bytes.length) devWord u9e0)
    have hm_tail := Satisfies.mono (sepConj_mono_left htail_ent) hm_d40'
    simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_tail
    obtain ⟨g, hm_tail⟩ := hm_tail
    have htm : Tails.TailModel (h45_kitF_placed kit) st0 ikit ist0 C S uuidTryParse encRecord x
        (answersOfTrust r (.ok false)) (.error (.untrustedIdentity x.rem.val)) s0 s_d40 := by
      rw [h45_tailModel_kitF_placed]
      exact StepsThroughEncrypt.tailModel_trust_false (encRecord := encRecord) (s0 := s0) (s := s_d40)
        h15 htrustRel (htr_d40.trans htrm')
    have hdraws : x.draws S (answersOfTrust r (.ok false)) = draws :=
      StepsThroughEncrypt.draws_eq h15 (answersOfTrust r (.ok false)) rfl
    refine SegExitPlaced.of_false
      (tailCmDrop_placed_ok env x R0 s0 s_d40 (answersOfTrust r (.ok false)) (.untrustedIdentity x.rem.val)
        (speWord 12) cap ptr (BitVec.ofNat 64 x.rem.name.bytes.length) devWord u9e0
        (vecU8Body A cap ptr x.rem.name.bytes) cmScratch (Or.inr rfl)
        g (takenRecord sess taken) (some (pqCap', pqPtr', otr')) m
        htm
        (speStaged_untrusted A x.ret x.rem.val cap ptr
          (BitVec.ofNat 64 x.rem.name.bytes.length) devWord u9e0 rfl hdev) ?_)
    refine ⟨hpc_d40,
      ⟨hrun_d40, hsp_d40.trans hspm', hsp0_al, hsp_d40_al,
      by rw [hx29_d40, hx29m, hx29], by rw [hx19_d40, hx19m, hx19], hcrl_d40,
      by rw [hvregs_d40, hvregsm, hvregs]⟩,
      ⟨by rw [hx26_d40, hx26m, hx26], by rw [hx28_d40, hx28m, hx28],
       hx27_d40, hx21_d40, hx23_d40⟩,
      hstk, ?_⟩
    rw [hdraws, (StepsThroughEncrypt.model_trust_false h15)]; rw [hsp] at hm_tail
    dsimp only [sp, draws, SessionStoreSpec.storeFinal, StoreKit.Identity.IdentityStoreSpec.idFinal, answersOfTrust, R'] at hm_tail ⊢
    exact Eq.mp (congrArg (s_d40.mem ⊨ ·) (by ac_rfl)) hm_tail
  · obtain ⟨rfl, hw1, rfl⟩ := hans
    have hmm_emp : sm.mem ⊨ emp ∗
        (((trustBaseActivePlaced ikit.id_vt A s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          (((s.sp + 0x970#64) ↦₆₄ w3) ∗ ((s.sp + 0x978#64) ↦₆₄ w4) ∗ ((s.sp + 0x980#64) ↦₆₄ w5)) ∗
          memRegion (s.sp + 0x9d0#64) 24) ∗ F) ∗ R') := by
      simp only [sepConj_emp, emp_sepConj] at hmm ⊢
      exact Eq.mp (congrArg (sm.mem ⊨ ·) (by ac_rfl)) hmm
    refine SegExitPlaced.of_sepWP hmm_emp (step_bc4_ok_true_placed hpcm hrunm hx27m hx21m hw1) ?_
    rintro s_ok _ _ hsteps_ok hpc_ok hrun_ok hm_ok
      ⟨rfl, hsp_ok, htr_ok, hx19_ok, hx20_ok, hx22_ok, hx25_ok, hx26_ok, hx28_ok, hx29_ok, hvregs_ok⟩
    rw [emp_sepConj] at hm_ok
    have hcrl_ok : StoreKit.LibsignalCodeRoLoaded lsmpl s_ok.mem := hcrlm.of_keepsFrozen hsteps_ok.keepsFrozen
    have hm_ok_970 : s_ok.mem ⊨
        (((s.sp + 0x970#64) ↦₆₄ w3) ∗ ((s.sp + 0x970#64 + 8#64) ↦₆₄ w4) ∗ ((s.sp + 0x970#64 + 16#64) ↦₆₄ w5)) ∗
        ((trustBaseActivePlaced ikit.id_vt A s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          memRegion (s.sp + 0x9d0#64) 24) ∗ F ∗ R') := by
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok
    have hm_ok_fold := Satisfies.mono (sepConj_mono_left
      (words3_entails_memRegion24 (s.sp + 0x970#64) w3 w4 w5)) hm_ok_970
    have hm_ok_seam : s_ok.mem ⊨
        ((trustBaseActivePlaced ikit.id_vt A s.sp x k ∗
          memRegion (s.sp + 0x470#64) 16 ∗ memRegion (s.sp + 0x580#64) 48 ∗
          memRegion (s.sp + 0x970#64) 24 ∗ memRegion (s.sp + 0x9d0#64) 24) ∗
          cliTrustPassive kit.ss_vt ikit.id_vt A ctl x sess taken otr' pqCap' pqPtr' m draws s0) ∗ R' := by
      dsimp only [F] at hm_ok_fold
      exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok_fold
    rw [← seam_mem_split_placed kit.ss_vt ikit.id_vt A ctl x sess taken otr' pqCap' pqPtr' k m draws s0 s.sp hsp] at hm_ok_seam
    rw [hsp] at hm_ok_seam
    refine SegExitPlaced.next ⟨⟨h15, htrustRel⟩, hpc_ok,
      ⟨hrun_ok, hsp_ok.trans hspm', hsp0_al,
        CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.spAligned_of_sp_eq hspm_al hsp_ok,
        by rw [hx29_ok, hx29m, hx29], by rw [hx19_ok, hx19m, hx19], hcrl_ok,
        by rw [hvregs_ok, hvregsm, hvregs]⟩,
      htr_ok.trans htrm',
      ⟨by rw [hx20_ok, hx20m, hx20], by rw [hx22_ok, hspm'],
       by rw [hx25_ok, hx25m, hx25], by rw [hx26_ok, hx26m, hx26],
       by rw [hx28_ok, hx28m, hx28]⟩,
      hpt, hrest, hloc, hnow, hstk, ?_⟩
    dsimp only [sp, draws, R'] at hm_ok_seam ⊢
    exact Eq.mp (congrArg (s_ok.mem ⊨ ·) (by ac_rfl)) hm_ok_seam

end SegTrust

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
