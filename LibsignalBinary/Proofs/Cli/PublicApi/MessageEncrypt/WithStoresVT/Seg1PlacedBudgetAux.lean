/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1Placed
public import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable `WithStoresVT` (Part 1a): `EncEnvTPlaced` and Bridges

Defines the framed budget-threaded contracts `withStoresEncPlacedSpecVT` and
`otrEncryptPlacedSpecQT`, the environment bundles `EncCalleesTPlaced`, `EncEnvTPlaced`, and
`EncTailsVTPlaced`, and restricted-kit/scope monotonicity bridges on Block `464` (`lsProg_464 H`)
under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux

open Arm64 ProofLib
open CryptoGames.LibsignalSession
  (Crypto IdentityKey OutgoingTripleRatchet SessionState)
open CryptoGames.LibsignalSessionApi
  (CiphertextMessage Session SessionRecord StoreAnswers StoreCall)
open CryptoVerification
  (LibsignalHooks LibsignalPlacement libsignalSessionLib lsmpl)
open CryptoVerification.CliRatchet.EncPlaced (lsProg_464)
open CryptoVerification.Cli.LibsignalTripleRatchet (otrEncryptName)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
  (h45_ScopeNone_placed h45_callsRel_kitF_placed h45_kitF_placed h45_kitL_placed h45_storeFinal_kitF_placed
   h45_tailModel_kitF_placed h45_traceOfWith_kitF_placed)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
  (RecordInScopeEnc StepsThroughEncrypt WithStoresEncGhost storedRecord withStoresEncStackV)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (IdentityVtablesPlacedOk SessionOnlyVtablesPlacedOk SessionStoreSpec
   extract_withLsRoCl withEnvPre_pre_elim withLsCodeRoLoaded withLsRoCl)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalTripleRatchet (OtrEncryptGhost SpqrModel)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget SeqEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE kitLoadPollPlacedSpecS
   kitStorePollPlacedSpec)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudget
  (EncCalleesPlaced EncEnvPlaced EncTailVPlaced EncTailsVPlaced PublicApiEncHooksPlaced
   SegExitPlaced otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF toTempTwinsIkitEnv toTempTwinsKitEnv
   withStoresEncPlacedSpecV withStoresEncPlacedSpecV_eq_tempTwins)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
  (SegExitBudget SpqrSendBudgetEnv WithStoresEncEnv)

export CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
  (h45_kitF_placed h45_storeFinal_kitF_placed h45_callsRel_kitF_placed h45_traceOfWith_kitF_placed)
export CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
  (h45_tailModel_kitF_placed h45_ScopeNone_placed h45_kitL_placed)

/-! ## 1. Framed Budget Contracts, `EncCalleesTPlaced`, `EncEnvTPlaced`, & `EncTailsVTPlaced` -/

/-- Relocatable budget-threaded `withStoresEncPlacedSpecV` with `64 ≤ x.rest.length` and `F`
    (e.g. `TokenInit img`) framed in `pre` and `post`. -/
def withStoresEncPlacedSpecVT [LibsignalPlacement] {M : AllocCostModel}
    (F : SepProp) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec (WithStoresEncGhost × M.σ) :=
  let base :=
    withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidParse S sendEnv encRecord
  { base with
    pre := fun (x, st_init) s =>
      ⌜64 ≤ x.rest.length⌝ ∗ F ∗ base.pre (x, st_init) s
    post := fun (x, st_init) s0 sf =>
      F ∗ base.post (x, st_init) s0 sf }

/-- Relocatable budget-threaded `OTR::encrypt::<Coins>` spec at
    `Q := (pq.length < 2^32 ∧ 64 ≤ rest.length)` with `F` framed. -/
def otrEncryptPlacedSpecQT [LibsignalPlacement] {M : AllocCostModel}
    (F : SepProp) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) :
    Spec (OtrEncryptGhost × M.σ) :=
  otrEncryptPlacedSpecQF (fun pq rest => pq.length < 2 ^ 32 ∧ 64 ≤ rest.length)
    F C A lim ctl parse S sendEnv

/-- Relocatable budget-threaded `EncCalleesPlaced` bundle with `otrEnc` using
    `otrEncryptPlacedSpecQT F`. -/
structure EncCalleesTPlaced [LibsignalPlacement] {M : AllocCostModel}
    (F : SepProp) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (H : LibsignalHooks) : Prop where
  otrFrom : subroutine_ok (lsProg_464 H) (lsmpl.base 19)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.FrameBudget.otrFromRawPlacedSpec
        M A lim))
  otrApply : subroutine_ok (lsProg_464 H) (lsmpl.base 20)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.ApplyBudget.otrApplyPlacedSpec
        M A lim))
  remoteIk : subroutine_ok (lsProg_464 H) (lsmpl.base 29)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget.remoteIdentityKeyPlacedSpec
        A.repAlloc))
  otrEnc : subroutine_ok (lsProg_464 H)
    (libsignalSessionLib.fnAddr lsmpl otrEncryptName)
    (withLsRoCl lsmpl (otrEncryptPlacedSpecQT F C A lim ctl parse S sendEnv))
  unack : subroutine_ok (lsProg_464 H) (lsmpl.base 36)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.UnackItemsBudget.unackItemsPlacedSpec
        A.repAlloc))
  kyber : subroutine_ok (lsProg_464 H) (lsmpl.base 430)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget.kyberMapSpec M A lim))
  psmNew : subroutine_ok (lsProg_464 H) (lsmpl.base 41)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget.preKeyMsgNewSpec M A lim))
  cmDrop : subroutine_ok (lsProg_464 H) (lsmpl.base 438)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget.cmDropSpec M A lim))
  dropSs : subroutine_ok (lsProg_464 H) (lsmpl.base 442)
    (withLsRoCl lsmpl
      (LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget.dropSessionStructureLocal2Spec
        M A lim))

theorem h45_otrEncryptPlacedOkQ_false [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {H : LibsignalHooks} :
    subroutine_ok (lsProg_464 H)
      (libsignalSessionLib.fnAddr lsmpl otrEncryptName)
      (withLsRoCl lsmpl (otrEncryptPlacedSpecQ (fun _ => False) C A lim ctl parse S sendEnv)) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 _hpc _hrun hpre _hal => ?_
  refine reaches_outcome.of_codeLoaded fun _hL => ?_
  have ⟨_, hp⟩ := extract_withLsRoCl hpre
  dsimp only [otrEncryptPlacedSpecQ,
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQ] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  have hp2 := hp.2
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp2
  exact False.elim hp2.1

/-- Discharge all 8 proved budget-threaded in-library callees of `EncCalleesTPlaced` from
    `PublicApiEncHooksPlaced A lim H`, leaving only `otrEnc` as an assumption. -/
theorem EncCalleesTPlaced.of_otrEnc [LibsignalPlacement] {M : AllocCostModel}
    {F : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {H : LibsignalHooks}
    (hhooks : PublicApiEncHooksPlaced A lim H)
    (hotrEnc : subroutine_ok (lsProg_464 H)
      (libsignalSessionLib.fnAddr lsmpl otrEncryptName)
      (withLsRoCl lsmpl (otrEncryptPlacedSpecQT F C A lim ctl parse S sendEnv))) :
    EncCalleesTPlaced F C A lim ctl parse S sendEnv H := by
  have hC := EncCalleesPlaced.of_otrEnc hhooks
    (h45_otrEncryptPlacedOkQ_false (C := C) (ctl := ctl) (parse := parse) (S := S) (sendEnv := sendEnv))
  exact ⟨hC.otrFrom, hC.otrApply, hC.remoteIk, hotrEnc, hC.unack, hC.kyber, hC.psmNew, hC.cmDrop,
    hC.dropSs⟩

/-- Relocatable budget-threaded `EncEnvPlaced` with `callees : EncCalleesTPlaced F`
    (`otrEncryptPlacedSpecQT F`) and `scopeQ` specialized to `s.state.pqRatchetState.length < 2 ^ 32`. -/
structure EncEnvTPlaced [LibsignalPlacement] {M : AllocCostModel}
    (F : SepProp) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (_ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop where
  hooks : PublicApiEncHooksPlaced A lim H
  kitOk : SessionOnlyKitPlacedOkSE A lim kit kitEnv Scope encRecord H
  ikitOk : IdentityStoreKitPlacedOkI A lim ikit ikitEnv H
  callees : EncCalleesTPlaced F C A lim ctl parse S sendEnv H
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

/-- Session-kit/scope-polymorphic bundle of all 9 shared error/result tail contracts on `lsProg_464 H`
    (satisfied uniformly once `TailsPlacedBudget` discharges `EncTailsVPlaced` from `hEnv.hooks`). -/
abbrev EncTailsVTPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  ∀ {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState} {Scope : SessionRecord (List (BitVec 8)) → Prop},
    EncTailsVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H

/-! ## 2. Restricted-Kit / Scope Monotonicity & `SegExitPlaced` Bridges -/

@[reducible] def h45_kitEnvF {A : RustAlloc} {b : BitVec 64} {kit : SessionStoreSpec A b}
    (kitEnv : SessionStoreBudgetEnv kit) : SessionStoreBudgetEnv (h45_kitF_placed kit) where
  loadPollEnv := kitEnv.loadPollEnv
  storePollEnv := kitEnv.storePollEnv

@[reducible] def h45_kitEnvL {A : RustAlloc} {b : BitVec 64} {kit : SessionStoreSpec A b}
    (kitEnv : SessionStoreBudgetEnv kit) : SessionStoreBudgetEnv (h45_kitL_placed kit) where
  loadPollEnv := kitEnv.loadPollEnv
  storePollEnv := kitEnv.storePollEnv

private theorem seqEnv_mono_right {E₁ E₂ E₂' : List AllocEvent → Prop}
    (h : ∀ evs, E₂ evs → E₂' evs) {evs : List AllocEvent} :
    SeqEnv E₁ E₂ evs → SeqEnv E₁ E₂' evs
  | Or.inl h1 => Or.inl h1
  | Or.inr ⟨e1, e2, heq, h1, h2⟩ => Or.inr ⟨e1, e2, heq, h1, h e2 h2⟩

theorem h45_withStoresEncEnv_kitF {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) (parse : UuidParser)
    (x : WithStoresEncGhost) :
    WithStoresEncEnv (h45_kitF_placed kit) (toTempTwinsKitEnv (h45_kitEnvF kitEnv)) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C S sendEnv parse x =
    WithStoresEncEnv kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C S sendEnv parse x :=
  rfl

theorem h45_withStoresEncEnv_mono_scope {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64}
    {kitEnv : LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64}
    {ikitEnv : LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    {Scope Scope' : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv} {parse : UuidParser}
    {x : WithStoresEncGhost} {evs : List AllocEvent}
    (himp : ∀ r, Scope' r → Scope r)
    (h : WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope' C S sendEnv parse x evs) :
    WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv parse x evs := by
  refine seqEnv_mono_right (fun _ h2 => ?_) h
  rcases h2 with hfree | hclone | hrest
  · exact Or.inl hfree
  · exact Or.inr (Or.inl hclone)
  · refine Or.inr (Or.inr (seqEnv_mono_right (fun _ h4 => ?_) hrest))
    rcases h4 with hfree' | ⟨r, sess, otr, taken, ⟨hsc, hl⟩, hcur, hfrom, hotr⟩
    · exact Or.inl hfree'
    · exact Or.inr ⟨r, sess, otr, taken, ⟨himp r hsc, hl⟩, hcur, hfrom, hotr⟩

theorem h45_withStoresEncEnv_kitL {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope Scope' : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv} {parse : UuidParser}
    {x : WithStoresEncGhost} {evs : List AllocEvent}
    (h : WithStoresEncEnv (h45_kitL_placed kit) (toTempTwinsKitEnv (h45_kitEnvL kitEnv)) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope' C S sendEnv parse x evs) :
    WithStoresEncEnv kit (toTempTwinsKitEnv kitEnv) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope C S sendEnv parse x evs := by
  refine seqEnv_mono_right (fun _ h2 => ?_) h
  rcases h2 with hfree | hclone | hrest
  · exact Or.inl hfree
  · exact Or.inr (Or.inl hclone)
  · refine Or.inr (Or.inr (seqEnv_mono_right (fun _ h4 => ?_) hrest))
    rcases h4 with hfree' | ⟨_, _, _, _, ⟨_, hfalse⟩, _, _, _⟩
    · exact Or.inl hfree'
    · exact False.elim hfalse

theorem h45_subroutineOutcome_kitF_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (st_init : M.σ) (R0 : SepProp) (s0 sf : State) :
    SubroutineOutcome
      (withStoresEncPlacedSpecV A lim (h45_kitF_placed kit) (h45_kitEnvF kitEnv) st0
        ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord) (x, st_init) R0 s0 sf =
    SubroutineOutcome
      (withStoresEncPlacedSpecV A lim kit kitEnv st0
        ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord) (x, st_init) R0 s0 sf := by
  have hpost :
      (withStoresEncPlacedSpecV A lim (h45_kitF_placed kit) (h45_kitEnvF kitEnv) st0
        ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord).post =
      (withStoresEncPlacedSpecV A lim kit kitEnv st0
        ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord).post := by
    funext ⟨x', st'⟩ s0' sf'
    dsimp only [withStoresEncPlacedSpecV, withLsCodeRoLoaded]
    refine congrArg sepExists (funext fun answers => congrArg sepExists (funext fun evs => ?_))
    rw [h45_callsRel_kitF_placed, h45_storeFinal_kitF_placed]
    rfl
  unfold SubroutineOutcome
  rw [hpost]
  rfl

theorem h45_segExit_kitF_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (x : WithStoresEncGhost) (st_init : M.σ) (R0 : SepProp) (s0 s : State)
    (next : State → Prop) :
    SegExitPlaced A lim (h45_kitF_placed kit) (h45_kitEnvF kitEnv) st0 ikit ikitEnv ist0 Scope
      C ctl parse S sendEnv encRecord H x st_init R0 s0 s next =
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
      C ctl parse S sendEnv encRecord H x st_init R0 s0 s next := by
  simp only [SegExitPlaced, h45_subroutineOutcome_kitF_placed]

theorem h45_encTailV_kitF_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (x : WithStoresEncGhost) (st_init st : M.σ) (ans : StoreAnswers (List (BitVec 8)) Unit)
    (pc : BitVec 64) (regs : BitVec 64 → State → Prop) (slots : BitVec 64 → SepProp)
    (R0 : SepProp) (s0 s : State) :
    EncTailVPlaced A lim (h45_kitF_placed kit) (h45_kitEnvF kitEnv) st0 ikit ikitEnv ist0 Scope
      C ctl parse S sendEnv x st_init st ans pc regs slots R0 s0 s =
    EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
      C ctl parse S sendEnv x st_init st ans pc regs slots R0 s0 s := by
  have h1 :
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.EncTailVPlaced
        (LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore
          (A' := A.atState lim st s) (h45_kitF_placed kit)) st0
        (LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore
          (A' := A.atState lim st s) ikit) ist0 C ctl parse S x ans pc regs slots R0 s0 s =
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails.EncTailVPlaced
        (LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore
          (A' := A.atState lim st s) kit) st0
        (LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore
          (A' := A.atState lim st s) ikit) ist0 C ctl parse S x ans pc regs slots R0 s0 s :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.h45_encTailV_kitF_placed
      (LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.retagSessionStore
        (A' := A.atState lim st s) kit) st0
      (LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.retagIdentityStore
        (A' := A.atState lim st s) ikit) ist0 C ctl parse S x ans pc regs slots R0 s0 s
  unfold EncTailVPlaced
  rw [h45_withStoresEncEnv_kitF, h1]

theorem h45_subroutineOutcome_mono_scope_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope Scope' : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {st_init : M.σ} {R0 : SepProp} {s0 sf : State}
    (himp : ∀ r, Scope' r → Scope r)
    (h : SubroutineOutcome
      (withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope'
        C ctl parse S sendEnv encRecord) (x, st_init) R0 s0 sf) :
    SubroutineOutcome
      (withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl parse S sendEnv encRecord) (x, st_init) R0 s0 sf := by
  rcases h with ⟨hret, hcs, hpost⟩ | ⟨hpan, honp⟩ | ⟨code, hexit, honex⟩ | ⟨hoom, honoom⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [withStoresEncPlacedSpecV, withLsCodeRoLoaded] at hpost ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨answers, evs, ⟨hnp, hcr, hicr, htr, henv⟩, hmem⟩
    exact ⟨answers, evs,
      ⟨hnp, hcr, hicr, htr, h45_withStoresEncEnv_mono_scope himp henv⟩, hmem⟩
  · exact Or.inr (Or.inl ⟨hpan, honp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hexit, honex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, honoom⟩))

theorem h45_segExit_mono_scope_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope Scope' : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R0 : SepProp} {s0 s : State}
    {next : State → Prop}
    (himp : ∀ r, Scope' r → Scope r)
    (h : SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope'
      C ctl parse S sendEnv encRecord H x st_init R0 s0 s next) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
      C ctl parse S sendEnv encRecord H x st_init R0 s0 s next := by
  intro hL
  obtain ⟨sf, hsteps, hnext | hout⟩ := h hL
  · exact ⟨sf, hsteps, Or.inl hnext⟩
  · exact ⟨sf, hsteps, Or.inr (h45_subroutineOutcome_mono_scope_placed himp hout)⟩

private theorem storeFinal_kitL {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (h45_kitL_placed kit).storeFinal st0 ans calls = kit.storeFinal st0 ans calls := by
  induction calls generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> exact ih _

private theorem callsRel_kitL_imp {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (h45_kitL_placed kit).callsRel st0 ans calls → kit.callsRel st0 ans calls := by
  induction calls with
  | nil => exact id
  | cons c cs ih =>
    cases c with
    | loadSession _ => intro h; exact False.elim h.1
    | isTrustedIdentity _ _ _ => exact ih
    | saveIdentity _ _ => exact ih
    | storeSession _ _ => intro ⟨h1, h2⟩; exact ⟨h1, ih h2⟩

theorem h45_subroutineOutcome_kitL_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope Scope' : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {st_init : M.σ} {R0 : SepProp} {s0 sf : State}
    (h : SubroutineOutcome
      (withStoresEncPlacedSpecV A lim (h45_kitL_placed kit) (h45_kitEnvL kitEnv) st0
        ikit ikitEnv ist0 Scope' C ctl parse S sendEnv encRecord) (x, st_init) R0 s0 sf) :
    SubroutineOutcome
      (withStoresEncPlacedSpecV A lim kit kitEnv st0
        ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord) (x, st_init) R0 s0 sf := by
  rcases h with ⟨hret, hcs, hpost⟩ | ⟨hpan, honp⟩ | ⟨code, hexit, honex⟩ | ⟨hoom, honoom⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [withStoresEncPlacedSpecV, withLsCodeRoLoaded] at hpost ⊢
    simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc,
      satisfies_pure_sepConj] at hpost ⊢
    rcases hpost with ⟨answers, evs, ⟨hnp, hcr, hicr, htr, henv⟩, hmem⟩
    have hsf := storeFinal_kitL kit st0 answers (x.model C S parse answers).2
    have htr_eq :
        ikit.traceOfWith (h45_kitL_placed kit) encRecord answers (x.model C S parse answers).2 =
        ikit.traceOfWith kit encRecord answers (x.model C S parse answers).2 := rfl
    have hstk_eq : withStoresEncStackV (h45_kitL_placed kit) ikit = withStoresEncStackV kit ikit := rfl
    rw [htr_eq] at htr
    dsimp only [h45_kitL_placed] at hmem
    rw [hsf, hstk_eq] at hmem
    exact ⟨answers, evs,
      ⟨hnp, callsRel_kitL_imp kit st0 answers _ hcr, hicr, htr, h45_withStoresEncEnv_kitL henv⟩,
      hmem⟩
  · dsimp only [withStoresEncPlacedSpecV, withLsCodeRoLoaded, h45_kitL_placed] at honp
    rw [sepConj_assoc, satisfies_pure_sepConj] at honp
    rcases honp.1.2 with ⟨_, hfalse, _⟩
    exact False.elim hfalse
  · exact Or.inr (Or.inr (Or.inl ⟨code, hexit, honex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, honoom⟩))

theorem h45_segExit_kitL_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope Scope' : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R0 : SepProp} {s0 s : State}
    {next : State → Prop}
    (h : SegExitPlaced A lim (h45_kitL_placed kit) (h45_kitEnvL kitEnv) st0 ikit ikitEnv ist0 Scope'
      C ctl parse S sendEnv encRecord H x st_init R0 s0 s next) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
      C ctl parse S sendEnv encRecord H x st_init R0 s0 s next := by
  intro hL
  obtain ⟨sf, hsteps, hnext | hout⟩ := h hL
  · exact ⟨sf, hsteps, Or.inl hnext⟩
  · exact ⟨sf, hsteps, Or.inr (h45_subroutineOutcome_kitL_placed hout)⟩

theorem h45_segExit_of_tempTwins_kitF_scope [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope Scope' : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R0 : SepProp}
    {s0 s : State} {mid next : State → Prop}
    (himp : ∀ r, Scope' r → Scope r)
    (h1 : SegExitBudget A lim (h45_kitF_placed kit) (toTempTwinsKitEnv (h45_kitEnvF kitEnv)) st0
      ikit (toTempTwinsIkitEnv ikitEnv) ist0 Scope' C ctl parse S sendEnv encRecord Hk
      x st_init R0 s0 s mid)
    (h2 : ∀ sm, Steps (lsProg_464 Hk) s sm → mid sm →
      SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
        x st_init R0 s0 sm next) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps1, hmid | hout⟩ := h1 hL
  · obtain ⟨sf, hsteps2, hout2⟩ := h2 sm hsteps1 hmid (hsteps1.codeLoaded hL)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · refine ⟨sm, hsteps1, Or.inr ?_⟩
    rw [← withStoresEncPlacedSpecV_eq_tempTwins] at hout
    rw [h45_subroutineOutcome_kitF_placed] at hout
    exact h45_subroutineOutcome_mono_scope_placed himp hout

theorem h45_envF_placed [LibsignalPlacement] {M : AllocCostModel}
    {F : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvTPlaced F A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord H) :
    EncEnvPlaced A lim (h45_kitF_placed kit) (h45_kitEnvF kitEnv) st0 ikit ikitEnv ist0
      (fun _ => False) (fun _ => False) C ctl uuidTryParse S sendEnv encRecord H where
  hooks := hEnv.hooks
  kitOk := {
    loadShim := hEnv.kitOk.loadShim
    loadPoll := by
      intro callerProg callerBlk _ _hblk
      refine subroutine_ok_outcome_intro fun (x, self, st0', st) R s0 _hpc _hrun hpre _hal => ?_
      refine reaches_outcome.of_codeLoaded fun _hL => ?_
      have ⟨_, hp⟩ := extract_withLsRoCl hpre
      obtain ⟨_, hp2⟩ := withEnvPre_pre_elim hp
      dsimp only [kitLoadPollPlacedSpecS, h45_kitF_placed] at hp2
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp2
      exact False.elim hp2.1.2.2.1
    loadFutDrop := hEnv.kitOk.loadFutDrop
    storeShim := hEnv.kitOk.storeShim
    storePoll := by
      intro callerProg callerBlk _ _hblk
      refine subroutine_ok_outcome_intro fun (x, self, st0', st) R s0 _hpc _hrun hpre _hal => ?_
      refine reaches_outcome.of_codeLoaded fun _hL => ?_
      have ⟨_, hp⟩ := extract_withLsRoCl hpre
      obtain ⟨_, hp2⟩ := withEnvPre_pre_elim hp
      dsimp only [kitStorePollPlacedSpec, h45_kitF_placed] at hp2
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp2
      exact False.elim hp2.1.2.2.2.1
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

theorem h45_subroutineOutcome_vt_of_v_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : SepProp}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {uuidParse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome
      (withStoresEncPlacedSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidParse S sendEnv encRecord)
      (x, st_init) (F ∗ R) s0 sf) :
    SubroutineOutcome
      (withStoresEncPlacedSpecVT F A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidParse S sendEnv encRecord)
      (x, st_init) R s0 sf := by
  rcases h with ⟨h1, hcs, hpost⟩ | ⟨hpan, honp⟩ | ⟨code, hexit, honex⟩ | ⟨_hoom, honoom⟩
  · refine Or.inl ⟨h1, hcs, ?_⟩
    dsimp only [withStoresEncPlacedSpecVT]
    refine Satisfies.mono ?_ hpost
    exact Entails.of_eq (by sep_ac_rfl)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withStoresEncPlacedSpecVT, withStoresEncPlacedSpecV, withLsCodeRoLoaded] at honp ⊢
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

theorem h45_envNone_placed [LibsignalPlacement] {M : AllocCostModel}
    {F : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvTPlaced F A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord H) :
    EncEnvPlaced A lim (h45_kitF_placed kit) (h45_kitEnvF kitEnv) st0 ikit ikitEnv ist0
      (h45_ScopeNone_placed Scope) (fun _ => False) C ctl uuidTryParse S sendEnv encRecord H :=
  { h45_envF_placed hEnv with
    kitOk := {
      (h45_envF_placed hEnv).kitOk with
      loadPoll := by
        intro callerProg callerBlk _ _hblk
        refine subroutine_ok_outcome_intro fun (x, self, st0', st) R s0 _hpc _hrun hpre _hal => ?_
        refine reaches_outcome.of_codeLoaded fun _hL => ?_
        have ⟨_, hp⟩ := extract_withLsRoCl hpre
        obtain ⟨_, hp2⟩ := withEnvPre_pre_elim hp
        dsimp only [kitLoadPollPlacedSpecS, h45_kitF_placed] at hp2
        rw [sepConj_assoc, satisfies_pure_sepConj] at hp2
        exact False.elim hp2.1.2.2.1
    }
    scopeIn := fun r h => hEnv.scopeIn r ⟨h.1.1, h.2⟩
    scopeQ := fun _ _ h hs => by rw [h.1.2] at hs; cases hs
    recOk := fun h => by have hnone := h.2.1.1.2; rw [h.1] at hnone; cases hnone }

theorem h45_envL_placed [LibsignalPlacement] {M : AllocCostModel}
    {F : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvTPlaced F A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord H) :
    EncEnvPlaced A lim (h45_kitL_placed kit) (h45_kitEnvL kitEnv) st0 ikit ikitEnv ist0
      Scope (fun _ => False) C ctl uuidTryParse S sendEnv encRecord H where
  hooks := hEnv.hooks
  kitOk := {
    loadShim := hEnv.kitOk.loadShim
    loadPoll := by
      intro callerProg callerBlk _ _hblk
      refine subroutine_ok_outcome_intro fun (x, self, st0', st) R s0 _hpc _hrun hpre _hal => ?_
      refine reaches_outcome.of_codeLoaded fun _hL => ?_
      have ⟨_, hp⟩ := extract_withLsRoCl hpre
      obtain ⟨_, hp2⟩ := withEnvPre_pre_elim hp
      dsimp only [kitLoadPollPlacedSpecS, h45_kitL_placed] at hp2
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp2
      exact False.elim hp2.1.2.2.1
    loadFutDrop := hEnv.kitOk.loadFutDrop
    storeShim := hEnv.kitOk.storeShim
    storePoll := by
      intro callerProg callerBlk _ _hblk
      refine subroutine_ok_outcome_intro fun (x, self, st0', st) R s0 _hpc _hrun hpre _hal => ?_
      refine reaches_outcome.of_codeLoaded fun _hL => ?_
      have ⟨_, hp⟩ := extract_withLsRoCl hpre
      obtain ⟨_, hp2⟩ := withEnvPre_pre_elim hp
      dsimp only [kitStorePollPlacedSpec, h45_kitL_placed] at hp2
      rw [sepConj_assoc, satisfies_pure_sepConj] at hp2
      exact False.elim hp2.1.2.2.2.1
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

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg1PlacedBudgetAux
