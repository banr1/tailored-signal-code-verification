/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.Seg.SegDispatchAuxPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.SessionOnlyKitEPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefs
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `WithStoresVT` Foundations (`ExtDefsPlaced`)

Relocatable (`[LibsignalPlacement]`) filesystem carrier and weak-precondition (`RecordInScopeP`)
hypothesis bundle on `lsProg_463 H`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open CryptoVerification.RustHeap CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced withStoresDecPlacedSpecVX withStoresDecPlacedSpecV_eq_VX DecSegVXPlaced DecSegVPlaced_eq_VX decSegVXPlaced_chain
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegDispatch (allocFailedIn_trans')

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Filesystem invariant carrier for `decrypt_signal` on `lsProg_463 H`. -/
abbrev DecFsCtxExtPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (H : LibsignalHooks) (s0 s : State) : Prop :=
  DecFsCtxPlaced kit ikit H s0 s

/-- Relocatable hypothesis bundle for `MessageDecrypt` segments on `lsProg_463 H` under `RecordInScopeP`. -/
structure DecHypsExtPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (ss : SessionStoreSpec A 0#64)
    (id : IdentityStoreSpec A 0#64)
    (st0 : ss.StoreState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop where
  hooks : PublicApiDecHooksPlaced A H
  kit : SessionOnlyKitPlacedOkSE ss Scope encRecord H
  ikit : IdentityStoreKitPlacedOkI id H
  scopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r
  recOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
    ss.addrOk x.rem.val →
    ss.ScopeAt Scope st0 x.rem.val rec →
    decryptRecord C S parse x rec = .ok (pt, rec') →
    ss.RecOk rec'

/-- Weakens `DecHypsVPlaced` to `DecHypsExtPlaced`. -/
theorem DecHypsExtPlaced.of_vPlaced [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {ss : SessionStoreSpec A 0#64}
    {id : IdentityStoreSpec A 0#64}
    {st0 : ss.StoreState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (h : DecHypsVPlaced C A parse S encRecord H ss id Scope) :
    DecHypsExtPlaced C A parse S encRecord H ss id st0 Scope where
  hooks := h.hooks
  kit := h.kit
  ikit := h.ikit
  scopeInP r hr := CryptoVerification.E2E.RecordX.recordInScopeP_of_recordInScope (h.scopeIn r hr)
  recOk x rec pt rec' _ hsc hdec := h.recOk x st0 rec rec' pt hsc hdec

theorem decSegVXPlaced_of_sepWPp [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (lsProg_463 H) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Out sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (withStoresDecPlacedSpecVX
          C A ctl parse S encRecord kit ikit st0 ist0 Scope Extra).onPanic x s0 sf ∗ R))) :
    DecSegVXPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope Extra x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hOut⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hOut hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hqp hmf⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem decSegVXPlaced_of_sepWP_mid [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {mid : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (lsProg_463 H) mid s P
      (fun sm Pm => StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → (sm.mem ⊨ Pm ∗ R) →
        DecSegVXPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope Extra x R s0 sm Out)) :
    DecSegVXPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope Extra x R s0 s Out := by
  intro hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hmm, hnext⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ := hnext (hcrl.of_keepsFrozen hsteps.keepsFrozen) hmm (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem decSegVXPlaced_of_sepWP_done [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {Out : State → Prop}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (lsProg_463 H) target s P
      (fun sf P_f => StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem → (sf.mem ⊨ P_f ∗ R) → Out sf)) :
    DecSegVXPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope Extra x R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, ⟨_, _, P_f, hmf, hOut⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  exact ⟨sf, hsteps, Or.inl (hOut (hcrl.of_keepsFrozen hsteps.keepsFrozen) hmf)⟩

theorem DecSegVXPlaced.mono_extra [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra1 Extra2 : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s : State} {Out : State → Prop}
    (himp : ∀ ans, Extra1 x ans → Extra2 x ans)
    (h : DecSegVXPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope Extra1 x R s0 s Out) :
    DecSegVXPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope Extra2 x R s0 s Out := by
  intro hL
  obtain ⟨s', hsteps, hOut | hSub⟩ := h hL
  · exact ⟨s', hsteps, Or.inl hOut⟩
  · refine ⟨s', hsteps, Or.inr ?_⟩
    rcases hSub with hRet | ⟨hpan, hmf⟩ | hExit | hOom
    · exact Or.inl hRet
    · refine Or.inr (Or.inl ⟨hpan, Satisfies.mono (sepConj_mono_left ?_) hmf⟩)
      dsimp only [withStoresDecPlacedSpecVX, StoreKit.withLsCodeRoLoaded]
      apply Entails.pure_left
      rintro ⟨hpref, halloc | ⟨ans, hrel, hlpref, hmod | hex⟩⟩
      · exact Entails.pure_right ⟨hpref, Or.inl halloc⟩ (Entails.refl _)
      · exact Entails.pure_right ⟨hpref, Or.inr ⟨ans, hrel, hlpref, Or.inl hmod⟩⟩ (Entails.refl _)
      · exact Entails.pure_right ⟨hpref, Or.inr ⟨ans, hrel, hlpref, Or.inr (himp ans hex)⟩⟩ (Entails.refl _)
    · exact Or.inr (Or.inr (Or.inl hExit))
    · exact Or.inr (Or.inr (Or.inr hOom))

theorem loadShim_onPanic_entailsVX_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {s0 s sf : State} {F : SepProp}
    (htr : s.trace = s0.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      (withStoresDecPlacedSpecVX
        C A ctl parse S encRecord kit ikit st0 ist0 Scope Extra).onPanic x s0 sf := by
  dsimp only [withStoresDecPlacedSpecVX, StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  unfold allocFailedIn at halloc ⊢
  rw [htr] at halloc hpref
  exact Entails.pure_right ⟨hpref, Or.inl halloc⟩ (entails_anyHeap _)

theorem stringClone_onPanic_entailsVX_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {s0 s sf : State} {F : SepProp}
    (h0s : s0.trace <+: s.trace) :
    (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F ⊢
      (withStoresDecPlacedSpecVX
        C A ctl parse S encRecord kit ikit st0 ist0 Scope Extra).onPanic x s0 sf := by
  dsimp only [withStoresDecPlacedSpecVX, StoreKit.withLsCodeRoLoaded]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨halloc, hpref⟩ => ?_
  exact Entails.pure_right ⟨h0s.trans hpref, Or.inl (allocFailedIn_trans' h0s halloc)⟩
    (entails_anyHeap _)

theorem panic_outcome_of_allocFailedInVX_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 s sf : State}
    (htr0 : s0.trace <+: s.trace)
    (hpan : sf.status = .Panicked)
    (hm : sf.mem ⊨ (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R) :
    SubroutineOutcome (withStoresDecPlacedSpecVX
      C A ctl parse S encRecord kit ikit st0 ist0 Scope Extra) x R s0 sf := by
  refine Or.inr (Or.inl ⟨hpan, ?_⟩)
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  unfold withStoresDecPlacedSpecVX StoreKit.withLsCodeRoLoaded
  dsimp only
  apply Entails.pure_left
  rintro ⟨haf, htr⟩
  have haf0 : allocFailedIn s0 sf := by
    obtain ⟨t, ht⟩ := htr0
    unfold allocFailedIn at haf ⊢
    rw [← ht, List.length_append, ← List.drop_drop] at haf
    exact List.mem_of_mem_drop haf
  refine Entails.pure_right ⟨htr0.trans htr, Or.inl haf0⟩ (Entails.refl _)

end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt.WithStoresVT
