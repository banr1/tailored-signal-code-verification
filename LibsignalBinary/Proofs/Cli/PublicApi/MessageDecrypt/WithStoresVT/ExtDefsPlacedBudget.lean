/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlaced

/-!
# Budget-Threaded Relocatable `WithStoresVT` Foundations (`ExtDefsPlacedBudget`)

Budget-threaded (`RustCliAllocBudget M`) relocatable filesystem carrier and weak-precondition
(`RecordInScopeP`) hypothesis bundle on `lsProg_463 H`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalHooks LibsignalPlacement lsmpl)
open CryptoVerification.CliRatchet.DecPlaced (lsProg_463)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoGames.LibsignalSession (Crypto)
open CryptoGames.LibsignalSessionApi (SessionRecord StoreAnswers)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (decryptRecord)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (LibsignalCodeRoLoaded SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt (DecFsCtxPlaced)
open LibsignalBinary.Heap (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget (SessionStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget (IdentityStoreBudgetEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
  (IdentityStoreKitPlacedOkI SessionOnlyKitPlacedOkSE)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsPlacedBudget
  (DecHypsVPlaced PublicApiDecHooksPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.DefsVXPlacedBudget
  (DecSegVXPlaced withStoresDecPlacedSpecVX)

/-- Filesystem invariant carrier for `decrypt_signal` on `lsProg_463 H`. -/
abbrev DecFsCtxExtPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (H : LibsignalHooks) (s0 s : State) : Prop :=
  DecFsCtxPlaced kit ikit H s0 s

/-- Budget-threaded relocatable hypothesis bundle for `MessageDecrypt` segments on `lsProg_463 H` under `RecordInScopeP`. -/
structure DecHypsExtPlaced [LibsignalPlacement] {M : AllocCostModel} (C : Crypto)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (ss : SessionStoreSpec A.repAlloc 0#64) (ssEnv : SessionStoreBudgetEnv ss)
    (id : IdentityStoreSpec A.repAlloc 0#64) (idEnv : IdentityStoreBudgetEnv id)
    (st0 : ss.StoreState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop where
  hooks : PublicApiDecHooksPlaced A lim H
  kit : SessionOnlyKitPlacedOkSE A lim ss ssEnv Scope encRecord H
  ikit : IdentityStoreKitPlacedOkI A lim id idEnv H
  scopeInP : ∀ r, Scope r → CryptoVerification.E2E.RecordX.RecordInScopeP r
  recOk : ∀ (x : DecryptGhost) (rec : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)) (rec' : SessionRecord (List (BitVec 8))),
    ss.addrOk x.rem.val →
    ss.ScopeAt Scope st0 x.rem.val rec →
    decryptRecord C S parse x rec = .ok (pt, rec') →
    ss.RecOk rec'

/-- Weakens `DecHypsVPlaced` to `DecHypsExtPlaced`. -/
theorem DecHypsExtPlaced.of_vPlaced [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {parse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {ss : SessionStoreSpec A.repAlloc 0#64} {ssEnv : SessionStoreBudgetEnv ss}
    {id : IdentityStoreSpec A.repAlloc 0#64} {idEnv : IdentityStoreBudgetEnv id}
    {st0 : ss.StoreState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (h : DecHypsVPlaced C A lim parse S encRecord H ss ssEnv id idEnv Scope) :
    DecHypsExtPlaced C A lim parse S encRecord H ss ssEnv id idEnv st0 Scope where
  hooks := h.hooks
  kit := h.kit
  ikit := h.ikit
  scopeInP r hr := CryptoVerification.E2E.RecordX.recordInScopeP_of_recordInScope (h.scopeIn r hr)
  recOk x rec pt rec' _ hsc hdec := h.recOk x st0 rec rec' pt hsc hdec

theorem decSegVXPlaced_of_sepWPp [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s : State} {target : BitVec 64}
    {P : SepProp} {Out : State → Prop}
    (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWPp (lsProg_463 H) target s P
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → Out sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (withStoresDecPlacedSpecVX
          C A lim ctl parse S tdEnv encRecord kit kitEnv ikit ikitEnv st0 ist0 Scope Extra).onPanic
          (x, st_init) s0 sf ∗ R))) :
    DecSegVXPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv
      st0 ist0 Scope Extra x st_init R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := hwp R hm hL
  rcases hout with ⟨_, _, P_f, hmf, hOut⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hOut hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hqp hmf⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem decSegVXPlaced_of_sepWP_mid [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s : State} {mid : BitVec 64}
    {P : SepProp} {Out : State → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (lsProg_463 H) mid s P
      (fun sm Pm => LibsignalCodeRoLoaded lsmpl sm.mem → (sm.mem ⊨ Pm ∗ R) →
        DecSegVXPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv
          st0 ist0 Scope Extra x st_init R s0 sm Out)) :
    DecSegVXPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv
      st0 ist0 Scope Extra x st_init R s0 s Out := by
  intro hL
  obtain ⟨sm, hsteps, ⟨_, _, Pm, hmm, hnext⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ :=
    hnext (hcrl.of_keepsFrozen hsteps.keepsFrozen) hmm (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem decSegVXPlaced_of_sepWP_done [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s : State} {target : BitVec 64}
    {P : SepProp} {Out : State → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (hm : s.mem ⊨ P ∗ R)
    (hwp : SepWP (lsProg_463 H) target s P
      (fun sf P_f => LibsignalCodeRoLoaded lsmpl sf.mem → (sf.mem ⊨ P_f ∗ R) → Out sf)) :
    DecSegVXPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv
      st0 ist0 Scope Extra x st_init R s0 s Out := by
  intro hL
  obtain ⟨sf, hsteps, ⟨_, _, P_f, hmf, hOut⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  exact ⟨sf, hsteps, Or.inl (hOut (hcrl.of_keepsFrozen hsteps.keepsFrozen) hmf)⟩

theorem DecSegVXPlaced.mono_extra [LibsignalPlacement] {M : AllocCostModel} {C : Crypto}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Extra1 Extra2 : DecryptGhost → StoreAnswers (List (BitVec 8)) Unit → Prop}
    {x : DecryptGhost} {st_init : M.σ} {R : SepProp} {s0 s : State} {Out : State → Prop}
    (himp : ∀ ans, Extra1 x ans → Extra2 x ans)
    (h : DecSegVXPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv
      st0 ist0 Scope Extra1 x st_init R s0 s Out) :
    DecSegVXPlaced C A lim ctl parse S tdEnv encRecord H kit kitEnv ikit ikitEnv
      st0 ist0 Scope Extra2 x st_init R s0 s Out := by
  intro hL
  obtain ⟨s', hsteps, hOut | hSub⟩ := h hL
  · exact ⟨s', hsteps, Or.inl hOut⟩
  · refine ⟨s', hsteps, Or.inr ?_⟩
    rcases hSub with hRet | ⟨hpan, hmf⟩ | hExit | hOom
    · exact Or.inl hRet
    · refine Or.inr (Or.inl ⟨hpan, Satisfies.mono (sepConj_mono_left ?_) hmf⟩)
      dsimp only [withStoresDecPlacedSpecVX]
      apply Entails.pure_left
      rintro ⟨hpref, ans, hrel, hlpref, hmod | hex⟩
      · exact Entails.pure_right ⟨hpref, ⟨ans, hrel, hlpref, Or.inl hmod⟩⟩ (Entails.refl _)
      · exact Entails.pure_right ⟨hpref, ⟨ans, hrel, hlpref, Or.inr (himp ans hex)⟩⟩ (Entails.refl _)
    · exact Or.inr (Or.inr (Or.inl hExit))
    · exact Or.inr (Or.inr (Or.inr hOom))

theorem false_onPanic_entails {P Q : SepProp} : ⌜False⌝ ∗ P ⊢ Q :=
  Entails.pure_left False.elim

end LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.WithStoresVT.ExtDefsPlacedBudget
