/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget

/-!
# W2 `try_decrypt_from_record` and `WithStoresDecEnv` Credit Bridges

Parametric `(M : AllocCostModel) [HasFineReallocCredit M]` `PhaseCreditSpec` bounds in binary execution
order for `try_decrypt_from_record` seam envelopes (`SegTailEnv` through `RecordDecryptEnv`), store-step
envelopes, and the `Scope`-guarded `WithStoresDecEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W2DecryptRecordStorePeak

open CryptoGames.LibsignalSession (Crypto IdentityKey SessionState)
open CryptoGames.LibsignalSessionApi (Direction Session SessionRecord)
open CryptoVerification.LibsignalPublicApi (DecryptGhost)
open CryptoVerification.LibsignalPublicApi.MessageDecrypt (decryptRecord recGhostOf)
open CryptoVerification.LibsignalPublicApi.StoreKit (SessionStoreSpec)
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity (IdentityStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal)
open CryptoVerification.LibsignalSessionRepr (VecGhost)
open CryptoVerification.LibsignalTripleRatchet (RecordDecryptGhost SpqrModel)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost UuidParser)
open CryptoVerification.RustHeap (RustAlloc)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ModelHyps PhaseCreditSpec stepEvents_freeOnly_le)
open LibsignalBinary.Proofs.PublicApi.MessageDecrypt.DefsBudget
  (FromKeyReadyEnv FromLoadPolledEnv FromPostSomeEnv FromRegionNoneEnv FromRegionSomeEnv
   FromStoreCallEnv FromTrustedFalseEnv FromTrustedTrueEnv LoadPollStepEnv
   SessionGhostValid WithStoresDecEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv SaveStepEnv TrustStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (SessionStoreBudgetEnv StoreStepEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (GrowOneSpeEnv)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
  (FromFEnv FromMEnv FromVEnv FromVPostTdEnv RecordDecryptEnv SegCloneEnv SegTailEnv
   TryDecryptEnvArgs recordTryDecryptEnvArgs)

/-! ## 1. Guarded Existential Combinator and Leaf Envelopes -/

theorem phaseCreditSpec_exists_guarded {α : Sort _} {M : AllocCostModel} [HasFineReallocCredit M]
    {P : α → Prop} {E : α → List AllocEvent → Prop} {c l p r : Nat}
    (h : ∀ a, P a → PhaseCreditSpec M (E a) c l p r) :
    PhaseCreditSpec M (fun evs => ∃ a, P a ∧ E a evs) c l p r where
  req_align evs := fun ⟨a, ha, hevs⟩ => (h a ha).req_align evs hevs
  credit_le st0 {_} := fun ⟨a, ha, hevs⟩ => (h a ha).credit_le st0 hevs

/-- Appends a trailing `FreeOnlyEvs` sequence while preserving `(c, l, p, r)` without requiring `l ≤ p`.
-/
theorem phaseCreditSpec_seq_freeOnly {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E₁ E₂ : List AllocEvent → Prop} {c l p r : Nat}
    (h₁ : PhaseCreditSpec M E₁ c l p r)
    (h₂ : ∀ evs, E₂ evs → FreeOnlyEvs evs) :
    PhaseCreditSpec M (SeqEnv E₁ E₂) c l p r where
  req_align evs hseq ev hev := by
    rcases hseq with he₁ | ⟨e₁, e₂, rfl, he₁, he₂⟩
    · exact h₁.req_align evs he₁ ev hev
    · rcases List.mem_append.mp hev with hev₁ | hev₂
      · exact h₁.req_align e₁ he₁ ev hev₁
      · obtain ⟨hr, hal⟩ := (PhaseCreditSpec.freeOnly_of_hyps hM).req_align e₂ (h₂ e₂ he₂) ev hev₂
        exact ⟨Nat.le_trans hr (Nat.zero_le r), hal⟩
  credit_le st0 {evs} hseq := by
    rcases hseq with he₁ | ⟨e₁, e₂, rfl, he₁, he₂⟩
    · exact h₁.credit_le st0 he₁
    · rw [AllocCostModel.stepEvents_append]
      obtain ⟨hc₁, hl₁, hp₁⟩ := h₁.credit_le st0 he₁
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_freeOnly_le hM.freeNonInc (h₂ e₂ he₂) (M.stepEvents e₁ st0)
      exact ⟨Nat.le_trans hc₂ hc₁, Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩

theorem phaseCreditSpec_rustAlloc_small_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {req al : Nat} (hal : al ≤ 16)
    (hsmall : req ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = rustAllocEvents req al) (2 * req + 9539) 0 0 req :=
  (PhaseCreditSpec.rustAlloc_small_any hM hal hsmall).mono
    (hM.smallAlloc_le hsmall) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl req)

theorem phaseCreditSpec_boxAlloc_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {boxSize : Nat}
    (hsmall : boxSize ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (BoxAllocEnv boxSize) (2 * boxSize + 9539) 0 0 boxSize := by
  refine (PhaseCreditSpec.or_of_imp ?_ (PhaseCreditSpec.nil M)
    (phaseCreditSpec_rustAlloc_small_aff hM (al := 8) (by omega) hsmall)).mono
    (by omega) (by omega) (by omega) (by omega)
  rintro evs (⟨_, rfl⟩ | ⟨_, h2⟩)
  · exact Or.inl rfl
  · exact Or.inr h2

theorem phaseCreditSpec_boxAlloc_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (boxSize : Nat) :
    PhaseCreditSpec M (BoxAllocEnv boxSize)
      (2 * boxSize + 9539) (boxSize + 8195) (boxSize + 8195) boxSize := by
  refine (PhaseCreditSpec.or_of_imp ?_ (PhaseCreditSpec.nil M)
    (PhaseCreditSpec.rustAlloc_aff hM (req := boxSize) (al := 8) (by omega))).mono
    (by omega) (by omega) (by omega) (by omega)
  rintro evs (⟨_, rfl⟩ | ⟨_, h2⟩)
  · exact Or.inl rfl
  · exact Or.inr h2

theorem phaseCreditSpec_stringClone_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (g : VecGhost)
    (hsmall : g.bytes.length ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (StringCloneEnv g) (2 * g.bytes.length + 9539) 0 0 g.bytes.length := by
  refine (PhaseCreditSpec.or_of_imp ?_ (PhaseCreditSpec.nil M)
    (phaseCreditSpec_rustAlloc_small_aff hM (al := 1) (by omega) hsmall)).mono
    (by omega) (by omega) (by omega) (by omega)
  rintro evs (⟨_, rfl⟩ | ⟨_, h2⟩)
  · exact Or.inl rfl
  · exact Or.inr h2

theorem phaseCreditSpec_stringClone_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (g : VecGhost) :
    PhaseCreditSpec M (StringCloneEnv g)
      (2 * g.bytes.length + 9539) (g.bytes.length + 8195) (g.bytes.length + 8195)
      g.bytes.length := by
  refine (PhaseCreditSpec.or_of_imp ?_ (PhaseCreditSpec.nil M)
    (PhaseCreditSpec.rustAlloc_aff hM (req := g.bytes.length) (al := 1) (by omega))).mono
    (by omega) (by omega) (by omega) (by omega)
  rintro evs (⟨_, rfl⟩ | ⟨_, h2⟩)
  · exact Or.inl rfl
  · exact Or.inr h2

theorem phaseCreditSpec_growOneSpe_zero {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 192 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (GrowOneSpeEnv 0#64) 9923 0 0 192 := by
  refine (phaseCreditSpec_rustAlloc_small_aff hM (req := 192) (al := 8) (by omega) hsmall).congr_mono
    ?_ (by omega) (by omega) (by omega) (by omega)
  rintro evs (⟨_, h1⟩ | ⟨hne, _⟩)
  · exact h1
  · exact absurd rfl hne

/-! ## 2. `try_decrypt_from_record` Seam Envelopes -/

theorem phaseCreditSpec_segTailEnv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 17 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M SegTailEnv 9573 0 0 17 :=
  (PhaseCreditSpec.seq (PhaseCreditSpec.freeOnly_of_hyps hM)
    (phaseCreditSpec_rustAlloc_small_aff hM (req := 17) (al := 1) (by omega) hsmall)).mono
    (by omega) (by omega) (by omega) (by omega)

theorem phaseCreditSpec_fromFEnv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 17 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M FromFEnv 9573 0 0 17 :=
  (PhaseCreditSpec.seq (phaseCreditSpec_segTailEnv hM hsmall)
    (PhaseCreditSpec.freeOnly_of_hyps hM)).mono (by omega) (by omega) (by omega) (by omega)

theorem phaseCreditSpec_fromMEnv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 192 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M FromMEnv 19496 0 0 192 :=
  (PhaseCreditSpec.seq (phaseCreditSpec_growOneSpe_zero hM hsmall)
    (phaseCreditSpec_fromFEnv hM (by omega))).mono (by omega) (by omega) (by omega) (by omega)

theorem phaseCreditSpec_fromVPostTdEnv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 192 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M FromVPostTdEnv 19496 0 0 192 :=
  (PhaseCreditSpec.or (PhaseCreditSpec.freeOnly_of_hyps hM)
    (phaseCreditSpec_fromMEnv hM hsmall)).mono (by omega) (by omega) (by omega) (by omega)

theorem phaseCreditSpec_fromVEnv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 192 ≤ HasFineReallocCredit.smallMaxReq M)
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : RecordDecryptGhost} {G₁ : SessionGhost} {c_td l_td p_td r_td : Nat}
    (htd : PhaseCreditSpec M (tdEnv (recordTryDecryptEnvArgs x G₁)) c_td l_td p_td r_td) :
    PhaseCreditSpec M (FromVEnv tdEnv x G₁)
      (c_td + 19496) l_td (max p_td l_td) (max r_td 192) :=
  (PhaseCreditSpec.seq htd (phaseCreditSpec_fromVPostTdEnv hM hsmall)).mono
    (by omega) (by omega) (by omega) (by omega)

theorem phaseCreditSpec_recordDecryptEnv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 192 ≤ HasFineReallocCredit.smallMaxReq M)
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : RecordDecryptGhost} {c_cl l_cl p_cl r_cl c_td l_td p_td r_td : Nat}
    (hClone : PhaseCreditSpec M (SegCloneEnv x.G x.st) c_cl l_cl p_cl r_cl)
    (hTd : ∀ G₁ : SessionGhost, CloneRel x.G G₁ →
      PhaseCreditSpec M (tdEnv (recordTryDecryptEnvArgs x G₁)) c_td l_td p_td r_td) :
    PhaseCreditSpec M (RecordDecryptEnv tdEnv x)
      (c_cl + c_td + 19496) (l_cl + l_td) (max p_cl (l_cl + max p_td l_td))
      (max (max r_cl r_td) 192) := by
  unfold RecordDecryptEnv
  split
  · refine phaseCreditSpec_exists_guarded fun G₁ hRel => ?_
    exact (PhaseCreditSpec.seq hClone
      (phaseCreditSpec_fromVEnv hM hsmall (hTd G₁ hRel))).mono
      (by omega) (by omega) (by omega) (by omega)
  · exact (PhaseCreditSpec.seq hClone (phaseCreditSpec_fromMEnv hM hsmall)).mono
      (by omega) (by omega) (by omega) (by omega)

/-! ## 3. Store-Step and Guarded `WithStoresDecEnv` Composition -/

theorem phaseCreditSpec_loadPollStep_smallBox {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} {b : BitVec 64}
    (hM : ModelHyps M) {kit : SessionStoreSpec A b} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState} {rem : AddrVal} {c_p l_p p_p r_p : Nat}
    (hbox : kit.loadBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hpoll : PhaseCreditSpec M (kitEnv.loadPollEnv st0 rem) c_p l_p p_p r_p) :
    PhaseCreditSpec M (LoadPollStepEnv kit kitEnv st0 rem)
      (2 * kit.loadBoxSize + 9539 + c_p) l_p p_p (max kit.loadBoxSize r_p) :=
  (PhaseCreditSpec.seq (phaseCreditSpec_boxAlloc_small hM hbox) hpoll).mono
    (by omega) (by omega) (by omega) (by omega)

theorem phaseCreditSpec_trustStep_smallBox {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} {b : BitVec 64}
    (hM : ModelHyps M) {ikit : IdentityStoreSpec A b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState} {rem : AddrVal} {key : IdentityKey}
    {d : Direction} {c_p l_p p_p r_p : Nat}
    (hbox : ikit.trustBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hpoll : PhaseCreditSpec M (ikitEnv.trustPollEnv ist0 rem key d) c_p l_p p_p r_p) :
    PhaseCreditSpec M (TrustStepEnv ikit ikitEnv ist0 rem key d)
      (2 * ikit.trustBoxSize + 9539 + c_p) l_p p_p (max ikit.trustBoxSize r_p) := by
  have htail := phaseCreditSpec_seq_freeOnly (E₂ := (· = rustDeallocEvents ikit.trustBoxSize 8))
    hM hpoll (by rintro _ rfl; exact FreeOnlyEvs.singleton 8 ikit.trustBoxSize)
  exact (PhaseCreditSpec.seq (phaseCreditSpec_boxAlloc_small hM hbox) htail).mono
    (by omega) (by omega) (by omega) (by omega)

theorem phaseCreditSpec_saveStep_smallBox {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} {b : BitVec 64}
    (hM : ModelHyps M) {ikit : IdentityStoreSpec A b} {ikitEnv : IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState} {rem : AddrVal} {key : IdentityKey} {c_p l_p p_p r_p : Nat}
    (hbox : ikit.saveBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hpoll : PhaseCreditSpec M (ikitEnv.savePollEnv ist0 rem key) c_p l_p p_p r_p) :
    PhaseCreditSpec M (SaveStepEnv ikit ikitEnv ist0 rem key)
      (2 * ikit.saveBoxSize + 9539 + c_p) l_p p_p (max ikit.saveBoxSize r_p) := by
  have htail := phaseCreditSpec_seq_freeOnly (E₂ := (· = rustDeallocEvents ikit.saveBoxSize 8))
    hM hpoll (by rintro _ rfl; exact FreeOnlyEvs.singleton 8 ikit.saveBoxSize)
  exact (PhaseCreditSpec.seq (phaseCreditSpec_boxAlloc_small hM hbox) htail).mono
    (by omega) (by omega) (by omega) (by omega)

theorem phaseCreditSpec_storeStep_smallBox {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} {b : BitVec 64}
    (hM : ModelHyps M) {kit : SessionStoreSpec A b} {kitEnv : SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState} {rem : AddrVal} {rec' : SessionRecord (List (BitVec 8))}
    {c_p l_p p_p r_p : Nat}
    (hbox : kit.storeBoxSize ≤ HasFineReallocCredit.smallMaxReq M)
    (hpoll : PhaseCreditSpec M (kitEnv.storePollEnv st0 rem rec') c_p l_p p_p r_p) :
    PhaseCreditSpec M (StoreStepEnv kit kitEnv st0 rem rec')
      (2 * kit.storeBoxSize + 9539 + c_p) l_p p_p (max kit.storeBoxSize r_p) := by
  have htail := phaseCreditSpec_seq_freeOnly (E₂ := (· = rustDeallocEvents kit.storeBoxSize 8))
    hM hpoll (by rintro _ rfl; exact FreeOnlyEvs.singleton 8 kit.storeBoxSize)
  exact (PhaseCreditSpec.seq (phaseCreditSpec_boxAlloc_small hM hbox) htail).mono
    (by omega) (by omega) (by omega) (by omega)

theorem phaseCreditSpec_fromRegionNoneEnv {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 17 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M FromRegionNoneEnv 9573 0 0 17 :=
  (PhaseCreditSpec.seq (phaseCreditSpec_rustAlloc_small_aff hM (req := 17) (al := 1) (by omega) hsmall)
    (PhaseCreditSpec.freeOnly_of_hyps hM)).mono (by omega) (by omega) (by omega) (by omega)

theorem phaseCreditSpec_fromKeyReadyEnv {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} (hM : ModelHyps M)
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {x : DecryptGhost} {rec' : SessionRecord (List (BitVec 8))} {k : IdentityKey}
    {c_tr l_tr p_tr r_tr c_sv l_sv p_sv r_sv c_st l_st p_st r_st : Nat}
    (htrust : PhaseCreditSpec M (TrustStepEnv ikit ikitEnv ist0 x.rem.val k .receiving)
      c_tr l_tr p_tr r_tr)
    (hsave : PhaseCreditSpec M
      (SaveStepEnv ikit ikitEnv (ikit.trustUpdate ist0 x.rem.val k .receiving (.ok true)) x.rem.val k)
      c_sv l_sv p_sv r_sv)
    (hstore : PhaseCreditSpec M (StoreStepEnv kit kitEnv st0 x.rem.val rec')
      c_st l_st p_st r_st) :
    let c_sc := 2 * x.rem.name.bytes.length + 9539
    let l_sc := x.rem.name.bytes.length + 8195
    PhaseCreditSpec M (FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k)
      (c_tr + max c_sc (c_sv + c_st))
      (l_tr + max l_sc (l_sv + l_st))
      (max p_tr (l_tr + max l_sc (max p_sv (l_sv + p_st))))
      (max r_tr (max x.rem.name.bytes.length (max r_sv r_st))) := by
  intro c_sc l_sc
  have hStoreCall : PhaseCreditSpec M (FromStoreCallEnv kit kitEnv st0 x.rem.val rec')
      c_st l_st p_st r_st :=
    phaseCreditSpec_seq_freeOnly hM hstore (fun _ h => h)
  have hFalse : PhaseCreditSpec M (FromTrustedFalseEnv x)
      c_sc l_sc l_sc x.rem.name.bytes.length :=
    (PhaseCreditSpec.seq (phaseCreditSpec_stringClone_aff hM x.rem.name)
      (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
      (by omega) (by omega) (by omega) (by omega)
  have hTrueTail := PhaseCreditSpec.or (PhaseCreditSpec.freeOnly_of_hyps hM) hStoreCall
  have hTrue : PhaseCreditSpec M
      (FromTrustedTrueEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k)
      (c_sv + c_st) (l_sv + l_st) (max p_sv (l_sv + p_st)) (max r_sv r_st) :=
    (PhaseCreditSpec.seq hsave hTrueTail).mono
      (by omega) (by omega) (by omega) (by omega)
  have hCont := PhaseCreditSpec.or (PhaseCreditSpec.freeOnly_of_hyps hM)
    (PhaseCreditSpec.or hFalse hTrue)
  exact (PhaseCreditSpec.seq htrust hCont).mono
    (by omega) (by omega) (by omega) (by omega)

/-- End-to-end `PhaseCreditSpec` for the `Scope`-guarded `WithStoresDecEnv`, threading
`kit.ScopeAt Scope st0 x.rem.val rec`, `rec.currentSession = some ses`, and `SessionGhostValid G ses`
across `RecordDecryptEnv` and post-decryption store steps. -/
theorem phaseCreditSpec_withStoresDecEnv {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustAlloc} (hM : ModelHyps M) (hsmall17 : 17 ≤ HasFineReallocCredit.smallMaxReq M)
    {kit : SessionStoreSpec A 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {C : Crypto} {S : SpqrModel} {parse : UuidParser}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {x : DecryptGhost}
    {c_ld l_ld p_ld r_ld c_rd l_rd p_rd r_rd c_tr l_tr p_tr r_tr
     c_sv l_sv p_sv r_sv c_st l_st p_st r_st : Nat}
    (hLoad : PhaseCreditSpec M (LoadPollStepEnv kit kitEnv st0 x.rem.val) c_ld l_ld p_ld r_ld)
    (hRecDec : ∀ rec ses G,
      kit.ScopeAt Scope st0 x.rem.val rec →
      rec.currentSession = some ses →
      SessionGhostValid G ses →
      PhaseCreditSpec M (RecordDecryptEnv tdEnv (recGhostOf x 0#64 G ses.state))
        c_rd l_rd p_rd r_rd)
    (hTrust : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseCreditSpec M (TrustStepEnv ikit ikitEnv ist0 x.rem.val k .receiving)
        c_tr l_tr p_tr r_tr)
    (hSave : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseCreditSpec M
        (SaveStepEnv ikit ikitEnv (ikit.trustUpdate ist0 x.rem.val k .receiving (.ok true))
          x.rem.val k)
        c_sv l_sv p_sv r_sv)
    (hStore : ∀ rec pt rec' ses k,
      kit.ScopeAt Scope st0 x.rem.val rec →
      decryptRecord C S parse x rec = .ok (pt, rec') →
      rec'.currentSession = some ses →
      ses.state.remoteIdentity = some k →
      PhaseCreditSpec M (StoreStepEnv kit kitEnv st0 x.rem.val rec')
        c_st l_st p_st r_st) :
    let c_sc := 2 * x.rem.name.bytes.length + 9539
    let l_sc := x.rem.name.bytes.length + 8195
    let c_kr := c_tr + max c_sc (c_sv + c_st)
    let l_kr := l_tr + max l_sc (l_sv + l_st)
    let p_kr := max p_tr (l_tr + max l_sc (max p_sv (l_sv + p_st)))
    let r_kr := max r_tr (max x.rem.name.bytes.length (max r_sv r_st))
    let c_some := c_rd + c_kr
    let l_some := l_rd + l_kr
    let p_some := max p_rd (l_rd + p_kr)
    let r_some := max r_rd r_kr
    PhaseCreditSpec M
      (WithStoresDecEnv kit kitEnv st0 ikit ikitEnv ist0 C S parse tdEnv Scope x)
      (c_ld + max (max c_sc 9573) c_some)
      (l_ld + max l_sc l_some)
      (max p_ld (l_ld + max l_sc p_some))
      (max r_ld (max (max x.rem.name.bytes.length 17) r_some)) := by
  intro c_sc l_sc c_kr l_kr p_kr r_kr c_some l_some p_some r_some
  have hArm2 : PhaseCreditSpec M (SeqEnv (StringCloneEnv x.rem.name) FreeOnlyEvs)
      c_sc l_sc l_sc x.rem.name.bytes.length :=
    (PhaseCreditSpec.seq (phaseCreditSpec_stringClone_aff hM x.rem.name)
      (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
      (by omega) (by omega) (by omega) (by omega)
  have hArm3 := phaseCreditSpec_fromRegionNoneEnv hM hsmall17
  have hArm4 : PhaseCreditSpec M
      (fun evs => ∃ rec ses G,
        kit.ScopeAt Scope st0 x.rem.val rec ∧
        rec.currentSession = some ses ∧
        SessionGhostValid G ses ∧
        FromRegionSomeEnv C S parse tdEnv kit kitEnv st0 ikit ikitEnv ist0 x rec G ses.state evs)
      c_some l_some p_some r_some := by
    refine
      { req_align := ?_
        credit_le := ?_ }
    · rintro evs ⟨rec, ses, G, hsc, hcur, hgv, hf⟩
      have hPostSome : PhaseCreditSpec M
          (FromPostSomeEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x rec)
          c_kr l_kr p_kr r_kr := by
        have hexKr : PhaseCreditSpec M
            (fun evs' => ∃ pt rec' ses' k,
              decryptRecord C S parse x rec = .ok (pt, rec') ∧
              rec'.currentSession = some ses' ∧
              ses'.state.remoteIdentity = some k ∧
              FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k evs')
            c_kr l_kr p_kr r_kr :=
          { req_align := fun evs' ⟨pt, rec', ses', k, hdec, hc', hk, hfe⟩ =>
              (phaseCreditSpec_fromKeyReadyEnv hM
                (hTrust rec pt rec' ses' k hsc hdec hc' hk)
                (hSave rec pt rec' ses' k hsc hdec hc' hk)
                (hStore rec pt rec' ses' k hsc hdec hc' hk)).req_align evs' hfe
            credit_le := fun st0' {_} ⟨pt, rec', ses', k, hdec, hc', hk, hfe⟩ =>
              (phaseCreditSpec_fromKeyReadyEnv hM
                (hTrust rec pt rec' ses' k hsc hdec hc' hk)
                (hSave rec pt rec' ses' k hsc hdec hc' hk)
                (hStore rec pt rec' ses' k hsc hdec hc' hk)).credit_le st0' hfe }
        exact (PhaseCreditSpec.or (PhaseCreditSpec.freeOnly_of_hyps hM) hexKr).mono
          (by omega) (by omega) (by omega) (by omega)
      exact (PhaseCreditSpec.seq (hRecDec rec ses G hsc hcur hgv) hPostSome).req_align evs hf
    · rintro st0' evs ⟨rec, ses, G, hsc, hcur, hgv, hf⟩
      have hPostSome : PhaseCreditSpec M
          (FromPostSomeEnv C S parse kit kitEnv st0 ikit ikitEnv ist0 x rec)
          c_kr l_kr p_kr r_kr := by
        have hexKr : PhaseCreditSpec M
            (fun evs' => ∃ pt rec' ses' k,
              decryptRecord C S parse x rec = .ok (pt, rec') ∧
              rec'.currentSession = some ses' ∧
              ses'.state.remoteIdentity = some k ∧
              FromKeyReadyEnv kit kitEnv st0 ikit ikitEnv ist0 x rec' k evs')
            c_kr l_kr p_kr r_kr :=
          { req_align := fun evs' ⟨pt, rec', ses', k, hdec, hc', hk, hfe⟩ =>
              (phaseCreditSpec_fromKeyReadyEnv hM
                (hTrust rec pt rec' ses' k hsc hdec hc' hk)
                (hSave rec pt rec' ses' k hsc hdec hc' hk)
                (hStore rec pt rec' ses' k hsc hdec hc' hk)).req_align evs' hfe
            credit_le := fun st0'' {_} ⟨pt, rec', ses', k, hdec, hc', hk, hfe⟩ =>
              (phaseCreditSpec_fromKeyReadyEnv hM
                (hTrust rec pt rec' ses' k hsc hdec hc' hk)
                (hSave rec pt rec' ses' k hsc hdec hc' hk)
                (hStore rec pt rec' ses' k hsc hdec hc' hk)).credit_le st0'' hfe }
        exact (PhaseCreditSpec.or (PhaseCreditSpec.freeOnly_of_hyps hM) hexKr).mono
          (by omega) (by omega) (by omega) (by omega)
      exact (PhaseCreditSpec.seq (hRecDec rec ses G hsc hcur hgv) hPostSome).credit_le st0' hf
  have hBranches := PhaseCreditSpec.or (PhaseCreditSpec.freeOnly_of_hyps hM)
    (PhaseCreditSpec.or hArm2 (PhaseCreditSpec.or hArm3 hArm4))
  have hFromLoad := PhaseCreditSpec.seq
    (PhaseCreditSpec.rustDealloc_align16 M (req := kit.loadBoxSize) (al := 8) (by omega)) hBranches
  exact (PhaseCreditSpec.seq hLoad hFromLoad).mono
    (by omega) (by omega) (by omega) (by omega)

end LibsignalBinary.Proofs.PeakBudget.W2DecryptRecordStorePeak
