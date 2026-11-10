/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
public import LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget

/-!
# Concrete CLI Store-Step & Stage `PhaseCreditSpec` Kit

Stage-level `PhaseCreditSpec M` combinators for `process_prekey` / `decrypt_prekey` in exact binary
call order:
1. Free-only tail composition (`phaseCreditSpec_seq_freeOnly_exact`), `BoxAllocEnv`, boxed async
   store steps (`W4BoxedStoreStepEnv`), and `GrowOneSpeEnv 0#64` bounds.
2. Concrete CLI store-step specs (`W4SmallStoreStepEnv`, `W4SessLoadStepEnv`, `W4SessStoreStepEnv`,
   `W4SessStorePrev1StepEnv`).
3. Stage P1 (`.ok` and `.untrusted`), Stage P2 (`InitialStateEnv` and PQXDH responder handshake),
   and Stage P4 (`Matched`, `0`-prev, and `prev1`) composers.
-/

@[expose] public section

namespace LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers

set_option autoImplicit false

open CryptoGames.LibsignalSession (IdentityKey ShaCompress)
open CryptoGames.LibsignalSessionApi (Direction Session SessionRecord)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalPublicApi.StoreKit
  (FsFiles IdentitySelfStoreSpec IdentityStoreSpec SessionStoreSpec)
open CryptoVerification.LibsignalPublicApiRepr (AddrVal RecordGhost)
open CryptoVerification.LibsignalSessionRepr (VecGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost)
open CryptoVerification.SignalSession.Cli
  (DirGhost ReadRule StoresGhost addressText baseKeysName keyName pathOf)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (StringCloneEnv)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (BoundedRustEvs)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (DirDomainCaps addressText_length_le baseKeysName_length_le
   dirDomainCaps_opened_kpkLr dirDomainCaps_opened_kpkOt dirDomainCaps_opened_opk
   dirDomainCaps_opened_own dirDomainCaps_opened_peers dirDomainCaps_opened_sess
   dirDomainCaps_opened_signed keyName_length_le)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (FreeOnlyAlign16Evs ModelHyps PhaseCreditSpec stepEvents_freeOnly_le)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec
  (CliSessLoadPollEnv CliSessStorePollEnv CliSessStorePollPrev1Env CliSmallStorePollEnv
   boundedRustEvs_phaseCredit cliStorePollPrev1_phaseCredit
   sessLoadPollDeltaCum sessLoadPollDeltaLive sessLoadPollDeltaPeak sessLoadPollMaxReq
   sessLoadPoll_phaseCredit
   sessStorePollDeltaCum sessStorePollDeltaLive sessStorePollDeltaPeak sessStorePollMaxReq
   sessStorePoll_phaseCredit
   smallStorePollDeltaCum smallStorePollDeltaLive smallStorePollDeltaPeak smallStorePollMaxReq
   smallStorePoll_phaseCredit)
open LibsignalBinary.Proofs.PeakBudget.SessionSerializeCredit
  (recordSerializeCum recordSerializeMaxReq recordSerializeOutLarge recordSerializePeak
   serializePrev1Cum serializePrev1MaxReq serializePrev1OutLarge serializePrev1Peak)
open LibsignalBinary.Proofs.PeakBudget.SpqrCodecPeakSpec (initialState_phaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers
  (phaseCreditSpec_ite_nil stringClone_phaseCredit_aff stringClone_phaseCredit_small)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
  (IdentitySelfStoreBudgetEnv KpStepEnv RegIdStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget
  (IdentityStoreBudgetEnv SaveStepEnv TrustStepEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (BoxAllocEnv BoxDeallocEnv)
open LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget
  (LoadStepEnv SessionStoreBudgetEnv StoreStepEnv)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (GrowOneSpeEnv)

/-! ## Unconditional `FreeOnlyEvs` Tail, `BoxAllocEnv`, `StoreKit` Steps, & `GrowOneSpeEnv` -/

/-- Appending `FreeOnlyEvs` in exact binary order (`SeqEnv E FreeOnlyEvs`) preserves exact
`(c, l, p, r)` without requiring `l ≤ p`, via `stepEvents_freeOnly_le`. -/
theorem phaseCreditSpec_seq_freeOnly_exact
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (SeqEnv E FreeOnlyEvs) c l p r where
  req_align evs hE ev hev := by
    rcases hE with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
    · exact h.req_align evs h1 ev hev
    · rcases List.mem_append.mp hev with he1 | he2
      · exact h.req_align evs₁ h1 ev he1
      · obtain ⟨al, sz, rfl⟩ := h2 ev he2
        exact ⟨Nat.zero_le r, Nat.le_refl 16⟩
  credit_le st0 {_} hE := by
    rcases hE with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
    · exact h.credit_le st0 h1
    · rw [M.stepEvents_append evs₁ evs₂ st0]
      obtain ⟨hc₁, hl₁, hp₁⟩ := h.credit_le st0 h1
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_freeOnly_le hM.freeNonInc h2 (M.stepEvents evs₁ st0)
      exact ⟨Nat.le_trans hc₂ hc₁, Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩

/-- Appending any free-only predicate `F` (`∀ evs, F evs → FreeOnlyEvs evs`) in exact binary order
preserves `(c, l, p, r)` unconditionally. -/
theorem phaseCreditSpec_seq_freeOnlyPred_exact
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {E F : List AllocEvent → Prop} {c l p r : Nat}
    (hF : ∀ evs, F evs → FreeOnlyEvs evs)
    (h : PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (SeqEnv E F) c l p r :=
  PhaseCreditSpec.of_imp
    (fun _ hevs => LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.SeqEnv.mono (fun _ hx => hx) hF hevs)
    (phaseCreditSpec_seq_freeOnly_exact hM h)

theorem rustDealloc8_freeOnly {boxSz : Nat} {evs : List AllocEvent}
    (h : evs = rustDeallocEvents boxSz 8) : FreeOnlyEvs evs := by
  subst h
  exact FreeOnlyAlign16Evs.toFreeOnlyEvs
    (FreeOnlyAlign16Evs.rustDealloc (by decide) boxSz)

/-- Regime-uniform `PhaseCreditSpec` for `PreKeyStoreKitBudget.BoxAllocEnv boxSz`
(covering both `boxSz = 0` and `0 < boxSz`). -/
theorem boxAllocEnv_phaseCredit_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (boxSz : Nat) :
    PhaseCreditSpec M (BoxAllocEnv boxSz)
      (2 * boxSz + 9539) (boxSz + 8195) (boxSz + 8195) boxSz := by
  have h1 : PhaseCreditSpec M (fun evs => boxSz = 0 ∧ evs = []) 0 0 0 0 :=
    PhaseCreditSpec.of_eq_nil (M := M) (fun _ h => h.2)
  have h2 : PhaseCreditSpec M (fun evs => 0 < boxSz ∧ evs = rustAllocEvents boxSz 8)
      (2 * boxSz + 9539) (boxSz + 8195) (boxSz + 8195) boxSz :=
    PhaseCreditSpec.of_imp (fun _ h => h.2)
      (PhaseCreditSpec.rustAlloc_aff (req := boxSz) (al := 8) hM (by decide))
  exact (PhaseCreditSpec.or_of_imp (fun _ h => h) h1 h2).mono
    (by omega) (by omega) (by omega) (by omega)

/-- Small-regime (`boxSz ≤ smallMaxReq M`) `PhaseCreditSpec` for `BoxAllocEnv boxSz`
(`Δlive = 0`, `Δpeak = 0`). -/
theorem boxAllocEnv_phaseCredit_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (boxSz : Nat)
    (hsz : boxSz ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (BoxAllocEnv boxSz) (2 * boxSz + 9539) 0 0 boxSz := by
  have h1 : PhaseCreditSpec M (fun evs => boxSz = 0 ∧ evs = []) 0 0 0 0 :=
    PhaseCreditSpec.of_eq_nil (M := M) (fun _ h => h.2)
  have h2 : PhaseCreditSpec M (fun evs => 0 < boxSz ∧ evs = rustAllocEvents boxSz 8)
      (2 * boxSz + 9539) 0 0 boxSz :=
    (PhaseCreditSpec.of_imp (fun _ h => h.2)
      (PhaseCreditSpec.rustAlloc_small_any (req := boxSz) (al := 8) hM (by decide) hsz)).mono
      (hM.smallAlloc_le hsz) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl boxSz)
  exact (PhaseCreditSpec.or_of_imp (fun _ h => h) h1 h2).mono
    (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)

/-- Boxed-future async store step (`BoxAllocEnv boxSz → E_poll → FreeOnlyEvs`) in exact binary
call order. -/
def W4BoxedStoreStepEnv (boxSz : Nat) (E_poll : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (BoxAllocEnv boxSz) (SeqEnv E_poll FreeOnlyEvs) evs

def w4BoxedStepCum (boxSz pollCum : Nat) : Nat := (2 * boxSz + 9539) + pollCum
def w4BoxedStepLive (boxSz pollLive : Nat) : Nat := (boxSz + 8195) + pollLive
def w4BoxedStepPeak (boxSz pollPeak : Nat) : Nat := (boxSz + 8195) + pollPeak
def w4BoxedStepMaxReq (boxSz pollMaxReq : Nat) : Nat := max boxSz pollMaxReq

/-- Regime-uniform `PhaseCreditSpec` for `W4BoxedStoreStepEnv boxSz E_poll` (unconditional in
`l_p`, `p_p`). -/
theorem w4BoxedStoreStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (boxSz : Nat) {E_poll : List AllocEvent → Prop}
    {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec M E_poll c_p l_p p_p r_p) :
    PhaseCreditSpec M (W4BoxedStoreStepEnv boxSz E_poll)
      (w4BoxedStepCum boxSz c_p)
      (w4BoxedStepLive boxSz l_p)
      (w4BoxedStepPeak boxSz p_p)
      (w4BoxedStepMaxReq boxSz r_p) := by
  have hbox := boxAllocEnv_phaseCredit_aff hM boxSz
  have hpollF := phaseCreditSpec_seq_freeOnly_exact hM hpoll
  exact (hbox.seq hpollF).mono
    (Nat.le_refl _) (Nat.le_refl _)
    (Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_refl _⟩)
    (Nat.le_refl _)

/-- Small-regime (`boxSz ≤ smallMaxReq M`) `PhaseCreditSpec` for `W4BoxedStoreStepEnv boxSz E_poll`
with zero live or peak overhead from the `Box<dyn Future>` wrapper. -/
theorem w4BoxedStoreStep_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (boxSz : Nat)
    (hsz : boxSz ≤ HasFineReallocCredit.smallMaxReq M)
    {E_poll : List AllocEvent → Prop} {c_p l_p p_p r_p : Nat}
    (hpoll : PhaseCreditSpec M E_poll c_p l_p p_p r_p) :
    PhaseCreditSpec M (W4BoxedStoreStepEnv boxSz E_poll)
      (w4BoxedStepCum boxSz c_p) l_p p_p (w4BoxedStepMaxReq boxSz r_p) := by
  have hbox := boxAllocEnv_phaseCredit_small hM boxSz hsz
  have hpollF := phaseCreditSpec_seq_freeOnly_exact hM hpoll
  exact (hbox.seq hpollF).mono
    (by dsimp [w4BoxedStepCum]; omega)
    (by omega)
    (by omega)
    (by dsimp [w4BoxedStepMaxReq]; omega)

/-- Any `SeqEnv (BoxAllocEnv boxSz) (SeqEnv E_poll DeallocEv)` with free-only `DeallocEv`
implies `W4BoxedStoreStepEnv boxSz E_poll`. -/
theorem boxedDeallocPred_to_w4BoxedStoreStep {boxSz : Nat}
    {E_poll DeallocEv : List AllocEvent → Prop}
    (hDealloc : ∀ evs, DeallocEv evs → FreeOnlyEvs evs)
    {evs : List AllocEvent}
    (h : SeqEnv (BoxAllocEnv boxSz) (SeqEnv E_poll DeallocEv) evs) :
    W4BoxedStoreStepEnv boxSz E_poll evs :=
  LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.SeqEnv.mono (fun _ hx => hx)
    (fun _ hy => LibsignalBinary.Proofs.PeakBudget.SeqCreditKit.SeqEnv.mono (fun _ hz => hz) hDealloc hy) h

theorem boxDeallocStep_to_w4BoxedStoreStep {boxSz : Nat}
    {E_poll : List AllocEvent → Prop} {evs : List AllocEvent}
    (h : SeqEnv (BoxAllocEnv boxSz) (SeqEnv E_poll (BoxDeallocEnv boxSz)) evs) :
    W4BoxedStoreStepEnv boxSz E_poll evs :=
  boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => hd.freeOnly) h

theorem loadStepEnv_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (st0 : kit.StoreState) (rem : AddrVal) {c l p r : Nat}
    (hpoll : PhaseCreditSpec M (kitEnv.loadPollEnv st0 rem) c l p r) :
    PhaseCreditSpec M (LoadStepEnv kit kitEnv st0 rem)
      (w4BoxedStepCum kit.loadBoxSize c)
      (w4BoxedStepLive kit.loadBoxSize l)
      (w4BoxedStepPeak kit.loadBoxSize p)
      (w4BoxedStepMaxReq kit.loadBoxSize r) :=
  PhaseCreditSpec.of_imp
    (fun _ h => boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h)
    (w4BoxedStoreStep_phaseCredit hM kit.loadBoxSize hpoll)

theorem storeStepEnv_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (kitEnv : SessionStoreBudgetEnv kit)
    (st0 : kit.StoreState) (rem : AddrVal) (rec : SessionRecord (List (BitVec 8)))
    {c l p r : Nat}
    (hpoll : PhaseCreditSpec M (kitEnv.storePollEnv st0 rem rec) c l p r) :
    PhaseCreditSpec M (StoreStepEnv kit kitEnv st0 rem rec)
      (w4BoxedStepCum kit.storeBoxSize c)
      (w4BoxedStepLive kit.storeBoxSize l)
      (w4BoxedStepPeak kit.storeBoxSize p)
      (w4BoxedStepMaxReq kit.storeBoxSize r) :=
  PhaseCreditSpec.of_imp
    (fun _ h => boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h)
    (w4BoxedStoreStep_phaseCredit hM kit.storeBoxSize hpoll)

theorem trustStepEnv_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (rem : AddrVal) (key : IdentityKey) (d : Direction)
    {c l p r : Nat}
    (hpoll : PhaseCreditSpec M (ikitEnv.trustPollEnv ist0 rem key d) c l p r) :
    PhaseCreditSpec M (TrustStepEnv ikit ikitEnv ist0 rem key d)
      (w4BoxedStepCum ikit.trustBoxSize c)
      (w4BoxedStepLive ikit.trustBoxSize l)
      (w4BoxedStepPeak ikit.trustBoxSize p)
      (w4BoxedStepMaxReq ikit.trustBoxSize r) :=
  PhaseCreditSpec.of_imp
    (fun _ h => boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h)
    (w4BoxedStoreStep_phaseCredit hM ikit.trustBoxSize hpoll)

theorem saveStepEnv_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ikitEnv : IdentityStoreBudgetEnv ikit)
    (ist0 : ikit.IdState) (rem : AddrVal) (key : IdentityKey)
    {c l p r : Nat}
    (hpoll : PhaseCreditSpec M (ikitEnv.savePollEnv ist0 rem key) c l p r) :
    PhaseCreditSpec M (SaveStepEnv ikit ikitEnv ist0 rem key)
      (w4BoxedStepCum ikit.saveBoxSize c)
      (w4BoxedStepLive ikit.saveBoxSize l)
      (w4BoxedStepPeak ikit.saveBoxSize p)
      (w4BoxedStepMaxReq ikit.saveBoxSize r) :=
  PhaseCreditSpec.of_imp
    (fun _ h => boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h)
    (w4BoxedStoreStep_phaseCredit hM ikit.saveBoxSize hpoll)

theorem kpStepEnv_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (ist0 : ikit.IdState) {c l p r : Nat}
    (hpoll : PhaseCreditSpec M (senv.kpPollEnv ist0) c l p r) :
    PhaseCreditSpec M (KpStepEnv skit senv ist0)
      (w4BoxedStepCum skit.kpBoxSize c)
      (w4BoxedStepLive skit.kpBoxSize l)
      (w4BoxedStepPeak skit.kpBoxSize p)
      (w4BoxedStepMaxReq skit.kpBoxSize r) :=
  PhaseCreditSpec.of_imp
    (fun _ h => boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h)
    (w4BoxedStoreStep_phaseCredit hM skit.kpBoxSize hpoll)

theorem regIdStepEnv_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {A : RustAlloc} {b : BitVec 64} {ikit : IdentityStoreSpec A b}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (ist0 : ikit.IdState) {c l p r : Nat}
    (hpoll : PhaseCreditSpec M (senv.regIdPollEnv ist0) c l p r) :
    PhaseCreditSpec M (RegIdStepEnv skit senv ist0)
      (w4BoxedStepCum skit.regIdBoxSize c)
      (w4BoxedStepLive skit.regIdBoxSize l)
      (w4BoxedStepPeak skit.regIdBoxSize p)
      (w4BoxedStepMaxReq skit.regIdBoxSize r) :=
  PhaseCreditSpec.of_imp
    (fun _ h => boxedDeallocPred_to_w4BoxedStoreStep (fun _ hd => rustDealloc8_freeOnly hd) h)
    (w4BoxedStoreStep_phaseCredit hM skit.regIdBoxSize hpoll)

/-- Regime-uniform `PhaseCreditSpec` for `GrowOneSpeEnv 0#64` (`192`-byte `SignalProtocolError`
vec allocation on `try_decrypt_pq` error). -/
theorem growOneSpeZero_phaseCredit_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M (GrowOneSpeEnv 0#64) 9923 8387 8387 192 := by
  refine W4OuterHelpers.alloc192_phaseCredit_aff hM ?_
  rintro evs (⟨_, rfl⟩ | ⟨hne, _⟩)
  · rfl
  · exact False.elim (hne rfl)

/-- Small-regime (`192 ≤ smallMaxReq M`) `PhaseCreditSpec` for `GrowOneSpeEnv 0#64`. -/
theorem growOneSpeZero_phaseCredit_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 192 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (GrowOneSpeEnv 0#64) 9923 0 0 192 := by
  refine W4OuterHelpers.alloc192_phaseCredit_small hM ?_ hsmall
  rintro evs (⟨_, rfl⟩ | ⟨hne, _⟩)
  · rfl
  · exact False.elim (hne rfl)

/-! ## Concrete CLI Boxed Store-Step Specs -/

/-- Small-store async step (`idTrust 32 B`, `idSave 32 B`, `idKp 16 B`, `idRegId 16 B`,
`spkGet 16 B`, `kpkGet 16 B`, `pkGet 16 B`, `pkRemove 16 B`, `kpkMark 32 B`). -/
def W4SmallStoreStepEnv (boxSz : Nat) (rd : ReadRule) (files : FsFiles)
    (dir : DirGhost) (name : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  W4BoxedStoreStepEnv boxSz (CliSmallStorePollEnv rd files dir name) evs

theorem w4SmallStoreStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (boxSz : Nat) {rd : ReadRule} {files : FsFiles}
    {dir : DirGhost} {name : List (BitVec 8)}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hname : name.length ≤ 64)
    (hcap : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M (W4SmallStoreStepEnv boxSz rd files dir name)
      (w4BoxedStepCum boxSz (smallStorePollDeltaCum (max maxVal fileCap) maxEntries))
      (w4BoxedStepLive boxSz (smallStorePollDeltaLive (max maxVal fileCap) maxEntries))
      (w4BoxedStepPeak boxSz (smallStorePollDeltaPeak (max maxVal fileCap) maxEntries))
      (w4BoxedStepMaxReq boxSz (smallStorePollMaxReq (max maxVal fileCap) maxEntries)) :=
  w4BoxedStoreStep_phaseCredit hM boxSz (smallStorePoll_phaseCredit hM hdc hdir hname hcap)

theorem w4SmallStoreStep_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (boxSz : Nat)
    (hsz : boxSz ≤ HasFineReallocCredit.smallMaxReq M)
    {rd : ReadRule} {files : FsFiles} {dir : DirGhost} {name : List (BitVec 8)}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hname : name.length ≤ 64)
    (hcap : ∀ bs, rd files (pathOf dir.path name) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M (W4SmallStoreStepEnv boxSz rd files dir name)
      (w4BoxedStepCum boxSz (smallStorePollDeltaCum (max maxVal fileCap) maxEntries))
      (smallStorePollDeltaLive (max maxVal fileCap) maxEntries)
      (smallStorePollDeltaPeak (max maxVal fileCap) maxEntries)
      (w4BoxedStepMaxReq boxSz (smallStorePollMaxReq (max maxVal fileCap) maxEntries)) :=
  w4BoxedStoreStep_small_phaseCredit hM boxSz hsz
    (smallStorePoll_phaseCredit hM hdc hdir hname hcap)

/-- Peer-address length bound: `peer.name.bytes.length ≤ 40 ⇒ (addressText peer.val).length ≤ 64`. -/
theorem addressText_peer_length_le_64 {peer : AddrGhost}
    (hpeer : peer.name.bytes.length ≤ 40) :
    (addressText peer.val).length ≤ 64 := by
  have hlen := addressText_length_le peer.val
  rw [show peer.val.name = peer.name.bytes from rfl] at hlen
  omega

/-- Peer-indexed small-store step (`idTrust` / `idSave`, `boxSz = 32`, `name = addressText peer.val`). -/
theorem w4PeerSmallStoreStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (boxSz : Nat) {rd : ReadRule} {files : FsFiles}
    {peersDir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd files (pathOf peersDir.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap) :
    PhaseCreditSpec M (W4SmallStoreStepEnv boxSz rd files peersDir (addressText peer.val))
      (w4BoxedStepCum boxSz (smallStorePollDeltaCum (max maxVal fileCap) maxEntries))
      (w4BoxedStepLive boxSz (smallStorePollDeltaLive (max maxVal fileCap) maxEntries))
      (w4BoxedStepPeak boxSz (smallStorePollDeltaPeak (max maxVal fileCap) maxEntries))
      (w4BoxedStepMaxReq boxSz (smallStorePollMaxReq (max maxVal fileCap) maxEntries)) :=
  w4SmallStoreStep_phaseCredit hM boxSz hdc hdir (addressText_peer_length_le_64 hpeer) hcap

/-- Key-ID-indexed small-store step (`spkGet`, `kpkGet`, `pkGet`, `pkRemove`, `boxSz = 16`,
`name = keyName id`, `(keyName id).length ≤ 10 ≤ 64`). -/
theorem w4KeyIdSmallStoreStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (boxSz : Nat) {rd : ReadRule} {files : FsFiles}
    {dir : DirGhost} (id : BitVec 32)
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hcap : ∀ bs, rd files (pathOf dir.path (keyName id)) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M (W4SmallStoreStepEnv boxSz rd files dir (keyName id))
      (w4BoxedStepCum boxSz (smallStorePollDeltaCum (max maxVal fileCap) maxEntries))
      (w4BoxedStepLive boxSz (smallStorePollDeltaLive (max maxVal fileCap) maxEntries))
      (w4BoxedStepPeak boxSz (smallStorePollDeltaPeak (max maxVal fileCap) maxEntries))
      (w4BoxedStepMaxReq boxSz (smallStorePollMaxReq (max maxVal fileCap) maxEntries)) :=
  w4SmallStoreStep_phaseCredit hM boxSz hdc hdir
    (Nat.le_trans (keyName_length_le id) (by decide)) hcap

/-- Base-keys-indexed small-store step (`kpkMark`, `boxSz = 32`, `name = baseKeysName id`,
`(baseKeysName id).length ≤ 20 ≤ 64`). -/
theorem w4BaseKeysSmallStoreStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (boxSz : Nat) {rd : ReadRule} {files : FsFiles}
    {dir : DirGhost} (id : BitVec 32)
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal dir)
    (hdir : maxDir ≤ 64)
    (hcap : ∀ bs, rd files (pathOf dir.path (baseKeysName id)) = .ok bs → bs.length ≤ fileCap) :
    PhaseCreditSpec M (W4SmallStoreStepEnv boxSz rd files dir (baseKeysName id))
      (w4BoxedStepCum boxSz (smallStorePollDeltaCum (max maxVal fileCap) maxEntries))
      (w4BoxedStepLive boxSz (smallStorePollDeltaLive (max maxVal fileCap) maxEntries))
      (w4BoxedStepPeak boxSz (smallStorePollDeltaPeak (max maxVal fileCap) maxEntries))
      (w4BoxedStepMaxReq boxSz (smallStorePollMaxReq (max maxVal fileCap) maxEntries)) :=
  w4SmallStoreStep_phaseCredit hM boxSz hdc hdir
    (Nat.le_trans (baseKeysName_length_le id) (by decide)) hcap

/-- Stage P1 `load_session` async step (`24 B` box + `CliSessLoadPollEnv` + `FreeOnlyEvs`). -/
def W4SessLoadStepEnv (rd : ReadRule)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (files : FsFiles) (sessDir : DirGhost) (peer : AddrGhost)
    (evs : List AllocEvent) : Prop :=
  W4BoxedStoreStepEnv 24 (CliSessLoadPollEnv rd DeserEnv files sessDir peer) evs

theorem w4SessLoadStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {sessDir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hcap : ∀ bs, rd files (pathOf sessDir.path (addressText peer.val)) = .ok bs →
      bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    PhaseCreditSpec M (W4SessLoadStepEnv rd DeserEnv files sessDir peer)
      (w4BoxedStepCum 24 (sessLoadPollDeltaCum (max maxVal fileCap) deserCum))
      (w4BoxedStepLive 24 (sessLoadPollDeltaLive (max maxVal fileCap) deserLive))
      (w4BoxedStepPeak 24 (sessLoadPollDeltaPeak (max maxVal fileCap) deserPeak))
      (w4BoxedStepMaxReq 24 (sessLoadPollMaxReq (max maxVal fileCap) deserMaxReq)) :=
  w4BoxedStoreStep_phaseCredit hM 24 (sessLoadPoll_phaseCredit hM hdc hdir hpeer hcap hdeser)

/-- Stage P4 `0`-prev `store_session` async step (`32 B` box + `CliSessStorePollEnv` + `FreeOnlyEvs`). -/
def W4SessStoreStepEnv (sessDir : DirGhost) (peer : AddrGhost)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  W4BoxedStoreStepEnv 32 (CliSessStorePollEnv sessDir peer g_rec r_rec) evs

theorem w4SessStoreStep_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {sessDir : DirGhost} {peer : AddrGhost}
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    {maxDir maxEntries maxVal : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec M (W4SessStoreStepEnv sessDir peer g_rec r_rec)
      (w4BoxedStepCum 32 (sessStorePollDeltaCum (recordSerializeCum g_rec r_rec) maxEntries))
      (w4BoxedStepLive 32 (sessStorePollDeltaLive (recordSerializeOutLarge M g_rec r_rec) maxEntries))
      (w4BoxedStepPeak 32 (sessStorePollDeltaPeak (recordSerializePeak M g_rec r_rec) maxEntries))
      (w4BoxedStepMaxReq 32 (sessStorePollMaxReq (recordSerializeMaxReq g_rec r_rec) maxEntries)) :=
  w4BoxedStoreStep_phaseCredit hM 32 (sessStorePoll_phaseCredit hM hdc hpeer)

/-- Stage P4 Path C `prev1` `store_session` async step (`32 B` box + `CliSessStorePollPrev1Env` +
`FreeOnlyEvs`). -/
def W4SessStorePrev1StepEnv (sessDir : DirGhost) (peer : AddrGhost)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (enc : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  W4BoxedStoreStepEnv 32 (CliSessStorePollPrev1Env sessDir peer G sess enc) evs

theorem w4SessStorePrev1Step_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {sessDir : DirGhost} {peer : AddrGhost}
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (enc : List (BitVec 8))
    {maxDir maxEntries maxVal : Nat}
    (hdc : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hpeer : peer.name.bytes.length ≤ 40) :
    PhaseCreditSpec M (W4SessStorePrev1StepEnv sessDir peer G sess enc)
      (w4BoxedStepCum 32 (sessStorePollDeltaCum (serializePrev1Cum G sess enc) maxEntries))
      (w4BoxedStepLive 32 (sessStorePollDeltaLive (serializePrev1OutLarge M G sess enc) maxEntries))
      (w4BoxedStepPeak 32 (sessStorePollDeltaPeak (serializePrev1Peak M G sess enc) maxEntries))
      (w4BoxedStepMaxReq 32 (sessStorePollMaxReq (serializePrev1MaxReq G sess enc) maxEntries)) :=
  w4BoxedStoreStep_phaseCredit hM 32 (cliStorePollPrev1_phaseCredit hM hdc hpeer)

/-! ## Stage P1 Concrete CLI Envelopes & `PhaseCreditSpec`s -/

/-- Concrete CLI Stage P1 `.ok` (`is_trusted_identity = .ok true`) envelope:
`W4SessLoadStepEnv` (`24 B`) → `W4SmallStoreStepEnv 32` (`idTrust`). -/
def W4StageP1OkCliEnv (rd : ReadRule)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (files : FsFiles) (sessDir peersDir : DirGhost) (peer : AddrGhost)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (W4SessLoadStepEnv rd DeserEnv files sessDir peer)
    (W4SmallStoreStepEnv 32 rd files peersDir (addressText peer.val)) evs

/-- Concrete CLI Stage P1 `.untrusted` (`is_trusted_identity = .ok false`) envelope:
`W4SessLoadStepEnv` (`24 B`) → `W4SmallStoreStepEnv 32` (`idTrust`) →
`StringCloneEnv peer.name` → `FreeOnlyEvs` (record/coro drop). -/
def W4StageP1UntrustedCliEnv (rd : ReadRule)
    (DeserEnv : List (BitVec 8) → List AllocEvent → Prop)
    (files : FsFiles) (sessDir peersDir : DirGhost) (peer : AddrGhost)
    (evs : List AllocEvent) : Prop :=
  SeqEnv (W4SessLoadStepEnv rd DeserEnv files sessDir peer)
    (SeqEnv (W4SmallStoreStepEnv 32 rd files peersDir (addressText peer.val))
      (SeqEnv (StringCloneEnv peer.name) FreeOnlyEvs)) evs

theorem w4StageP1OkCli_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {sessDir peersDir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hfileCap : ∀ p bs, rd files p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    let cap := max maxVal fileCap
    let cL := w4BoxedStepCum 24 (sessLoadPollDeltaCum cap deserCum)
    let lL := w4BoxedStepLive 24 (sessLoadPollDeltaLive cap deserLive)
    let pL := w4BoxedStepPeak 24 (sessLoadPollDeltaPeak cap deserPeak)
    let rL := w4BoxedStepMaxReq 24 (sessLoadPollMaxReq cap deserMaxReq)
    let cT := w4BoxedStepCum 32 (smallStorePollDeltaCum cap maxEntries)
    let lT := w4BoxedStepLive 32 (smallStorePollDeltaLive cap maxEntries)
    let pT := w4BoxedStepPeak 32 (smallStorePollDeltaPeak cap maxEntries)
    let rT := w4BoxedStepMaxReq 32 (smallStorePollMaxReq cap maxEntries)
    PhaseCreditSpec M (W4StageP1OkCliEnv rd DeserEnv files sessDir peersDir peer)
      (cL + cT) (lL + lT) (max pL (lL + pT)) (max rL rT) := by
  intro cap cL lL pL rL cT lT pT rT
  have hLoad := w4SessLoadStep_phaseCredit hM hdcSess hdir hpeer (fun bs hr => hfileCap _ bs hr) hdeser
  have hTrust := w4PeerSmallStoreStep_phaseCredit hM 32 hdcPeers hdir hpeer
    (fun bs hr => hfileCap _ bs hr)
  exact hLoad.seq hTrust

theorem w4StageP1UntrustedCli_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {sessDir peersDir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hfileCap : ∀ p bs, rd files p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    let cap := max maxVal fileCap
    let cL := w4BoxedStepCum 24 (sessLoadPollDeltaCum cap deserCum)
    let lL := w4BoxedStepLive 24 (sessLoadPollDeltaLive cap deserLive)
    let pL := w4BoxedStepPeak 24 (sessLoadPollDeltaPeak cap deserPeak)
    let rL := w4BoxedStepMaxReq 24 (sessLoadPollMaxReq cap deserMaxReq)
    let cT := w4BoxedStepCum 32 (smallStorePollDeltaCum cap maxEntries)
    let lT := w4BoxedStepLive 32 (smallStorePollDeltaLive cap maxEntries)
    let pT := w4BoxedStepPeak 32 (smallStorePollDeltaPeak cap maxEntries)
    let rT := w4BoxedStepMaxReq 32 (smallStorePollMaxReq cap maxEntries)
    PhaseCreditSpec M (W4StageP1UntrustedCliEnv rd DeserEnv files sessDir peersDir peer)
      (cL + cT + (2 * 40 + 9539))
      (lL + lT + (40 + 8195))
      (max pL (lL + max pT (lT + (40 + 8195))))
      (max rL (max rT 40)) := by
  dsimp only
  have hLoad := w4SessLoadStep_phaseCredit hM hdcSess hdir hpeer (fun bs hr => hfileCap _ bs hr) hdeser
  have hTrust := w4PeerSmallStoreStep_phaseCredit hM 32 hdcPeers hdir hpeer
    (fun bs hr => hfileCap _ bs hr)
  have hClone := phaseCreditSpec_seq_freeOnly_exact hM (stringClone_phaseCredit_aff hM hpeer)
  have hTC := hTrust.seq hClone
  exact (hLoad.seq hTC).mono (by omega) (by omega) (by omega) (by omega)

theorem w4StageP1UntrustedCli_small_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall : 40 ≤ HasFineReallocCredit.smallMaxReq M)
    {rd : ReadRule} {DeserEnv : List (BitVec 8) → List AllocEvent → Prop}
    {files : FsFiles} {sessDir peersDir : DirGhost} {peer : AddrGhost}
    {maxDir maxEntries maxVal fileCap deserCum deserLive deserPeak deserMaxReq : Nat}
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hfileCap : ∀ p bs, rd files p = .ok bs → bs.length ≤ fileCap)
    (hdeser : ∀ bs, bs.length ≤ 2097152 →
      PhaseCreditSpec M (DeserEnv bs) deserCum deserLive deserPeak deserMaxReq) :
    let cap := max maxVal fileCap
    let cL := w4BoxedStepCum 24 (sessLoadPollDeltaCum cap deserCum)
    let lL := w4BoxedStepLive 24 (sessLoadPollDeltaLive cap deserLive)
    let pL := w4BoxedStepPeak 24 (sessLoadPollDeltaPeak cap deserPeak)
    let rL := w4BoxedStepMaxReq 24 (sessLoadPollMaxReq cap deserMaxReq)
    let cT := w4BoxedStepCum 32 (smallStorePollDeltaCum cap maxEntries)
    let lT := w4BoxedStepLive 32 (smallStorePollDeltaLive cap maxEntries)
    let pT := w4BoxedStepPeak 32 (smallStorePollDeltaPeak cap maxEntries)
    let rT := w4BoxedStepMaxReq 32 (smallStorePollMaxReq cap maxEntries)
    PhaseCreditSpec M (W4StageP1UntrustedCliEnv rd DeserEnv files sessDir peersDir peer)
      (cL + cT + (2 * 40 + 9539))
      (lL + lT)
      (max pL (lL + max pT lT))
      (max rL (max rT 40)) := by
  dsimp only
  have hLoad := w4SessLoadStep_phaseCredit hM hdcSess hdir hpeer (fun bs hr => hfileCap _ bs hr) hdeser
  have hTrust := w4PeerSmallStoreStep_phaseCredit hM 32 hdcPeers hdir hpeer
    (fun bs hr => hfileCap _ bs hr)
  have hClone := phaseCreditSpec_seq_freeOnly_exact hM
    (stringClone_phaseCredit_small hM hpeer hsmall)
  have hTC := hTrust.seq hClone
  exact (hLoad.seq hTC).mono (by omega) (by omega) (by omega) (by omega)

/-! ## Stage P2 `InitialStateEnv` & Key-Lookup + Handshake Composer -/

def w4SpqrInitReq (authKeyLen : Nat) : Nat := 4 * authKeyLen + 4096
def w4SpqrInitCum (authKeyLen : Nat) : Nat := 128 * (2 * w4SpqrInitReq authKeyLen + 9539)
def w4SpqrInitLive (authKeyLen : Nat) : Nat := 128 * (w4SpqrInitReq authKeyLen + 8195)
def w4SpqrInitPeak (authKeyLen : Nat) : Nat := 128 * (w4SpqrInitReq authKeyLen + 8195)

/-- `32`-byte root-key specialization (`x_spqr.p.authKey.length ≤ 32 ⇒ R ≤ 4224`) of
`SpqrCodecPeakSpec.initialState_phaseCreditSpec`. -/
theorem w4SpqrInit32_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress) (x_spqr : InitialStateGhost)
    (hkey : x_spqr.p.authKey.length ≤ 32) :
    PhaseCreditSpec M (InitialStateEnv F x_spqr)
      (w4SpqrInitCum 32) (w4SpqrInitLive 32) (w4SpqrInitPeak 32) 4224 := by
  have h0 := initialState_phaseCreditSpec hM F x_spqr
  have hreq : w4SpqrInitReq x_spqr.p.authKey.length ≤ w4SpqrInitReq 32 := by
    dsimp [w4SpqrInitReq]; omega
  have hcum : w4SpqrInitCum x_spqr.p.authKey.length ≤ w4SpqrInitCum 32 :=
    Nat.mul_le_mul_left 128 (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hreq) 9539)
  have hlive : w4SpqrInitLive x_spqr.p.authKey.length ≤ w4SpqrInitLive 32 :=
    Nat.mul_le_mul_left 128 (Nat.add_le_add_right hreq 8195)
  exact h0.mono hcum hlive hlive hreq

/-- Stage P2 (Path A / Path C) key-lookup & PQXDH responder handshake envelope in exact binary
call order (`SpkGet → KpkGet → opt PkGet → IdKp → PreAccept → InitialStateEnv → BobInit →
IdRegId → FreeOnlyEvs` early-exit/drop closure). -/
def W4StageP2ShapeEnv (hasOpk : Bool)
    (SpkGet KpkGet PkGet IdKp PreAccept SpqrInit BobInit IdRegId : List AllocEvent → Prop)
    (evs : List AllocEvent) : Prop :=
  SeqEnv
    (SeqEnv SpkGet
      (SeqEnv KpkGet
        (SeqEnv (if hasOpk then PkGet else (· = []))
          (SeqEnv IdKp
            (SeqEnv PreAccept
              (SeqEnv SpqrInit
                (SeqEnv BobInit IdRegId)))))))
    FreeOnlyEvs evs

theorem w4StageP2Shape_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hasOpk : Bool)
    {SpkGet KpkGet PkGet IdKp PreAccept SpqrInit BobInit IdRegId : List AllocEvent → Prop}
    {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ c₃ l₃ p₃ r₃ c₄ l₄ p₄ r₄
     c₅ l₅ p₅ r₅ c₆ l₆ p₆ r₆ c₇ l₇ p₇ r₇ c₈ l₈ p₈ r₈ : Nat}
    (hSpk : PhaseCreditSpec M SpkGet c₁ l₁ p₁ r₁)
    (hKpk : PhaseCreditSpec M KpkGet c₂ l₂ p₂ r₂)
    (hPk : hasOpk = true → PhaseCreditSpec M PkGet c₃ l₃ p₃ r₃)
    (hKp : PhaseCreditSpec M IdKp c₄ l₄ p₄ r₄)
    (hPre : PhaseCreditSpec M PreAccept c₅ l₅ p₅ r₅)
    (hSpqr : PhaseCreditSpec M SpqrInit c₆ l₆ p₆ r₆)
    (hBob : PhaseCreditSpec M BobInit c₇ l₇ p₇ r₇)
    (hReg : PhaseCreditSpec M IdRegId c₈ l₈ p₈ r₈) :
    PhaseCreditSpec M
      (W4StageP2ShapeEnv hasOpk SpkGet KpkGet PkGet IdKp PreAccept SpqrInit BobInit IdRegId)
      (c₁ + c₂ + c₃ + c₄ + c₅ + c₆ + c₇ + c₈)
      (l₁ + l₂ + l₃ + l₄ + l₅ + l₆ + l₇ + l₈)
      (max p₁ (l₁ + max p₂ (l₂ + max p₃ (l₃ + max p₄
        (l₄ + max p₅ (l₅ + max p₆ (l₆ + max p₇ (l₇ + p₈))))))))
      (max (max (max r₁ r₂) (max r₃ r₄)) (max (max r₅ r₆) (max r₇ r₈))) := by
  have hOptPk := phaseCreditSpec_ite_nil hasOpk hPk
  have h78 := hBob.seq hReg
  have h68 := hSpqr.seq h78
  have h58 := hPre.seq h68
  have h48 := hKp.seq h58
  have h38 := hOptPk.seq h48
  have h28 := hKpk.seq h38
  have h18 := hSpk.seq h28
  exact (phaseCreditSpec_seq_freeOnly_exact hM h18).mono
    (by omega) (by omega) (by omega) (by omega)

/-! ## Stage P4 Concrete CLI Composers (`Matched`, `PathA` `0`-prev, & `PathC` `prev1`) -/

/-- Concrete CLI Stage P4 Path B (`Matched`) envelope in exact binary order:
`idSave (32 B)` → `sessStore 0-prev (32 B)` → `FreeOnlyEvs`. -/
def W4StageP4MatchedCliEnv (rd : ReadRule) (files : FsFiles)
    (peersDir sessDir : DirGhost) (peer : AddrGhost)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (W4SmallStoreStepEnv 32 rd files peersDir (addressText peer.val))
    (SeqEnv (W4SessStoreStepEnv sessDir peer g_rec r_rec) FreeOnlyEvs) evs

theorem w4StageP4MatchedCli_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {rd : ReadRule} {files : FsFiles}
    {peersDir sessDir : DirGhost} {peer : AddrGhost}
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hfileCap : ∀ p bs, rd files p = .ok bs → bs.length ≤ fileCap) :
    let cap := max maxVal fileCap
    let cS := w4BoxedStepCum 32 (smallStorePollDeltaCum cap maxEntries)
    let lS := w4BoxedStepLive 32 (smallStorePollDeltaLive cap maxEntries)
    let pS := w4BoxedStepPeak 32 (smallStorePollDeltaPeak cap maxEntries)
    let rS := w4BoxedStepMaxReq 32 (smallStorePollMaxReq cap maxEntries)
    let cSt := w4BoxedStepCum 32 (sessStorePollDeltaCum (recordSerializeCum g_rec r_rec) maxEntries)
    let lSt := w4BoxedStepLive 32
      (sessStorePollDeltaLive (recordSerializeOutLarge M g_rec r_rec) maxEntries)
    let pSt := w4BoxedStepPeak 32
      (sessStorePollDeltaPeak (recordSerializePeak M g_rec r_rec) maxEntries)
    let rSt := w4BoxedStepMaxReq 32
      (sessStorePollMaxReq (recordSerializeMaxReq g_rec r_rec) maxEntries)
    PhaseCreditSpec M (W4StageP4MatchedCliEnv rd files peersDir sessDir peer g_rec r_rec)
      (cS + cSt) (lS + lSt) (max pS (lS + pSt)) (max rS rSt) := by
  intro cap cS lS pS rS cSt lSt pSt rSt
  have hSave := w4PeerSmallStoreStep_phaseCredit hM 32 hdcPeers hdir hpeer
    (fun bs hr => hfileCap _ bs hr)
  have hStore := phaseCreditSpec_seq_freeOnly_exact hM
    (w4SessStoreStep_phaseCredit hM g_rec r_rec hdcSess hpeer)
  exact hSave.seq hStore

/-- Concrete CLI Stage P4 Path A (`0`-prev) envelope in exact binary order:
`idSave (32 B)` → `kpkMark (32 B)` → `opt pkRemove (16 B)` → `sessStore 0-prev (32 B)` → `FreeOnlyEvs`. -/
def W4StageP4PathACliEnv (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peersDir kpkDir opkDir sessDir : DirGhost) (peer : AddrGhost)
    (kpkName : List (BitVec 8)) (opkId : BitVec 32)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (W4SmallStoreStepEnv 32 rd files peersDir (addressText peer.val))
    (SeqEnv (W4SmallStoreStepEnv 32 rd files kpkDir kpkName)
      (SeqEnv (if hasOpk then W4SmallStoreStepEnv 16 rd files opkDir (keyName opkId) else (· = []))
        (SeqEnv (W4SessStoreStepEnv sessDir peer g_rec r_rec) FreeOnlyEvs))) evs

theorem w4StageP4PathACli_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} (opkId : BitVec 32)
    (g_rec : RecordGhost) (r_rec : SessionRecord (List (BitVec 8)))
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hkpkName : kpkName.length ≤ 64)
    (hfileCap : ∀ p bs, rd files p = .ok bs → bs.length ≤ fileCap) :
    let cap := max maxVal fileCap
    let c32 := w4BoxedStepCum 32 (smallStorePollDeltaCum cap maxEntries)
    let l32 := w4BoxedStepLive 32 (smallStorePollDeltaLive cap maxEntries)
    let p32 := w4BoxedStepPeak 32 (smallStorePollDeltaPeak cap maxEntries)
    let r32 := w4BoxedStepMaxReq 32 (smallStorePollMaxReq cap maxEntries)
    let c16 := w4BoxedStepCum 16 (smallStorePollDeltaCum cap maxEntries)
    let l16 := w4BoxedStepLive 16 (smallStorePollDeltaLive cap maxEntries)
    let p16 := w4BoxedStepPeak 16 (smallStorePollDeltaPeak cap maxEntries)
    let r16 := w4BoxedStepMaxReq 16 (smallStorePollMaxReq cap maxEntries)
    let cSt := w4BoxedStepCum 32 (sessStorePollDeltaCum (recordSerializeCum g_rec r_rec) maxEntries)
    let lSt := w4BoxedStepLive 32
      (sessStorePollDeltaLive (recordSerializeOutLarge M g_rec r_rec) maxEntries)
    let pSt := w4BoxedStepPeak 32
      (sessStorePollDeltaPeak (recordSerializePeak M g_rec r_rec) maxEntries)
    let rSt := w4BoxedStepMaxReq 32
      (sessStorePollMaxReq (recordSerializeMaxReq g_rec r_rec) maxEntries)
    PhaseCreditSpec M
      (W4StageP4PathACliEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer kpkName opkId
        g_rec r_rec)
      (c32 + c32 + c16 + cSt)
      (l32 + l32 + l16 + lSt)
      (max p32 (l32 + max p32 (l32 + max p16 (l16 + pSt))))
      (max (max r32 r32) (max r16 rSt)) := by
  dsimp only
  have hSave := w4PeerSmallStoreStep_phaseCredit hM 32 hdcPeers hdir hpeer
    (fun bs hr => hfileCap _ bs hr)
  have hMark := w4SmallStoreStep_phaseCredit hM 32 hdcKpk hdir hkpkName
    (fun bs hr => hfileCap _ bs hr)
  have hRem := phaseCreditSpec_ite_nil hasOpk fun _ =>
    w4KeyIdSmallStoreStep_phaseCredit hM 16 opkId hdcOpk hdir (fun bs hr => hfileCap _ bs hr)
  have hStore := phaseCreditSpec_seq_freeOnly_exact hM
    (w4SessStoreStep_phaseCredit hM g_rec r_rec hdcSess hpeer)
  have h34 := hRem.seq hStore
  have h24 := hMark.seq h34
  exact (hSave.seq h24).mono (by omega) (by omega) (by omega) (by omega)

/-- Concrete CLI Stage P4 Path C (`prev1`) envelope in exact binary order:
`idSave (32 B)` → `kpkMark (32 B)` → `opt pkRemove (16 B)` → `sessStorePrev1 (32 B)` → `FreeOnlyEvs`. -/
def W4StageP4PathCCliEnv (hasOpk : Bool) (rd : ReadRule) (files : FsFiles)
    (peersDir kpkDir opkDir sessDir : DirGhost) (peer : AddrGhost)
    (kpkName : List (BitVec 8)) (opkId : BitVec 32)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (enc : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  SeqEnv (W4SmallStoreStepEnv 32 rd files peersDir (addressText peer.val))
    (SeqEnv (W4SmallStoreStepEnv 32 rd files kpkDir kpkName)
      (SeqEnv (if hasOpk then W4SmallStoreStepEnv 16 rd files opkDir (keyName opkId) else (· = []))
        (SeqEnv (W4SessStorePrev1StepEnv sessDir peer G sess enc) FreeOnlyEvs))) evs

theorem w4StageP4PathCCli_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hasOpk : Bool) {rd : ReadRule} {files : FsFiles}
    {peersDir kpkDir opkDir sessDir : DirGhost} {peer : AddrGhost}
    {kpkName : List (BitVec 8)} (opkId : BitVec 32)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (enc : List (BitVec 8))
    {maxDir maxEntries maxVal fileCap : Nat}
    (hdcPeers : DirDomainCaps maxDir maxEntries maxVal peersDir)
    (hdcKpk : DirDomainCaps maxDir maxEntries maxVal kpkDir)
    (hdcOpk : DirDomainCaps maxDir maxEntries maxVal opkDir)
    (hdcSess : DirDomainCaps maxDir maxEntries maxVal sessDir)
    (hdir : maxDir ≤ 64)
    (hpeer : peer.name.bytes.length ≤ 40)
    (hkpkName : kpkName.length ≤ 64)
    (hfileCap : ∀ p bs, rd files p = .ok bs → bs.length ≤ fileCap) :
    let cap := max maxVal fileCap
    let c32 := w4BoxedStepCum 32 (smallStorePollDeltaCum cap maxEntries)
    let l32 := w4BoxedStepLive 32 (smallStorePollDeltaLive cap maxEntries)
    let p32 := w4BoxedStepPeak 32 (smallStorePollDeltaPeak cap maxEntries)
    let r32 := w4BoxedStepMaxReq 32 (smallStorePollMaxReq cap maxEntries)
    let c16 := w4BoxedStepCum 16 (smallStorePollDeltaCum cap maxEntries)
    let l16 := w4BoxedStepLive 16 (smallStorePollDeltaLive cap maxEntries)
    let p16 := w4BoxedStepPeak 16 (smallStorePollDeltaPeak cap maxEntries)
    let r16 := w4BoxedStepMaxReq 16 (smallStorePollMaxReq cap maxEntries)
    let cSt := w4BoxedStepCum 32 (sessStorePollDeltaCum (serializePrev1Cum G sess enc) maxEntries)
    let lSt := w4BoxedStepLive 32
      (sessStorePollDeltaLive (serializePrev1OutLarge M G sess enc) maxEntries)
    let pSt := w4BoxedStepPeak 32
      (sessStorePollDeltaPeak (serializePrev1Peak M G sess enc) maxEntries)
    let rSt := w4BoxedStepMaxReq 32
      (sessStorePollMaxReq (serializePrev1MaxReq G sess enc) maxEntries)
    PhaseCreditSpec M
      (W4StageP4PathCCliEnv hasOpk rd files peersDir kpkDir opkDir sessDir peer kpkName opkId
        G sess enc)
      (c32 + c32 + c16 + cSt)
      (l32 + l32 + l16 + lSt)
      (max p32 (l32 + max p32 (l32 + max p16 (l16 + pSt))))
      (max (max r32 r32) (max r16 rSt)) := by
  dsimp only
  have hSave := w4PeerSmallStoreStep_phaseCredit hM 32 hdcPeers hdir hpeer
    (fun bs hr => hfileCap _ bs hr)
  have hMark := w4SmallStoreStep_phaseCredit hM 32 hdcKpk hdir hkpkName
    (fun bs hr => hfileCap _ bs hr)
  have hRem := phaseCreditSpec_ite_nil hasOpk fun _ =>
    w4KeyIdSmallStoreStep_phaseCredit hM 16 opkId hdcOpk hdir (fun bs hr => hfileCap _ bs hr)
  have hStore := phaseCreditSpec_seq_freeOnly_exact hM
    (w4SessStorePrev1Step_phaseCredit hM G sess enc hdcSess hpeer)
  have h34 := hRem.seq hStore
  have h24 := hMark.seq h34
  exact (hSave.seq h24).mono (by omega) (by omega) (by omega) (by omega)

/-- Bundled `DirDomainCaps 26 0 0` predicate across all 7 directories of `StoresGhost.opened`. -/
theorem opened_all_dirDomainCaps :
    DirDomainCaps 26 0 0 StoresGhost.opened.identity.own ∧
    DirDomainCaps 26 0 0 StoresGhost.opened.identity.peers ∧
    DirDomainCaps 26 0 0 StoresGhost.opened.signed ∧
    DirDomainCaps 26 0 0 StoresGhost.opened.kyber.oneTime ∧
    DirDomainCaps 26 0 0 StoresGhost.opened.kyber.lastResort ∧
    DirDomainCaps 26 0 0 StoresGhost.opened.oneTime ∧
    DirDomainCaps 26 0 0 StoresGhost.opened.sessions :=
  ⟨dirDomainCaps_opened_own, dirDomainCaps_opened_peers, dirDomainCaps_opened_signed,
   dirDomainCaps_opened_kpkOt, dirDomainCaps_opened_kpkLr, dirDomainCaps_opened_opk,
   dirDomainCaps_opened_sess⟩

end LibsignalBinary.Proofs.PeakBudget.W4OuterStageHelpers
