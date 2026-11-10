/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit

/-!
# Sequential `PhaseCreditSpec` Combinators for W4 Outer `process_prekey`

`GeneratedLean`-free `PhaseCreditSpec` combinators in binary execution order for W4 `decrypt_prekey` /
`process_prekey`: trailing `FreeOnlyEvs` suffixes, optional conditional steps, 3-way and 4-way arm
dispatch, boxed store-future steps, `StringCloneEnv` / `SignalProtocolError` allocations, and
Stage P1, Stage P4, and `SlotW4` pipelines.
-/

@[expose] public section

namespace LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers

set_option autoImplicit false

open CryptoVerification.LibsignalSessionRepr (VecGhost)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel SeqEnv FreeOnlyEvs
   rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (StringCloneEnv stringCloneEvents stringCloneEvents_eq_of_env)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
  (HasFineReallocCredit)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ModelHyps PhaseCreditSpec FreeOnlyAlign16Evs)

/-! ## 1. Trailing `FreeOnlyEvs`, Optional Steps, and Multi-Arm Dispatch -/

theorem phaseCreditSpec_seq_freeOnly {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (SeqEnv E FreeOnlyEvs) c l (max p l) r := by
  exact (h.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
    (by omega) (by omega) (by omega) (by omega)

theorem phaseCreditSpec_seq_freeOnly_of_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec M E c l p r) (hlp : l ≤ p) :
    PhaseCreditSpec M (SeqEnv E FreeOnlyEvs) c l p r := by
  exact (phaseCreditSpec_seq_freeOnly hM h).mono
    (Nat.le_refl _) (Nat.le_refl _) (by omega) (Nat.le_refl _)

theorem phaseCreditSpec_seq_freeOnly_pred {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E F : List AllocEvent → Prop} {c l p r : Nat}
    (hF : ∀ evs, F evs → FreeOnlyEvs evs)
    (h : PhaseCreditSpec M E c l p r) (hlp : l ≤ p) :
    PhaseCreditSpec M (SeqEnv E F) c l p r := by
  exact (h.seq (PhaseCreditSpec.of_freeOnlyEvs_hyps hM hF)).mono
    (by omega) (by omega) (by omega) (by omega)

/-- Optional binary step `if cond then E else (· = [])`. -/
theorem phaseCreditSpec_ite_nil {M : AllocCostModel} [HasFineReallocCredit M]
    (cond : Bool) {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : cond = true → PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (if cond then E else (· = [])) c l p r := by
  cases hcond : cond
  · simpa [hcond] using (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · simpa [hcond] using h hcond

theorem phaseCreditSpec_dite_nil {M : AllocCostModel} [HasFineReallocCredit M]
    (P : Prop) [Decidable P] {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : P → PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (if P then E else (· = [])) c l p r := by
  by_cases hP : P
  · simpa [hP] using h hP
  · simpa [hP] using (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

theorem phaseCreditSpec_or3 {M : AllocCostModel} [HasFineReallocCredit M]
    {E E₁ E₂ E₃ : List AllocEvent → Prop}
    {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ c₃ l₃ p₃ r₃ : Nat}
    (himp : ∀ evs, E evs → E₁ evs ∨ E₂ evs ∨ E₃ evs)
    (h₁ : PhaseCreditSpec M E₁ c₁ l₁ p₁ r₁)
    (h₂ : PhaseCreditSpec M E₂ c₂ l₂ p₂ r₂)
    (h₃ : PhaseCreditSpec M E₃ c₃ l₃ p₃ r₃) :
    PhaseCreditSpec M E
      (max c₁ (max c₂ c₃))
      (max l₁ (max l₂ l₃))
      (max p₁ (max p₂ p₃))
      (max r₁ (max r₂ r₃)) := by
  exact PhaseCreditSpec.or_of_imp himp h₁ (h₂.or h₃)

/-- 4-arm disjunction combinator (`Untrusted | PathA | PathB | PathC`). -/
theorem phaseCreditSpec_or4 {M : AllocCostModel} [HasFineReallocCredit M]
    {E E₁ E₂ E₃ E₄ : List AllocEvent → Prop}
    {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ c₃ l₃ p₃ r₃ c₄ l₄ p₄ r₄ : Nat}
    (himp : ∀ evs, E evs → E₁ evs ∨ E₂ evs ∨ E₃ evs ∨ E₄ evs)
    (h₁ : PhaseCreditSpec M E₁ c₁ l₁ p₁ r₁)
    (h₂ : PhaseCreditSpec M E₂ c₂ l₂ p₂ r₂)
    (h₃ : PhaseCreditSpec M E₃ c₃ l₃ p₃ r₃)
    (h₄ : PhaseCreditSpec M E₄ c₄ l₄ p₄ r₄) :
    PhaseCreditSpec M E
      (max (max c₁ c₂) (max c₃ c₄))
      (max (max l₁ l₂) (max l₃ l₄))
      (max (max p₁ p₂) (max p₃ p₄))
      (max (max r₁ r₂) (max r₃ r₄)) := by
  refine PhaseCreditSpec.or_of_imp ?_ (h₁.or h₂) (h₃.or h₄)
  intro evs hevs
  rcases himp evs hevs with h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-! ## 2. Boxed Store-Future Steps (`BoxAlloc → Poll → BoxDealloc`) -/

/-- Boxed store-future allocation predicate. -/
def BoxPtrAllocEnv (boxSize : Nat) (evs : List AllocEvent) : Prop :=
  ∃ boxPtr : BitVec 64, boxPtr ≠ 0#64 ∧ evs = rustAllocEvents boxSize 8

/-- Boxed store-future deallocation predicate. -/
def BoxPtrDeallocEnv (boxSize : Nat) (evs : List AllocEvent) : Prop :=
  evs = rustDeallocEvents boxSize 8

theorem boxPtrAllocEnv_events {boxSize : Nat} {evs : List AllocEvent}
    (h : BoxPtrAllocEnv boxSize evs) : evs = rustAllocEvents boxSize 8 := by
  rcases h with ⟨_, _, rfl⟩
  rfl

theorem boxPtrDeallocEnv_freeOnly {boxSize : Nat} {evs : List AllocEvent}
    (h : BoxPtrDeallocEnv boxSize evs) : FreeOnlyEvs evs := by
  subst h
  exact FreeOnlyAlign16Evs.toFreeOnlyEvs
    (FreeOnlyAlign16Evs.rustDealloc (by decide) boxSize)

theorem boxAlloc_phaseCredit_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {BoxEv : List AllocEvent → Prop} {boxSz : Nat}
    (hBox : ∀ evs, BoxEv evs → evs = rustAllocEvents boxSz 8) :
    PhaseCreditSpec M BoxEv (2 * boxSz + 9539) (boxSz + 8195) (boxSz + 8195) boxSz := by
  exact PhaseCreditSpec.of_imp hBox
    (PhaseCreditSpec.rustAlloc_aff (req := boxSz) (al := 8) hM (by decide))

theorem boxAlloc_phaseCredit_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {BoxEv : List AllocEvent → Prop} {boxSz : Nat}
    (hBox : ∀ evs, BoxEv evs → evs = rustAllocEvents boxSz 8)
    (hsz : boxSz ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M BoxEv (2 * boxSz + 9539) 0 0 boxSz := by
  refine (PhaseCreditSpec.of_imp hBox
    (PhaseCreditSpec.rustAlloc_small_any (req := boxSz) (al := 8) hM (by decide) hsz)).mono
    (hM.smallAlloc_le hsz) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl boxSz)

theorem boxDealloc_phaseCredit (M : AllocCostModel) [HasFineReallocCredit M]
    {DeallocEv : List AllocEvent → Prop} {boxSz : Nat}
    (hDealloc : ∀ evs, DeallocEv evs → evs = rustDeallocEvents boxSz 8) :
    PhaseCreditSpec M DeallocEv 0 0 0 0 := by
  exact PhaseCreditSpec.of_imp hDealloc
    (PhaseCreditSpec.rustDealloc_align16 M (req := boxSz) (al := 8) (by decide))

/-- Regime-uniform `PhaseCreditSpec` for a boxed store-future step (`Box::new → poll → Box::drop`).
-/
theorem boxStep_phaseCredit_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {BoxEv PollEnv DeallocEv : List AllocEvent → Prop}
    {boxSz c l p r : Nat}
    (hBox : ∀ evs, BoxEv evs → evs = rustAllocEvents boxSz 8)
    (hDealloc : ∀ evs, DeallocEv evs → evs = rustDeallocEvents boxSz 8)
    (hPoll : PhaseCreditSpec M PollEnv c l p r) :
    PhaseCreditSpec M (SeqEnv BoxEv (SeqEnv PollEnv DeallocEv))
      ((2 * boxSz + 9539) + c)
      ((boxSz + 8195) + l)
      ((boxSz + 8195) + max l p)
      (max boxSz r) := by
  have hA := boxAlloc_phaseCredit_aff hM hBox
  have hD := boxDealloc_phaseCredit M hDealloc
  have hPD := hPoll.seq hD
  exact (hA.seq hPD).mono (by omega) (by omega) (by omega) (by omega)

/-- Small-regime (`boxSz ≤ smallMaxReq M`) `PhaseCreditSpec` for a boxed store-future step. -/
theorem boxStep_phaseCredit_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {BoxEv PollEnv DeallocEv : List AllocEvent → Prop}
    {boxSz c l p r : Nat}
    (hBox : ∀ evs, BoxEv evs → evs = rustAllocEvents boxSz 8)
    (hDealloc : ∀ evs, DeallocEv evs → evs = rustDeallocEvents boxSz 8)
    (hsz : boxSz ≤ HasFineReallocCredit.smallMaxReq M)
    (hPoll : PhaseCreditSpec M PollEnv c l p r) (hlp : l ≤ p) :
    PhaseCreditSpec M (SeqEnv BoxEv (SeqEnv PollEnv DeallocEv))
      ((2 * boxSz + 9539) + c) l p (max boxSz r) := by
  have hA := boxAlloc_phaseCredit_small hM hBox hsz
  have hD := boxDealloc_phaseCredit M hDealloc
  have hPD := hPoll.seq hD
  exact (hA.seq hPD).mono (by omega) (by omega) (by omega) (by omega)

/-! ## 3. `StringCloneEnv` and `192`-Byte `SignalProtocolError` Allocation -/

theorem stringClone_phaseCredit_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {g : VecGhost} {maxLen : Nat}
    (hlen : g.bytes.length ≤ maxLen) :
    PhaseCreditSpec M (StringCloneEnv g)
      (2 * maxLen + 9539) (maxLen + 8195) (maxLen + 8195) maxLen := by
  by_cases hz : g.bytes.length = 0
  · refine (PhaseCreditSpec.of_eq_nil (M := M) ?_).mono
      (by omega) (by omega) (by omega) (by omega)
    intro evs hevs
    rw [stringCloneEvents_eq_of_env hevs]
    simp [stringCloneEvents, hz]
  · have hEq : ∀ evs, StringCloneEnv g evs → evs = rustAllocEvents g.bytes.length 1 := by
      intro evs hevs
      rw [stringCloneEvents_eq_of_env hevs]
      simp [stringCloneEvents, hz]
    exact (PhaseCreditSpec.of_imp hEq
      (PhaseCreditSpec.rustAlloc_aff (req := g.bytes.length) (al := 1) hM (by decide))).mono
      (by omega) (by omega) (by omega) hlen

theorem stringClone_phaseCredit_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {g : VecGhost} {maxLen : Nat}
    (hlen : g.bytes.length ≤ maxLen) (hsmall : maxLen ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (StringCloneEnv g) (2 * maxLen + 9539) 0 0 maxLen := by
  by_cases hz : g.bytes.length = 0
  · refine (PhaseCreditSpec.of_eq_nil (M := M) ?_).mono
      (by omega) (Nat.le_refl _) (Nat.le_refl _) (by omega)
    intro evs hevs
    rw [stringCloneEvents_eq_of_env hevs]
    simp [stringCloneEvents, hz]
  · have hEq : ∀ evs, StringCloneEnv g evs → evs = rustAllocEvents g.bytes.length 1 := by
      intro evs hevs
      rw [stringCloneEvents_eq_of_env hevs]
      simp [stringCloneEvents, hz]
    have hle : g.bytes.length ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hlen hsmall
    exact (PhaseCreditSpec.of_imp hEq
      (PhaseCreditSpec.rustAlloc_small_any (req := g.bytes.length) (al := 1) hM (by decide) hle)).mono
      (Nat.le_trans (hM.smallAlloc_le hle) (by omega)) (Nat.le_refl _) (Nat.le_refl _) hlen

theorem alloc192_phaseCredit_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {ErrEv : List AllocEvent → Prop}
    (hErr : ∀ evs, ErrEv evs → evs = rustAllocEvents 192 8) :
    PhaseCreditSpec M ErrEv 9923 8387 8387 192 := by
  exact (PhaseCreditSpec.of_imp hErr
    (PhaseCreditSpec.rustAlloc_aff (req := 192) (al := 8) hM (by decide))).mono
    (by omega) (by omega) (by omega) (Nat.le_refl _)

theorem alloc192_phaseCredit_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {ErrEv : List AllocEvent → Prop}
    (hErr : ∀ evs, ErrEv evs → evs = rustAllocEvents 192 8)
    (hsmall : 192 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M ErrEv 9923 0 0 192 := by
  exact (PhaseCreditSpec.of_imp hErr
    (PhaseCreditSpec.rustAlloc_small_any (req := 192) (al := 8) hM (by decide) hsmall)).mono
    (Nat.le_trans (hM.smallAlloc_le hsmall) (by omega))
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-! ## 4. Stage P1, Stage P4, and `SlotW4` Sequential Pipelines -/

theorem stageP1OkShape_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    {LoadStep TrustStep : List AllocEvent → Prop}
    {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (hLoad : PhaseCreditSpec M LoadStep c₁ l₁ p₁ r₁)
    (hTrust : PhaseCreditSpec M TrustStep c₂ l₂ p₂ r₂) :
    PhaseCreditSpec M (SeqEnv LoadStep TrustStep)
      (c₁ + c₂) (l₁ + l₂) (max p₁ (l₁ + p₂)) (max r₁ r₂) :=
  hLoad.seq hTrust

/-- Regime-uniform Stage P1 untrusted-identity pipeline (`LoadStep → TrustStep → StringCloneEnv → FreeOnlyEvs`).
-/
theorem stageP1UntrustedShape_phaseCredit_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {LoadStep TrustStep : List AllocEvent → Prop}
    {peerName : VecGhost} {maxPeerLen c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (hLoad : PhaseCreditSpec M LoadStep c₁ l₁ p₁ r₁)
    (hTrust : PhaseCreditSpec M TrustStep c₂ l₂ p₂ r₂)
    (hPeer : peerName.bytes.length ≤ maxPeerLen) :
    PhaseCreditSpec M
      (SeqEnv LoadStep (SeqEnv TrustStep (SeqEnv (StringCloneEnv peerName) FreeOnlyEvs)))
      (c₁ + c₂ + (2 * maxPeerLen + 9539))
      (l₁ + l₂ + (maxPeerLen + 8195))
      (max p₁ (l₁ + max p₂ (l₂ + (maxPeerLen + 8195))))
      (max r₁ (max r₂ maxPeerLen)) := by
  have hClone := phaseCreditSpec_seq_freeOnly_of_le hM
    (stringClone_phaseCredit_aff hM hPeer) (Nat.le_refl _)
  have hTC := hTrust.seq hClone
  exact (hLoad.seq hTC).mono (by omega) (by omega) (by omega) (by omega)

/-- Small-regime Stage P1 untrusted-identity pipeline. -/
theorem stageP1UntrustedShape_phaseCredit_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {LoadStep TrustStep : List AllocEvent → Prop}
    {peerName : VecGhost} {maxPeerLen c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (hLoad : PhaseCreditSpec M LoadStep c₁ l₁ p₁ r₁)
    (hTrust : PhaseCreditSpec M TrustStep c₂ l₂ p₂ r₂)
    (hPeer : peerName.bytes.length ≤ maxPeerLen)
    (hSmall : maxPeerLen ≤ HasFineReallocCredit.smallMaxReq M) (hlp₂ : l₂ ≤ p₂) :
    PhaseCreditSpec M
      (SeqEnv LoadStep (SeqEnv TrustStep (SeqEnv (StringCloneEnv peerName) FreeOnlyEvs)))
      (c₁ + c₂ + (2 * maxPeerLen + 9539))
      (l₁ + l₂)
      (max p₁ (l₁ + p₂))
      (max r₁ (max r₂ maxPeerLen)) := by
  have hClone := phaseCreditSpec_seq_freeOnly_of_le hM
    (stringClone_phaseCredit_small hM hPeer hSmall) (Nat.le_refl _)
  have hTC := hTrust.seq hClone
  exact (hLoad.seq hTC).mono (by omega) (by omega) (by omega) (by omega)

/-- Stage P4 Path B (`Matched`) pipeline (`SaveStep → StoreStep → FreeOnlyEvs`). -/
theorem stageP4MatchedShape_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {SaveStep StoreStep : List AllocEvent → Prop}
    {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (hSave : PhaseCreditSpec M SaveStep c₁ l₁ p₁ r₁)
    (hStore : PhaseCreditSpec M StoreStep c₂ l₂ p₂ r₂)
    (hlp₂ : l₂ ≤ p₂) :
    PhaseCreditSpec M (SeqEnv SaveStep (SeqEnv StoreStep FreeOnlyEvs))
      (c₁ + c₂) (l₁ + l₂) (max p₁ (l₁ + p₂)) (max r₁ r₂) := by
  have hStoreFree := phaseCreditSpec_seq_freeOnly_of_le hM hStore hlp₂
  exact (hSave.seq hStoreFree).mono (by omega) (by omega) (by omega) (by omega)

/-- Stage P4 full pipeline (`SaveStep → MarkStep → opt RemoveStep → StoreStep → FreeOnlyEvs`). -/
theorem stageP4FullShape_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hasOpk : Bool)
    {SaveStep MarkStep RemoveStep StoreStep : List AllocEvent → Prop}
    {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ c₃ l₃ p₃ r₃ c₄ l₄ p₄ r₄ : Nat}
    (hSave : PhaseCreditSpec M SaveStep c₁ l₁ p₁ r₁)
    (hMark : PhaseCreditSpec M MarkStep c₂ l₂ p₂ r₂)
    (hRem : hasOpk = true → PhaseCreditSpec M RemoveStep c₃ l₃ p₃ r₃)
    (hStore : PhaseCreditSpec M StoreStep c₄ l₄ p₄ r₄)
    (hlp₄ : l₄ ≤ p₄) :
    PhaseCreditSpec M
      (SeqEnv SaveStep
        (SeqEnv MarkStep
          (SeqEnv (if hasOpk then RemoveStep else (· = []))
            (SeqEnv StoreStep FreeOnlyEvs))))
      (c₁ + c₂ + c₃ + c₄)
      (l₁ + l₂ + l₃ + l₄)
      (max p₁ (l₁ + max p₂ (l₂ + max p₃ (l₃ + p₄))))
      (max (max r₁ r₂) (max r₃ r₄)) := by
  have hOptRem := phaseCreditSpec_ite_nil hasOpk hRem
  have hStoreFree := phaseCreditSpec_seq_freeOnly_of_le hM hStore hlp₄
  have h34 := hOptRem.seq hStoreFree
  have h234 := hMark.seq h34
  exact (hSave.seq h234).mono (by omega) (by omega) (by omega) (by omega)

/-- Outer `SlotW4` pipeline (`PksmTryFrom → DecPkSlot → FreeOnlyEvs`). -/
theorem slotW4Shape_phaseCredit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {PksmEnv DecPkEnv : List AllocEvent → Prop}
    {c₁ l₁ p₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (hPksm : PhaseCreditSpec M PksmEnv c₁ l₁ p₁ r₁)
    (hDecPk : PhaseCreditSpec M DecPkEnv c₂ l₂ p₂ r₂)
    (hlp₂ : l₂ ≤ p₂) :
    PhaseCreditSpec M (SeqEnv PksmEnv (SeqEnv DecPkEnv FreeOnlyEvs))
      (c₁ + c₂) (l₁ + l₂) (max p₁ (l₁ + p₂)) (max r₁ r₂) := by
  have hDecFree := phaseCreditSpec_seq_freeOnly_of_le hM hDecPk hlp₂
  exact (hPksm.seq hDecFree).mono (by omega) (by omega) (by omega) (by omega)

end LibsignalBinary.Proofs.PeakBudget.W4OuterHelpers
