/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudget
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak
public import LibsignalBinary.Proofs.PeakBudget.W4InnerHelpers
public import LibsignalBinary.Proofs.PeakBudget.W4PrevDecPeak
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget

/-!
# W4 `init_bob` (`initialize_bob_session`) Peak Live-Heap Bounds

Parametric `(M : AllocCostModel) [HasFineReallocCredit M]` (`ModelHyps M`) sequential
`PhaseCreditSpec` bounds in binary call order for W4 responder session initialization (`init_bob` in
`process_prekey` Stage P2): `W4BoundedEvs` combinators, PQXDH responder primitives (`W4PqxdhAcceptEnv`),
`W4BobSessionBuildEnv`, `W4InitBobEnv`, and Stage P2 `Over`-path composition (`W4StageP2OverBobEnv`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
  rustAllocEvents rustDeallocEvents rustReallocEvents
)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesBudget (
  DoReserveEnv KemSerialize1569Env doReserveEvents
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (
  ConcatEnv ModelHyps PhaseCreditSpec stepEvents_freeOnly_le
)
open LibsignalBinary.Proofs.PeakBudget.W4ArchiveCancelPeak (
  PromoteStateArchiveEnv phaseCredit_promoteStateArchive
)
open LibsignalBinary.Proofs.PeakBudget.W4InnerHelpers (
  phaseCredit_doReserve_small phaseCredit_kemSerialize1569
)
open LibsignalBinary.Proofs.PeakBudget.W4PrevDecPeak (phaseCredit_rustRealloc_aff)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (publicKeySerializeEvents)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (GrowOneSpeEnv)

/-! ## 1. `FreeOnlyEvs` Suffix and `W4BoundedEvs` Combinators -/

/-- `SeqEnv E FreeOnlyEvs` bound preserving `(c, l, p, r)` directly. -/
theorem phaseCredit_seq_freeOnly {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E : List AllocEvent → Prop} {c l p r : Nat}
    (hE : PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (SeqEnv E FreeOnlyEvs) c l p r where
  req_align evs h ev hev := by
    rcases h with h1 | ⟨evs₁, evs₂, rfl, h1, hfo⟩
    · exact hE.req_align evs h1 ev hev
    · rcases List.mem_append.mp hev with he1 | he2
      · exact hE.req_align evs₁ h1 ev he1
      · obtain ⟨al, sz, rfl⟩ := hfo ev he2
        exact ⟨Nat.zero_le r, Nat.le_refl 16⟩
  credit_le st0 {_} h := by
    rcases h with h1 | ⟨evs₁, evs₂, rfl, h1, hfo⟩
    · exact hE.credit_le st0 h1
    · rw [M.stepEvents_append evs₁ evs₂ st0]
      obtain ⟨hc₁, hl₁, hp₁⟩ := hE.credit_le st0 h1
      obtain ⟨hc₂, hl₂, hp₂⟩ :=
        stepEvents_freeOnly_le hM.freeNonInc hfo (M.stepEvents evs₁ st0)
      exact ⟨Nat.le_trans hc₂ hc₁, Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩

def nonFreeCount : List AllocEvent → Nat
  | [] => 0
  | .free _ _ :: tl => nonFreeCount tl
  | _ :: tl => nonFreeCount tl + 1

/-- Bounded-count, bounded-request (`align ≤ 16`) allocator event predicate with interleaved `.free` events.
-/
def W4BoundedEvs (maxOps maxReq : Nat) (evs : List AllocEvent) : Prop :=
  nonFreeCount evs ≤ maxOps ∧
  ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16

private theorem step_single_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {ev : AllocEvent} {maxReq : Nat} (st : M.σ)
    (hSmall : maxReq ≤ HasFineReallocCredit.smallMaxReq M)
    (hreq : eventStepReq ev ≤ maxReq) (hal : eventStepAlign ev ≤ 16) :
    let st' := M.step ev st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + (2 * maxReq + 9539) ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  cases ev with
  | free al sz =>
    obtain ⟨hc, hl, hp⟩ := hM.freeNonInc al sz st
    exact ⟨by omega, hl, hp⟩
  | alloc req =>
    simp only [eventStepReq] at hreq
    have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hSmall
    obtain ⟨hc, hl, hp⟩ := hM.step_alloc_small_any st hle
    have hsa := hM.smallAlloc_le hle
    exact ⟨by omega, hl, hp⟩
  | aligned al req =>
    simp only [eventStepReq, eventStepAlign] at hreq hal
    have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hSmall
    obtain ⟨hc, hl, hp⟩ := hM.step_aligned_small_any st hal hle
    have hsa := hM.smallAlloc_le hle
    exact ⟨by omega, hl, hp⟩
  | realloc al old new =>
    simp only [eventStepReq, eventStepAlign] at hreq hal
    have hnew_le : new ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hSmall
    by_cases hold_le : old ≤ HasFineReallocCredit.smallMaxReq M
    · obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_small_any st hal hold_le hnew_le
      have hsr := hM.smallRealloc_le hnew_le
      exact ⟨by omega, hl, hp⟩
    · have hold_gt : HasFineReallocCredit.smallMaxReq M < old := by omega
      obtain ⟨hc, hl, hp⟩ := hM.step_realloc_large_small_any st hal hold_gt hnew_le
      have hsr := hM.smallRealloc_le hnew_le
      exact ⟨by omega, by omega, hp⟩

private theorem add_step_le {a b c k C : Nat}
    (h1 : b ≤ a + C) (h2 : c ≤ b + k * C) :
    c ≤ a + (k + 1) * C := by
  rw [Nat.succ_mul]
  omega

private theorem max_step_free_le {p0 p1 p2 l0 l1 kL : Nat}
    (hp1 : p1 ≤ p0) (hl1 : l1 ≤ l0) (hp2 : p2 ≤ max p1 (l1 + kL)) :
    p2 ≤ max p0 (l0 + kL) := by
  omega

private theorem max_step_nonFree_le {p0 p1 p2 l0 l1 k L : Nat}
    (hl1 : l1 ≤ l0 + L) (hp1 : p1 ≤ max p0 (l0 + L))
    (hp2 : p2 ≤ max p1 (l1 + k * L)) :
    p2 ≤ max p0 (l0 + (k + 1) * L) := by
  rw [Nat.succ_mul]
  omega

private theorem stepEvents_w4Bounded_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {maxReq : Nat}
    (hSmall : maxReq ≤ HasFineReallocCredit.smallMaxReq M) :
    ∀ (evs : List AllocEvent) (st : M.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      let k := nonFreeCount evs
      HasFineReallocCredit.cumSmall (M.stepEvents evs st) ≤
        HasFineReallocCredit.cumSmall st + k * (2 * maxReq + 9539) ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤
        HasFineReallocCredit.liveLarge st ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤
        HasFineReallocCredit.peakLarge st
  | [], st, _ => by
    simp only [nonFreeCount, AllocCostModel.stepEvents_nil, Nat.zero_mul, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | ev :: tl, st, hra => by
    have hev := hra ev List.mem_cons_self
    have htl : ∀ e ∈ tl, eventStepReq e ≤ maxReq ∧ eventStepAlign e ≤ 16 :=
      fun e he => hra e (List.mem_cons_of_mem ev he)
    cases ev with
    | free al sz =>
      dsimp only [nonFreeCount]
      rw [AllocCostModel.stepEvents_cons]
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.freeNonInc al sz st
      obtain ⟨hc₂, hl₂, hp₂⟩ :=
        stepEvents_w4Bounded_small hM hSmall tl (M.step (.free al sz) st) htl
      exact ⟨Nat.le_trans hc₂ (Nat.add_le_add_right hc₁ _),
        Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩
    | alloc req =>
      dsimp only [nonFreeCount]
      rw [AllocCostModel.stepEvents_cons]
      obtain ⟨hc₁, hl₁, hp₁⟩ := step_single_small hM st hSmall hev.1 hev.2
      obtain ⟨hc₂, hl₂, hp₂⟩ :=
        stepEvents_w4Bounded_small hM hSmall tl (M.step (.alloc req) st) htl
      exact ⟨add_step_le hc₁ hc₂, Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩
    | aligned al req =>
      dsimp only [nonFreeCount]
      rw [AllocCostModel.stepEvents_cons]
      obtain ⟨hc₁, hl₁, hp₁⟩ := step_single_small hM st hSmall hev.1 hev.2
      obtain ⟨hc₂, hl₂, hp₂⟩ :=
        stepEvents_w4Bounded_small hM hSmall tl (M.step (.aligned al req) st) htl
      exact ⟨add_step_le hc₁ hc₂, Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩
    | realloc al old new =>
      dsimp only [nonFreeCount]
      rw [AllocCostModel.stepEvents_cons]
      obtain ⟨hc₁, hl₁, hp₁⟩ := step_single_small hM st hSmall hev.1 hev.2
      obtain ⟨hc₂, hl₂, hp₂⟩ :=
        stepEvents_w4Bounded_small hM hSmall tl (M.step (.realloc al old new) st) htl
      exact ⟨add_step_le hc₁ hc₂, Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩

private theorem stepEvents_w4Bounded_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {maxReq : Nat} :
    ∀ (evs : List AllocEvent) (st : M.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      let k := nonFreeCount evs
      HasFineReallocCredit.cumSmall (M.stepEvents evs st) ≤
        HasFineReallocCredit.cumSmall st + k * (2 * maxReq + 9539) ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤
        HasFineReallocCredit.liveLarge st + k * (maxReq + 8195) ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤
        max (HasFineReallocCredit.peakLarge st)
          (HasFineReallocCredit.liveLarge st + k * (maxReq + 8195))
  | [], st, _ => by
    simp only [nonFreeCount, AllocCostModel.stepEvents_nil, Nat.zero_mul, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _⟩
  | ev :: tl, st, hra => by
    have hev := hra ev List.mem_cons_self
    have htl : ∀ e ∈ tl, eventStepReq e ≤ maxReq ∧ eventStepAlign e ≤ 16 :=
      fun e he => hra e (List.mem_cons_of_mem ev he)
    cases ev with
    | free al sz =>
      dsimp only [nonFreeCount]
      rw [AllocCostModel.stepEvents_cons]
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.freeNonInc al sz st
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_w4Bounded_aff hM tl (M.step (.free al sz) st) htl
      exact ⟨Nat.le_trans hc₂ (Nat.add_le_add_right hc₁ _),
        Nat.le_trans hl₂ (Nat.add_le_add_right hl₁ _),
        max_step_free_le hp₁ hl₁ hp₂⟩
    | alloc req =>
      dsimp only [nonFreeCount]
      rw [AllocCostModel.stepEvents_cons]
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_nonFree_aff st hev.1 hev.2
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_w4Bounded_aff hM tl (M.step (.alloc req) st) htl
      exact ⟨add_step_le hc₁ hc₂, add_step_le hl₁ hl₂, max_step_nonFree_le hl₁ hp₁ hp₂⟩
    | aligned al req =>
      dsimp only [nonFreeCount]
      rw [AllocCostModel.stepEvents_cons]
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_nonFree_aff st hev.1 hev.2
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_w4Bounded_aff hM tl (M.step (.aligned al req) st) htl
      exact ⟨add_step_le hc₁ hc₂, add_step_le hl₁ hl₂, max_step_nonFree_le hl₁ hp₁ hp₂⟩
    | realloc al old new =>
      dsimp only [nonFreeCount]
      rw [AllocCostModel.stepEvents_cons]
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_nonFree_aff st hev.1 hev.2
      obtain ⟨hc₂, hl₂, hp₂⟩ :=
        stepEvents_w4Bounded_aff hM tl (M.step (.realloc al old new) st) htl
      exact ⟨add_step_le hc₁ hc₂, add_step_le hl₁ hl₂, max_step_nonFree_le hl₁ hp₁ hp₂⟩

/-- Small-regime (`maxReq ≤ smallMaxReq M`) `PhaseCreditSpec` for `W4BoundedEvs maxOps maxReq`. -/
theorem phaseCredit_w4BoundedEvs_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (maxOps maxReq : Nat)
    (hSmall : maxReq ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (W4BoundedEvs maxOps maxReq)
      (maxOps * (2 * maxReq + 9539)) 0 0 maxReq where
  req_align _ h := h.2
  credit_le st0 {evs} h := by
    obtain ⟨hc, hl, hp⟩ := stepEvents_w4Bounded_small hM hSmall evs st0 h.2
    have hmul : nonFreeCount evs * (2 * maxReq + 9539) ≤ maxOps * (2 * maxReq + 9539) :=
      Nat.mul_le_mul_right _ h.1
    exact ⟨Nat.le_trans hc (Nat.add_le_add_left hmul _),
      Nat.le_trans hl (Nat.le_add_right _ 0),
      Nat.le_trans hp (Nat.le_max_left _ _)⟩

theorem phaseCredit_w4BoundedEvs_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (maxOps maxReq : Nat) :
    PhaseCreditSpec M (W4BoundedEvs maxOps maxReq)
      (maxOps * (2 * maxReq + 9539))
      (maxOps * (maxReq + 8195))
      (maxOps * (maxReq + 8195))
      maxReq where
  req_align _ h := h.2
  credit_le st0 {evs} h := by
    obtain ⟨hc, hl, hp⟩ := stepEvents_w4Bounded_aff hM evs st0 h.2
    have hmulC : nonFreeCount evs * (2 * maxReq + 9539) ≤ maxOps * (2 * maxReq + 9539) :=
      Nat.mul_le_mul_right _ h.1
    have hmulL : nonFreeCount evs * (maxReq + 8195) ≤ maxOps * (maxReq + 8195) :=
      Nat.mul_le_mul_right _ h.1
    exact ⟨Nat.le_trans hc (Nat.add_le_add_left hmulC _),
      Nat.le_trans hl (Nat.add_le_add_left hmulL _),
      Nat.le_trans hp (Nat.max_le.mpr ⟨Nat.le_max_left _ _,
        Nat.le_trans (Nat.add_le_add_left hmulL _) (Nat.le_max_right _ _)⟩)⟩

/-! ## 2. `init_bob` and PQXDH Responder Primitive Bounds -/

theorem phaseCredit_kemSerialize1569_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M KemSerialize1569Env 12677 9764 9764 1569 :=
  (PhaseCreditSpec.rustAlloc_aff hM (req := 1569) (al := 1) (by decide)).of_imp fun _ h => h

theorem phaseCredit_doReserve_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {x : DoReserveCall} {cap : Nat}
    (hnew : reserveCap x.cap.toNat x.bs.length x.additional ≤ cap) :
    PhaseCreditSpec M (DoReserveEnv x)
      (2 * cap + 9539) (cap + 8195) (cap + 8195) cap := by
  set newCap := reserveCap x.cap.toNat x.bs.length x.additional
  by_cases hc0 : x.cap = 0#64
  · have h := PhaseCreditSpec.rustAlloc_aff hM (req := newCap) (al := 1) (by decide)
    have heq : ∀ evs, DoReserveEnv x evs → evs = rustAllocEvents newCap 1 := by
      intro evs he
      simpa [DoReserveEnv, doReserveEvents, hc0, newCap] using he
    exact (h.of_imp heq).mono (by omega) (by omega) (by omega) hnew
  · have h := phaseCredit_rustRealloc_aff hM x.cap.toNat newCap 1 (by decide)
    have heq : ∀ evs, DoReserveEnv x evs → evs = rustReallocEvents x.cap.toNat newCap 1 := by
      intro evs he
      simpa [DoReserveEnv, doReserveEvents, hc0, newCap] using he
    exact (h.of_imp heq).mono (by omega) (by omega) (by omega) hnew

theorem phaseCredit_publicKeySerialize_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hSmall33 : 33 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = publicKeySerializeEvents) 9605 0 0 33 := by
  have h := PhaseCreditSpec.rustAlloc_small_any hM (req := 33) (al := 1) (by decide) hSmall33
  have ha := hM.smallAlloc_le hSmall33
  exact (h.of_imp fun _ he => he).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 33)

theorem phaseCredit_publicKeySerialize_tempFree_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M (· = publicKeySerializeEvents ++ rustDeallocEvents 33 1)
      9605 0 8228 33 := by
  have h := PhaseCreditSpec.tempAllocFree_aff hM (req := 33) (al := 1) (by decide)
  exact h.of_imp fun _ he => ⟨publicKeySerializeEvents, rustDeallocEvents 33 1, he, rfl, rfl⟩

theorem phaseCredit_growOneSpeZero_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hSmall192 : 192 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (GrowOneSpeEnv 0#64) 9923 0 0 192 := by
  have h := PhaseCreditSpec.rustAlloc_small_any hM (req := 192) (al := 8) (by decide) hSmall192
  have ha := hM.smallAlloc_le hSmall192
  have himp : ∀ evs, GrowOneSpeEnv 0#64 evs → evs = rustAllocEvents 192 8 := by
    rintro _ (⟨_, h⟩ | ⟨hne, _⟩)
    · exact h
    · exact False.elim (hne rfl)
  exact (h.of_imp himp).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 192)

theorem phaseCredit_growOneSpeZero_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M (GrowOneSpeEnv 0#64) 9923 8387 8387 192 := by
  have h := PhaseCreditSpec.rustAlloc_aff hM (req := 192) (al := 8) (by decide)
  have himp : ∀ evs, GrowOneSpeEnv 0#64 evs → evs = rustAllocEvents 192 8 := by
    rintro _ (⟨_, h⟩ | ⟨hne, _⟩)
    · exact h
    · exact False.elim (hne rfl)
  exact h.of_imp himp

/-! ## 3. `pqxdhAccept`, `W4BobSessionBuildEnv`, and `W4InitBobEnv` Bounds -/

/-- DH `PublicKey::serialize` sub-phase of `pqxdhAccept` (`3` or `4` `33`-byte serializations with drops).
-/
def W4PqxdhDhKeysEnv (hasOpk : Bool) : List AllocEvent → Prop :=
  W4BoundedEvs (if hasOpk then 4 else 3) 33

/-- `.ok` allocator trace envelope of `pqxdhAccept` (`DoReserveEnv` → `W4PqxdhDhKeysEnv` → `KemSerialize1569Env` → `FreeOnlyEvs`).
-/
def W4PqxdhAcceptOkEnv (x_res : DoReserveCall) (hasOpk : Bool) : List AllocEvent → Prop :=
  SeqEnv (DoReserveEnv x_res)
    (SeqEnv (W4PqxdhDhKeysEnv hasOpk)
      (SeqEnv KemSerialize1569Env FreeOnlyEvs))

/-- Full `.ok`/`.error` allocator trace envelope of `pqxdhAccept`. -/
def W4PqxdhAcceptEnv (x_res : DoReserveCall) (hasOpk : Bool) (evs : List AllocEvent) : Prop :=
  W4PqxdhAcceptOkEnv x_res hasOpk evs ∨
  SeqEnv (W4PqxdhAcceptOkEnv x_res hasOpk)
    (SeqEnv (GrowOneSpeEnv 0#64) FreeOnlyEvs) evs

/-- Post-`initial_state` `SessionState::new` responder session assembly envelope (`≤ 6` small ops `≤ 68` B + `FreeOnlyEvs`).
-/
def W4BobSessionBuildEnv : List AllocEvent → Prop :=
  SeqEnv (W4BoundedEvs 6 68) FreeOnlyEvs

/-- Full `initialize_bob_session` (`init_bob`) envelope (`W4PqxdhAcceptEnv → E_spqrInit → W4BobSessionBuildEnv`).
-/
def W4InitBobEnv (x_res : DoReserveCall) (hasOpk : Bool)
    (E_spqrInit : List AllocEvent → Prop) : List AllocEvent → Prop :=
  SeqEnv (W4PqxdhAcceptEnv x_res hasOpk)
    (SeqEnv E_spqrInit W4BobSessionBuildEnv)

abbrev W4InitBobSpqrEnv (F : ShaCompress) (x_res : DoReserveCall) (hasOpk : Bool)
    (x_spqr : InitialStateGhost) : List AllocEvent → Prop :=
  W4InitBobEnv x_res hasOpk (InitialStateEnv F x_spqr)

def w4PqxdhAcceptCum (ikmCap : Nat) : Nat :=
  (2 * ikmCap + 9539) + 38420 + 12677 + 9923

def w4InitBobOuterCum (ikmCap : Nat) : Nat :=
  w4PqxdhAcceptCum ikmCap + 58050

/-- Small-regime (`max ikmCap 1569 ≤ smallMaxReq M`) `PhaseCreditSpec` for `W4PqxdhAcceptEnv` (`Δlive = 0`, `Δpeak = 0`).
-/
theorem phaseCredit_w4PqxdhAccept_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {x_res : DoReserveCall} {hasOpk : Bool} {ikmCap : Nat}
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (W4PqxdhAcceptEnv x_res hasOpk)
      (w4PqxdhAcceptCum ikmCap) 0 0 (max ikmCap 1569) := by
  have hSmIkm : ikmCap ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans (Nat.le_max_left _ _) hSmall
  have hSm1569 : 1569 ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans (Nat.le_max_right _ _) hSmall
  have hSm33 : 33 ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans (by decide : 33 ≤ 1569) hSm1569
  have hSm192 : 192 ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans (by decide : 192 ≤ 1569) hSm1569
  have hRes := phaseCredit_doReserve_small hM hold hnew hSmIkm
  have hDh : PhaseCreditSpec M (W4PqxdhDhKeysEnv hasOpk) 38420 0 0 33 := by
    unfold W4PqxdhDhKeysEnv
    refine (phaseCredit_w4BoundedEvs_small hM (if hasOpk then 4 else 3) 33 hSm33).mono
      ?_ (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 33)
    cases hasOpk <;> decide
  have hKem := phaseCredit_seq_freeOnly hM (phaseCredit_kemSerialize1569 hM hSm1569)
  have hOk := hRes.seq (hDh.seq hKem)
  have hSpe := phaseCredit_seq_freeOnly hM (phaseCredit_growOneSpeZero_small hM hSm192)
  have hErr := hOk.seq hSpe
  refine (hOk.or hErr).mono ?_ (by omega) (by omega) ?_
  · unfold w4PqxdhAcceptCum; omega
  · omega

theorem phaseCredit_w4BobSessionBuild_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hSmall68 : 68 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M W4BobSessionBuildEnv 58050 0 0 68 :=
  (phaseCredit_seq_freeOnly hM (phaseCredit_w4BoundedEvs_small hM 6 68 hSmall68)).mono
    (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 68)

/-- Small-regime `PhaseCreditSpec` for `W4InitBobEnv`, adding `w4InitBobOuterCum ikmCap` to `Δcum` and preserving `(l_q, max p_q l_q)` from `E_spqrInit`.
-/
theorem phaseCredit_w4InitBob_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {x_res : DoReserveCall} {hasOpk : Bool}
    {E_spqrInit : List AllocEvent → Prop} {ikmCap c_q l_q p_q r_q : Nat}
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSpqr : PhaseCreditSpec M E_spqrInit c_q l_q p_q r_q) :
    PhaseCreditSpec M (W4InitBobEnv x_res hasOpk E_spqrInit)
      (w4InitBobOuterCum ikmCap + c_q)
      l_q
      (max p_q l_q)
      (max (max ikmCap 1569) (max r_q 68)) := by
  have hSm68 : 68 ≤ HasFineReallocCredit.smallMaxReq M :=
    Nat.le_trans (by decide : 68 ≤ 1569) (Nat.le_trans (Nat.le_max_right _ _) hSmall)
  have hPq := phaseCredit_w4PqxdhAccept_small hM (hasOpk := hasOpk) hold hnew hSmall
  have hBuild := phaseCredit_w4BobSessionBuild_small hM hSm68
  have hFull := hPq.seq (hSpqr.seq hBuild)
  refine hFull.mono ?_ (by omega) (by omega) (Nat.le_refl _)
  unfold w4InitBobOuterCum
  omega

/-- Regime-uniform `PhaseCreditSpec` for `W4InitBobEnv` under `ModelHyps M`. -/
theorem phaseCredit_w4InitBob_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {x_res : DoReserveCall} {hasOpk : Bool}
    {E_spqrInit : List AllocEvent → Prop} {ikmCap c_q l_q p_q r_q : Nat}
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSpqr : PhaseCreditSpec M E_spqrInit c_q l_q p_q r_q) :
    PhaseCreditSpec M (W4InitBobEnv x_res hasOpk E_spqrInit)
      (w4InitBobOuterCum ikmCap + c_q)
      ((ikmCap + 8195) + 4 * (33 + 8195) + 9764 + 8387 + l_q + 6 * (68 + 8195))
      ((ikmCap + 8195) + 4 * (33 + 8195) + 9764 + 8387 + max p_q (l_q + 6 * (68 + 8195)))
      (max (max ikmCap 1569) (max r_q 68)) := by
  have hRes := phaseCredit_doReserve_aff hM hnew
  have hDh : PhaseCreditSpec M (W4PqxdhDhKeysEnv hasOpk) 38420 (4 * (33 + 8195))
      (4 * (33 + 8195)) 33 := by
    unfold W4PqxdhDhKeysEnv
    refine (phaseCredit_w4BoundedEvs_aff hM (if hasOpk then 4 else 3) 33).mono ?_ ?_ ?_
      (Nat.le_refl 33)
    · cases hasOpk <;> decide
    · cases hasOpk <;> decide
    · cases hasOpk <;> decide
  have hKem := phaseCredit_seq_freeOnly hM (phaseCredit_kemSerialize1569_aff hM)
  have hOk := hRes.seq (hDh.seq hKem)
  have hSpe := phaseCredit_seq_freeOnly hM (phaseCredit_growOneSpeZero_aff hM)
  have hPq := hOk.or (hOk.seq hSpe)
  have hBuild := phaseCredit_seq_freeOnly hM (phaseCredit_w4BoundedEvs_aff hM 6 68)
  have hFull := hPq.seq (hSpqr.seq hBuild)
  refine hFull.mono ?_ (by omega) (by omega) ?_
  · unfold w4InitBobOuterCum w4PqxdhAcceptCum; omega
  · omega

/-! ## 4. Stage P2 `Over`-Path Composition -/

/-- Stage P2 `Over` responder envelope (`PromoteStateArchiveEnv → W4InitBobEnv`). -/
def W4StageP2OverBobEnv
    (SerializeArchivedEnv VecPushEnv : List AllocEvent → Prop)
    (x_res : DoReserveCall) (hasOpk : Bool)
    (E_spqrInit : List AllocEvent → Prop) : List AllocEvent → Prop :=
  SeqEnv (PromoteStateArchiveEnv SerializeArchivedEnv VecPushEnv)
    (W4InitBobEnv x_res hasOpk E_spqrInit)

/-- Small-regime `PhaseCreditSpec` for `W4StageP2OverBobEnv`. -/
theorem phaseCredit_w4StageP2OverBob_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    {SerializeArchivedEnv VecPushEnv E_spqrInit : List AllocEvent → Prop}
    {x_res : DoReserveCall} {hasOpk : Bool}
    {c_ser l_ser p_ser r_ser c_push r_push ikmCap c_q l_q p_q r_q : Nat}
    (hSer : PhaseCreditSpec M SerializeArchivedEnv c_ser l_ser p_ser r_ser)
    (hPush : PhaseCreditSpec M VecPushEnv c_push 0 0 r_push)
    (hold : x_res.cap.toNat ≤ ikmCap)
    (hnew : reserveCap x_res.cap.toNat x_res.bs.length x_res.additional ≤ ikmCap)
    (hSmall : max ikmCap 1569 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSpqr : PhaseCreditSpec M E_spqrInit c_q l_q p_q r_q) :
    PhaseCreditSpec M
      (W4StageP2OverBobEnv SerializeArchivedEnv VecPushEnv x_res hasOpk E_spqrInit)
      (c_ser + c_push + w4InitBobOuterCum ikmCap + c_q)
      (l_ser + l_q)
      (max p_ser (l_ser + max p_q l_q))
      (max (max r_ser r_push) (max (max ikmCap 1569) (max r_q 68))) := by
  have hProm := phaseCredit_promoteStateArchive hM hSer hPush
  have hBob := phaseCredit_w4InitBob_small hM (hasOpk := hasOpk) hold hnew hSmall hSpqr
  exact (hProm.seq hBob).mono (by omega) (Nat.le_refl _) (by omega) (Nat.le_refl _)

end LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak
