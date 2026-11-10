/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge

/-!
# Auxiliary Arithmetic and Recurrence Lemmas for `VecGrowCredit`

`Heap`-level realloc-credit transitions across small/large size regimes, super-doubling geometric
series bounds (`IsSuperDoubling`), and parametric `RawVec` doubling-ladder recurrences.
-/

@[expose] public section

namespace LibsignalBinary.Proofs.PeakBudget.VecGrowCreditHelpers

set_option autoImplicit false

open CryptoVerification.LibsignalSpqrV1 (GrowOneCall)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepReq eventStepAlign)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (rawVecNewCap rawVecGrowEvents RawVecGrowEnv rawVecGrowEvents_eq_of_env)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
  (HasFineReallocCredit
   stepEvents_rustAlloc_small stepEvents_rustAlloc_large
   stepEvents_rustDealloc_small stepEvents_rustDealloc_large
   stepEvents_rustRealloc_small_small stepEvents_rustRealloc_small_large
   stepEvents_rustRealloc_large_large stepEvents_rustRealloc_large_small)

/-! ## 1. Core `sc = 63` Realloc-Credit Primitives -/

/-- Direct-`mmap` (`sc = 63`) live-byte contribution of an allocation of `req` bytes:
`0` in the small-class regime (`req ≤ smallMaxReq M`), and `largeCost M req` above it. -/
def allocLargeLive (M : AllocCostModel) [HasFineReallocCredit M] (req : Nat) : Nat :=
  if req ≤ HasFineReallocCredit.smallMaxReq M then 0
  else HasFineReallocCredit.largeCost M req

/-- Single-step `cumSmall` charge of `rustAllocEvents req align` (`0 < req`, `align ≤ 16`). -/
def allocStepCum (M : AllocCostModel) [HasFineReallocCredit M] (req : Nat) : Nat :=
  if req ≤ HasFineReallocCredit.smallMaxReq M then
    HasFineReallocCredit.smallAllocCost M req
  else
    HasFineReallocCredit.largeMetaCost M

/-- Single-step `cumSmall` charge of `rustReallocEvents oldReq newReq align` (`0 < oldReq`,
`0 < newReq`, `align ≤ 16`), covering both `[.realloc align oldReq newReq]` (`align ≤ newReq`)
and `[.aligned (max align 8) newReq, .free align oldReq]` (`newReq < align`). -/
def reallocStepCum (M : AllocCostModel) [HasFineReallocCredit M]
    (newReq align : Nat) : Nat :=
  if newReq ≤ HasFineReallocCredit.smallMaxReq M then
    if align ≤ newReq then HasFineReallocCredit.smallReallocCost M newReq
    else HasFineReallocCredit.smallAllocCost M newReq
  else
    HasFineReallocCredit.largeMetaCost M

/-- Unified `AllocEvent` list for fresh allocation (`oldReq = 0`) vs reallocation (`0 < oldReq`). -/
def growOrReallocEvents (oldReq newReq align : Nat) : List AllocEvent :=
  if oldReq = 0 then rustAllocEvents newReq align
  else rustReallocEvents oldReq newReq align

/-- Unified `cumSmall` step charge matching `growOrReallocEvents oldReq newReq align`. -/
def growOrReallocStepCum (M : AllocCostModel) [HasFineReallocCredit M]
    (oldReq newReq align : Nat) : Nat :=
  if oldReq = 0 then allocStepCum M newReq
  else reallocStepCum M newReq align

@[simp] theorem allocLargeLive_zero (M : AllocCostModel) [HasFineReallocCredit M] :
    allocLargeLive M 0 = 0 := by
  unfold allocLargeLive
  simp

theorem allocLargeLive_of_le (M : AllocCostModel) [HasFineReallocCredit M]
    {req : Nat} (hle : req ≤ HasFineReallocCredit.smallMaxReq M) :
    allocLargeLive M req = 0 := by
  unfold allocLargeLive
  simp [hle]

theorem allocLargeLive_of_gt (M : AllocCostModel) [HasFineReallocCredit M]
    {req : Nat} (hgt : HasFineReallocCredit.smallMaxReq M < req) :
    allocLargeLive M req = HasFineReallocCredit.largeCost M req := by
  unfold allocLargeLive
  have hnot : ¬ req ≤ HasFineReallocCredit.smallMaxReq M := Nat.not_le.mpr hgt
  simp [hnot]

theorem allocLargeLive_le_affine (M : AllocCostModel) [HasFineReallocCredit M]
    (hLargeAff : ∀ r, HasFineReallocCredit.smallMaxReq M < r →
      HasFineReallocCredit.largeCost M r ≤ r + 8195)
    (req : Nat) :
    allocLargeLive M req ≤
      if req ≤ HasFineReallocCredit.smallMaxReq M then 0 else req + 8195 := by
  unfold allocLargeLive
  split
  · exact Nat.le_refl 0
  · next hnot =>
    exact hLargeAff req (Nat.lt_of_not_ge hnot)

theorem allocStepCum_le_affine (M : AllocCostModel) [HasFineReallocCredit M]
    (hSmallAlloc : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallAllocCost M r ≤ 2 * r + 9539)
    (hMeta : HasFineReallocCredit.largeMetaCost M ≤ 122)
    (req : Nat) :
    allocStepCum M req ≤
      if req ≤ HasFineReallocCredit.smallMaxReq M then 2 * req + 9539 else 122 := by
  unfold allocStepCum
  split
  · next hle => exact hSmallAlloc req hle
  · exact hMeta

theorem growOrReallocStepCum_le_affine (M : AllocCostModel) [HasFineReallocCredit M]
    (hSmallAlloc : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallAllocCost M r ≤ 2 * r + 9539)
    (hSmallRealloc : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallReallocCost M r ≤ 2 * r + 9539)
    (hMeta : HasFineReallocCredit.largeMetaCost M ≤ 122)
    (oldReq newReq align : Nat) :
    growOrReallocStepCum M oldReq newReq align ≤
      if newReq ≤ HasFineReallocCredit.smallMaxReq M then 2 * newReq + 9539 else 122 := by
  unfold growOrReallocStepCum allocStepCum reallocStepCum
  by_cases hold : oldReq = 0
  · simp only [hold, ↓reduceIte]
    split
    · next hle => exact hSmallAlloc newReq hle
    · exact hMeta
  · simp only [hold, ↓reduceIte]
    split
    · next hle =>
      split
      · exact hSmallRealloc newReq hle
      · exact hSmallAlloc newReq hle
    · exact hMeta

theorem rustAllocEvents_req_align {req align : Nat} (hal : align ≤ 16) :
    ∀ ev ∈ rustAllocEvents req align,
      eventStepReq ev ≤ req ∧ eventStepAlign ev ≤ 16 := by
  unfold rustAllocEvents
  split <;> intro ev hev <;> simp only [List.mem_singleton] at hev <;> subst hev
  · exact ⟨Nat.le_refl req, Nat.le_refl 16⟩
  · exact ⟨Nat.le_refl req, by dsimp [eventStepAlign]; omega⟩

theorem rustDeallocEvents_req_align (req align : Nat) :
    ∀ ev ∈ rustDeallocEvents req align,
      eventStepReq ev = 0 ∧ eventStepAlign ev ≤ 16 := by
  intro ev hev
  unfold rustDeallocEvents at hev
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨rfl, Nat.le_refl 16⟩

theorem rustReallocEvents_req_align {oldReq newReq align : Nat} (hal : align ≤ 16) :
    ∀ ev ∈ rustReallocEvents oldReq newReq align,
      eventStepReq ev ≤ newReq ∧ eventStepAlign ev ≤ 16 := by
  unfold rustReallocEvents
  split
  · intro ev hev
    simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨Nat.le_refl newReq, hal⟩
  · intro ev hev
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
    rcases hev with rfl | rfl
    · exact ⟨Nat.le_refl newReq, by dsimp [eventStepAlign]; omega⟩
    · exact ⟨Nat.zero_le newReq, Nat.le_refl 16⟩

theorem growOrReallocEvents_req_align {oldReq newReq align : Nat} (hal : align ≤ 16) :
    ∀ ev ∈ growOrReallocEvents oldReq newReq align,
      eventStepReq ev ≤ newReq ∧ eventStepAlign ev ≤ 16 := by
  unfold growOrReallocEvents
  split
  · exact rustAllocEvents_req_align hal
  · exact rustReallocEvents_req_align hal

/-! ## 2. `HasFineReallocCredit` Potential Transitions -/

theorem stepEvents_rustAlloc_credit (M : AllocCostModel) [HasFineReallocCredit M]
    {req align : Nat} (st : M.σ)
    (hal : align ≤ 16) (hpos : 0 < req) :
    let st' := M.stepEvents (rustAllocEvents req align) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + allocStepCum M req ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st + allocLargeLive M req ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + allocLargeLive M req) := by
  by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
  · obtain ⟨hcum, hlive, hpeak⟩ := stepEvents_rustAlloc_small M st hal hpos hle
    simp only [allocStepCum, allocLargeLive, hle, ↓reduceIte, Nat.add_zero]
    exact ⟨hcum, hlive, Nat.le_trans hpeak (Nat.le_max_left _ _)⟩
  · have hgt : HasFineReallocCredit.smallMaxReq M < req := Nat.lt_of_not_ge hle
    obtain ⟨hcum, hlive, hpeak⟩ := stepEvents_rustAlloc_large M st hal hgt
    simp only [allocStepCum, allocLargeLive, hle, ↓reduceIte]
    exact ⟨hcum, hlive, hpeak⟩

/-- Credit transition for `rustDeallocEvents req align` (`align ≤ 16`), cancelling `allocLargeLive M req` from `liveLarge`.
-/
theorem stepEvents_rustDealloc_credit (M : AllocCostModel) [HasFineReallocCredit M]
    {req align L_base : Nat} (st : M.σ)
    (hal : align ≤ 16)
    (hlive : HasFineReallocCredit.liveLarge st ≤ L_base + allocLargeLive M req) :
    let st' := M.stepEvents (rustDeallocEvents req align) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤ L_base ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
  · obtain ⟨hcum, hlive', hpeak⟩ := stepEvents_rustDealloc_small M st hal hle
    rw [allocLargeLive_of_le M hle, Nat.add_zero] at hlive
    exact ⟨hcum, Nat.le_trans hlive' hlive, hpeak⟩
  · have hgt : HasFineReallocCredit.smallMaxReq M < req := Nat.lt_of_not_ge hle
    obtain ⟨hcum, hlive', hpeak⟩ := stepEvents_rustDealloc_large M st hal hgt
    rw [allocLargeLive_of_gt M hgt] at hlive
    exact ⟨hcum, by omega, hpeak⟩

/-- Four-quadrant credit transition for `rustReallocEvents oldReq newReq align` (`0 < oldReq`,
`0 < newReq`, `align ≤ 16`), cancelling `allocLargeLive M oldReq` from `liveLarge`. -/
theorem stepEvents_rustRealloc_any_credit (M : AllocCostModel) [HasFineReallocCredit M]
    {oldReq newReq align L_base : Nat} (st : M.σ)
    (hal : align ≤ 16) (hold_pos : 0 < oldReq) (hnew_pos : 0 < newReq)
    (hlive : HasFineReallocCredit.liveLarge st ≤ L_base + allocLargeLive M oldReq) :
    let st' := M.stepEvents (rustReallocEvents oldReq newReq align) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + reallocStepCum M newReq align ∧
    HasFineReallocCredit.liveLarge st' ≤ L_base + allocLargeLive M newReq ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (L_base + allocLargeLive M oldReq + allocLargeLive M newReq) := by
  by_cases hal_new : align ≤ newReq
  · by_cases hold_le : oldReq ≤ HasFineReallocCredit.smallMaxReq M
    · by_cases hnew_le : newReq ≤ HasFineReallocCredit.smallMaxReq M
      · obtain ⟨hc, hl, hp⟩ :=
          stepEvents_rustRealloc_small_small M st hal hal_new hold_pos hold_le hnew_pos hnew_le
        simp only [reallocStepCum, allocLargeLive, hold_le, hnew_le, hal_new, ↓reduceIte,
          Nat.add_zero] at hlive ⊢
        exact ⟨hc, Nat.le_trans hl hlive, Nat.le_trans hp (Nat.le_max_left _ _)⟩
      · have hnew_gt : HasFineReallocCredit.smallMaxReq M < newReq := Nat.lt_of_not_ge hnew_le
        obtain ⟨hc, hl, hp⟩ :=
          stepEvents_rustRealloc_small_large M st hal hal_new hold_pos hold_le hnew_gt
        simp only [reallocStepCum, allocLargeLive, hold_le, hnew_le, ↓reduceIte,
          Nat.add_zero] at hlive ⊢
        exact ⟨hc, by omega, by omega⟩
    · have hold_gt : HasFineReallocCredit.smallMaxReq M < oldReq := Nat.lt_of_not_ge hold_le
      by_cases hnew_le : newReq ≤ HasFineReallocCredit.smallMaxReq M
      · obtain ⟨hc, hl, hp⟩ :=
          stepEvents_rustRealloc_large_small M st hal hal_new hold_gt hnew_pos hnew_le
        simp only [reallocStepCum, allocLargeLive, hold_le, hnew_le, hal_new, ↓reduceIte,
          Nat.add_zero] at hlive ⊢
        exact ⟨hc, by omega, Nat.le_trans hp (Nat.le_max_left _ _)⟩
      · have hnew_gt : HasFineReallocCredit.smallMaxReq M < newReq := Nat.lt_of_not_ge hnew_le
        obtain ⟨hc, hl, hp⟩ :=
          stepEvents_rustRealloc_large_large M st hal hal_new hold_gt hnew_gt
        simp only [reallocStepCum, allocLargeLive, hold_le, hnew_le, ↓reduceIte] at hlive ⊢
        exact ⟨hc, by omega, by omega⟩
  · have hcond : ¬ (align ≤ 16 ∧ align ≤ newReq) := fun h => hal_new h.2
    have hsplit : rustReallocEvents oldReq newReq align =
        [.aligned (max align 8) newReq] ++ rustDeallocEvents oldReq align := by
      unfold rustReallocEvents rustDeallocEvents
      simp [hcond]
    rw [hsplit, AllocCostModel.stepEvents_append,
      show M.stepEvents [.aligned (max align 8) newReq] st =
        M.step (.aligned (max align 8) newReq) st from rfl]
    have hal8 : max align 8 ≤ 16 := by omega
    have hst1 :
        HasFineReallocCredit.cumSmall (M.step (.aligned (max align 8) newReq) st) ≤
          HasFineReallocCredit.cumSmall st + reallocStepCum M newReq align ∧
        HasFineReallocCredit.liveLarge (M.step (.aligned (max align 8) newReq) st) ≤
          (L_base + allocLargeLive M newReq) + allocLargeLive M oldReq ∧
        HasFineReallocCredit.peakLarge (M.step (.aligned (max align 8) newReq) st) ≤
          max (HasFineReallocCredit.peakLarge st)
            (L_base + allocLargeLive M oldReq + allocLargeLive M newReq) := by
      by_cases hnew_le : newReq ≤ HasFineReallocCredit.smallMaxReq M
      · obtain ⟨hc, hl, hp⟩ :=
          HasFineReallocCredit.step_aligned_small (M := M) st hal8 hnew_pos hnew_le
        simp only [reallocStepCum, allocLargeLive, hnew_le, hal_new, ↓reduceIte,
          Nat.add_zero] at *
        exact ⟨hc, Nat.le_trans hl hlive, Nat.le_trans hp (Nat.le_max_left _ _)⟩
      · have hnew_gt : HasFineReallocCredit.smallMaxReq M < newReq := Nat.lt_of_not_ge hnew_le
        obtain ⟨hc, hl, hp⟩ :=
          HasFineReallocCredit.step_aligned_large (M := M) st hal8 hnew_gt
        simp only [reallocStepCum, allocLargeLive, hnew_le, ↓reduceIte] at *
        exact ⟨hc, by omega, by omega⟩
    obtain ⟨hc1, hl1, hp1⟩ := hst1
    obtain ⟨hc2, hl2, hp2⟩ :=
      stepEvents_rustDealloc_credit M (M.step (.aligned (max align 8) newReq) st) hal hl1
    exact ⟨Nat.le_trans hc2 hc1, hl2, Nat.le_trans hp2 hp1⟩

/-- Unified credit transition for `growOrReallocEvents oldReq newReq align` (`0 < newReq`,
`align ≤ 16`), cancelling `allocLargeLive M oldReq` from `liveLarge`. -/
theorem stepEvents_growOrRealloc_credit (M : AllocCostModel) [HasFineReallocCredit M]
    {oldReq newReq align L_base : Nat} (st : M.σ)
    (hal : align ≤ 16) (hnew_pos : 0 < newReq)
    (hlive : HasFineReallocCredit.liveLarge st ≤ L_base + allocLargeLive M oldReq) :
    let st' := M.stepEvents (growOrReallocEvents oldReq newReq align) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + growOrReallocStepCum M oldReq newReq align ∧
    HasFineReallocCredit.liveLarge st' ≤ L_base + allocLargeLive M newReq ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (L_base + allocLargeLive M oldReq + allocLargeLive M newReq) := by
  unfold growOrReallocEvents growOrReallocStepCum
  by_cases hold : oldReq = 0
  · subst hold
    simp only [↓reduceIte, allocLargeLive_zero, Nat.add_zero] at hlive ⊢
    obtain ⟨hc, hl, hp⟩ := stepEvents_rustAlloc_credit M st hal hnew_pos
    exact ⟨hc, by omega, by omega⟩
  · simp only [hold, ↓reduceIte]
    exact stepEvents_rustRealloc_any_credit M st hal (Nat.pos_of_ne_zero hold) hnew_pos hlive

/-- State-universal delta bound for `growOrReallocEvents oldReq newReq align` without a `liveLarge` premise.
-/
theorem stepEvents_growOrRealloc_delta (M : AllocCostModel) [HasFineReallocCredit M]
    {oldReq newReq align : Nat} (st : M.σ)
    (hal : align ≤ 16) (hnew_pos : 0 < newReq) :
    let st' := M.stepEvents (growOrReallocEvents oldReq newReq align) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + growOrReallocStepCum M oldReq newReq align ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st +
        (allocLargeLive M newReq - allocLargeLive M oldReq) ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + allocLargeLive M newReq) := by
  unfold growOrReallocEvents growOrReallocStepCum
  by_cases hold : oldReq = 0
  · subst hold
    simp only [↓reduceIte, allocLargeLive_zero, Nat.sub_zero]
    exact stepEvents_rustAlloc_credit M st hal hnew_pos
  · simp only [hold, ↓reduceIte]
    have hold_pos : 0 < oldReq := Nat.pos_of_ne_zero hold
    by_cases hal_new : align ≤ newReq
    · by_cases hold_le : oldReq ≤ HasFineReallocCredit.smallMaxReq M
      · by_cases hnew_le : newReq ≤ HasFineReallocCredit.smallMaxReq M
        · obtain ⟨hc, hl, hp⟩ :=
            stepEvents_rustRealloc_small_small M st hal hal_new hold_pos hold_le hnew_pos hnew_le
          simp only [reallocStepCum, allocLargeLive, hold_le, hnew_le, hal_new, ↓reduceIte]
          exact ⟨hc, by omega, by omega⟩
        · have hnew_gt : HasFineReallocCredit.smallMaxReq M < newReq := Nat.lt_of_not_ge hnew_le
          obtain ⟨hc, hl, hp⟩ :=
            stepEvents_rustRealloc_small_large M st hal hal_new hold_pos hold_le hnew_gt
          simp only [reallocStepCum, allocLargeLive, hold_le, hnew_le, ↓reduceIte]
          exact ⟨hc, by omega, hp⟩
      · have hold_gt : HasFineReallocCredit.smallMaxReq M < oldReq := Nat.lt_of_not_ge hold_le
        by_cases hnew_le : newReq ≤ HasFineReallocCredit.smallMaxReq M
        · obtain ⟨hc, hl, hp⟩ :=
            stepEvents_rustRealloc_large_small M st hal hal_new hold_gt hnew_pos hnew_le
          simp only [reallocStepCum, allocLargeLive, hold_le, hnew_le, hal_new, ↓reduceIte]
          exact ⟨hc, by omega, by omega⟩
        · have hnew_gt : HasFineReallocCredit.smallMaxReq M < newReq := Nat.lt_of_not_ge hnew_le
          obtain ⟨hc, hl, hp⟩ :=
            stepEvents_rustRealloc_large_large M st hal hal_new hold_gt hnew_gt
          simp only [reallocStepCum, allocLargeLive, hold_le, hnew_le, ↓reduceIte]
          exact ⟨hc, by omega, hp⟩
    · have hcond : ¬ (align ≤ 16 ∧ align ≤ newReq) := fun h => hal_new h.2
      have hsplit : rustReallocEvents oldReq newReq align =
          [.aligned (max align 8) newReq] ++ rustDeallocEvents oldReq align := by
        unfold rustReallocEvents rustDeallocEvents
        simp [hcond]
      rw [hsplit, AllocCostModel.stepEvents_append,
        show M.stepEvents [.aligned (max align 8) newReq] st =
          M.step (.aligned (max align 8) newReq) st from rfl]
      have hal8 : max align 8 ≤ 16 := by omega
      have hst1 :
          HasFineReallocCredit.cumSmall (M.step (.aligned (max align 8) newReq) st) ≤
            HasFineReallocCredit.cumSmall st + reallocStepCum M newReq align ∧
          HasFineReallocCredit.liveLarge (M.step (.aligned (max align 8) newReq) st) ≤
            HasFineReallocCredit.liveLarge st + allocLargeLive M newReq ∧
          HasFineReallocCredit.peakLarge (M.step (.aligned (max align 8) newReq) st) ≤
            max (HasFineReallocCredit.peakLarge st)
              (HasFineReallocCredit.liveLarge st + allocLargeLive M newReq) := by
        by_cases hnew_le : newReq ≤ HasFineReallocCredit.smallMaxReq M
        · obtain ⟨hc, hl, hp⟩ :=
            HasFineReallocCredit.step_aligned_small (M := M) st hal8 hnew_pos hnew_le
          simp only [reallocStepCum, allocLargeLive, hnew_le, hal_new, ↓reduceIte, Nat.add_zero]
          exact ⟨hc, hl, Nat.le_trans hp (Nat.le_max_left _ _)⟩
        · have hnew_gt : HasFineReallocCredit.smallMaxReq M < newReq := Nat.lt_of_not_ge hnew_le
          obtain ⟨hc, hl, hp⟩ :=
            HasFineReallocCredit.step_aligned_large (M := M) st hal8 hnew_gt
          simp only [reallocStepCum, allocLargeLive, hnew_le, ↓reduceIte]
          exact ⟨hc, hl, hp⟩
      obtain ⟨hc1, hl1, hp1⟩ := hst1
      by_cases hold_le : oldReq ≤ HasFineReallocCredit.smallMaxReq M
      · obtain ⟨hc2, hl2, hp2⟩ :=
          stepEvents_rustDealloc_small M (M.step (.aligned (max align 8) newReq) st) hal hold_le
        rw [allocLargeLive_of_le M hold_le, Nat.sub_zero]
        exact ⟨Nat.le_trans hc2 hc1, Nat.le_trans hl2 hl1, Nat.le_trans hp2 hp1⟩
      · have hold_gt : HasFineReallocCredit.smallMaxReq M < oldReq := Nat.lt_of_not_ge hold_le
        obtain ⟨hc2, hl2, hp2⟩ :=
          stepEvents_rustDealloc_large M (M.step (.aligned (max align 8) newReq) st) hal hold_gt
        rw [allocLargeLive_of_gt M hold_gt]
        exact ⟨Nat.le_trans hc2 hc1, by omega, Nat.le_trans hp2 hp1⟩

/-- Credit cancellation for `alloc tmp ++ dealloc tmp` (`0 < tmpReq`, `align ≤ 16`). -/
theorem stepEvents_alloc_dealloc_credit (M : AllocCostModel) [HasFineReallocCredit M]
    {tmpReq align L_base : Nat} (st : M.σ)
    (hal : align ≤ 16) (htmp_pos : 0 < tmpReq)
    (hlive : HasFineReallocCredit.liveLarge st ≤ L_base) :
    let st' := M.stepEvents (rustAllocEvents tmpReq align ++ rustDeallocEvents tmpReq align) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + allocStepCum M tmpReq ∧
    HasFineReallocCredit.liveLarge st' ≤ L_base ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st) (L_base + allocLargeLive M tmpReq) := by
  rw [AllocCostModel.stepEvents_append]
  obtain ⟨hc1, hl1, hp1⟩ := stepEvents_rustAlloc_credit M st hal htmp_pos
  have hl1' : HasFineReallocCredit.liveLarge (M.stepEvents (rustAllocEvents tmpReq align) st) ≤
      L_base + allocLargeLive M tmpReq := by omega
  obtain ⟨hc2, hl2, hp2⟩ := stepEvents_rustDealloc_credit M _ hal hl1'
  exact ⟨Nat.le_trans hc2 hc1, hl2, by omega⟩

/-- Credit transition for `alloc tmp ++ growOrRealloc oldCap newCap ++ dealloc tmp`, cancelling both
`allocLargeLive M oldCap` and `allocLargeLive M tmpReq` from `liveLarge`. -/
theorem stepEvents_alloc_growOrRealloc_dealloc_credit
    (M : AllocCostModel) [HasFineReallocCredit M]
    {tmpReq oldCap newCap alignTmp alignBuf L_base : Nat} (st : M.σ)
    (halTmp : alignTmp ≤ 16) (halBuf : alignBuf ≤ 16)
    (htmp_pos : 0 < tmpReq) (hnew_pos : 0 < newCap)
    (hlive : HasFineReallocCredit.liveLarge st ≤ L_base + allocLargeLive M oldCap) :
    let evs := rustAllocEvents tmpReq alignTmp ++
      growOrReallocEvents oldCap newCap alignBuf ++
      rustDeallocEvents tmpReq alignTmp
    let st' := M.stepEvents evs st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + allocStepCum M tmpReq +
        growOrReallocStepCum M oldCap newCap alignBuf ∧
    HasFineReallocCredit.liveLarge st' ≤ L_base + allocLargeLive M newCap ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (L_base + allocLargeLive M tmpReq +
          allocLargeLive M oldCap + allocLargeLive M newCap) := by
  intro evs st'
  have hevs : st' =
      M.stepEvents (rustDeallocEvents tmpReq alignTmp)
        (M.stepEvents (growOrReallocEvents oldCap newCap alignBuf)
          (M.stepEvents (rustAllocEvents tmpReq alignTmp) st)) := by
    dsimp [st', evs]
    rw [AllocCostModel.stepEvents_append, AllocCostModel.stepEvents_append]
  rw [hevs]
  obtain ⟨hc1, hl1, hp1⟩ := stepEvents_rustAlloc_credit M st halTmp htmp_pos
  have hl1' : HasFineReallocCredit.liveLarge (M.stepEvents (rustAllocEvents tmpReq alignTmp) st) ≤
      (L_base + allocLargeLive M tmpReq) + allocLargeLive M oldCap := by omega
  obtain ⟨hc2, hl2, hp2⟩ := stepEvents_growOrRealloc_credit M _ halBuf hnew_pos hl1'
  have hl2' :
      HasFineReallocCredit.liveLarge
          (M.stepEvents (growOrReallocEvents oldCap newCap alignBuf)
            (M.stepEvents (rustAllocEvents tmpReq alignTmp) st)) ≤
        (L_base + allocLargeLive M newCap) + allocLargeLive M tmpReq := by omega
  obtain ⟨hc3, hl3, hp3⟩ := stepEvents_rustDealloc_credit M _ halTmp hl2'
  exact ⟨by omega, hl3, by omega⟩

/-! ## 3. Super-Doubling Capacity Traces -/

def headOrZero : List Nat → Nat
  | [] => 0
  | x :: _ => x

def lastOrZero : List Nat → Nat
  | [] => 0
  | [x] => x
  | _ :: b :: rest => lastOrZero (b :: rest)

/-- Super-doubling capacity trace (`∀ i, 2 * cs[i] ≤ cs[i+1]`). -/
inductive IsSuperDoubling : List Nat → Prop where
  | nil : IsSuperDoubling []
  | singleton (c : Nat) : IsSuperDoubling [c]
  | cons {a b : Nat} {rest : List Nat} :
      2 * a ≤ b → IsSuperDoubling (b :: rest) → IsSuperDoubling (a :: b :: rest)

theorem IsSuperDoubling.sum_add_head_le_two_mul_last {cs : List Nat}
    (h : IsSuperDoubling cs) :
    cs.sum + headOrZero cs ≤ 2 * lastOrZero cs := by
  induction h with
  | nil => simp [headOrZero, lastOrZero]
  | singleton c =>
    simp only [List.sum_cons, List.sum_nil, headOrZero, lastOrZero]
    omega
  | @cons a b rest hab _ ih =>
    simp only [List.sum_cons, headOrZero, lastOrZero] at ih ⊢
    omega

theorem super_doubling_sum_le {cs : List Nat} {capMax : Nat}
    (h : IsSuperDoubling cs) (hlast : lastOrZero cs ≤ capMax) :
    cs.sum ≤ 2 * capMax := by
  have hsum := h.sum_add_head_le_two_mul_last
  omega

theorem IsSuperDoubling.head_mul_two_pow_le_last {cs : List Nat}
    (h : IsSuperDoubling cs) :
    headOrZero cs * 2 ^ (cs.length - 1) ≤ lastOrZero cs := by
  induction h with
  | nil => simp [headOrZero, lastOrZero]
  | singleton c => simp [headOrZero, lastOrZero]
  | @cons a b rest hab _ ih =>
    simp only [headOrZero, lastOrZero, List.length_cons, Nat.add_sub_cancel] at ih ⊢
    have hpow : a * 2 ^ (rest.length + 1) = (2 * a) * 2 ^ rest.length := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ rest.length) 2, ← Nat.mul_assoc, Nat.mul_comm a 2]
    rw [hpow]
    exact Nat.le_trans (Nat.mul_le_mul_right (2 ^ rest.length) hab) ih

/-- Amortized potential step for a super-doubling jump `2 * oldReq ≤ newReq` under potential `Φ(r) = 4 * min r S`.
-/
theorem super_doubling_potential_step {S oldReq newReq : Nat} (h2 : 2 * oldReq ≤ newReq) :
    4 * min oldReq S + (if newReq ≤ S then 2 * newReq else 0) ≤ 4 * min newReq S := by
  split
  · next hle =>
    have hold : oldReq ≤ S := by omega
    rw [Nat.min_eq_left hold, Nat.min_eq_left hle]
    omega
  · next hgt =>
    have hmin_old : min oldReq S ≤ S := Nat.min_le_right oldReq S
    have hmin_new : min newReq S = S := by omega
    omega

/-- Amortized `cumSmall` step bound for a super-doubling `growOrReallocEvents oldReq newReq align` (`2 * oldReq ≤ newReq`).
-/
theorem growOrReallocStepCum_amortized (M : AllocCostModel) [HasFineReallocCredit M]
    (hSmallAlloc : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallAllocCost M r ≤ 2 * r + 9539)
    (hSmallRealloc : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallReallocCost M r ≤ 2 * r + 9539)
    (hMeta : HasFineReallocCredit.largeMetaCost M ≤ 122)
    {oldReq newReq align : Nat} (h2 : 2 * oldReq ≤ newReq) :
    growOrReallocStepCum M oldReq newReq align +
      4 * min oldReq (HasFineReallocCredit.smallMaxReq M) ≤
      4 * min newReq (HasFineReallocCredit.smallMaxReq M) + 9539 := by
  have hstep := growOrReallocStepCum_le_affine M hSmallAlloc hSmallRealloc hMeta
    oldReq newReq align
  have hpot := super_doubling_potential_step (S := HasFineReallocCredit.smallMaxReq M) h2
  split at hstep <;> split at hpot <;> omega

/-! ## 4. Parametric `RawVec` Doubling Ladder and Affine Bounds -/

/-- Capacity reached after `k` `RawVec<T>::grow_one` calls from initial capacity `0`:
`0` at `k = 0`, and `minCap * 2 ^ (k - 1)` for `k ≥ 1`. -/
def doublingCap (minCap : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => minCap * 2 ^ k

/-- Auxiliary positive-target step counter for `doublingSteps`. -/
def doublingStepsPos (minCap rem : Nat) : Nat :=
  if h : minCap = 0 ∨ rem ≤ minCap then 1
  else 1 + doublingStepsPos minCap ((rem + 1) / 2)
termination_by rem
decreasing_by
  omega

/-- Number of `grow_one` steps from `0` needed to reach capacity `≥ targetCap` (for `0 < minCap`). -/
def doublingSteps (minCap targetCap : Nat) : Nat :=
  if targetCap = 0 then 0 else doublingStepsPos minCap targetCap

@[simp] theorem doublingCap_zero (minCap : Nat) : doublingCap minCap 0 = 0 := rfl

@[simp] theorem doublingCap_one (minCap : Nat) : doublingCap minCap 1 = minCap := by
  simp [doublingCap]

theorem doublingCap_succ_succ (minCap k : Nat) :
    doublingCap minCap (k + 2) = 2 * doublingCap minCap (k + 1) := by
  simp only [doublingCap, Nat.pow_succ]
  rw [← Nat.mul_assoc, Nat.mul_comm _ 2]

theorem doublingCap_pos {minCap k : Nat} (hmin : 0 < minCap) (hk : 0 < k) :
    0 < doublingCap minCap k := by
  cases k with
  | zero => omega
  | succ m =>
    dsimp [doublingCap]
    exact Nat.mul_pos hmin (Nat.two_pow_pos m)

theorem two_mul_doublingCap_le_succ (minCap k : Nat) :
    2 * doublingCap minCap k ≤ doublingCap minCap (k + 1) := by
  cases k with
  | zero => simp [doublingCap]
  | succ m => rw [doublingCap_succ_succ]

theorem doublingCap_mono (minCap : Nat) {j k : Nat} (hjk : j ≤ k) :
    doublingCap minCap j ≤ doublingCap minCap k := by
  induction hjk with
  | refl => exact Nat.le_refl _
  | @step m _ ih =>
    have hstep : doublingCap minCap m ≤ doublingCap minCap (m + 1) := by
      have h2 := two_mul_doublingCap_le_succ minCap m
      omega
    exact Nat.le_trans ih hstep

theorem rawVecNewCap_doublingCap {minCap j : Nat} (hmin : 0 < minCap) :
    rawVecNewCap minCap (doublingCap minCap j) = doublingCap minCap (j + 1) := by
  cases j with
  | zero => simp [doublingCap, rawVecNewCap]
  | succ m =>
    have hge : minCap ≤ minCap * 2 ^ m :=
      Nat.le_mul_of_pos_right minCap Nat.one_le_two_pow
    have hmul : minCap * 2 ^ (m + 1) = 2 * (minCap * 2 ^ m) :=
      doublingCap_succ_succ minCap m
    dsimp [doublingCap, rawVecNewCap]
    rw [hmul]
    omega

theorem doublingStepsPos_pos (minCap rem : Nat) :
    0 < doublingStepsPos minCap rem := by
  unfold doublingStepsPos
  split <;> omega

private theorem doublingStepsPos_spec {minCap : Nat} (hmin : 0 < minCap) (rem : Nat)
    (hrem : 0 < rem) :
    rem ≤ doublingCap minCap (doublingStepsPos minCap rem) ∧
    doublingCap minCap (doublingStepsPos minCap rem) ≤ max minCap (2 * rem - 2) := by
  induction rem using Nat.strongRecOn with
  | ind n ih =>
    unfold doublingStepsPos
    by_cases hle : minCap = 0 ∨ n ≤ minCap
    · simp only [hle, ↓reduceDIte, doublingCap_one]
      rcases hle with rfl | hn
      · omega
      · exact ⟨hn, Nat.le_max_left _ _⟩
    · simp only [hle, ↓reduceDIte]
      have hgt : minCap < n := by omega
      have hhalf_lt : (n + 1) / 2 < n := by omega
      have hhalf_pos : 0 < (n + 1) / 2 := by omega
      obtain ⟨hlo, hhi⟩ := ih ((n + 1) / 2) hhalf_lt hhalf_pos
      have hk_pos : 0 < doublingStepsPos minCap ((n + 1) / 2) :=
        doublingStepsPos_pos minCap ((n + 1) / 2)
      obtain ⟨m, hm⟩ : ∃ m, doublingStepsPos minCap ((n + 1) / 2) = m + 1 :=
        ⟨doublingStepsPos minCap ((n + 1) / 2) - 1, by omega⟩
      have hstep_eq :
          doublingCap minCap (1 + doublingStepsPos minCap ((n + 1) / 2)) =
            2 * doublingCap minCap (doublingStepsPos minCap ((n + 1) / 2)) := by
        rw [Nat.add_comm 1, hm, doublingCap_succ_succ]
      rw [hstep_eq]
      refine ⟨by omega, ?_⟩
      have hmax : max minCap (2 * ((n + 1) / 2) - 2) ≤ n - 1 := by omega
      have hmul : 2 * doublingCap minCap (doublingStepsPos minCap ((n + 1) / 2)) ≤
          2 * (n - 1) := by omega
      omega

theorem doublingCap_doublingSteps_ge {minCap : Nat} (hmin : 0 < minCap) (targetCap : Nat) :
    targetCap ≤ doublingCap minCap (doublingSteps minCap targetCap) := by
  unfold doublingSteps
  by_cases ht : targetCap = 0
  · subst ht; simp
  · simp only [ht, ↓reduceIte]
    exact (doublingStepsPos_spec hmin targetCap (Nat.pos_of_ne_zero ht)).1

theorem doublingCap_doublingSteps_le {minCap : Nat} (hmin : 0 < minCap) {targetCap : Nat}
    (ht : 0 < targetCap) :
    doublingCap minCap (doublingSteps minCap targetCap) ≤ max minCap (2 * targetCap - 2) := by
  unfold doublingSteps
  have hne : targetCap ≠ 0 := Nat.ne_of_gt ht
  simp only [hne, ↓reduceIte]
  exact (doublingStepsPos_spec hmin targetCap ht).2

theorem rawVecGrowEvents_eq_growOrReallocEvents {elemSz minCap align j : Nat} {cap : BitVec 64}
    (helem : 0 < elemSz) (hmin : 0 < minCap) (hcap : cap.toNat = doublingCap minCap j) :
    rawVecGrowEvents elemSz minCap align cap =
      growOrReallocEvents
        (doublingCap minCap j * elemSz)
        (doublingCap minCap (j + 1) * elemSz)
        align := by
  unfold rawVecGrowEvents growOrReallocEvents
  rw [hcap, rawVecNewCap_doublingCap hmin]
  cases j with
  | zero =>
    have hcap0 : cap = 0#64 := BitVec.eq_of_toNat_eq (by simpa [doublingCap] using hcap)
    simp [hcap0, doublingCap]
  | succ m =>
    have hpos : 0 < doublingCap minCap (m + 1) := doublingCap_pos hmin (Nat.succ_pos m)
    have hcap_ne : cap ≠ 0#64 := by
      intro heq
      rw [heq] at hcap
      simp at hcap
      omega
    have hmul_ne : doublingCap minCap (m + 1) * elemSz ≠ 0 :=
      Nat.ne_of_gt (Nat.mul_pos hpos helem)
    simp [hcap_ne, hmul_ne]

/-- Post-step `sc = 63` live-byte footprint of a `RawVec` buffer of capacity `cap` and stride `elemSz`. -/
def rawVecLargeLive (M : AllocCostModel) [HasFineReallocCredit M]
    (elemSz cap : Nat) : Nat :=
  allocLargeLive M (cap * elemSz)

/-- Single-step `cumSmall` charge of the `j`-th `RawVec<T>::grow_one` transition
(`doublingCap minCap j → doublingCap minCap (j + 1)`). -/
def rawVecStepCum (M : AllocCostModel) [HasFineReallocCredit M]
    (elemSz minCap align j : Nat) : Nat :=
  growOrReallocStepCum M
    (doublingCap minCap j * elemSz)
    (doublingCap minCap (j + 1) * elemSz)
    align

/-- Cumulative `cumSmall` charge across `k` `RawVec<T>::grow_one` transitions from `0` to
`doublingCap minCap k`. -/
def rawVecCumOfSteps (M : AllocCostModel) [HasFineReallocCredit M]
    (elemSz minCap align : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => rawVecCumOfSteps M elemSz minCap align k + rawVecStepCum M elemSz minCap align k

/-- Worst-case transient `sc = 63` overlap (`old + new`) across `k` `RawVec<T>::grow_one`
transitions from `0` to `doublingCap minCap k`. -/
def rawVecPeakOfSteps (M : AllocCostModel) [HasFineReallocCredit M]
    (elemSz minCap : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    max (rawVecPeakOfSteps M elemSz minCap k)
      (rawVecLargeLive M elemSz (doublingCap minCap k) +
        rawVecLargeLive M elemSz (doublingCap minCap (k + 1)))

@[simp] theorem rawVecLargeLive_zero_cap (M : AllocCostModel) [HasFineReallocCredit M]
    (elemSz : Nat) :
    rawVecLargeLive M elemSz 0 = 0 := by
  simp [rawVecLargeLive]

theorem rawVecGrowEnv_req_align {elemSz minCap align j : Nat} {x : GrowOneCall}
    {evs : List AllocEvent}
    (helem : 0 < elemSz) (hmin : 0 < minCap) (hal : align ≤ 16)
    (hcap : x.cap.toNat = doublingCap minCap j)
    (hEnv : RawVecGrowEnv elemSz minCap align x evs) :
    ∀ ev ∈ evs,
      eventStepReq ev ≤ doublingCap minCap (j + 1) * elemSz ∧
      eventStepAlign ev ≤ 16 := by
  rw [rawVecGrowEvents_eq_of_env hEnv, rawVecGrowEvents_eq_growOrReallocEvents helem hmin hcap]
  exact growOrReallocEvents_req_align hal

/-- Credit transition for `RawVecGrowEnv elemSz minCap align x evs` at `x.cap.toNat = doublingCap minCap j`.
-/
theorem stepEvents_rawVecGrow_credit (M : AllocCostModel) [HasFineReallocCredit M]
    {elemSz minCap align j L_base : Nat} {x : GrowOneCall} {evs : List AllocEvent} (st : M.σ)
    (helem : 0 < elemSz) (hmin : 0 < minCap) (hal : align ≤ 16)
    (hcap : x.cap.toNat = doublingCap minCap j)
    (hEnv : RawVecGrowEnv elemSz minCap align x evs)
    (hlive : HasFineReallocCredit.liveLarge st ≤
      L_base + rawVecLargeLive M elemSz (doublingCap minCap j)) :
    let st' := M.stepEvents evs st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + rawVecStepCum M elemSz minCap align j ∧
    HasFineReallocCredit.liveLarge st' ≤
      L_base + rawVecLargeLive M elemSz (doublingCap minCap (j + 1)) ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (L_base + rawVecLargeLive M elemSz (doublingCap minCap j) +
          rawVecLargeLive M elemSz (doublingCap minCap (j + 1))) := by
  rw [rawVecGrowEvents_eq_of_env hEnv, rawVecGrowEvents_eq_growOrReallocEvents helem hmin hcap]
  have hnew_pos : 0 < doublingCap minCap (j + 1) * elemSz :=
    Nat.mul_pos (doublingCap_pos hmin (Nat.succ_pos j)) helem
  exact stepEvents_growOrRealloc_credit M st hal hnew_pos hlive

private def smallBytesSum (S elemSz minCap : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    smallBytesSum S elemSz minCap k +
      if doublingCap minCap (k + 1) * elemSz ≤ S then
        doublingCap minCap (k + 1) * elemSz
      else 0

private theorem smallBytesSum_le_two_mul_min (S elemSz minCap : Nat) :
    ∀ k : Nat,
      smallBytesSum S elemSz minCap k ≤ 2 * min (doublingCap minCap k * elemSz) S
  | 0 => by simp [smallBytesSum]
  | 1 => by
    simp only [smallBytesSum, Nat.zero_add]
    split <;> omega
  | m + 2 => by
    have ih := smallBytesSum_le_two_mul_min S elemSz minCap (m + 1)
    have hdouble :
        doublingCap minCap (m + 2) * elemSz = 2 * (doublingCap minCap (m + 1) * elemSz) := by
      rw [doublingCap_succ_succ, Nat.mul_assoc]
    change smallBytesSum S elemSz minCap (m + 1) +
        (if doublingCap minCap (m + 2) * elemSz ≤ S then
          doublingCap minCap (m + 2) * elemSz
        else 0) ≤
      2 * min (doublingCap minCap (m + 2) * elemSz) S
    by_cases hle : doublingCap minCap (m + 2) * elemSz ≤ S
    · have hle_prev : doublingCap minCap (m + 1) * elemSz ≤ S := by omega
      have hmin_prev : min (doublingCap minCap (m + 1) * elemSz) S =
          doublingCap minCap (m + 1) * elemSz := Nat.min_eq_left hle_prev
      have hmin_cur : min (doublingCap minCap (m + 2) * elemSz) S =
          doublingCap minCap (m + 2) * elemSz := Nat.min_eq_left hle
      simp only [hle, ↓reduceIte]
      omega
    · have hmin_prev : min (doublingCap minCap (m + 1) * elemSz) S ≤ S := Nat.min_le_right _ _
      have hmin_cur : min (doublingCap minCap (m + 2) * elemSz) S = S :=
        Nat.min_eq_right (Nat.le_of_not_ge hle)
      simp only [hle, ↓reduceIte]
      omega

private theorem rawVecCumOfSteps_le_smallBytesSum (M : AllocCostModel) [HasFineReallocCredit M]
    (hSmallAlloc : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallAllocCost M r ≤ 2 * r + 9539)
    (hSmallRealloc : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallReallocCost M r ≤ 2 * r + 9539)
    (hMeta : HasFineReallocCredit.largeMetaCost M ≤ 122)
    (elemSz minCap align : Nat) :
    ∀ k : Nat,
      rawVecCumOfSteps M elemSz minCap align k ≤
        2 * smallBytesSum (HasFineReallocCredit.smallMaxReq M) elemSz minCap k + 9539 * k
  | 0 => by simp [rawVecCumOfSteps, smallBytesSum]
  | k + 1 => by
    have ih := rawVecCumOfSteps_le_smallBytesSum M hSmallAlloc hSmallRealloc hMeta
      elemSz minCap align k
    have hstep := growOrReallocStepCum_le_affine M hSmallAlloc hSmallRealloc hMeta
      (doublingCap minCap k * elemSz) (doublingCap minCap (k + 1) * elemSz) align
    change rawVecCumOfSteps M elemSz minCap align k +
        growOrReallocStepCum M (doublingCap minCap k * elemSz)
          (doublingCap minCap (k + 1) * elemSz) align ≤
      2 * (smallBytesSum (HasFineReallocCredit.smallMaxReq M) elemSz minCap k +
        (if doublingCap minCap (k + 1) * elemSz ≤ HasFineReallocCredit.smallMaxReq M then
          doublingCap minCap (k + 1) * elemSz
        else 0)) + 9539 * (k + 1)
    by_cases hle : doublingCap minCap (k + 1) * elemSz ≤ HasFineReallocCredit.smallMaxReq M
    · simp only [hle, ↓reduceIte] at hstep ⊢
      omega
    · simp only [hle, ↓reduceIte] at hstep ⊢
      omega

/-- Closed-form affine upper bound on `rawVecCumOfSteps`:
`rawVecCumOfSteps M elemSz minCap align k ≤ 4 * min (doublingCap minCap k * elemSz) (smallMaxReq M) + 9539 * k`.
-/
theorem rawVecCumOfSteps_le_affine (M : AllocCostModel) [HasFineReallocCredit M]
    (hSmallAlloc : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallAllocCost M r ≤ 2 * r + 9539)
    (hSmallRealloc : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
      HasFineReallocCredit.smallReallocCost M r ≤ 2 * r + 9539)
    (hMeta : HasFineReallocCredit.largeMetaCost M ≤ 122)
    (elemSz minCap align k : Nat) :
    rawVecCumOfSteps M elemSz minCap align k ≤
      4 * min (doublingCap minCap k * elemSz) (HasFineReallocCredit.smallMaxReq M) + 9539 * k := by
  have h1 := rawVecCumOfSteps_le_smallBytesSum M hSmallAlloc hSmallRealloc hMeta
    elemSz minCap align k
  have h2 := smallBytesSum_le_two_mul_min (HasFineReallocCredit.smallMaxReq M) elemSz minCap k
  omega

theorem rawVecLargeLive_le_affine (M : AllocCostModel) [HasFineReallocCredit M]
    (hLargeAff : ∀ r, HasFineReallocCredit.smallMaxReq M < r →
      HasFineReallocCredit.largeCost M r ≤ r + 8195)
    (elemSz cap : Nat) :
    rawVecLargeLive M elemSz cap ≤
      if cap * elemSz ≤ HasFineReallocCredit.smallMaxReq M then 0
      else cap * elemSz + 8195 :=
  allocLargeLive_le_affine M hLargeAff (cap * elemSz)

/-- Worst-case post-step `sc = 63` live-byte footprint across prefixes `0 ≤ m ≤ k` of the `RawVec` doubling ladder.
-/
def rawVecMaxLiveOfSteps (M : AllocCostModel) [HasFineReallocCredit M]
    (elemSz minCap : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    max (rawVecMaxLiveOfSteps M elemSz minCap k)
      (rawVecLargeLive M elemSz (doublingCap minCap (k + 1)))

/-- Capacity words `[doublingCap minCap j, ..., doublingCap minCap (j + n - 1)]` for `n`
consecutive `grow_one` calls starting from ladder index `j`. -/
def doublingCapsFrom (minCap j : Nat) : Nat → List (BitVec 64)
  | 0 => []
  | n + 1 => BitVec.ofNat 64 (doublingCap minCap j) :: doublingCapsFrom minCap (j + 1) n

/-- Capacity words `[0, minCap, 2 * minCap, ..., minCap * 2 ^ (k - 2)]` for `k` consecutive
`grow_one` calls from initial capacity `0` to `doublingCap minCap k`. -/
abbrev doublingCaps (minCap k : Nat) : List (BitVec 64) :=
  doublingCapsFrom minCap 0 k

theorem rawVecLargeLive_le_maxLiveOfSteps (M : AllocCostModel) [HasFineReallocCredit M]
    (elemSz minCap : Nat) :
    ∀ j : Nat, rawVecLargeLive M elemSz (doublingCap minCap j) ≤
      rawVecMaxLiveOfSteps M elemSz minCap j
  | 0 => by simp [rawVecMaxLiveOfSteps]
  | j + 1 => Nat.le_max_right _ _

theorem rawVecMaxLiveOfSteps_mono (M : AllocCostModel) [HasFineReallocCredit M]
    (elemSz minCap : Nat) {j k : Nat} (hjk : j ≤ k) :
    rawVecMaxLiveOfSteps M elemSz minCap j ≤ rawVecMaxLiveOfSteps M elemSz minCap k := by
  induction hjk with
  | refl => exact Nat.le_refl _
  | @step m _ ih => exact Nat.le_trans ih (Nat.le_max_left _ _)

theorem rawVecPeakOfSteps_mono (M : AllocCostModel) [HasFineReallocCredit M]
    (elemSz minCap : Nat) {j k : Nat} (hjk : j ≤ k) :
    rawVecPeakOfSteps M elemSz minCap j ≤ rawVecPeakOfSteps M elemSz minCap k := by
  induction hjk with
  | refl => exact Nat.le_refl _
  | @step m _ ih => exact Nat.le_trans ih (Nat.le_max_left _ _)

theorem rawVecStepPeak_le_peakOfSteps (M : AllocCostModel) [HasFineReallocCredit M]
    (elemSz minCap : Nat) {j k : Nat} (hjk : j + 1 ≤ k) :
    rawVecLargeLive M elemSz (doublingCap minCap j) +
      rawVecLargeLive M elemSz (doublingCap minCap (j + 1)) ≤
      rawVecPeakOfSteps M elemSz minCap k := by
  have h1 : rawVecLargeLive M elemSz (doublingCap minCap j) +
      rawVecLargeLive M elemSz (doublingCap minCap (j + 1)) ≤
      rawVecPeakOfSteps M elemSz minCap (j + 1) := Nat.le_max_right _ _
  exact Nat.le_trans h1 (rawVecPeakOfSteps_mono M elemSz minCap hjk)

theorem rawVecMaxLiveOfSteps_le_affine (M : AllocCostModel) [HasFineReallocCredit M]
    (hLargeAff : ∀ r, HasFineReallocCredit.smallMaxReq M < r →
      HasFineReallocCredit.largeCost M r ≤ r + 8195)
    (elemSz minCap : Nat) :
    ∀ k : Nat,
      rawVecMaxLiveOfSteps M elemSz minCap k ≤
        if doublingCap minCap k * elemSz ≤ HasFineReallocCredit.smallMaxReq M then 0
        else doublingCap minCap k * elemSz + 8195
  | 0 => by simp [rawVecMaxLiveOfSteps]
  | k + 1 => by
    have ih := rawVecMaxLiveOfSteps_le_affine M hLargeAff elemSz minCap k
    have hcur := rawVecLargeLive_le_affine M hLargeAff elemSz (doublingCap minCap (k + 1))
    have hmono : doublingCap minCap k * elemSz ≤ doublingCap minCap (k + 1) * elemSz :=
      Nat.mul_le_mul_right elemSz (doublingCap_mono minCap (Nat.le_succ k))
    simp only [rawVecMaxLiveOfSteps]
    by_cases hle : doublingCap minCap (k + 1) * elemSz ≤ HasFineReallocCredit.smallMaxReq M
    · have hle_prev : doublingCap minCap k * elemSz ≤ HasFineReallocCredit.smallMaxReq M :=
        Nat.le_trans hmono hle
      simp only [hle, hle_prev, ↓reduceIte] at ih hcur ⊢
      omega
    · simp only [hle, ↓reduceIte] at hcur ⊢
      split at ih <;> omega

theorem rawVecPeakOfSteps_le_affine (M : AllocCostModel) [HasFineReallocCredit M]
    (hLargeAff : ∀ r, HasFineReallocCredit.smallMaxReq M < r →
      HasFineReallocCredit.largeCost M r ≤ r + 8195)
    (elemSz minCap : Nat) :
    ∀ k : Nat,
      rawVecPeakOfSteps M elemSz minCap k ≤
        if doublingCap minCap k * elemSz ≤ HasFineReallocCredit.smallMaxReq M then 0
        else (3 * (doublingCap minCap k * elemSz)) / 2 + 16390
  | 0 => by simp [rawVecPeakOfSteps]
  | k + 1 => by
    have ih := rawVecPeakOfSteps_le_affine M hLargeAff elemSz minCap k
    have hmono : doublingCap minCap k * elemSz ≤ doublingCap minCap (k + 1) * elemSz :=
      Nat.mul_le_mul_right elemSz (doublingCap_mono minCap (Nat.le_succ k))
    have h2 : 2 * (doublingCap minCap k * elemSz) ≤ doublingCap minCap (k + 1) * elemSz := by
      have hcap2 := two_mul_doublingCap_le_succ minCap k
      calc
        2 * (doublingCap minCap k * elemSz) = (2 * doublingCap minCap k) * elemSz :=
          (Nat.mul_assoc 2 _ _).symm
        _ ≤ doublingCap minCap (k + 1) * elemSz := Nat.mul_le_mul_right elemSz hcap2
    have hprev := rawVecLargeLive_le_affine M hLargeAff elemSz (doublingCap minCap k)
    have hcur := rawVecLargeLive_le_affine M hLargeAff elemSz (doublingCap minCap (k + 1))
    simp only [rawVecPeakOfSteps]
    by_cases hle : doublingCap minCap (k + 1) * elemSz ≤ HasFineReallocCredit.smallMaxReq M
    · have hle_prev : doublingCap minCap k * elemSz ≤ HasFineReallocCredit.smallMaxReq M :=
        Nat.le_trans hmono hle
      simp only [hle, hle_prev, ↓reduceIte] at ih hprev hcur ⊢
      omega
    · simp only [hle, ↓reduceIte] at hcur ⊢
      split at ih <;> split at hprev <;> omega

end LibsignalBinary.Proofs.PeakBudget.VecGrowCreditHelpers
