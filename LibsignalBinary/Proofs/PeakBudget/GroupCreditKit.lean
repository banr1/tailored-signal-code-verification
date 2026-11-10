/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas

/-!
# Small-Allocation Group Credit Kit and Decoupled `FitsTrace`/`FitsEnv` Bridges

Tracks `mallocng` slot-group creation (`cumSmallGroupsS + FineScale * finePeak63Count`) separately
from cumulative small-allocation byte volume (`fineCumSmall`):
1. Scaled group counter `fineGroupsScaled` (`FineScale = 65,536`) and decoupled `*OfGroups` bounds
   (`fineMaxGroupsOfGroups`, `fineMaxMetaAreasOfGroups`, `fineDynIvsOfGroups`,
   `fineStepReserveOfGroups`).
2. `HasFineGroupCredit` typeclass, its `fineCostModel` instance, and per-size-class group weights.
3. Composable `NonFreeBound` and `PhaseGroupSpec` combinators, plus decoupled `FitsStep`,
   `FitsTrace`, and `FitsEnv` bridges on `fineCostModel`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.GroupCreditKit

open Arm64 ProofLib
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize mallocngAlignedEffSize)
open VerifiedLibraries.Mallocng.Proofs (sizeToClassUnits)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits
  FitsStep FitsEvent FitsEvents FitsTrace FitsEnv
  SeqEnv FreeOnlyEvs
  rustAllocEvents rustDeallocEvents rustReallocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit fitsStep_of_fine_bounds
)
open LibsignalBinary.Heap.Fine (
  FineBudget FineEvent FineScale MmapThresholdReq Guaranteed63Threshold FineStepBound
  gBaseConst coarseGrpWtS coarseWt_le_cap
  finePeak63Bytes finePeak63Count fineMaxGroups fineMaxMetaAreas fineMaxDynIvs
  fineCostModel toFineEvent
)
open LibsignalBinary.Heap.Fine.ClientBounds (
  gBaseConst_eq fineCostModel_baseFine_eq
  eventStepReq eventStepAlign FineStepBound_mono fineCostModel_stepReserve_eq
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (
  ConcatEnv IterSeqEnv IterConcatEnv FreeOnlyAlign16Evs PhaseCreditSpec
)

/-! ## 1. Scaled Group Counter and Decoupled `*OfGroups` Bounds -/

/-- Scaled cumulative small-group + peak large-group counter (`FineScale = 65,536` units per group). -/
def fineGroupsScaled (b : FineBudget) : Nat :=
  b.cumSmallGroupsS + FineScale * finePeak63Count b

theorem fineGroupsScaled_init : fineGroupsScaled FineBudget.init = 0 := rfl

/-- Closed-form upper bound on `fineMaxGroups b` when `(fineGroupsScaled b + FineScale - 1) / FineScale ≤ grpB`
(`gBaseConst = 272`). -/
def fineMaxGroupsOfGroups (grpB : Nat) : Nat :=
  272 + grpB

/-- Closed-form upper bound on `fineMaxMetaAreas b` (`1 + (7 + fineMaxGroups) / 101`) from `grpB`. -/
def fineMaxMetaAreasOfGroups (grpB : Nat) : Nat :=
  1 + (279 + grpB) / 101

/-- Closed-form upper bound on `fineCostModel.maxDynIvs b` from `grpB`. -/
def fineDynIvsOfGroups (grpB : Nat) : Nat :=
  3 * fineMaxMetaAreasOfGroups grpB + 2 + fineMaxGroupsOfGroups grpB

/-- Closed-form upper bound on `fineCostModel.stepReserve ev b` from `(maxReq, maxAlign, grpB)`. -/
def fineStepReserveOfGroups (maxReq maxAlign grpB : Nat) : Nat :=
  FineStepBound maxReq maxAlign (fineMaxMetaAreasOfGroups grpB)

theorem fineMaxGroupsOfGroups_mono {g₁ g₂ : Nat} (h : g₁ ≤ g₂) :
    fineMaxGroupsOfGroups g₁ ≤ fineMaxGroupsOfGroups g₂ := by
  unfold fineMaxGroupsOfGroups; omega

theorem fineMaxMetaAreasOfGroups_mono {g₁ g₂ : Nat} (h : g₁ ≤ g₂) :
    fineMaxMetaAreasOfGroups g₁ ≤ fineMaxMetaAreasOfGroups g₂ := by
  unfold fineMaxMetaAreasOfGroups; omega

theorem fineDynIvsOfGroups_mono {g₁ g₂ : Nat} (h : g₁ ≤ g₂) :
    fineDynIvsOfGroups g₁ ≤ fineDynIvsOfGroups g₂ := by
  have hm := fineMaxMetaAreasOfGroups_mono h
  have hg := fineMaxGroupsOfGroups_mono h
  unfold fineDynIvsOfGroups; omega

theorem fineStepReserveOfGroups_mono {r₁ r₂ a₁ a₂ g₁ g₂ : Nat}
    (hr : r₁ ≤ r₂) (ha : max a₁ 16 ≤ max a₂ 16) (hg : g₁ ≤ g₂) :
    fineStepReserveOfGroups r₁ a₁ g₁ ≤ fineStepReserveOfGroups r₂ a₂ g₂ :=
  FineStepBound_mono hr ha (fineMaxMetaAreasOfGroups_mono hg)

theorem fineMaxGroups_le_of_groupsScaled {b : FineBudget} {grpB : Nat}
    (hgrp : (fineGroupsScaled b + FineScale - 1) / FineScale ≤ grpB) :
    fineMaxGroups b ≤ fineMaxGroupsOfGroups grpB := by
  unfold fineMaxGroups fineMaxGroupsOfGroups fineGroupsScaled FineScale at *
  rw [gBaseConst_eq]
  omega

theorem fineMaxMetaAreas_le_of_groupsScaled {b : FineBudget} {grpB : Nat}
    (hgrp : (fineGroupsScaled b + FineScale - 1) / FineScale ≤ grpB) :
    fineMaxMetaAreas b ≤ fineMaxMetaAreasOfGroups grpB := by
  have hg := fineMaxGroups_le_of_groupsScaled hgrp
  unfold fineMaxMetaAreas fineMaxMetaAreasOfGroups fineMaxGroupsOfGroups at *
  omega

theorem fineMaxDynIvs_le_of_groupsScaled {b : fineCostModel.σ} {grpB : Nat}
    (hgrp : (fineGroupsScaled b + FineScale - 1) / FineScale ≤ grpB) :
    fineCostModel.maxDynIvs b ≤ fineDynIvsOfGroups grpB := by
  have hg := fineMaxGroups_le_of_groupsScaled hgrp
  have hm := fineMaxMetaAreas_le_of_groupsScaled hgrp
  change fineMaxDynIvs b ≤ fineDynIvsOfGroups grpB
  unfold fineMaxDynIvs fineDynIvsOfGroups
  omega

theorem fineStepReserve_le_of_groupsScaled {ev : AllocEvent} {b : fineCostModel.σ}
    {maxReq maxAlign grpB : Nat}
    (hreq : eventStepReq ev ≤ maxReq)
    (hal : max (eventStepAlign ev) 16 ≤ max maxAlign 16)
    (hgrp : (fineGroupsScaled b + FineScale - 1) / FineScale ≤ grpB) :
    fineCostModel.stepReserve ev b ≤ fineStepReserveOfGroups maxReq maxAlign grpB := by
  rw [fineCostModel_stepReserve_eq]
  exact FineStepBound_mono hreq hal (fineMaxMetaAreas_le_of_groupsScaled hgrp)

theorem withinMaxAlloc_of_fineStepBound_le_2pow48
    {ev : AllocEvent} {maxReq maxAlign m : Nat}
    (hreq : eventStepReq ev ≤ maxReq)
    (hal : max (eventStepAlign ev) 16 ≤ max maxAlign 16)
    (hstep : FineStepBound maxReq maxAlign m ≤ 2 ^ 48) :
    ev.withinMaxAlloc := by
  have hbase : maxReq + (max maxAlign 16 - 16) ≤ FineStepBound maxReq maxAlign m := by
    unfold FineStepBound
    have hle := pageAlignUp_le (maxReq + (max maxAlign 16 - 16) + 8192)
    omega
  cases ev with
  | alloc req =>
    simp only [eventStepReq] at hreq
    unfold AllocEvent.withinMaxAlloc MallocngMaxAllocSize
    omega
  | aligned align req =>
    simp only [eventStepReq] at hreq
    simp only [eventStepAlign] at hal
    simp only [AllocEvent.withinMaxAlloc, mallocngAlignedEffSize, MallocngMaxAllocSize]
    split <;> omega
  | free _ _ =>
    exact True.intro
  | realloc _ _ newSz =>
    simp only [eventStepReq] at hreq
    unfold AllocEvent.withinMaxAlloc MallocngMaxAllocSize
    omega

/-! ## 2. `HasFineGroupCredit` Class and `fineCostModel` Instance -/

/-- Per-request `FineScale`-scaled group weight for `.alloc req` and `al ≤ 16` `.aligned al req`
with `req ≤ MmapThresholdReq` (`131,051`). -/
def fineSmallAllocGroupS (req : Nat) : Nat :=
  coarseGrpWtS (sizeToClassUnits ((req + 3) / 16))

/-- Per-request `FineScale`-scaled group weight for `al ≤ 16` `.realloc` into
`newSz ≤ MmapThresholdReq` (`131,051`). -/
def fineSmallReallocGroupS (newSz : Nat) : Nat :=
  max (coarseGrpWtS (sizeToClassUnits ((newSz + 3) / 16))) FineScale

/-- Companion cost-model extension tracking `FineScale`-scaled group creation independently of
byte volume (`HasFineReallocCredit.cumSmall`). -/
class HasFineGroupCredit (M : AllocCostModel) where
  groupsScaled : M.σ → Nat
  smallAllocGroupS : Nat → Nat
  smallReallocGroupS : Nat → Nat
  groupsScaled_init : groupsScaled M.init = 0
  smallAllocGroupS_le_smallReallocGroupS : ∀ req : Nat,
    smallAllocGroupS req ≤ smallReallocGroupS req
  step_free_le : ∀ (al sz : Nat) (st : M.σ),
    groupsScaled (M.step (.free al sz) st) ≤ groupsScaled st
  step_any_le : ∀ (ev : AllocEvent) (st : M.σ),
    groupsScaled (M.step ev st) ≤ groupsScaled st + 3 * FineScale
  step_alloc_small_le : ∀ {req : Nat} (st : M.σ), req ≤ MmapThresholdReq →
    groupsScaled (M.step (.alloc req) st) ≤ groupsScaled st + smallAllocGroupS req
  step_aligned_small_le : ∀ {al req : Nat} (st : M.σ), al ≤ 16 → req ≤ MmapThresholdReq →
    groupsScaled (M.step (.aligned al req) st) ≤ groupsScaled st + smallAllocGroupS req
  step_realloc_small_le : ∀ {al old newSz : Nat} (st : M.σ), al ≤ 16 → newSz ≤ MmapThresholdReq →
    groupsScaled (M.step (.realloc al old newSz) st) ≤ groupsScaled st + smallReallocGroupS newSz
  step_large_le : ∀ {ev : AllocEvent} (st : M.σ),
    eventStepAlign ev ≤ 16 → MmapThresholdReq < eventStepReq ev →
    groupsScaled (M.step ev st) ≤ groupsScaled st + FineScale

theorem stepFree_groupsScaled_eq (al sz : Nat) (b : FineBudget) :
    fineGroupsScaled (FineBudget.stepFree al sz b) = fineGroupsScaled b := by
  unfold FineBudget.stepFree fineGroupsScaled finePeak63Count
  dsimp only
  split <;> simp

theorem stepAligned_groupsScaled_any (al req : Nat) (b : FineBudget) :
    fineGroupsScaled (FineBudget.stepAligned al req b) ≤ fineGroupsScaled b + 3 * FineScale := by
  have hCap := (coarseWt_le_cap (sizeToClassUnits ((req + (max al 16 - 16) + 3) / 16))).2
  unfold FineBudget.stepAligned fineGroupsScaled finePeak63Count FineScale at *
  dsimp only
  by_cases hBig : Guaranteed63Threshold ≤ req
  · simp only [hBig, ↓reduceIte]
    omega
  · simp only [hBig, ↓reduceIte]
    by_cases hSm : req + (max al 16 - 16) ≤ MmapThresholdReq <;>
      simp only [hSm, ↓reduceIte] <;> omega

theorem stepReallocAdd_groupsScaled_any (al newSz : Nat) (b : FineBudget) :
    fineGroupsScaled (FineBudget.stepReallocAdd al newSz b) ≤ fineGroupsScaled b + 3 * FineScale := by
  unfold FineBudget.stepReallocAdd
  dsimp only
  by_cases hBig : Guaranteed63Threshold ≤ newSz
  · simp only [hBig, ↓reduceIte]
    exact stepAligned_groupsScaled_any al newSz b
  · simp only [hBig, ↓reduceIte]
    have hCap := (coarseWt_le_cap (sizeToClassUnits ((newSz + 3) / 16))).2
    unfold fineGroupsScaled finePeak63Count FineScale at *
    by_cases hSm : newSz ≤ MmapThresholdReq <;> simp only [hSm, ↓reduceIte] <;> omega

theorem stepAligned_groupsScaled_small {al req : Nat} (b : FineBudget)
    (hal : al ≤ 16) (hle : req ≤ MmapThresholdReq) :
    fineGroupsScaled (FineBudget.stepAligned al req b) ≤
      fineGroupsScaled b + fineSmallAllocGroupS req := by
  have hNot63 : ¬ (Guaranteed63Threshold ≤ req) := by
    unfold Guaranteed63Threshold MmapThresholdReq at *; omega
  have hMaxAl : max al 16 = 16 := by omega
  unfold FineBudget.stepAligned fineSmallAllocGroupS fineGroupsScaled finePeak63Count FineScale
  dsimp only
  simp only [hNot63, hMaxAl, Nat.sub_self, Nat.add_zero, hle, ↓reduceIte]
  omega

theorem stepAligned_groupsScaled_gt_mmap {al req : Nat} (b : FineBudget)
    (hal : al ≤ 16) (hgt : MmapThresholdReq < req) :
    fineGroupsScaled (FineBudget.stepAligned al req b) ≤ fineGroupsScaled b + FineScale := by
  have hMaxAl : max al 16 = 16 := by omega
  have hNotSm : ¬ (req ≤ MmapThresholdReq) := by omega
  unfold FineBudget.stepAligned fineGroupsScaled finePeak63Count FineScale at *
  dsimp only
  by_cases hBig : Guaranteed63Threshold ≤ req
  · simp only [hBig, ↓reduceIte]
    omega
  · simp only [hBig, hMaxAl, Nat.sub_self, Nat.add_zero, hNotSm, ↓reduceIte]
    omega

instance : HasFineGroupCredit fineCostModel where
  groupsScaled := fineGroupsScaled
  smallAllocGroupS := fineSmallAllocGroupS
  smallReallocGroupS := fineSmallReallocGroupS
  groupsScaled_init := rfl
  smallAllocGroupS_le_smallReallocGroupS _ := Nat.le_max_left _ _
  step_free_le al sz b := Nat.le_of_eq (stepFree_groupsScaled_eq al sz b)
  step_any_le ev b := by
    cases ev with
    | alloc req => exact stepAligned_groupsScaled_any 16 req b
    | aligned al req => exact stepAligned_groupsScaled_any al req b
    | free al sz =>
      have h := stepFree_groupsScaled_eq al sz b
      change fineGroupsScaled (FineBudget.stepFree al sz b) ≤ _
      omega
    | realloc al old newSz =>
      change fineGroupsScaled (FineBudget.stepFree al old (FineBudget.stepReallocAdd al newSz b)) ≤ _
      rw [stepFree_groupsScaled_eq]
      exact stepReallocAdd_groupsScaled_any al newSz b
  step_alloc_small_le b hle := stepAligned_groupsScaled_small b (by decide) hle
  step_aligned_small_le b hal hle := stepAligned_groupsScaled_small b hal hle
  step_realloc_small_le {al old newSz} b _hal hle := by
    have hNot63 : ¬ (Guaranteed63Threshold ≤ newSz) := by
      unfold Guaranteed63Threshold MmapThresholdReq at *; omega
    change fineGroupsScaled (FineBudget.stepFree al old (FineBudget.stepReallocAdd al newSz b)) ≤ _
    rw [stepFree_groupsScaled_eq]
    unfold FineBudget.stepReallocAdd fineSmallReallocGroupS fineGroupsScaled finePeak63Count FineScale
    dsimp only
    simp only [hNot63, hle, ↓reduceIte]
    omega
  step_large_le {ev} b hal hgt := by
    cases ev with
    | alloc req =>
      simp only [eventStepReq] at hgt
      exact stepAligned_groupsScaled_gt_mmap b (by decide) hgt
    | aligned al req =>
      simp only [eventStepAlign] at hal
      simp only [eventStepReq] at hgt
      exact stepAligned_groupsScaled_gt_mmap b hal hgt
    | free _ _ =>
      simp only [eventStepReq] at hgt
      omega
    | realloc al old newSz =>
      simp only [eventStepAlign] at hal
      simp only [eventStepReq] at hgt
      change fineGroupsScaled (FineBudget.stepFree al old (FineBudget.stepReallocAdd al newSz b)) ≤ _
      rw [stepFree_groupsScaled_eq]
      unfold FineBudget.stepReallocAdd
      dsimp only
      by_cases hBig : Guaranteed63Threshold ≤ newSz
      · simp only [hBig, ↓reduceIte]
        exact stepAligned_groupsScaled_gt_mmap b hal hgt
      · have hNotSm : ¬ (newSz ≤ MmapThresholdReq) := by omega
        unfold fineGroupsScaled finePeak63Count FineScale
        simp only [hBig, hNotSm, ↓reduceIte]
        omega

theorem groupsScaled_fineCostModel_eq (b : fineCostModel.σ) :
    HasFineGroupCredit.groupsScaled (M := fineCostModel) b = fineGroupsScaled b := rfl

theorem smallAllocGroupS_fineCostModel_eq (req : Nat) :
    HasFineGroupCredit.smallAllocGroupS fineCostModel req = fineSmallAllocGroupS req := rfl

theorem smallReallocGroupS_fineCostModel_eq (newSz : Nat) :
    HasFineGroupCredit.smallReallocGroupS fineCostModel newSz = fineSmallReallocGroupS newSz := rfl

/-! ## 3. Small-Bucket Group Weights (`coarseGrpWtS` Evaluations) -/

/-- `sc = 0` (`req ≤ 12`): at most `4,737 / 65,536 ≈ 0.0723` groups per allocation. -/
theorem smallAllocGroupS_le_4737_of_le_12 {req : Nat} (h : req ≤ 12) :
    fineSmallAllocGroupS req ≤ 4737 := by
  unfold fineSmallAllocGroupS
  have hu : (req + 3) / 16 = 0 := by omega
  rw [hu]; decide

/-- `sc ≤ 1` (`req ≤ 28`, e.g. `28 B` `<Chain>::recv_key` allocations):
at most `11,056 / 65,536 ≈ 0.1687` groups per allocation. -/
theorem smallAllocGroupS_le_11056_of_le_28 {req : Nat} (h : req ≤ 28) :
    fineSmallAllocGroupS req ≤ 11056 := by
  unfold fineSmallAllocGroupS
  have hu : (req + 3) / 16 = 0 ∨ (req + 3) / 16 = 1 := by omega
  rcases hu with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide

/-- `sc ≤ 2` (`req ≤ 44`, e.g. `32 B` OOO message-key seeds and `33 B` `cmkJump` keys):
at most `16,659 / 65,536 ≈ 0.2542` groups per allocation. -/
theorem smallAllocGroupS_le_16659_of_le_44 {req : Nat} (h : req ≤ 44) :
    fineSmallAllocGroupS req ≤ 16659 := by
  unfold fineSmallAllocGroupS
  have hu : (req + 3) / 16 = 0 ∨ (req + 3) / 16 = 1 ∨ (req + 3) / 16 = 2 := by omega
  rcases hu with h0 | h1 | h2
  · rw [h0]; decide
  · rw [h1]; decide
  · rw [h2]; decide

/-- `sc ≤ 3` (`req ≤ 60`, e.g. `48 B` / `56 B` small buffers):
at most `24,623 / 65,536 ≈ 0.3757` groups per allocation. -/
theorem smallAllocGroupS_le_24623_of_le_60 {req : Nat} (h : req ≤ 60) :
    fineSmallAllocGroupS req ≤ 24623 := by
  unfold fineSmallAllocGroupS
  have hu : (req + 3) / 16 = 0 ∨ (req + 3) / 16 = 1 ∨ (req + 3) / 16 = 2 ∨ (req + 3) / 16 = 3 := by
    omega
  rcases hu with h0 | h1 | h2 | h3
  · rw [h0]; decide
  · rw [h1]; decide
  · rw [h2]; decide
  · rw [h3]; decide

/-- `sc ≤ 6` (`req ≤ 108`, e.g. `64 B`–`104 B` structs):
at most `43,464 / 65,536 ≈ 0.6632` groups per allocation. -/
theorem smallAllocGroupS_le_43464_of_le_108 {req : Nat} (h : req ≤ 108) :
    fineSmallAllocGroupS req ≤ 43464 := by
  unfold fineSmallAllocGroupS
  have hu : (req + 3) / 16 = 0 ∨ (req + 3) / 16 = 1 ∨ (req + 3) / 16 = 2 ∨
      (req + 3) / 16 = 3 ∨ (req + 3) / 16 = 4 ∨ (req + 3) / 16 = 5 ∨ (req + 3) / 16 = 6 := by
    omega
  rcases hu with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · rw [h0]; decide
  · rw [h1]; decide
  · rw [h2]; decide
  · rw [h3]; decide
  · rw [h4]; decide
  · rw [h5]; decide
  · rw [h6]; decide

theorem smallAllocGroupS_le_three_scale (req : Nat) :
    fineSmallAllocGroupS req ≤ 3 * FineScale :=
  (coarseWt_le_cap (sizeToClassUnits ((req + 3) / 16))).2

theorem smallReallocGroupS_le_three_scale (newSz : Nat) :
    fineSmallReallocGroupS newSz ≤ 3 * FineScale := by
  unfold fineSmallReallocGroupS FineScale
  have hCap := (coarseWt_le_cap (sizeToClassUnits ((newSz + 3) / 16))).2
  unfold FineScale at hCap
  omega

/-! ## 4. `NonFreeBound` and `PhaseGroupSpec` Combinators -/

/-- Count of non-`.free` allocator operations in `evs`. -/
def nonFreeCount : List AllocEvent → Nat
  | [] => 0
  | .free _ _ :: tl => nonFreeCount tl
  | _ :: tl => nonFreeCount tl + 1

theorem nonFreeCount_nil : nonFreeCount [] = 0 := rfl

theorem nonFreeCount_append (xs ys : List AllocEvent) :
    nonFreeCount (xs ++ ys) = nonFreeCount xs + nonFreeCount ys := by
  induction xs with
  | nil => simp [nonFreeCount]
  | cons ev tl ih =>
    cases ev <;> simp [nonFreeCount, ih] <;> omega

theorem nonFreeCount_rustAllocEvents (size align : Nat) :
    nonFreeCount (rustAllocEvents size align) = 1 := by
  unfold rustAllocEvents
  split <;> rfl

theorem nonFreeCount_rustDeallocEvents (size align : Nat) :
    nonFreeCount (rustDeallocEvents size align) = 0 := rfl

theorem nonFreeCount_rustReallocEvents (oldSz newSz align : Nat) :
    nonFreeCount (rustReallocEvents oldSz newSz align) = 1 := by
  unfold rustReallocEvents
  split <;> rfl

/-- Envelope-level bound on the number of non-`.free` allocator events. -/
def NonFreeBound (Env : List AllocEvent → Prop) (maxOps : Nat) : Prop :=
  ∀ evs, Env evs → nonFreeCount evs ≤ maxOps

theorem NonFreeBound.nil : NonFreeBound (· = []) 0 := by
  rintro _ rfl; rfl

theorem NonFreeBound.mono {Env : List AllocEvent → Prop} {k₁ k₂ : Nat}
    (h : NonFreeBound Env k₁) (hk : k₁ ≤ k₂) :
    NonFreeBound Env k₂ :=
  fun evs hE => Nat.le_trans (h evs hE) hk

theorem NonFreeBound.of_imp {E₁ E₂ : List AllocEvent → Prop} {k : Nat}
    (h : NonFreeBound E₂ k) (himp : ∀ evs, E₁ evs → E₂ evs) :
    NonFreeBound E₁ k :=
  fun evs hE => h evs (himp evs hE)

theorem NonFreeBound.or {E₁ E₂ : List AllocEvent → Prop} {k₁ k₂ : Nat}
    (h₁ : NonFreeBound E₁ k₁) (h₂ : NonFreeBound E₂ k₂) :
    NonFreeBound (fun evs => E₁ evs ∨ E₂ evs) (max k₁ k₂) := by
  rintro evs (hE1 | hE2)
  · exact Nat.le_trans (h₁ evs hE1) (Nat.le_max_left k₁ k₂)
  · exact Nat.le_trans (h₂ evs hE2) (Nat.le_max_right k₁ k₂)

theorem NonFreeBound.concat {E₁ E₂ : List AllocEvent → Prop} {k₁ k₂ : Nat}
    (h₁ : NonFreeBound E₁ k₁) (h₂ : NonFreeBound E₂ k₂) :
    NonFreeBound (ConcatEnv E₁ E₂) (k₁ + k₂) := by
  rintro _ ⟨evs₁, evs₂, rfl, hE1, hE2⟩
  rw [nonFreeCount_append]
  exact Nat.add_le_add (h₁ evs₁ hE1) (h₂ evs₂ hE2)

theorem NonFreeBound.seq {E₁ E₂ : List AllocEvent → Prop} {k₁ k₂ : Nat}
    (h₁ : NonFreeBound E₁ k₁) (h₂ : NonFreeBound E₂ k₂) :
    NonFreeBound (SeqEnv E₁ E₂) (k₁ + k₂) := by
  rintro evs (hE1 | hCat)
  · exact Nat.le_trans (h₁ evs hE1) (Nat.le_add_right k₁ k₂)
  · exact (h₁.concat h₂) evs hCat

theorem NonFreeBound.iterSeq {α : Type} {Step : α → List AllocEvent → Prop}
    (k : α → Nat) (xs : List α)
    (hstep : ∀ x ∈ xs, NonFreeBound (Step x) (k x)) :
    NonFreeBound (IterSeqEnv Step xs) ((xs.map k).sum) := by
  induction xs with
  | nil => exact NonFreeBound.nil
  | cons x tl ih =>
    have hx := hstep x List.mem_cons_self
    have htl := ih (fun y hy => hstep y (List.mem_cons_of_mem _ hy))
    simpa [IterSeqEnv] using hx.seq htl

theorem NonFreeBound.freeOnly : NonFreeBound FreeOnlyEvs 0 := by
  intro evs hf
  induction evs with
  | nil => rfl
  | cons ev tl ih =>
    obtain ⟨al, sz, rfl⟩ := hf ev List.mem_cons_self
    exact ih (fun e he => hf e (List.mem_cons_of_mem _ he))

theorem NonFreeBound.freeOnlyAlign16 : NonFreeBound FreeOnlyAlign16Evs 0 := by
  intro evs hf
  refine NonFreeBound.freeOnly evs (fun ev hmem => ?_)
  obtain ⟨al, _, sz, rfl⟩ := hf ev hmem
  exact ⟨al, sz, rfl⟩

theorem NonFreeBound.rustAlloc (size align : Nat) :
    NonFreeBound (· = rustAllocEvents size align) 1 := by
  rintro _ rfl
  rw [nonFreeCount_rustAllocEvents]

theorem NonFreeBound.rustDealloc (size align : Nat) :
    NonFreeBound (· = rustDeallocEvents size align) 0 := by
  rintro _ rfl
  rfl

theorem NonFreeBound.rustRealloc (oldSz newSz align : Nat) :
    NonFreeBound (· = rustReallocEvents oldSz newSz align) 1 := by
  rintro _ rfl
  rw [nonFreeCount_rustReallocEvents]

/-- State-threaded `FineScale`-scaled group specification for an allocator event envelope `Env`,
parallel to `SeqCreditKit.PhaseCreditSpec`. -/
structure PhaseGroupSpec (M : AllocCostModel) [HasFineGroupCredit M]
    (Env : List AllocEvent → Prop) (ΔgrpS : Nat) : Prop where
  groups_le : ∀ (st0 : M.σ) {evs : List AllocEvent}, Env evs →
    HasFineGroupCredit.groupsScaled (M.stepEvents evs st0) ≤
      HasFineGroupCredit.groupsScaled st0 + ΔgrpS

theorem PhaseGroupSpec.nil (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M (· = []) 0 where
  groups_le st0 {_} h := by subst h; simp

theorem PhaseGroupSpec.mono {M : AllocCostModel} [HasFineGroupCredit M]
    {Env : List AllocEvent → Prop} {g₁ g₂ : Nat}
    (h : PhaseGroupSpec M Env g₁) (hg : g₁ ≤ g₂) :
    PhaseGroupSpec M Env g₂ where
  groups_le st0 {_} hE := Nat.le_trans (h.groups_le st0 hE) (Nat.add_le_add_left hg _)

theorem PhaseGroupSpec.of_imp {M : AllocCostModel} [HasFineGroupCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {g : Nat}
    (h : PhaseGroupSpec M E₂ g) (himp : ∀ evs, E₁ evs → E₂ evs) :
    PhaseGroupSpec M E₁ g where
  groups_le st0 {_} hE := h.groups_le st0 (himp _ hE)

theorem PhaseGroupSpec.or {M : AllocCostModel} [HasFineGroupCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {g₁ g₂ : Nat}
    (h₁ : PhaseGroupSpec M E₁ g₁) (h₂ : PhaseGroupSpec M E₂ g₂) :
    PhaseGroupSpec M (fun evs => E₁ evs ∨ E₂ evs) (max g₁ g₂) where
  groups_le st0 {_} hE := by
    rcases hE with h1 | h2
    · exact Nat.le_trans (h₁.groups_le st0 h1) (Nat.add_le_add_left (Nat.le_max_left g₁ g₂) _)
    · exact Nat.le_trans (h₂.groups_le st0 h2) (Nat.add_le_add_left (Nat.le_max_right g₁ g₂) _)

theorem PhaseGroupSpec.concat {M : AllocCostModel} [HasFineGroupCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {g₁ g₂ : Nat}
    (h₁ : PhaseGroupSpec M E₁ g₁) (h₂ : PhaseGroupSpec M E₂ g₂) :
    PhaseGroupSpec M (ConcatEnv E₁ E₂) (g₁ + g₂) where
  groups_le st0 {_} := by
    rintro ⟨evs₁, evs₂, rfl, hE1, hE2⟩
    rw [AllocCostModel.stepEvents_append]
    have b1 := h₁.groups_le st0 hE1
    have b2 := h₂.groups_le (M.stepEvents evs₁ st0) hE2
    omega

theorem PhaseGroupSpec.seq {M : AllocCostModel} [HasFineGroupCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {g₁ g₂ : Nat}
    (h₁ : PhaseGroupSpec M E₁ g₁) (h₂ : PhaseGroupSpec M E₂ g₂) :
    PhaseGroupSpec M (SeqEnv E₁ E₂) (g₁ + g₂) where
  groups_le st0 {_} hE := by
    rcases hE with hE1 | hCat
    · exact Nat.le_trans (h₁.groups_le st0 hE1) (Nat.add_le_add_left (Nat.le_add_right g₁ g₂) _)
    · exact (h₁.concat h₂).groups_le st0 hCat

theorem PhaseGroupSpec.iterSeq {α : Type} {M : AllocCostModel} [HasFineGroupCredit M]
    {Step : α → List AllocEvent → Prop} (g : α → Nat) (xs : List α)
    (hstep : ∀ x ∈ xs, PhaseGroupSpec M (Step x) (g x)) :
    PhaseGroupSpec M (IterSeqEnv Step xs) ((xs.map g).sum) := by
  induction xs with
  | nil => exact PhaseGroupSpec.nil M
  | cons x tl ih =>
    have hx := hstep x List.mem_cons_self
    have htl := ih (fun y hy => hstep y (List.mem_cons_of_mem _ hy))
    simpa [IterSeqEnv] using hx.seq htl

theorem PhaseGroupSpec.iterSeq_const {α : Type} {M : AllocCostModel} [HasFineGroupCredit M]
    {Step : α → List AllocEvent → Prop} (g : Nat) (xs : List α)
    (hstep : ∀ x ∈ xs, PhaseGroupSpec M (Step x) g) :
    PhaseGroupSpec M (IterSeqEnv Step xs) (xs.length * g) := by
  have h := PhaseGroupSpec.iterSeq (fun _ => g) xs hstep
  simpa [List.sum_replicate] using h

theorem PhaseGroupSpec.iterConcat {α : Type} {M : AllocCostModel} [HasFineGroupCredit M]
    {Step : α → List AllocEvent → Prop} (g : α → Nat) (xs : List α)
    (hstep : ∀ x ∈ xs, PhaseGroupSpec M (Step x) (g x)) :
    PhaseGroupSpec M (IterConcatEnv Step xs) ((xs.map g).sum) := by
  induction xs with
  | nil => exact PhaseGroupSpec.nil M
  | cons x tl ih =>
    have hx := hstep x List.mem_cons_self
    have htl := ih (fun y hy => hstep y (List.mem_cons_of_mem _ hy))
    simpa [IterConcatEnv] using hx.concat htl

theorem PhaseGroupSpec.iterConcat_const {α : Type} {M : AllocCostModel} [HasFineGroupCredit M]
    {Step : α → List AllocEvent → Prop} (g : Nat) (xs : List α)
    (hstep : ∀ x ∈ xs, PhaseGroupSpec M (Step x) g) :
    PhaseGroupSpec M (IterConcatEnv Step xs) (xs.length * g) := by
  have h := PhaseGroupSpec.iterConcat (fun _ => g) xs hstep
  simpa [List.sum_replicate] using h

theorem stepEvents_groupsScaled_le_nonFreeCount (M : AllocCostModel) [HasFineGroupCredit M] :
    ∀ (evs : List AllocEvent) (st0 : M.σ),
      HasFineGroupCredit.groupsScaled (M.stepEvents evs st0) ≤
        HasFineGroupCredit.groupsScaled st0 + 3 * FineScale * nonFreeCount evs
  | [], st0 => by simp [nonFreeCount]
  | ev :: tl, st0 => by
    rw [AllocCostModel.stepEvents_cons]
    cases ev with
    | free al sz =>
      have hf := HasFineGroupCredit.step_free_le (M := M) al sz st0
      have htl := stepEvents_groupsScaled_le_nonFreeCount M tl (M.step (.free al sz) st0)
      simp only [nonFreeCount]
      omega
    | alloc req =>
      have ha := HasFineGroupCredit.step_any_le (M := M) (.alloc req) st0
      have htl := stepEvents_groupsScaled_le_nonFreeCount M tl (M.step (.alloc req) st0)
      simp only [nonFreeCount, Nat.mul_add, Nat.mul_one]
      omega
    | aligned al req =>
      have ha := HasFineGroupCredit.step_any_le (M := M) (.aligned al req) st0
      have htl := stepEvents_groupsScaled_le_nonFreeCount M tl (M.step (.aligned al req) st0)
      simp only [nonFreeCount, Nat.mul_add, Nat.mul_one]
      omega
    | realloc al old newSz =>
      have ha := HasFineGroupCredit.step_any_le (M := M) (.realloc al old newSz) st0
      have htl := stepEvents_groupsScaled_le_nonFreeCount M tl (M.step (.realloc al old newSz) st0)
      simp only [nonFreeCount, Nat.mul_add, Nat.mul_one]
      omega

theorem PhaseGroupSpec.of_nonFreeBound (M : AllocCostModel) [HasFineGroupCredit M]
    {Env : List AllocEvent → Prop} {maxOps : Nat}
    (h : NonFreeBound Env maxOps) :
    PhaseGroupSpec M Env (3 * FineScale * maxOps) where
  groups_le st0 {evs} hE := by
    have h1 := stepEvents_groupsScaled_le_nonFreeCount M evs st0
    have h2 := Nat.mul_le_mul_left (3 * FineScale) (h evs hE)
    omega

theorem PhaseGroupSpec.freeOnly (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M FreeOnlyEvs 0 := by
  simpa using PhaseGroupSpec.of_nonFreeBound M NonFreeBound.freeOnly

theorem PhaseGroupSpec.freeOnlyAlign16 (M : AllocCostModel) [HasFineGroupCredit M] :
    PhaseGroupSpec M FreeOnlyAlign16Evs 0 := by
  simpa using PhaseGroupSpec.of_nonFreeBound M NonFreeBound.freeOnlyAlign16

theorem PhaseGroupSpec.rustAlloc_any (M : AllocCostModel) [HasFineGroupCredit M]
    (size align : Nat) :
    PhaseGroupSpec M (· = rustAllocEvents size align) (3 * FineScale) := by
  simpa using PhaseGroupSpec.of_nonFreeBound M (NonFreeBound.rustAlloc size align)

theorem PhaseGroupSpec.rustAlloc_small (M : AllocCostModel) [HasFineGroupCredit M]
    {size align : Nat} (hal : align ≤ 16) (hle : size ≤ MmapThresholdReq) :
    PhaseGroupSpec M (· = rustAllocEvents size align)
      (HasFineGroupCredit.smallAllocGroupS M size) where
  groups_le st0 {_} hE := by
    subst hE
    unfold rustAllocEvents
    split
    · exact HasFineGroupCredit.step_alloc_small_le st0 hle
    · exact HasFineGroupCredit.step_aligned_small_le st0 (by omega) hle

theorem PhaseGroupSpec.rustAlloc_large (M : AllocCostModel) [HasFineGroupCredit M]
    {size align : Nat} (hal : align ≤ 16) (hgt : MmapThresholdReq < size) :
    PhaseGroupSpec M (· = rustAllocEvents size align) FineScale where
  groups_le st0 {_} hE := by
    subst hE
    unfold rustAllocEvents
    split
    · exact HasFineGroupCredit.step_large_le (ev := .alloc size) st0
        (by simp [eventStepAlign]) (by simpa [eventStepReq] using hgt)
    · exact HasFineGroupCredit.step_large_le (ev := .aligned (max align 8) size) st0
        (by simp [eventStepAlign]; omega) (by simpa [eventStepReq] using hgt)

theorem PhaseGroupSpec.rustDealloc (M : AllocCostModel) [HasFineGroupCredit M]
    (size align : Nat) :
    PhaseGroupSpec M (· = rustDeallocEvents size align) 0 := by
  simpa using PhaseGroupSpec.of_nonFreeBound M (NonFreeBound.rustDealloc size align)

theorem PhaseGroupSpec.rustRealloc_any (M : AllocCostModel) [HasFineGroupCredit M]
    (oldSz newSz align : Nat) :
    PhaseGroupSpec M (· = rustReallocEvents oldSz newSz align) (3 * FineScale) := by
  simpa using PhaseGroupSpec.of_nonFreeBound M (NonFreeBound.rustRealloc oldSz newSz align)

theorem PhaseGroupSpec.rustRealloc_small (M : AllocCostModel) [HasFineGroupCredit M]
    {oldSz newSz align : Nat} (hal : align ≤ 16) (hle : newSz ≤ MmapThresholdReq) :
    PhaseGroupSpec M (· = rustReallocEvents oldSz newSz align)
      (HasFineGroupCredit.smallReallocGroupS M newSz) where
  groups_le st0 {_} hE := by
    subst hE
    unfold rustReallocEvents
    split
    · exact HasFineGroupCredit.step_realloc_small_le st0 hal hle
    · have h1 := HasFineGroupCredit.step_aligned_small_le (M := M) (al := max align 8)
        st0 (by omega) hle
      have h2 := HasFineGroupCredit.step_free_le (M := M) align oldSz
        (M.step (.aligned (max align 8) newSz) st0)
      have h3 := HasFineGroupCredit.smallAllocGroupS_le_smallReallocGroupS (M := M) newSz
      change HasFineGroupCredit.groupsScaled
        (M.step (.free align oldSz) (M.step (.aligned (max align 8) newSz) st0)) ≤ _
      omega

theorem PhaseGroupSpec.rustRealloc_large (M : AllocCostModel) [HasFineGroupCredit M]
    {oldSz newSz align : Nat} (hal : align ≤ 16) (hgt : MmapThresholdReq < newSz) :
    PhaseGroupSpec M (· = rustReallocEvents oldSz newSz align) FineScale where
  groups_le st0 {_} hE := by
    subst hE
    unfold rustReallocEvents
    split
    · exact HasFineGroupCredit.step_large_le (ev := .realloc align oldSz newSz) st0
        (by simpa [eventStepAlign] using hal) (by simpa [eventStepReq] using hgt)
    · have h1 := HasFineGroupCredit.step_large_le (M := M) (ev := .aligned (max align 8) newSz)
        st0 (by simp [eventStepAlign]; omega) (by simpa [eventStepReq] using hgt)
      have h2 := HasFineGroupCredit.step_free_le (M := M) align oldSz
        (M.step (.aligned (max align 8) newSz) st0)
      change HasFineGroupCredit.groupsScaled
        (M.step (.free align oldSz) (M.step (.aligned (max align 8) newSz) st0)) ≤ _
      omega

theorem PhaseGroupSpec.evalLog_le {M : AllocCostModel} [HasFineGroupCredit M]
    {Env : List AllocEvent → Prop} {ΔgrpS : Nat}
    (h : PhaseGroupSpec M Env ΔgrpS) {fullLog : List AllocEvent} (hEnv : Env fullLog) :
    HasFineGroupCredit.groupsScaled (M.evalLog fullLog) ≤ ΔgrpS := by
  have hb := h.groups_le M.init hEnv
  rw [HasFineGroupCredit.groupsScaled_init, Nat.zero_add] at hb
  exact hb

/-! ## 5. Decoupled `FitsStep`, `FitsTrace`, and `FitsEnv` Bridges on `fineCostModel` -/

/-- Decoupled `FitsStep` discharge on an arbitrary `fineCostModel` state `b` from `(stepB, cumB, peakB, grpB)`. -/
theorem fitsStep_fineCostModel_of_group_bounds
    {lim : BudgetLimits} {b : fineCostModel.σ} {stepB cumB peakB grpB : Nat}
    (henf : lim.enforced = true)
    (hgrp : (fineGroupsScaled b + FineScale - 1) / FineScale ≤ grpB)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge (M := fineCostModel) b ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge (M := fineCostModel) b ≤ peakB)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) + 2 * stepB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) + stepB +
      (lim.staticCount + fineDynIvsOfGroups grpB + 16) * (stepB + PAGE_SIZE) + stepB ≤ 2 ^ 48) :
    FitsStep lim stepB (fineCostModel.maxDynIvs b) (fineCostModel.footprint b) :=
  fitsStep_of_fine_bounds fineCostModel henf
    (fineMaxDynIvs_le_of_groupsScaled hgrp) hcum hlive hpeak
    (by rw [fineCostModel_baseFine_eq]; exact hram)
    (by rw [fineCostModel_baseFine_eq]; exact hva)

/-- Lifts `(PhaseCreditSpec, PhaseGroupSpec)` directly to `FitsStep` on `fineCostModel.evalLog fullLog`
at `stepB = fineStepReserveOfGroups maxReq 16 grpB`. -/
theorem fitsStep_fineCostModel_of_phaseCredit_groups
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {cumB liveB peakB maxReq grpS grpB : Nat}
    (hSpec : PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq)
    (hGrp : PhaseGroupSpec fineCostModel Env grpS)
    (hlp : liveB ≤ peakB)
    (hgrp : (grpS + FineScale - 1) / FineScale ≤ grpB)
    (henf : lim.enforced = true)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfGroups maxReq 16 grpB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfGroups maxReq 16 grpB +
      (lim.staticCount + fineDynIvsOfGroups grpB + 16) *
        (fineStepReserveOfGroups maxReq 16 grpB + PAGE_SIZE) +
      fineStepReserveOfGroups maxReq 16 grpB ≤ 2 ^ 48)
    {fullLog : List AllocEvent} (hEnv : Env fullLog) :
    FitsStep lim (fineStepReserveOfGroups maxReq 16 grpB)
      (fineCostModel.maxDynIvs (fineCostModel.evalLog fullLog))
      (fineCostModel.footprint (fineCostModel.evalLog fullLog)) := by
  obtain ⟨hcum, hlive, hpeak⟩ := hSpec.evalLog_bounds hEnv
  have hg0 : fineGroupsScaled (fineCostModel.evalLog fullLog) ≤ grpS := hGrp.evalLog_le hEnv
  have hgCeil : (fineGroupsScaled (fineCostModel.evalLog fullLog) + FineScale - 1) / FineScale ≤ grpB :=
    Nat.le_trans (Nat.div_le_div_right (by omega)) hgrp
  exact fitsStep_fineCostModel_of_group_bounds henf hgCeil hcum (Nat.le_trans hlive hlp) hpeak hram hva

/-- Lifts `(PhaseCreditSpec, PhaseGroupSpec)` directly to
`FitsTrace fineCostModel lim (fineStepReserveOfGroups maxReq 16 grpB) fullLog`. -/
theorem fitsTrace_fineCostModel_of_phaseCredit_groups
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {cumB liveB peakB maxReq grpS grpB : Nat}
    (hSpec : PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq)
    (hGrp : PhaseGroupSpec fineCostModel Env grpS)
    (hlp : liveB ≤ peakB)
    (hgrp : (grpS + FineScale - 1) / FineScale ≤ grpB)
    (henf : lim.enforced = true)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfGroups maxReq 16 grpB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfGroups maxReq 16 grpB +
      (lim.staticCount + fineDynIvsOfGroups grpB + 16) *
        (fineStepReserveOfGroups maxReq 16 grpB + PAGE_SIZE) +
      fineStepReserveOfGroups maxReq 16 grpB ≤ 2 ^ 48)
    {fullLog : List AllocEvent} (hEnv : Env fullLog) :
    FitsTrace fineCostModel lim (fineStepReserveOfGroups maxReq 16 grpB) fullLog := by
  have hg0 : fineGroupsScaled (fineCostModel.evalLog fullLog) ≤ grpS := hGrp.evalLog_le hEnv
  have hgCeil : (fineGroupsScaled (fineCostModel.evalLog fullLog) + FineScale - 1) / FineScale ≤ grpB :=
    Nat.le_trans (Nat.div_le_div_right (by omega)) hgrp
  refine ⟨fun ev hmem => ?_,
    fitsStep_fineCostModel_of_phaseCredit_groups hSpec hGrp hlp hgrp henf hram hva hEnv⟩
  obtain ⟨hreq, hal⟩ := hSpec.req_align fullLog hEnv ev hmem
  have hal16 : max (eventStepAlign ev) 16 ≤ max 16 16 := by omega
  exact ⟨withinMaxAlloc_of_fineStepBound_le_2pow48 (m := fineMaxMetaAreasOfGroups grpB)
      hreq hal16 (by unfold fineStepReserveOfGroups at hva; omega),
    fineStepReserve_le_of_groupsScaled hreq hal16 hgCeil⟩

/-- Lifts `(PhaseCreditSpec, PhaseGroupSpec)` directly to initial-state
`FitsEnv fineCostModel lim fineCostModel.init Env` via `FitsEnv.of_subtrace_fitsTrace`. -/
theorem fitsEnv_fineCostModel_of_phaseCredit_groups
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {cumB liveB peakB maxReq grpS grpB : Nat}
    (hSpec : PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq)
    (hGrp : PhaseGroupSpec fineCostModel Env grpS)
    (hlp : liveB ≤ peakB)
    (hgrp : (grpS + FineScale - 1) / FineScale ≤ grpB)
    (henf : lim.enforced = true)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfGroups maxReq 16 grpB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfGroups maxReq 16 grpB +
      (lim.staticCount + fineDynIvsOfGroups grpB + 16) *
        (fineStepReserveOfGroups maxReq 16 grpB + PAGE_SIZE) +
      fineStepReserveOfGroups maxReq 16 grpB ≤ 2 ^ 48) :
    FitsEnv fineCostModel lim fineCostModel.init Env := by
  intro evs hEnv
  have hFit := fitsTrace_fineCostModel_of_phaseCredit_groups hSpec hGrp hlp hgrp henf hram hva hEnv
  have hSub : ∀ e, (· = evs) e → ∃ suf, evs = ([] : List AllocEvent) ++ e ++ suf := by
    rintro _ rfl
    exact ⟨[], by simp⟩
  exact FitsEnv.of_subtrace_fitsTrace hSub hFit evs rfl

end LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
