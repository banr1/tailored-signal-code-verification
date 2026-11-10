/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Heap.Fine.Inv
public import LibsignalBinary.Heap.Fine.Init
public import LibsignalBinary.Heap.Fine.Footprint
public import LibsignalBinary.Heap.Fine.FineSpecs

/-!
# `fineCostModel`, `fineCostModelIface`, and `HasFineReallocCredit`

Instantiates `fineCostModel : AllocCostModel`, `fineCostModelIface : MallocngCostModelIface fineCostModel`,
and `HasFineReallocCredit fineCostModel` (`smallMaxReq = 135,167`, `largeMetaCost = 122`,
`largeCost req = req + 8,195`), and bridges `fine*Spec` to `mallocngModel*Spec`.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib
open VerifiedLibraries VerifiedLibraries.Mallocng.Proofs
open VerifiedLibraries.Mallocng hiding AllocCostModel AllocEvent MallocngCostModelIface
  MallocngCostModelSound MallocngModelEnv MallocngModelPlacedEntryContracts
  MallocngModelPostEnv MallocngStepOomCond
open LibsignalBinary.Heap
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit

/-! ## `AllocCostModel` and `MallocngCostModelIface` -/

/-- Bijection from `AllocEvent` to `FineEvent`. -/
def toFineEvent : AllocEvent → FineEvent
  | .alloc req => .alloc req
  | .aligned align req => .aligned align req
  | .free align req => .free align req
  | .realloc align old new => .realloc align old new

@[scoped simp] theorem toFineEvent_reqBytes (ev : AllocEvent) :
    (toFineEvent ev).reqBytes = ev.reqBytes := by
  cases ev <;> rfl

/-- Per-size-class `mallocng` `AllocCostModel` over `FineBudget`. -/
def fineCostModel : AllocCostModel where
  σ := FineBudget
  init := FineBudget.init
  step ev b := FineBudget.step (toFineEvent ev) b
  footprint := fineFootprint
  maxDynIvs := fineMaxDynIvs
  stepReserve ev b := fineStepReserve (toFineEvent ev) b
  liveBytes := fineLiveBytes
  footprint_mono ev b := fineFootprint_mono (toFineEvent ev) b
  maxDynIvs_mono ev b := fineMaxDynIvs_mono (toFineEvent ev) b
  stepReserve_mono ev₀ ev b := fineStepReserve_mono (toFineEvent ev₀) (toFineEvent ev) b
  req_le_stepReserve ev b := by
    rw [← toFineEvent_reqBytes]
    exact req_le_fineStepReserve (toFineEvent ev) b
  liveBytes_free_le al n b := fineLiveBytes_free_le al n b

/-- Separation-logic representation (`FineHeapImpl`, `FineCoreImpl`, `FineBlock`) for `fineCostModel`. -/
def fineCostModelIface : MallocngCostModelIface fineCostModel where
  HeapM := FineHeapImpl
  CoreM := FineCoreImpl
  BlockM := FineBlock
  block_noWrap := fineBlock_noWrap

/-! ## `HasFineReallocCredit` Instance -/

/-- Largest request byte size (`135,167 = Guaranteed63Threshold - 1`) treated as small/straddle. -/
def fineSmallMaxReq : Nat := 135167

/-- Per-request `cumSmall` charge for `.alloc req` and `al ≤ 16` `.aligned al req` (`req ≤ 135,167`). -/
def fineSmallAllocCost (req : Nat) : Nat :=
  if req ≤ MmapThresholdReq then
    let sc0 := sizeToClassUnits ((req + 3) / 16)
    coarseSlotWt sc0 + (122 * coarseGrpWtS sc0 + FineScale - 1) / FineScale
  else
    declCost63 req 16 + 122

/-- Per-request `cumSmall` charge for `al ≤ 16` `.realloc` into `newSz ≤ 135,167`. -/
def fineSmallReallocCost (newSz : Nat) : Nat :=
  let c63 := declCost63 newSz 16
  let wSmall :=
    if newSz ≤ MmapThresholdReq then coarseSlotWt (sizeToClassUnits ((newSz + 3) / 16)) else 0
  let gSmall :=
    if newSz ≤ MmapThresholdReq then coarseGrpWtS (sizeToClassUnits ((newSz + 3) / 16)) else 0
  max wSmall c63 + (122 * max gSmall FineScale + FineScale - 1) / FineScale

/-- Direct-`mmap` byte weight (`req + 8,195 = declCost63 req 16`) for `req > 135,167`, `al ≤ 16`. -/
def fineLargeCost (req : Nat) : Nat :=
  declCost63 req 16

/-- Out-of-line `meta_area` amortized byte charge (`⌈12,288 / 101⌉ = 122` B) per large allocation. -/
def fineLargeMetaCost : Nat := 122

/-- Constant base overhead in `fineFootprint` (`BaseRootFine` + initial `meta_area`/guard pages). -/
def fineBaseCredit : Nat :=
  BaseRootFine + 20480 + 12288 * ((7 + gBaseConst + 100) / 101) + 122

/-- Cumulative small-class and `meta_area` byte component of `b : FineBudget`. -/
def fineCumSmall (b : FineBudget) : Nat :=
  b.cumSmallBytes + (122 * b.cumSmallGroupsS) / FineScale + 122 * finePeak63Count b

/-- Currently live `sc = 63` large-allocation byte component of `b : FineBudget`. -/
def fineLiveLarge (b : FineBudget) : Nat :=
  b.live63Bytes

/-- Historical peak `sc = 63` large-allocation byte component of `b : FineBudget`. -/
def finePeakLarge (b : FineBudget) : Nat :=
  finePeak63Bytes b

private theorem add_div_101_le (A K : Nat) :
    (A + K) / 101 ≤ (A + 100) / 101 + K / 101 := by
  omega

private theorem mul_div_101_le_122 (K : Nat) :
    12288 * (K / 101) ≤ 122 * K := by
  have h := Nat.mul_div_le K 101
  omega

private theorem ceil_div_scale_mul_122 (G : Nat) :
    122 * ((G + FineScale - 1) / FineScale) ≤ 122 + (122 * G) / FineScale := by
  unfold FineScale
  omega

private theorem mul_122_add_div_scale_le (G d : Nat) :
    (122 * (G + d)) / FineScale ≤ (122 * G) / FineScale + (122 * d + FineScale - 1) / FineScale := by
  unfold FineScale
  omega

theorem fineFootprint_le_credit (b : FineBudget) :
    fineFootprint b ≤
      fineBaseCredit + fineCumSmall b + max (fineLiveLarge b) (finePeakLarge b) := by
  unfold fineFootprint fineMaxMetaAreas fineMaxGroups
    fineBaseCredit fineCumSmall fineLiveLarge finePeakLarge finePeak63Bytes
  let A := 7 + gBaseConst
  let gs := (b.cumSmallGroupsS + FineScale - 1) / FineScale
  let K := gs + finePeak63Count b
  have hAK : (7 + (gBaseConst + gs + finePeak63Count b)) = A + K := by omega
  have h1 := add_div_101_le A K
  have h2 := mul_div_101_le_122 K
  have h3 := ceil_div_scale_mul_122 b.cumSmallGroupsS
  have h4 : 12288 * ((A + K) / 101) ≤ 12288 * ((A + 100) / 101) + 122 * K := by
    have := Nat.mul_le_mul_left 12288 h1
    omega
  rw [hAK]
  omega

theorem stepAligned_small_credit {al req : Nat} (b : FineBudget)
    (hal : al ≤ 16) (hle : req ≤ fineSmallMaxReq) :
    fineCumSmall (FineBudget.stepAligned al req b) ≤ fineCumSmall b + fineSmallAllocCost req ∧
    fineLiveLarge (FineBudget.stepAligned al req b) ≤ fineLiveLarge b ∧
    finePeakLarge (FineBudget.stepAligned al req b) ≤ finePeakLarge b := by
  have hNot63 : ¬ (Guaranteed63Threshold ≤ req) := by
    unfold Guaranteed63Threshold fineSmallMaxReq at *; omega
  have hMaxAl : max al 16 = 16 := by omega
  unfold FineBudget.stepAligned fineSmallAllocCost
  dsimp only
  simp only [hNot63, hMaxAl, Nat.sub_self, Nat.add_zero, ↓reduceIte]
  by_cases hSm : req ≤ MmapThresholdReq
  · simp only [hSm, ↓reduceIte]
    have hDiv := mul_122_add_div_scale_le b.cumSmallGroupsS
      (coarseGrpWtS (sizeToClassUnits ((req + 3) / 16)))
    unfold fineCumSmall fineLiveLarge finePeakLarge finePeak63Bytes finePeak63Count
    dsimp only
    omega
  · simp only [hSm, ↓reduceIte]
    have hDiv := mul_122_add_div_scale_le b.cumSmallGroupsS FineScale
    have hScale : (122 * FineScale + FineScale - 1) / FineScale = 122 := by decide
    rw [hScale] at hDiv
    unfold fineCumSmall fineLiveLarge finePeakLarge finePeak63Bytes finePeak63Count
    dsimp only
    omega

theorem stepAligned_large_credit {al req : Nat} (b : FineBudget)
    (hal : al ≤ 16) (hgt : fineSmallMaxReq < req) :
    fineCumSmall (FineBudget.stepAligned al req b) ≤ fineCumSmall b + fineLargeMetaCost ∧
    fineLiveLarge (FineBudget.stepAligned al req b) ≤ fineLiveLarge b + fineLargeCost req ∧
    finePeakLarge (FineBudget.stepAligned al req b) ≤
      max (finePeakLarge b) (fineLiveLarge b + fineLargeCost req) := by
  have h63 : Guaranteed63Threshold ≤ req := by
    unfold Guaranteed63Threshold fineSmallMaxReq at *; omega
  have hMaxAl : max al 16 = 16 := by omega
  unfold FineBudget.stepAligned fineLargeMetaCost fineLargeCost
  dsimp only
  simp only [h63, hMaxAl, ↓reduceIte]
  unfold fineCumSmall fineLiveLarge finePeakLarge finePeak63Bytes finePeak63Count
  dsimp only
  omega

theorem stepReallocAdd_small_credit {al newSz : Nat} (b : FineBudget)
    (hal : al ≤ 16) (hle : newSz ≤ fineSmallMaxReq) :
    fineCumSmall (FineBudget.stepReallocAdd al newSz b) ≤
      fineCumSmall b + fineSmallReallocCost newSz ∧
    fineLiveLarge (FineBudget.stepReallocAdd al newSz b) = fineLiveLarge b ∧
    finePeakLarge (FineBudget.stepReallocAdd al newSz b) = finePeakLarge b := by
  have hNot63 : ¬ (Guaranteed63Threshold ≤ newSz) := by
    unfold Guaranteed63Threshold fineSmallMaxReq at *; omega
  have hMaxAl : max al 16 = 16 := by omega
  unfold FineBudget.stepReallocAdd fineSmallReallocCost
  dsimp only
  simp only [hNot63, hMaxAl, ↓reduceIte]
  have hDiv := mul_122_add_div_scale_le b.cumSmallGroupsS
    (max (if newSz ≤ MmapThresholdReq then coarseGrpWtS (sizeToClassUnits ((newSz + 3) / 16)) else 0)
      FineScale)
  unfold fineCumSmall fineLiveLarge finePeakLarge finePeak63Bytes finePeak63Count
  dsimp only
  omega

theorem stepFree_small_credit {al req : Nat} (b : FineBudget)
    (hle : req ≤ fineSmallMaxReq) :
    fineCumSmall (FineBudget.stepFree al req b) = fineCumSmall b ∧
    fineLiveLarge (FineBudget.stepFree al req b) = fineLiveLarge b ∧
    finePeakLarge (FineBudget.stepFree al req b) = finePeakLarge b := by
  have hNot63 : ¬ (Guaranteed63Threshold ≤ req) := by
    unfold Guaranteed63Threshold fineSmallMaxReq at *; omega
  unfold FineBudget.stepFree
  dsimp only
  simp only [hNot63, ↓reduceIte]
  unfold fineCumSmall fineLiveLarge finePeakLarge finePeak63Bytes finePeak63Count
  dsimp only
  omega

private theorem max_max_sub (x y k : Nat) : max (max x y) (y - k) = max x y :=
  Nat.max_eq_left (Nat.le_trans (Nat.sub_le y k) (Nat.le_max_right x y))

private theorem threshold_eq_add_one : fineSmallMaxReq + 1 = Guaranteed63Threshold := rfl

private theorem threshold_le_of_gt {req : Nat} (hgt : fineSmallMaxReq < req) :
    Guaranteed63Threshold ≤ req := by
  rw [← threshold_eq_add_one]
  exact hgt

private theorem stepFree_eq_large {al req : Nat} (b : FineBudget)
    (hal : al ≤ 16) (h63 : Guaranteed63Threshold ≤ req) :
    FineBudget.stepFree al req b =
      { b with
        live63Bytes   := b.live63Bytes - fineLargeCost req
        peak63Bytes   := finePeak63Bytes b
        live63Count   := b.live63Count - 1
        peak63Count   := finePeak63Count b
        liveUserBytes := b.liveUserBytes - req } := by
  have hMaxAl : max al 16 = 16 := Nat.max_eq_right hal
  unfold FineBudget.stepFree fineLargeCost
  dsimp only
  split
  · rw [hMaxAl]
  · contradiction

private theorem stepFree_large_cumSmall {al req : Nat} (b : FineBudget)
    (hal : al ≤ 16) (hgt : fineSmallMaxReq < req) :
    fineCumSmall (FineBudget.stepFree al req b) = fineCumSmall b := by
  rw [stepFree_eq_large b hal (threshold_le_of_gt hgt)]
  exact congrArg (fun x => b.cumSmallBytes + (122 * b.cumSmallGroupsS) / FineScale + 122 * x)
    (max_max_sub b.peak63Count b.live63Count 1)

private theorem proj_live63Bytes_sub (b : FineBudget) (c pB lC pC lU : Nat) :
    fineLiveLarge
      { b with
        live63Bytes   := b.live63Bytes - c
        peak63Bytes   := pB
        live63Count   := lC
        peak63Count   := pC
        liveUserBytes := lU } = fineLiveLarge b - c := rfl

private theorem proj_peak63Bytes_sub (b : FineBudget) (c lC pC lU : Nat) :
    finePeakLarge
      { b with
        live63Bytes   := b.live63Bytes - c
        peak63Bytes   := finePeak63Bytes b
        live63Count   := lC
        peak63Count   := pC
        liveUserBytes := lU } = finePeakLarge b :=
  max_max_sub b.peak63Bytes b.live63Bytes c

private theorem stepFree_large_liveLarge {al req : Nat} (b : FineBudget)
    (hal : al ≤ 16) (hgt : fineSmallMaxReq < req) :
    fineLiveLarge (FineBudget.stepFree al req b) = fineLiveLarge b - fineLargeCost req := by
  rw [stepFree_eq_large b hal (threshold_le_of_gt hgt)]
  exact proj_live63Bytes_sub b (fineLargeCost req) _ _ _ _

private theorem stepFree_large_peakLarge {al req : Nat} (b : FineBudget)
    (hal : al ≤ 16) (hgt : fineSmallMaxReq < req) :
    finePeakLarge (FineBudget.stepFree al req b) = finePeakLarge b := by
  rw [stepFree_eq_large b hal (threshold_le_of_gt hgt)]
  exact proj_peak63Bytes_sub b (fineLargeCost req) _ _ _

theorem stepFree_large_credit {al req : Nat} (b : FineBudget)
    (hal : al ≤ 16) (hgt : fineSmallMaxReq < req) :
    fineCumSmall (FineBudget.stepFree al req b) = fineCumSmall b ∧
    fineLiveLarge (FineBudget.stepFree al req b) = fineLiveLarge b - fineLargeCost req ∧
    finePeakLarge (FineBudget.stepFree al req b) = finePeakLarge b :=
  ⟨stepFree_large_cumSmall b hal hgt,
   stepFree_large_liveLarge b hal hgt,
   stepFree_large_peakLarge b hal hgt⟩

theorem stepRealloc_small_small_credit {al old new : Nat} (b : FineBudget)
    (hal : al ≤ 16) (hold_le : old ≤ fineSmallMaxReq) (hnew_le : new ≤ fineSmallMaxReq) :
    let b' := FineBudget.stepRealloc al old new b
    fineCumSmall b' ≤ fineCumSmall b + fineSmallReallocCost new ∧
    fineLiveLarge b' ≤ fineLiveLarge b ∧
    finePeakLarge b' ≤ finePeakLarge b := by
  dsimp only [FineBudget.stepRealloc]
  have ⟨hC1, hL1, hP1⟩ := stepReallocAdd_small_credit b hal hnew_le
  have ⟨hC2, hL2, hP2⟩ := stepFree_small_credit (al := al) (FineBudget.stepReallocAdd al new b) hold_le
  omega

theorem stepRealloc_small_large_credit {al old new : Nat} (b : FineBudget)
    (hal : al ≤ 16) (hold_le : old ≤ fineSmallMaxReq) (hnew_gt : fineSmallMaxReq < new) :
    let b' := FineBudget.stepRealloc al old new b
    fineCumSmall b' ≤ fineCumSmall b + fineLargeMetaCost ∧
    fineLiveLarge b' ≤ fineLiveLarge b + fineLargeCost new ∧
    finePeakLarge b' ≤ max (finePeakLarge b) (fineLiveLarge b + fineLargeCost new) := by
  dsimp only [FineBudget.stepRealloc]
  have h63 : Guaranteed63Threshold ≤ new := by
    unfold Guaranteed63Threshold fineSmallMaxReq at *; omega
  have hEqAdd : FineBudget.stepReallocAdd al new b = FineBudget.stepAligned al new b := by
    unfold FineBudget.stepReallocAdd; simp only [h63, ↓reduceIte]
  rw [hEqAdd]
  have ⟨hC1, hL1, hP1⟩ := stepAligned_large_credit b hal hnew_gt
  have ⟨hC2, hL2, hP2⟩ := stepFree_small_credit (al := al) (FineBudget.stepAligned al new b) hold_le
  omega

theorem stepRealloc_large_large_credit {al old new : Nat} (b : FineBudget)
    (hal : al ≤ 16) (hold_gt : fineSmallMaxReq < old) (hnew_gt : fineSmallMaxReq < new) :
    let b' := FineBudget.stepRealloc al old new b
    fineCumSmall b' ≤ fineCumSmall b + fineLargeMetaCost ∧
    fineLiveLarge b' ≤ (fineLiveLarge b + fineLargeCost new) - fineLargeCost old ∧
    finePeakLarge b' ≤ max (finePeakLarge b) (fineLiveLarge b + fineLargeCost new) := by
  dsimp only [FineBudget.stepRealloc]
  have h63 : Guaranteed63Threshold ≤ new := by
    unfold Guaranteed63Threshold fineSmallMaxReq at *; omega
  have hEqAdd : FineBudget.stepReallocAdd al new b = FineBudget.stepAligned al new b := by
    unfold FineBudget.stepReallocAdd; simp only [h63, ↓reduceIte]
  rw [hEqAdd]
  have ⟨hC1, hL1, hP1⟩ := stepAligned_large_credit b hal hnew_gt
  have ⟨hC2, hL2, hP2⟩ := stepFree_large_credit (FineBudget.stepAligned al new b) hal hold_gt
  omega

theorem stepRealloc_large_small_credit {al old new : Nat} (b : FineBudget)
    (hal : al ≤ 16) (hold_gt : fineSmallMaxReq < old) (hnew_le : new ≤ fineSmallMaxReq) :
    let b' := FineBudget.stepRealloc al old new b
    fineCumSmall b' ≤ fineCumSmall b + fineSmallReallocCost new ∧
    fineLiveLarge b' ≤ fineLiveLarge b - fineLargeCost old ∧
    finePeakLarge b' ≤ finePeakLarge b := by
  dsimp only [FineBudget.stepRealloc]
  have ⟨hC1, hL1, hP1⟩ := stepReallocAdd_small_credit b hal hnew_le
  have ⟨hC2, hL2, hP2⟩ := stepFree_large_credit (FineBudget.stepReallocAdd al new b) hal hold_gt
  omega

theorem stepFree_small_credit_le {al req : Nat} (b : FineBudget)
    (hle : req ≤ fineSmallMaxReq) :
    fineCumSmall (FineBudget.stepFree al req b) ≤ fineCumSmall b ∧
    fineLiveLarge (FineBudget.stepFree al req b) ≤ fineLiveLarge b ∧
    finePeakLarge (FineBudget.stepFree al req b) ≤ finePeakLarge b := by
  have ⟨hC, hL, hP⟩ := stepFree_small_credit (al := al) b hle
  omega

theorem stepFree_large_credit_le {al req : Nat} (b : FineBudget)
    (hal : al ≤ 16) (hgt : fineSmallMaxReq < req) :
    fineCumSmall (FineBudget.stepFree al req b) ≤ fineCumSmall b ∧
    fineLiveLarge (FineBudget.stepFree al req b) ≤ fineLiveLarge b - fineLargeCost req ∧
    finePeakLarge (FineBudget.stepFree al req b) ≤ finePeakLarge b := by
  have ⟨hC, hL, hP⟩ := stepFree_large_credit b hal hgt
  omega

instance : HasFineReallocCredit fineCostModel where
  smallMaxReq := fineSmallMaxReq
  smallAllocCost := fineSmallAllocCost
  smallReallocCost := fineSmallReallocCost
  largeCost := fineLargeCost
  largeMetaCost := fineLargeMetaCost
  baseFine := fineBaseCredit
  cumSmall := fineCumSmall
  liveLarge := fineLiveLarge
  peakLarge := finePeakLarge
  footprint_le := fineFootprint_le_credit
  cumSmall_init := rfl
  liveLarge_init := rfl
  peakLarge_init := rfl
  step_alloc_small b _ hle := stepAligned_small_credit b (by decide) hle
  step_alloc_large b hgt := stepAligned_large_credit b (by decide) hgt
  step_aligned_small b hal _ hle := stepAligned_small_credit b hal hle
  step_aligned_large b hal hgt := stepAligned_large_credit b hal hgt
  step_realloc_small_small b hal _ hold_le _ hnew_le :=
    stepRealloc_small_small_credit b hal hold_le hnew_le
  step_realloc_small_large b hal _ hold_le hnew_gt :=
    stepRealloc_small_large_credit b hal hold_le hnew_gt
  step_realloc_large_large b hal hold_gt hnew_gt :=
    stepRealloc_large_large_credit b hal hold_gt hnew_gt
  step_realloc_large_small b hal hold_gt _ hnew_le :=
    stepRealloc_large_small_credit b hal hold_gt hnew_le
  step_free_small b _ hle := stepFree_small_credit_le b hle
  step_free_large b hal hgt := stepFree_large_credit_le b hal hgt

/-! ## Entrypoint Specification Bridges -/

private theorem withCodeLoaded_eq_spec {α : Type} (lib : Obj.MultiPlacedLib)
    (mpl : Obj.MultiPlacement) {P : Program} {entry : BitVec 64}
    {s1 s2 : Spec α}
    (hpre : ∀ x, s1.pre x = s2.pre x)
    (hpost : ∀ x, s1.post x = s2.post x)
    (hpan : ∀ x, s1.onPanic x = s2.onPanic x)
    (hex : ∀ x, s1.onExit x = s2.onExit x)
    (hoom : ∀ x, s1.onOom x = s2.onOom x)
    (h : subroutine_ok P entry (lib.withCodeLoaded mpl s2)) :
    subroutine_ok P entry (lib.withCodeLoaded mpl s1) := by
  have hs : s1 = s2 := by
    cases s1; cases s2
    simp only [Spec.mk.injEq]
    exact ⟨funext hpre, funext hpost, funext hpan, funext hex, funext hoom⟩
  rwa [hs]

theorem fineMultiEntryOk_eq {S₁ S₂ α : Type}
    [ToBaseSpec S₁ α] [ToBaseSpec S₂ α]
    {mpl : Obj.MultiPlacement} {svc : State → State} {fnName : String}
    {spec₁ : S₁} {spec₂ : S₂}
    (hpre : ∀ b x, (ToBaseSpec.toSpec spec₁ b).pre x = (ToBaseSpec.toSpec spec₂ b).pre x)
    (hpost : ∀ b x, (ToBaseSpec.toSpec spec₁ b).post x = (ToBaseSpec.toSpec spec₂ b).post x)
    (hpan : ∀ b x, (ToBaseSpec.toSpec spec₁ b).onPanic x = (ToBaseSpec.toSpec spec₂ b).onPanic x)
    (hex : ∀ b x, (ToBaseSpec.toSpec spec₁ b).onExit x = (ToBaseSpec.toSpec spec₂ b).onExit x)
    (hoom : ∀ b x, (ToBaseSpec.toSpec spec₁ b).onOom x = (ToBaseSpec.toSpec spec₂ b).onOom x)
    (h : mallocngMultiEntryOk mpl svc fnName spec₂) :
    mallocngMultiEntryOk mpl svc fnName spec₁ := by
  rcases h with ⟨hexp, i, off, hfn, hsub⟩
  exact ⟨hexp, i, off, hfn,
    withCodeLoaded_eq_spec VerifiedLibraries.mallocngLib mpl
      (hpre (mpl.base i)) (hpost (mpl.base i)) (hpan (mpl.base i))
      (hex (mpl.base i)) (hoom (mpl.base i)) hsub⟩

theorem fineModelMalloc_of_fine {mpl : Obj.MultiPlacement} {svc : State → State} {γ : GhostName}
    (h : mallocngMultiEntryOk mpl svc "malloc"
      (fineMallocSpec svc γ (mallocngAddrsOfPlacement mpl))) :
    mallocngMultiEntryOk mpl svc "malloc"
      (mallocngModelMallocSpec fineCostModel fineCostModelIface svc γ
        (mallocngAddrsOfPlacement mpl)) :=
  fineMultiEntryOk_eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) h

theorem fineModelFree_of_fine {mpl : Obj.MultiPlacement} {svc : State → State} {γ : GhostName}
    (h : mallocngMultiEntryOk mpl svc "free"
      (fineFreeSpec γ (mallocngAddrsOfPlacement mpl))) :
    mallocngMultiEntryOk mpl svc "free"
      (mallocngModelFreeSpec fineCostModel fineCostModelIface γ
        (mallocngAddrsOfPlacement mpl)) :=
  fineMultiEntryOk_eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) h

theorem fineModelCalloc_of_fine {mpl : Obj.MultiPlacement} {svc : State → State} {γ : GhostName}
    (h : mallocngMultiEntryOk mpl svc "calloc"
      (fineCallocSpec svc γ (mallocngAddrsOfPlacement mpl))) :
    mallocngMultiEntryOk mpl svc "calloc"
      (mallocngModelCallocSpec fineCostModel fineCostModelIface svc γ
        (mallocngAddrsOfPlacement mpl)) :=
  fineMultiEntryOk_eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) h

theorem fineModelRealloc_of_fine {mpl : Obj.MultiPlacement} {svc : State → State} {γ : GhostName}
    (h : mallocngMultiEntryOk mpl svc "realloc"
      (fineReallocSpec svc γ (mallocngAddrsOfPlacement mpl))) :
    mallocngMultiEntryOk mpl svc "realloc"
      (mallocngModelReallocSpec fineCostModel fineCostModelIface svc γ
        (mallocngAddrsOfPlacement mpl)) :=
  fineMultiEntryOk_eq (spec₂ := fineReallocSpec svc γ (mallocngAddrsOfPlacement mpl))
    (fun _ _ => rfl)
    (fun _ ⟨_, newSize, _, oldBlk, _, _, _, _⟩ => by
      dsimp only [mallocngModelReallocSpec, fineReallocSpec, ToBaseSpec.toSpec,
        fineCostModel, toFineEvent]
      cases decide (newSize.toNat ≤ MallocngMaxAllocSize) <;> cases oldBlk <;> rfl)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun _ ⟨_, newSize, _, oldBlk, _, _, _, _⟩ => by
      dsimp only [mallocngModelReallocSpec, fineReallocSpec, ToBaseSpec.toSpec,
        fineCostModel, toFineEvent]
      cases decide (newSize.toNat ≤ MallocngMaxAllocSize) <;> cases oldBlk <;> rfl)
    h

theorem fineModelAlignedAlloc_of_fine {mpl : Obj.MultiPlacement} {svc : State → State}
    {γ : GhostName}
    (h : mallocngMultiEntryOk mpl svc "aligned_alloc"
      (fineAlignedAllocSpec svc γ (mallocngAddrsOfPlacement mpl))) :
    mallocngMultiEntryOk mpl svc "aligned_alloc"
      (mallocngModelAlignedAllocSpec fineCostModel fineCostModelIface svc γ
        (mallocngAddrsOfPlacement mpl)) :=
  fineMultiEntryOk_eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) h

theorem fineModelPosixMemalign_of_fine {mpl : Obj.MultiPlacement} {svc : State → State}
    {γ : GhostName}
    (h : mallocngMultiEntryOk mpl svc "posix_memalign"
      (finePosixMemalignSpec svc γ (mallocngAddrsOfPlacement mpl))) :
    mallocngMultiEntryOk mpl svc "posix_memalign"
      (mallocngModelPosixMemalignSpec fineCostModel fineCostModelIface svc γ
        (mallocngAddrsOfPlacement mpl)) :=
  fineMultiEntryOk_eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) h

end LibsignalBinary.Heap.Fine
