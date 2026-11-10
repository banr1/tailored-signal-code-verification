/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.CreditInst

/-!
# `fineCostModel` Client Bounds

Concrete parameter evaluations, affine upper bounds on `smallAllocCost` and `smallReallocCost`,
closed-form cumulative costs along `Vec<104>` and `Vec<u8>` / `String` doubling chains, and
`FitsStep` / `FitsEvent` / `FitsTrace` bridges for `fineCostModel`.
-/

set_option autoImplicit false

@[expose] public section

namespace LibsignalBinary.Heap.Fine.ClientBounds

open Arm64 ProofLib
open VerifiedLibraries.Mallocng.Proofs
open VerifiedLibraries.Mallocng hiding AllocCostModel AllocEvent MallocngCostModelIface
  MallocngCostModelSound MallocngModelEnv MallocngModelPlacedEntryContracts
  MallocngModelPostEnv MallocngStepOomCond
open LibsignalBinary.Heap
open LibsignalBinary.Heap.Fine
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit

@[scoped simp] theorem fineCostModel_smallMaxReq_eq :
    HasFineReallocCredit.smallMaxReq fineCostModel = 135167 :=
  rfl

theorem le_smallMaxReq_106496 :
    106496 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
  decide

theorem le_smallMaxReq_131072 :
    131072 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
  decide

@[scoped simp] theorem fineCostModel_largeMetaCost_eq :
    HasFineReallocCredit.largeMetaCost fineCostModel = 122 :=
  rfl

@[scoped simp] theorem fineCostModel_largeCost_eq (req : Nat) :
    HasFineReallocCredit.largeCost fineCostModel req = req + 8195 := by
  change declCost63 req 16 = req + 8195
  unfold declCost63
  omega

theorem fineCostModel_largeCost_le (req : Nat)
    (_hgt : HasFineReallocCredit.smallMaxReq fineCostModel < req) :
    HasFineReallocCredit.largeCost fineCostModel req ≤ req + 8195 := by
  rw [fineCostModel_largeCost_eq]
  exact Nat.le_refl _

theorem gBaseConst_eq : gBaseConst = 272 := by
  decide +kernel

theorem baseRootFine_eq : BaseRootFine = 18628686 := by
  decide +kernel

@[scoped simp] theorem fineCostModel_baseFine_eq :
    HasFineReallocCredit.baseFine fineCostModel = 18686152 := by
  change fineBaseCredit = 18686152
  unfold fineBaseCredit
  rw [gBaseConst_eq, baseRootFine_eq]

/-! ## Affine and Small-Bucket Bounds -/

/-- Minimal request byte count mapped into size class `sc < 48` by `sizeToClassUnits ((req + 3) / 16)`. -/
def reqMinOfClass (sc : Nat) : Nat :=
  if sc = 0 then 0 else nominalSlotCap (sc - 1) + 1

private def classAllocWt (sc : Nat) : Nat :=
  coarseSlotWt sc + (122 * coarseGrpWtS sc + FineScale - 1) / FineScale

private def classReallocGrpExtra (sc : Nat) : Nat :=
  (122 * max (coarseGrpWtS sc) FineScale + FineScale - 1) / FineScale

private def checkClassAffineBounds : Bool :=
  (List.range 48).all fun sc =>
    let rMin := reqMinOfClass sc
    let rMinPos := max 1 rMin
    let aWt := classAllocWt sc
    let rWt := coarseSlotWt sc + classReallocGrpExtra sc
    decide (
      aWt ≤ 2 * rMin + 9539 ∧
      rWt ≤ 2 * rMin + 9539 ∧
      aWt ≤ rMin + 26365 ∧
      rWt ≤ rMin + 26365 ∧
      aWt ≤ 77 * rMin + 188 ∧
      aWt ≤ 78 * rMinPos + 110 ∧
      aWt ≤ 79 * rMinPos + 109)

private theorem checkClassAffineBounds_true : checkClassAffineBounds = true := by
  decide +kernel

private theorem reqMinOfClass_le_of_le_mmap {req : Nat} (hreq : req ≤ MmapThresholdReq) :
    let sc0 := sizeToClassUnits ((req + 3) / 16)
    sc0 < 48 ∧ reqMinOfClass sc0 ≤ req := by
  have hspec := sizeToClass_spec (req := req) (by unfold MmapThresholdReq at hreq; exact hreq)
  dsimp only at hspec ⊢
  refine ⟨hspec.1, ?_⟩
  unfold reqMinOfClass
  rcases hspec.2.2 with h0 | hprev
  · simp [h0]
  · split <;> omega

private theorem classReallocGrpExtra_le_366 (sc : Nat) :
    classReallocGrpExtra sc ≤ 366 := by
  have hcap := (coarseWt_le_cap sc).2
  unfold classReallocGrpExtra FineScale at *
  omega

theorem smallAllocCost_le_two_mul_add (req : Nat) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 2 * req + 9539 := by
  change fineSmallAllocCost req ≤ 2 * req + 9539
  unfold fineSmallAllocCost
  by_cases hle : req ≤ MmapThresholdReq
  · simp only [hle, ↓reduceIte]
    obtain ⟨hsc, hrmin⟩ := reqMinOfClass_le_of_le_mmap hle
    have hcell := List.all_eq_true.mp checkClassAffineBounds_true _ (List.mem_range.mpr hsc)
    have hb := (of_decide_eq_true hcell).1
    unfold classAllocWt at hb
    omega
  · simp only [hle, ↓reduceIte, declCost63]
    omega

theorem smallReallocCost_le_two_mul_add (newSz : Nat) :
    HasFineReallocCredit.smallReallocCost fineCostModel newSz ≤ 2 * newSz + 9539 := by
  change fineSmallReallocCost newSz ≤ 2 * newSz + 9539
  unfold fineSmallReallocCost
  by_cases hle : newSz ≤ MmapThresholdReq
  · simp only [hle, ↓reduceIte]
    obtain ⟨hsc, hrmin⟩ := reqMinOfClass_le_of_le_mmap hle
    have hcell := List.all_eq_true.mp checkClassAffineBounds_true _ (List.mem_range.mpr hsc)
    have hb := (of_decide_eq_true hcell).2.1
    have hextra := classReallocGrpExtra_le_366 (sizeToClassUnits ((newSz + 3) / 16))
    unfold classReallocGrpExtra declCost63 at *
    omega
  · simp only [hle, ↓reduceIte, declCost63, FineScale]
    omega

theorem smallAllocCost_le_add_26365 (req : Nat) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ req + 26365 := by
  change fineSmallAllocCost req ≤ req + 26365
  unfold fineSmallAllocCost
  by_cases hle : req ≤ MmapThresholdReq
  · simp only [hle, ↓reduceIte]
    obtain ⟨hsc, hrmin⟩ := reqMinOfClass_le_of_le_mmap hle
    have hcell := List.all_eq_true.mp checkClassAffineBounds_true _ (List.mem_range.mpr hsc)
    have hb := (of_decide_eq_true hcell).2.2.1
    unfold classAllocWt at hb
    omega
  · simp only [hle, ↓reduceIte, declCost63]
    omega

theorem smallReallocCost_le_add_26365 (newSz : Nat) :
    HasFineReallocCredit.smallReallocCost fineCostModel newSz ≤ newSz + 26365 := by
  change fineSmallReallocCost newSz ≤ newSz + 26365
  unfold fineSmallReallocCost
  by_cases hle : newSz ≤ MmapThresholdReq
  · simp only [hle, ↓reduceIte]
    obtain ⟨hsc, hrmin⟩ := reqMinOfClass_le_of_le_mmap hle
    have hcell := List.all_eq_true.mp checkClassAffineBounds_true _ (List.mem_range.mpr hsc)
    have hb := (of_decide_eq_true hcell).2.2.2.1
    have hextra := classReallocGrpExtra_le_366 (sizeToClassUnits ((newSz + 3) / 16))
    unfold classReallocGrpExtra declCost63 at *
    omega
  · simp only [hle, ↓reduceIte, declCost63, FineScale]
    omega

theorem smallAllocCost_le_77_mul_add (req : Nat) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 77 * req + 188 := by
  change fineSmallAllocCost req ≤ 77 * req + 188
  unfold fineSmallAllocCost
  by_cases hle : req ≤ MmapThresholdReq
  · simp only [hle, ↓reduceIte]
    obtain ⟨hsc, hrmin⟩ := reqMinOfClass_le_of_le_mmap hle
    have hcell := List.all_eq_true.mp checkClassAffineBounds_true _ (List.mem_range.mpr hsc)
    have hb := (of_decide_eq_true hcell).2.2.2.2.1
    unfold classAllocWt at hb
    omega
  · simp only [hle, ↓reduceIte, declCost63]
    unfold MmapThresholdReq at hle
    omega

theorem smallAllocCost_pos_le_78_mul_add {req : Nat} (hpos : 0 < req) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 78 * req + 110 := by
  change fineSmallAllocCost req ≤ 78 * req + 110
  unfold fineSmallAllocCost
  by_cases hle : req ≤ MmapThresholdReq
  · simp only [hle, ↓reduceIte]
    obtain ⟨hsc, hrmin⟩ := reqMinOfClass_le_of_le_mmap hle
    have hcell := List.all_eq_true.mp checkClassAffineBounds_true _ (List.mem_range.mpr hsc)
    have hb := (of_decide_eq_true hcell).2.2.2.2.2.1
    unfold classAllocWt at hb
    omega
  · simp only [hle, ↓reduceIte, declCost63]
    unfold MmapThresholdReq at hle
    omega

theorem smallAllocCost_pos_le_79_mul_add {req : Nat} (hpos : 0 < req) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 79 * req + 109 := by
  change fineSmallAllocCost req ≤ 79 * req + 109
  unfold fineSmallAllocCost
  by_cases hle : req ≤ MmapThresholdReq
  · simp only [hle, ↓reduceIte]
    obtain ⟨hsc, hrmin⟩ := reqMinOfClass_le_of_le_mmap hle
    have hcell := List.all_eq_true.mp checkClassAffineBounds_true _ (List.mem_range.mpr hsc)
    have hb := (of_decide_eq_true hcell).2.2.2.2.2.2
    unfold classAllocWt at hb
    omega
  · simp only [hle, ↓reduceIte, declCost63]
    unfold MmapThresholdReq at hle
    omega

private def checkSmallBuckets : Bool :=
  (List.range 7).all fun u =>
    let aWt := classAllocWt (sizeToClassUnits u)
    decide (
      (u = 0 → aWt = 188) ∧
      (u ≤ 1 → aWt ≤ 488) ∧
      (u ≤ 2 → aWt ≤ 738) ∧
      (u ≤ 3 → aWt ≤ 1126) ∧
      (u ≤ 6 → aWt ≤ 1997))

private theorem checkSmallBuckets_true : checkSmallBuckets = true := by
  decide +kernel

theorem smallAllocCost_eq_188_of_le_12 {req : Nat} (hreq : req ≤ 12) :
    HasFineReallocCredit.smallAllocCost fineCostModel req = 188 := by
  change fineSmallAllocCost req = 188
  have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  have hu0 : (req + 3) / 16 = 0 := by omega
  unfold fineSmallAllocCost
  simp only [hle, ↓reduceIte, hu0]
  have hcell := List.all_eq_true.mp checkSmallBuckets_true 0 (by decide)
  exact (of_decide_eq_true hcell).1 rfl

theorem smallAllocCost_le_488_of_le_28 {req : Nat} (hreq : req ≤ 28) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 488 := by
  change fineSmallAllocCost req ≤ 488
  have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  have hu : (req + 3) / 16 < 7 := by omega
  have hu1 : (req + 3) / 16 ≤ 1 := by omega
  unfold fineSmallAllocCost
  simp only [hle, ↓reduceIte]
  have hcell := List.all_eq_true.mp checkSmallBuckets_true ((req + 3) / 16) (List.mem_range.mpr hu)
  exact (of_decide_eq_true hcell).2.1 hu1

theorem smallAllocCost_le_738_of_le_44 {req : Nat} (hreq : req ≤ 44) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 738 := by
  change fineSmallAllocCost req ≤ 738
  have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  have hu : (req + 3) / 16 < 7 := by omega
  have hu2 : (req + 3) / 16 ≤ 2 := by omega
  unfold fineSmallAllocCost
  simp only [hle, ↓reduceIte]
  have hcell := List.all_eq_true.mp checkSmallBuckets_true ((req + 3) / 16) (List.mem_range.mpr hu)
  exact (of_decide_eq_true hcell).2.2.1 hu2

theorem smallAllocCost_le_1126_of_le_60 {req : Nat} (hreq : req ≤ 60) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 1126 := by
  change fineSmallAllocCost req ≤ 1126
  have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  have hu : (req + 3) / 16 < 7 := by omega
  have hu3 : (req + 3) / 16 ≤ 3 := by omega
  unfold fineSmallAllocCost
  simp only [hle, ↓reduceIte]
  have hcell := List.all_eq_true.mp checkSmallBuckets_true ((req + 3) / 16) (List.mem_range.mpr hu)
  exact (of_decide_eq_true hcell).2.2.2.1 hu3

theorem smallAllocCost_le_1997_of_le_108 {req : Nat} (hreq : req ≤ 108) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 1997 := by
  change fineSmallAllocCost req ≤ 1997
  have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  have hu : (req + 3) / 16 < 7 := by omega
  have hu6 : (req + 3) / 16 ≤ 6 := by omega
  unfold fineSmallAllocCost
  simp only [hle, ↓reduceIte]
  have hcell := List.all_eq_true.mp checkSmallBuckets_true ((req + 3) / 16) (List.mem_range.mpr hu)
  exact (of_decide_eq_true hcell).2.2.2.2 hu6

/-! ## Capacity-Doubling Chains (`Vec<104>` and `Vec<u8>`) -/

private def vecPointPairs : List (Bool × Nat × Nat) :=
  [ (true, 416, 5491),
    (false, 832, 9149), (false, 1664, 9981), (false, 3328, 11645), (false, 6656, 14973),
    (false, 13312, 21629), (false, 26624, 34941), (false, 53248, 65658), (false, 106496, 131194),
    (true, 8, 188),
    (false, 16, 8333), (false, 32, 8349), (false, 64, 8381), (false, 128, 9789),
    (false, 256, 8637), (false, 512, 8829), (false, 1024, 9341), (false, 2048, 10365),
    (false, 4096, 12413), (false, 8192, 16509), (false, 16384, 24701), (false, 32768, 41085),
    (false, 65536, 77946), (false, 131072, 139389) ]

private def checkVecPoints : Bool :=
  vecPointPairs.all fun (isAlloc, req, expected) =>
    if isAlloc then fineSmallAllocCost req == expected
    else fineSmallReallocCost req == expected

private theorem checkVecPoints_true : checkVecPoints = true := by
  decide +kernel

private theorem extractAllocPoint {req expected : Nat}
    (hmem : (true, req, expected) ∈ vecPointPairs) :
    HasFineReallocCredit.smallAllocCost fineCostModel req = expected := by
  change fineSmallAllocCost req = expected
  have hcell := List.all_eq_true.mp checkVecPoints_true (true, req, expected) hmem
  exact of_decide_eq_true hcell

private theorem extractReallocPoint {req expected : Nat}
    (hmem : (false, req, expected) ∈ vecPointPairs) :
    HasFineReallocCredit.smallReallocCost fineCostModel req = expected := by
  change fineSmallReallocCost req = expected
  have hcell := List.all_eq_true.mp checkVecPoints_true (false, req, expected) hmem
  exact of_decide_eq_true hcell

@[scoped simp] theorem smallAllocCost_416 :
    HasFineReallocCredit.smallAllocCost fineCostModel 416 = 5491 :=
  extractAllocPoint (by decide)

@[scoped simp] theorem smallReallocCost_832 :
    HasFineReallocCredit.smallReallocCost fineCostModel 832 = 9149 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_1664 :
    HasFineReallocCredit.smallReallocCost fineCostModel 1664 = 9981 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_3328 :
    HasFineReallocCredit.smallReallocCost fineCostModel 3328 = 11645 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_6656 :
    HasFineReallocCredit.smallReallocCost fineCostModel 6656 = 14973 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_13312 :
    HasFineReallocCredit.smallReallocCost fineCostModel 13312 = 21629 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_26624 :
    HasFineReallocCredit.smallReallocCost fineCostModel 26624 = 34941 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_53248 :
    HasFineReallocCredit.smallReallocCost fineCostModel 53248 = 65658 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_106496 :
    HasFineReallocCredit.smallReallocCost fineCostModel 106496 = 131194 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallAllocCost_8 :
    HasFineReallocCredit.smallAllocCost fineCostModel 8 = 188 :=
  extractAllocPoint (by decide)

@[scoped simp] theorem smallReallocCost_16 :
    HasFineReallocCredit.smallReallocCost fineCostModel 16 = 8333 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_32 :
    HasFineReallocCredit.smallReallocCost fineCostModel 32 = 8349 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_64 :
    HasFineReallocCredit.smallReallocCost fineCostModel 64 = 8381 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_128 :
    HasFineReallocCredit.smallReallocCost fineCostModel 128 = 9789 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_256 :
    HasFineReallocCredit.smallReallocCost fineCostModel 256 = 8637 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_512 :
    HasFineReallocCredit.smallReallocCost fineCostModel 512 = 8829 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_1024 :
    HasFineReallocCredit.smallReallocCost fineCostModel 1024 = 9341 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_2048 :
    HasFineReallocCredit.smallReallocCost fineCostModel 2048 = 10365 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_4096 :
    HasFineReallocCredit.smallReallocCost fineCostModel 4096 = 12413 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_8192 :
    HasFineReallocCredit.smallReallocCost fineCostModel 8192 = 16509 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_16384 :
    HasFineReallocCredit.smallReallocCost fineCostModel 16384 = 24701 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_32768 :
    HasFineReallocCredit.smallReallocCost fineCostModel 32768 = 41085 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_65536 :
    HasFineReallocCredit.smallReallocCost fineCostModel 65536 = 77946 :=
  extractReallocPoint (by decide)

@[scoped simp] theorem smallReallocCost_131072 :
    HasFineReallocCredit.smallReallocCost fineCostModel 131072 = 139389 :=
  extractReallocPoint (by decide)

/-- Per-step `cumSmall` charge of one `RawVec<104>::grow_one` step (`0 → 4` or `cap → 2 * cap`,
stride `104`, align `8`). -/
def fineVec104StepCumCost (M : AllocCostModel) [HasFineReallocCredit M] (cap : Nat) : Nat :=
  if cap = 0 then
    if 4 * 104 ≤ HasFineReallocCredit.smallMaxReq M then
      HasFineReallocCredit.smallAllocCost M (4 * 104)
    else
      HasFineReallocCredit.largeMetaCost M
  else
    if 2 * cap * 104 ≤ HasFineReallocCredit.smallMaxReq M then
      HasFineReallocCredit.smallReallocCost M (2 * cap * 104)
    else
      HasFineReallocCredit.largeMetaCost M

/-- Cumulative `cumSmall` upper bound along the `Vec<104>` doubling chain `0 → 4 → 8 → … → cap`. -/
def fineVec104CumOfCap (M : AllocCostModel) [HasFineReallocCredit M] (cap : Nat) : Nat :=
  if cap < 4 then 0
  else if cap < 8 then fineVec104StepCumCost M 0
  else fineVec104CumOfCap M (cap / 2) + fineVec104StepCumCost M (cap / 2)
termination_by cap
decreasing_by omega

@[scoped simp] theorem fineVec104CumOfCap_zero (M : AllocCostModel) [HasFineReallocCredit M] :
    fineVec104CumOfCap M 0 = 0 := by
  unfold fineVec104CumOfCap
  rfl

theorem fineVec104CumOfCap_four (M : AllocCostModel) [HasFineReallocCredit M] :
    fineVec104CumOfCap M 4 = fineVec104StepCumCost M 0 := by
  unfold fineVec104CumOfCap
  rfl

theorem fineVec104CumOfCap_two_mul (M : AllocCostModel) [HasFineReallocCredit M]
    {cap : Nat} (hcap : 4 ≤ cap) :
    fineVec104CumOfCap M (2 * cap) = fineVec104CumOfCap M cap + fineVec104StepCumCost M cap := by
  conv_lhs => unfold fineVec104CumOfCap
  have h1 : ¬ (2 * cap < 4) := by omega
  have h2 : ¬ (2 * cap < 8) := by omega
  have hdiv : (2 * cap) / 2 = cap := by omega
  simp only [h1, h2, hdiv, ↓reduceIte]

theorem fineVec104CumOfCap_pow2_mono (M : AllocCostModel) [HasFineReallocCredit M]
    {i j : Nat} (hij : i ≤ j) :
    fineVec104CumOfCap M (4 * 2 ^ i) ≤ fineVec104CumOfCap M (4 * 2 ^ j) := by
  induction hij with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    rename_i k _
    have hge : 4 ≤ 4 * 2 ^ k := by
      have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    have heq : 4 * 2 ^ (k + 1) = 2 * (4 * 2 ^ k) := by rw [Nat.pow_succ]; omega
    rw [heq, fineVec104CumOfCap_two_mul M hge]
    omega

private theorem fineVec104StepCumCost_small {cap : Nat} (hne : cap ≠ 0)
    (hle : 2 * cap * 104 ≤ 135167) :
    fineVec104StepCumCost fineCostModel cap =
      HasFineReallocCredit.smallReallocCost fineCostModel (2 * cap * 104) := by
  unfold fineVec104StepCumCost
  simp only [hne, fineCostModel_smallMaxReq_eq, hle, ↓reduceIte]

theorem fineVec104StepCumCost_large_of_ge_1024 {cap : Nat} (hge : 1024 ≤ cap) :
    fineVec104StepCumCost fineCostModel cap = 122 := by
  have hne : cap ≠ 0 := by omega
  have hgt : ¬ (2 * cap * 104 ≤ 135167) := by omega
  unfold fineVec104StepCumCost
  simp only [hne, fineCostModel_smallMaxReq_eq, hgt, fineCostModel_largeMetaCost_eq, ↓reduceIte]

@[scoped simp] theorem fineVec104CumOfCap_4 :
    fineVec104CumOfCap fineCostModel 4 = 5491 := by
  rw [fineVec104CumOfCap_four]
  unfold fineVec104StepCumCost
  have hle : 4 * 104 ≤ 135167 := by decide
  simp only [fineCostModel_smallMaxReq_eq, hle, ↓reduceIte]
  exact smallAllocCost_416

@[scoped simp] theorem fineVec104CumOfCap_1024 :
    fineVec104CumOfCap fineCostModel 1024 = 304661 := by
  have h8 : fineVec104CumOfCap fineCostModel 8 = 14640 := by
    rw [show (8 : Nat) = 2 * 4 from rfl, fineVec104CumOfCap_two_mul _ (by decide),
      fineVec104CumOfCap_4, fineVec104StepCumCost_small (by decide) (by decide), smallReallocCost_832]
  have h16 : fineVec104CumOfCap fineCostModel 16 = 24621 := by
    rw [show (16 : Nat) = 2 * 8 from rfl, fineVec104CumOfCap_two_mul _ (by decide),
      h8, fineVec104StepCumCost_small (by decide) (by decide), smallReallocCost_1664]
  have h32 : fineVec104CumOfCap fineCostModel 32 = 36266 := by
    rw [show (32 : Nat) = 2 * 16 from rfl, fineVec104CumOfCap_two_mul _ (by decide),
      h16, fineVec104StepCumCost_small (by decide) (by decide), smallReallocCost_3328]
  have h64 : fineVec104CumOfCap fineCostModel 64 = 51239 := by
    rw [show (64 : Nat) = 2 * 32 from rfl, fineVec104CumOfCap_two_mul _ (by decide),
      h32, fineVec104StepCumCost_small (by decide) (by decide), smallReallocCost_6656]
  have h128 : fineVec104CumOfCap fineCostModel 128 = 72868 := by
    rw [show (128 : Nat) = 2 * 64 from rfl, fineVec104CumOfCap_two_mul _ (by decide),
      h64, fineVec104StepCumCost_small (by decide) (by decide), smallReallocCost_13312]
  have h256 : fineVec104CumOfCap fineCostModel 256 = 107809 := by
    rw [show (256 : Nat) = 2 * 128 from rfl, fineVec104CumOfCap_two_mul _ (by decide),
      h128, fineVec104StepCumCost_small (by decide) (by decide), smallReallocCost_26624]
  have h512 : fineVec104CumOfCap fineCostModel 512 = 173467 := by
    rw [show (512 : Nat) = 2 * 256 from rfl, fineVec104CumOfCap_two_mul _ (by decide),
      h256, fineVec104StepCumCost_small (by decide) (by decide), smallReallocCost_53248]
  rw [show (1024 : Nat) = 2 * 512 from rfl, fineVec104CumOfCap_two_mul _ (by decide),
    h512, fineVec104StepCumCost_small (by decide) (by decide), smallReallocCost_106496]

theorem fineVec104CumOfCap_pow2_ge_8 {j : Nat} (hj : 8 ≤ j) :
    fineVec104CumOfCap fineCostModel (4 * 2 ^ j) = 304661 + 122 * (j - 8) := by
  induction hj with
  | refl =>
    exact fineVec104CumOfCap_1024
  | @step k hle ih =>
    have hk : 8 ≤ k := hle
    have hk_pow : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    have hge1024 : 1024 ≤ 4 * 2 ^ k := by omega
    have heq : 4 * 2 ^ (k + 1) = 2 * (4 * 2 ^ k) := by rw [Nat.pow_succ]; omega
    rw [heq, fineVec104CumOfCap_two_mul _ (by omega), ih,
      fineVec104StepCumCost_large_of_ge_1024 hge1024]
    omega

@[scoped simp] theorem fineVec104CumOfCap_2pow20 :
    fineVec104CumOfCap fineCostModel (2 ^ 20) = 305881 := by
  have h := fineVec104CumOfCap_pow2_ge_8 (j := 18) (by decide)
  simpa using h

theorem fineVec104CumOfCap_le_304661 {cap : Nat}
    (hpow : cap = 0 ∨ ∃ j, cap = 4 * 2 ^ j) (hle : cap ≤ 1024) :
    fineVec104CumOfCap fineCostModel cap ≤ 304661 := by
  rcases hpow with rfl | ⟨j, rfl⟩
  · simp
  · have hj : j ≤ 8 := by
      by_contra hgt
      have h9 : 9 ≤ j := by omega
      have hp : 2 ^ 9 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) h9
      omega
    exact Nat.le_trans (fineVec104CumOfCap_pow2_mono fineCostModel hj)
      (Nat.le_of_eq fineVec104CumOfCap_1024)

theorem fineVec104CumOfCap_le_305881 {cap : Nat}
    (hpow : cap = 0 ∨ ∃ j, cap = 4 * 2 ^ j) (hle : cap ≤ 2 ^ 20) :
    fineVec104CumOfCap fineCostModel cap ≤ 305881 := by
  rcases hpow with rfl | ⟨j, rfl⟩
  · simp
  · have hj : j ≤ 18 := by
      by_contra hgt
      have h19 : 19 ≤ j := by omega
      have hp : 2 ^ 19 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) h19
      omega
    have hmono := fineVec104CumOfCap_pow2_mono fineCostModel hj
    have heq18 := fineVec104CumOfCap_pow2_ge_8 (j := 18) (by decide)
    omega

/-- Per-step `cumSmall` charge of one `RawVec<u8>::grow_one` step (`0 → 8` or `cap → 2 * cap`,
stride `1`, align `1`). -/
def fineVecU8StepCumCost (M : AllocCostModel) [HasFineReallocCredit M] (cap : Nat) : Nat :=
  if cap = 0 then
    if 8 ≤ HasFineReallocCredit.smallMaxReq M then
      HasFineReallocCredit.smallAllocCost M 8
    else
      HasFineReallocCredit.largeMetaCost M
  else
    if 2 * cap ≤ HasFineReallocCredit.smallMaxReq M then
      HasFineReallocCredit.smallReallocCost M (2 * cap)
    else
      HasFineReallocCredit.largeMetaCost M

/-- Cumulative `cumSmall` upper bound along the `Vec<u8>` / `String` doubling chain
`0 → 8 → 16 → 32 → … → cap`. -/
def fineVecU8DoublingCumOfCap (M : AllocCostModel) [HasFineReallocCredit M] (cap : Nat) : Nat :=
  if cap < 8 then 0
  else if cap < 16 then fineVecU8StepCumCost M 0
  else fineVecU8DoublingCumOfCap M (cap / 2) + fineVecU8StepCumCost M (cap / 2)
termination_by cap
decreasing_by omega

@[scoped simp] theorem fineVecU8DoublingCumOfCap_zero (M : AllocCostModel) [HasFineReallocCredit M] :
    fineVecU8DoublingCumOfCap M 0 = 0 := by
  unfold fineVecU8DoublingCumOfCap
  rfl

theorem fineVecU8DoublingCumOfCap_eight (M : AllocCostModel) [HasFineReallocCredit M] :
    fineVecU8DoublingCumOfCap M 8 = fineVecU8StepCumCost M 0 := by
  unfold fineVecU8DoublingCumOfCap
  rfl

theorem fineVecU8DoublingCumOfCap_two_mul (M : AllocCostModel) [HasFineReallocCredit M]
    {cap : Nat} (hcap : 8 ≤ cap) :
    fineVecU8DoublingCumOfCap M (2 * cap) =
      fineVecU8DoublingCumOfCap M cap + fineVecU8StepCumCost M cap := by
  conv_lhs => unfold fineVecU8DoublingCumOfCap
  have h1 : ¬ (2 * cap < 8) := by omega
  have h2 : ¬ (2 * cap < 16) := by omega
  have hdiv : (2 * cap) / 2 = cap := by omega
  simp only [h1, h2, hdiv, ↓reduceIte]

theorem fineVecU8DoublingCumOfCap_pow2_mono (M : AllocCostModel) [HasFineReallocCredit M]
    {i j : Nat} (hij : i ≤ j) :
    fineVecU8DoublingCumOfCap M (8 * 2 ^ i) ≤ fineVecU8DoublingCumOfCap M (8 * 2 ^ j) := by
  induction hij with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    rename_i k _
    have hge : 8 ≤ 8 * 2 ^ k := by
      have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega
    have heq : 8 * 2 ^ (k + 1) = 2 * (8 * 2 ^ k) := by rw [Nat.pow_succ]; omega
    rw [heq, fineVecU8DoublingCumOfCap_two_mul M hge]
    omega

private theorem fineVecU8StepCumCost_small {cap : Nat} (hne : cap ≠ 0)
    (hle : 2 * cap ≤ 135167) :
    fineVecU8StepCumCost fineCostModel cap =
      HasFineReallocCredit.smallReallocCost fineCostModel (2 * cap) := by
  unfold fineVecU8StepCumCost
  simp only [hne, fineCostModel_smallMaxReq_eq, hle, ↓reduceIte]

theorem fineVecU8StepCumCost_large_of_ge_131072 {cap : Nat} (hge : 131072 ≤ cap) :
    fineVecU8StepCumCost fineCostModel cap = 122 := by
  have hne : cap ≠ 0 := by omega
  have hgt : ¬ (2 * cap ≤ 135167) := by omega
  unfold fineVecU8StepCumCost
  simp only [hne, fineCostModel_smallMaxReq_eq, hgt, fineCostModel_largeMetaCost_eq, ↓reduceIte]

@[scoped simp] theorem fineVecU8DoublingCumOfCap_8 :
    fineVecU8DoublingCumOfCap fineCostModel 8 = 188 := by
  rw [fineVecU8DoublingCumOfCap_eight]
  unfold fineVecU8StepCumCost
  have hle : 8 ≤ 135167 := by decide
  simp only [fineCostModel_smallMaxReq_eq, hle, ↓reduceIte, smallAllocCost_8]

@[scoped simp] theorem fineVecU8DoublingCumOfCap_131072 :
    fineVecU8DoublingCumOfCap fineCostModel 131072 = 384255 := by
  have h16 : fineVecU8DoublingCumOfCap fineCostModel 16 = 8521 := by
    rw [show (16 : Nat) = 2 * 8 from rfl, fineVecU8DoublingCumOfCap_two_mul _ (by decide),
      fineVecU8DoublingCumOfCap_8, fineVecU8StepCumCost_small (by decide) (by decide), smallReallocCost_16]
  have h32 : fineVecU8DoublingCumOfCap fineCostModel 32 = 16870 := by
    rw [show (32 : Nat) = 2 * 16 from rfl, fineVecU8DoublingCumOfCap_two_mul _ (by decide),
      h16, fineVecU8StepCumCost_small (by decide) (by decide), smallReallocCost_32]
  have h64 : fineVecU8DoublingCumOfCap fineCostModel 64 = 25251 := by
    rw [show (64 : Nat) = 2 * 32 from rfl, fineVecU8DoublingCumOfCap_two_mul _ (by decide),
      h32, fineVecU8StepCumCost_small (by decide) (by decide), smallReallocCost_64]
  have h128 : fineVecU8DoublingCumOfCap fineCostModel 128 = 35040 := by
    rw [show (128 : Nat) = 2 * 64 from rfl, fineVecU8DoublingCumOfCap_two_mul _ (by decide),
      h64, fineVecU8StepCumCost_small (by decide) (by decide), smallReallocCost_128]
  have h256 : fineVecU8DoublingCumOfCap fineCostModel 256 = 43677 := by
    rw [show (256 : Nat) = 2 * 128 from rfl, fineVecU8DoublingCumOfCap_two_mul _ (by decide),
      h128, fineVecU8StepCumCost_small (by decide) (by decide), smallReallocCost_256]
  have h512 : fineVecU8DoublingCumOfCap fineCostModel 512 = 52506 := by
    rw [show (512 : Nat) = 2 * 256 from rfl, fineVecU8DoublingCumOfCap_two_mul _ (by decide),
      h256, fineVecU8StepCumCost_small (by decide) (by decide), smallReallocCost_512]
  have h1024 : fineVecU8DoublingCumOfCap fineCostModel 1024 = 61847 := by
    rw [show (1024 : Nat) = 2 * 512 from rfl, fineVecU8DoublingCumOfCap_two_mul _ (by decide),
      h512, fineVecU8StepCumCost_small (by decide) (by decide), smallReallocCost_1024]
  have h2048 : fineVecU8DoublingCumOfCap fineCostModel 2048 = 72212 := by
    rw [show (2048 : Nat) = 2 * 1024 from rfl, fineVecU8DoublingCumOfCap_two_mul _ (by decide),
      h1024, fineVecU8StepCumCost_small (by decide) (by decide), smallReallocCost_2048]
  have h4096 : fineVecU8DoublingCumOfCap fineCostModel 4096 = 84625 := by
    rw [show (4096 : Nat) = 2 * 2048 from rfl, fineVecU8DoublingCumOfCap_two_mul _ (by decide),
      h2048, fineVecU8StepCumCost_small (by decide) (by decide), smallReallocCost_4096]
  have h8192 : fineVecU8DoublingCumOfCap fineCostModel 8192 = 101134 := by
    rw [show (8192 : Nat) = 2 * 4096 from rfl, fineVecU8DoublingCumOfCap_two_mul _ (by decide),
      h4096, fineVecU8StepCumCost_small (by decide) (by decide), smallReallocCost_8192]
  have h16384 : fineVecU8DoublingCumOfCap fineCostModel 16384 = 125835 := by
    rw [show (16384 : Nat) = 2 * 8192 from rfl, fineVecU8DoublingCumOfCap_two_mul _ (by decide),
      h8192, fineVecU8StepCumCost_small (by decide) (by decide), smallReallocCost_16384]
  have h32768 : fineVecU8DoublingCumOfCap fineCostModel 32768 = 166920 := by
    rw [show (32768 : Nat) = 2 * 16384 from rfl, fineVecU8DoublingCumOfCap_two_mul _ (by decide),
      h16384, fineVecU8StepCumCost_small (by decide) (by decide), smallReallocCost_32768]
  have h65536 : fineVecU8DoublingCumOfCap fineCostModel 65536 = 244866 := by
    rw [show (65536 : Nat) = 2 * 32768 from rfl, fineVecU8DoublingCumOfCap_two_mul _ (by decide),
      h32768, fineVecU8StepCumCost_small (by decide) (by decide), smallReallocCost_65536]
  rw [show (131072 : Nat) = 2 * 65536 from rfl, fineVecU8DoublingCumOfCap_two_mul _ (by decide),
    h65536, fineVecU8StepCumCost_small (by decide) (by decide), smallReallocCost_131072]

theorem fineVecU8DoublingCumOfCap_pow2_ge_14 {j : Nat} (hj : 14 ≤ j) :
    fineVecU8DoublingCumOfCap fineCostModel (8 * 2 ^ j) = 384255 + 122 * (j - 14) := by
  induction hj with
  | refl =>
    exact fineVecU8DoublingCumOfCap_131072
  | @step k hle ih =>
    have hk : 14 ≤ k := hle
    have hk_pow : 2 ^ 14 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    have hge : 131072 ≤ 8 * 2 ^ k := by omega
    have heq : 8 * 2 ^ (k + 1) = 2 * (8 * 2 ^ k) := by rw [Nat.pow_succ]; omega
    rw [heq, fineVecU8DoublingCumOfCap_two_mul _ (by omega), ih,
      fineVecU8StepCumCost_large_of_ge_131072 hge]
    omega

theorem fineVecU8DoublingCumOfCap_le_385109 {cap : Nat}
    (hpow : cap = 0 ∨ ∃ j, cap = 8 * 2 ^ j) (hle : cap ≤ 2 ^ 24) :
    fineVecU8DoublingCumOfCap fineCostModel cap ≤ 385109 := by
  rcases hpow with rfl | ⟨j, rfl⟩
  · simp
  · have hj : j ≤ 21 := by
      by_contra hgt
      have h22 : 22 ≤ j := by omega
      have hp : 2 ^ 22 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) h22
      omega
    have hmono := fineVecU8DoublingCumOfCap_pow2_mono fineCostModel hj
    have heq21 := fineVecU8DoublingCumOfCap_pow2_ge_14 (j := 21) (by decide)
    omega

/-! ## Dynamic-Interval, Step-Reserve, and `FitsStep` Bridges -/

/-- Closed-form upper bound on `fineMaxGroups b` as a function of `cumSmall b ≤ cumB`. -/
def fineMaxGroupsOfCum (cumB : Nat) : Nat :=
  273 + cumB / 122

/-- Closed-form upper bound on `fineMaxMetaAreas b` as a function of `cumSmall b ≤ cumB`. -/
def fineMaxMetaAreasOfCum (cumB : Nat) : Nat :=
  1 + (280 + cumB / 122) / 101

/-- Closed-form upper bound on `fineCostModel.maxDynIvs b` as a function of `cumSmall b ≤ cumB`. -/
def fineDynIvsOfCum (cumB : Nat) : Nat :=
  3 * fineMaxMetaAreasOfCum cumB + 2 + fineMaxGroupsOfCum cumB

/-- Closed-form upper bound on `fineCostModel.stepReserve ev b` as a function of `(maxReq, maxAlign, cumB)`. -/
def fineStepReserveOfCum (maxReq maxAlign cumB : Nat) : Nat :=
  FineStepBound maxReq maxAlign (fineMaxMetaAreasOfCum cumB)

/-- Payload byte parameter entering `fineCostModel.stepReserve ev`. -/
def eventStepReq : AllocEvent → Nat
  | .alloc req => req
  | .aligned _ req => req
  | .free _ _ => 0
  | .realloc _ _ newSz => newSz

/-- Alignment parameter entering `fineCostModel.stepReserve ev`. -/
def eventStepAlign : AllocEvent → Nat
  | .alloc _ => 16
  | .aligned align _ => align
  | .free _ _ => 16
  | .realloc align _ _ => align

theorem fineMaxGroups_le_of_cumSmall {b : FineBudget} {cumB : Nat}
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB) :
    fineMaxGroups b ≤ fineMaxGroupsOfCum cumB := by
  change fineCumSmall b ≤ cumB at hcum
  unfold fineMaxGroups fineMaxGroupsOfCum fineCumSmall FineScale at *
  rw [gBaseConst_eq]
  omega

theorem fineMaxMetaAreas_le_of_cumSmall {b : FineBudget} {cumB : Nat}
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB) :
    fineMaxMetaAreas b ≤ fineMaxMetaAreasOfCum cumB := by
  have hg := fineMaxGroups_le_of_cumSmall hcum
  unfold fineMaxMetaAreas fineMaxMetaAreasOfCum fineMaxGroupsOfCum at *
  omega

theorem fineMaxDynIvs_le_of_cumSmall {b : fineCostModel.σ} {cumB : Nat}
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB) :
    fineCostModel.maxDynIvs b ≤ fineDynIvsOfCum cumB := by
  have hg := fineMaxGroups_le_of_cumSmall hcum
  have hm := fineMaxMetaAreas_le_of_cumSmall hcum
  change fineMaxDynIvs b ≤ fineDynIvsOfCum cumB
  unfold fineMaxDynIvs fineDynIvsOfCum
  omega

theorem FineStepBound_mono {req₁ req₂ align₁ align₂ m₁ m₂ : Nat}
    (hreq : req₁ ≤ req₂) (hal : max align₁ 16 ≤ max align₂ 16) (hm : m₁ ≤ m₂) :
    FineStepBound req₁ align₁ m₁ ≤ FineStepBound req₂ align₂ m₂ := by
  unfold FineStepBound pageAlignUp
  (try unfold PAGE_SIZE)
  omega

theorem fineCostModel_stepReserve_eq (ev : AllocEvent) (b : fineCostModel.σ) :
    fineCostModel.stepReserve ev b =
      FineStepBound (eventStepReq ev) (eventStepAlign ev) (fineMaxMetaAreas b) := by
  cases ev <;> rfl

theorem fineStepReserve_le_of_cumSmall {ev : AllocEvent} {b : fineCostModel.σ}
    {maxReq maxAlign cumB : Nat}
    (hreq : eventStepReq ev ≤ maxReq)
    (hal : max (eventStepAlign ev) 16 ≤ max maxAlign 16)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB) :
    fineCostModel.stepReserve ev b ≤ fineStepReserveOfCum maxReq maxAlign cumB := by
  rw [fineCostModel_stepReserve_eq]
  exact FineStepBound_mono hreq hal (fineMaxMetaAreas_le_of_cumSmall hcum)

theorem fineStepReserve_le_of_cumSmall_align16 {ev : AllocEvent} {b : fineCostModel.σ}
    {maxReq cumB : Nat}
    (hreq : eventStepReq ev ≤ maxReq)
    (hal : eventStepAlign ev ≤ 16)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB) :
    fineCostModel.stepReserve ev b ≤ fineStepReserveOfCum maxReq 16 cumB :=
  fineStepReserve_le_of_cumSmall hreq (by omega) hcum

/-- Specialization of `fitsStep_of_fine_bounds` to `fineCostModel`, discharging `maxDynIvs` via
`fineDynIvsOfCum cumB`. -/
theorem fitsStep_fineCostModel_of_bounds
    {lim : BudgetLimits} {b : fineCostModel.σ} {stepB cumB peakB : Nat}
    (henf : lim.enforced = true)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge (M := fineCostModel) b ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge (M := fineCostModel) b ≤ peakB)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) + 2 * stepB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) + stepB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) * (stepB + PAGE_SIZE) + stepB ≤ 2 ^ 48) :
    FitsStep lim stepB (fineCostModel.maxDynIvs b) (fineCostModel.footprint b) :=
  fitsStep_of_fine_bounds fineCostModel henf
    (fineMaxDynIvs_le_of_cumSmall hcum) hcum hlive hpeak
    (by simpa only [fineCostModel_baseFine_eq] using hram)
    (by simpa only [fineCostModel_baseFine_eq] using hva)

/-- Single-event `FitsEvent fineCostModel lim b ev` criterion from `(maxReq, maxAlign, cumB, peakB)`. -/
theorem fitsEvent_fineCostModel_of_bounds
    {lim : BudgetLimits} {b : fineCostModel.σ} {ev : AllocEvent}
    {maxReq maxAlign cumB peakB : Nat}
    (hwf : ev.withinMaxAlloc)
    (hreq : eventStepReq ev ≤ maxReq)
    (hal : max (eventStepAlign ev) 16 ≤ max maxAlign 16)
    (henf : lim.enforced = true)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) b ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge (M := fineCostModel) b ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge (M := fineCostModel) b ≤ peakB)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq maxAlign cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq maxAlign cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq maxAlign cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq maxAlign cumB ≤ 2 ^ 48) :
    FitsEvent fineCostModel lim b ev :=
  ⟨hwf, FitsStep.mono
    (fitsStep_fineCostModel_of_bounds henf hcum hlive hpeak hram hva)
    (fineStepReserve_le_of_cumSmall hreq hal hcum)
    (Nat.le_refl _) (Nat.le_refl _)⟩

/-- Whole-trace `FitsTrace fineCostModel` criterion at `fineCostModel.evalLog fullLog`. -/
theorem fitsTrace_fineCostModel_of_bounds
    {lim : BudgetLimits} {fullLog : List AllocEvent}
    {maxReq maxAlign cumB peakB : Nat}
    (hevs : ∀ ev ∈ fullLog,
      ev.withinMaxAlloc ∧ eventStepReq ev ≤ maxReq ∧ max (eventStepAlign ev) 16 ≤ max maxAlign 16)
    (henf : lim.enforced = true)
    (hcum : HasFineReallocCredit.cumSmall (M := fineCostModel) (fineCostModel.evalLog fullLog) ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge (M := fineCostModel) (fineCostModel.evalLog fullLog) ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge (M := fineCostModel) (fineCostModel.evalLog fullLog) ≤ peakB)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq maxAlign cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq maxAlign cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq maxAlign cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq maxAlign cumB ≤ 2 ^ 48) :
    FitsTrace fineCostModel lim (fineStepReserveOfCum maxReq maxAlign cumB) fullLog :=
  ⟨fun ev hmem =>
    let ⟨hwf, hreq, hal⟩ := hevs ev hmem
    ⟨hwf, fineStepReserve_le_of_cumSmall hreq hal hcum⟩,
   fitsStep_fineCostModel_of_bounds henf hcum hlive hpeak hram hva⟩

end LibsignalBinary.Heap.Fine.ClientBounds
