/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrSendCreditHelpers
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget

/-!
# 48-Class `fineCostModel` Bucket Bounds and Leaf Credit Specs for `spqr::send`

Provides `fineCostModel` small-class (`sc < 48`) allocation and reallocation bucket bounds, the
quantifier-free `FineSmallEvs` trace envelope with `nonFreeCount` composition lemmas, and closed
`fineCostModel` `PhaseCreditSpec` bounds for `Authenticator`, `<PolyEncoder>::encode_bytes`, and
`<Poly>::compute_at`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrSendTightBuckets

open VerifiedLibraries.Mallocng.Proofs (nominalSlotCap sizeToClassUnits sizeToClass_spec)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents
   rustReallocEvents)
open LibsignalBinary.Heap.Fine
  (FineScale MmapThresholdReq coarseGrpWtS coarseSlotWt declCost63 fineCostModel
   fineSmallAllocCost fineSmallReallocCost)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_smallMaxReq_eq smallAllocCost_eq_188_of_le_12
   smallAllocCost_le_738_of_le_44 smallAllocCost_le_1997_of_le_108)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacSha256Events)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv IterConcatEnv IterSeqEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
  (smallAllocCost_le_9789_of_le_2560 smallReallocCost_le_9789_of_le_384)
open LibsignalBinary.Proofs.PeakBudget.SpqrSendCreditHelpers
  (AuthMacHdrEnv AuthUpdateEnv BoundedCountEvs isFreeEv nonFreeCount_eq_nonFreeEvCount
   nonFreeEvCount)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget (sliceConcat2Events)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget (HkdfToVecEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecodedMessage.DefsBudget
  (ComputeAtCallEnv computeAtAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (EncodeBytesEnv encodeBytesAllocEvents)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (nonFreeCount nonFreeCount_append nonFreeCount_eq_zero_of_freeOnly)

/-! ## 48-Class `fineCostModel` Small Allocation and Reallocation Buckets -/

private def sendMinReq (sc : Nat) : Nat :=
  if sc = 0 then 0 else nominalSlotCap (sc - 1) + 1

private def sendClassAllocWt (sc : Nat) : Nat :=
  coarseSlotWt sc + (122 * coarseGrpWtS sc + FineScale - 1) / FineScale

private def sendClassReallocWt (cap sc : Nat) : Nat :=
  max (coarseSlotWt sc) (min cap (nominalSlotCap sc) + 8195) +
    (122 * max (coarseGrpWtS sc) FineScale + FineScale - 1) / FineScale

private def checkSendFineBuckets : Bool :=
  (List.range 48).all fun sc =>
    let rMin := sendMinReq sc
    let aWt := sendClassAllocWt sc
    decide (
      (rMin ≤ 72 → aWt ≤ 1607) ∧
      (aWt ≤ 143484) ∧
      (rMin ≤ 896 → sendClassReallocWt 896 sc ≤ 9789) ∧
      (rMin ≤ 2080 → sendClassReallocWt 2080 sc ≤ 10397) ∧
      (rMin ≤ 2400 → sendClassReallocWt 2400 sc ≤ 10717))

private theorem checkSendFineBuckets_true : checkSendFineBuckets = true := by
  decide +kernel

/-- Bounds `smallAllocCost fineCostModel req ≤ 1,607` for `req ≤ 72` (`sc ≤ 5`). -/
theorem smallAllocCost_le_1607_of_le_72 {req : Nat} (hreq : req ≤ 72) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 1607 := by
  change fineSmallAllocCost req ≤ 1607
  have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  have hspec := sizeToClass_spec (by unfold MmapThresholdReq at hle; exact hle)
  dsimp only at hspec
  have hrmin : sendMinReq (sizeToClassUnits ((req + 3) / 16)) ≤ 72 := by
    unfold sendMinReq
    rcases hspec.2.2 with h0 | hprev
    · simp [h0]
    · split <;> omega
  unfold fineSmallAllocCost
  simp only [hle, ↓reduceIte]
  have hcell := List.all_eq_true.mp checkSendFineBuckets_true _ (List.mem_range.mpr hspec.1)
  exact (of_decide_eq_true hcell).1 hrmin

/-- Bounds `smallAllocCost fineCostModel req ≤ 143,484` across all small-class requests `req ≤ 135,167`.
-/
theorem smallAllocCost_le_143484_of_le_135167 {req : Nat} (hreq : req ≤ 135167) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 143484 := by
  change fineSmallAllocCost req ≤ 143484
  unfold fineSmallAllocCost
  by_cases hle : req ≤ MmapThresholdReq
  · simp only [hle, ↓reduceIte]
    have hspec := sizeToClass_spec (by unfold MmapThresholdReq at hle; exact hle)
    dsimp only at hspec
    have hcell := List.all_eq_true.mp checkSendFineBuckets_true _ (List.mem_range.mpr hspec.1)
    exact (of_decide_eq_true hcell).2.1
  · simp only [hle, ↓reduceIte]
    have hdecl : declCost63 req 16 = req + 8195 := by unfold declCost63; omega
    rw [hdecl]
    exact Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right hreq 8195) 122) (by decide)

theorem smallReallocCost_le_9789_of_le_896 {newSz : Nat} (hnew : newSz ≤ 896) :
    HasFineReallocCredit.smallReallocCost fineCostModel newSz ≤ 9789 := by
  change fineSmallReallocCost newSz ≤ 9789
  have hle : newSz ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  have hspec := sizeToClass_spec (by unfold MmapThresholdReq at hle; exact hle)
  dsimp only at hspec
  have hrmin : sendMinReq (sizeToClassUnits ((newSz + 3) / 16)) ≤ 896 := by
    unfold sendMinReq
    rcases hspec.2.2 with h0 | hprev
    · simp [h0]
    · split <;> omega
  have hcell := List.all_eq_true.mp checkSendFineBuckets_true _ (List.mem_range.mpr hspec.1)
  have hb := (of_decide_eq_true hcell).2.2.1 hrmin
  have hcap : newSz ≤ nominalSlotCap (sizeToClassUnits ((newSz + 3) / 16)) := hspec.2.1
  unfold fineSmallReallocCost sendClassReallocWt declCost63 at *
  simp only [hle, ↓reduceIte]
  omega

theorem smallReallocCost_le_10397_of_le_2080 {newSz : Nat} (hnew : newSz ≤ 2080) :
    HasFineReallocCredit.smallReallocCost fineCostModel newSz ≤ 10397 := by
  change fineSmallReallocCost newSz ≤ 10397
  have hle : newSz ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  have hspec := sizeToClass_spec (by unfold MmapThresholdReq at hle; exact hle)
  dsimp only at hspec
  have hrmin : sendMinReq (sizeToClassUnits ((newSz + 3) / 16)) ≤ 2080 := by
    unfold sendMinReq
    rcases hspec.2.2 with h0 | hprev
    · simp [h0]
    · split <;> omega
  have hcell := List.all_eq_true.mp checkSendFineBuckets_true _ (List.mem_range.mpr hspec.1)
  have hb := (of_decide_eq_true hcell).2.2.2.1 hrmin
  have hcap : newSz ≤ nominalSlotCap (sizeToClassUnits ((newSz + 3) / 16)) := hspec.2.1
  unfold fineSmallReallocCost sendClassReallocWt declCost63 at *
  simp only [hle, ↓reduceIte]
  omega

theorem smallReallocCost_le_10717_of_le_2400 {newSz : Nat} (hnew : newSz ≤ 2400) :
    HasFineReallocCredit.smallReallocCost fineCostModel newSz ≤ 10717 := by
  change fineSmallReallocCost newSz ≤ 10717
  have hle : newSz ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  have hspec := sizeToClass_spec (by unfold MmapThresholdReq at hle; exact hle)
  dsimp only at hspec
  have hrmin : sendMinReq (sizeToClassUnits ((newSz + 3) / 16)) ≤ 2400 := by
    unfold sendMinReq
    rcases hspec.2.2 with h0 | hprev
    · simp [h0]
    · split <;> omega
  have hcell := List.all_eq_true.mp checkSendFineBuckets_true _ (List.mem_range.mpr hspec.1)
  have hb := (of_decide_eq_true hcell).2.2.2.2 hrmin
  have hcap : newSz ≤ nominalSlotCap (sizeToClassUnits ((newSz + 3) / 16)) := hspec.2.1
  unfold fineSmallReallocCost sendClassReallocWt declCost63 at *
  simp only [hle, ↓reduceIte]
  omega

theorem fineSmallAlloc_53 : fineSmallAllocCost 53 = 1126 := by decide +kernel
theorem fineSmallAlloc_64 : fineSmallAllocCost 64 = 1607 := by decide +kernel
theorem fineSmallAlloc_72 : fineSmallAllocCost 72 = 1607 := by decide +kernel
theorem fineSmallAlloc_96 : fineSmallAllocCost 96 = 1997 := by decide +kernel
theorem fineSmallAlloc_105 : fineSmallAllocCost 105 = 1997 := by decide +kernel
theorem fineSmallAlloc_112 : fineSmallAllocCost 112 = 2797 := by decide +kernel
theorem fineSmallAlloc_120 : fineSmallAllocCost 120 = 2797 := by decide +kernel
theorem fineSmallAlloc_136 : fineSmallAllocCost 136 = 9789 := by decide +kernel
theorem fineSmallAlloc_144 : fineSmallAllocCost 144 = 9789 := by decide +kernel
theorem fineSmallAlloc_224 : fineSmallAllocCost 224 = 8186 := by decide +kernel
theorem fineSmallAlloc_336 : fineSmallAllocCost 336 = 5822 := by decide +kernel
theorem fineSmallAlloc_384 : fineSmallAllocCost 384 = 5822 := by decide +kernel
theorem fineSmallAlloc_448 : fineSmallAllocCost 448 = 5491 := by decide +kernel
theorem fineSmallAlloc_672 : fineSmallAllocCost 672 = 3506 := by decide +kernel
theorem fineSmallAlloc_720 : fineSmallAllocCost 720 = 3506 := by decide +kernel
theorem fineSmallAlloc_816 : fineSmallAllocCost 816 = 3506 := by decide +kernel
theorem fineSmallAlloc_864 : fineSmallAllocCost 864 = 3506 := by decide +kernel
theorem fineSmallAlloc_896 : fineSmallAllocCost 896 = 3506 := by decide +kernel
theorem fineSmallAlloc_960 : fineSmallAllocCost 960 = 3506 := by decide +kernel

theorem fineSmallRealloc_8 : fineSmallReallocCost 8 = 8325 := by decide +kernel
theorem fineSmallRealloc_80 : fineSmallReallocCost 80 = 8397 := by decide +kernel
theorem fineSmallRealloc_448 : fineSmallReallocCost 448 = 8786 := by decide +kernel
theorem fineSmallRealloc_672 : fineSmallReallocCost 672 = 8989 := by decide +kernel
theorem fineSmallRealloc_896 : fineSmallReallocCost 896 = 9213 := by decide +kernel

theorem rustAlloc_fine_phaseCreditSpec {req al cap : Nat}
    (hal : al ≤ 16) (hreq : req ≤ 135167)
    (hcost : HasFineReallocCredit.smallAllocCost fineCostModel req ≤ cap) :
    PhaseCreditSpec fineCostModel (· = rustAllocEvents req al) cap 0 0 req := by
  have hsm : req ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    exact hreq
  exact (PhaseCreditSpec.rustAlloc_small_any fineCostModel_modelHyps hal hsm).mono
    hcost (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl req)

theorem rustRealloc_fine_phaseCreditSpec {old new al cap : Nat}
    (hal : al ≤ 16) (hal_new : al ≤ new)
    (hold_pos : 0 < old) (hold_le : old ≤ 135167)
    (hnew_pos : 0 < new) (hnew_le : new ≤ 135167)
    (hcost : HasFineReallocCredit.smallReallocCost fineCostModel new ≤ cap) :
    PhaseCreditSpec fineCostModel (· = rustReallocEvents old new al) cap 0 0 new := by
  have hold_sm : old ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    exact hold_le
  have hnew_sm : new ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    exact hnew_le
  exact (PhaseCreditSpec.rustRealloc_small_small fineCostModel hal hal_new
    hold_pos hold_sm hnew_pos hnew_sm).mono
    hcost (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl new)

private theorem step_nonFree_model_cap {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {maxReq stepCap : Nat}
    (st : M.σ) {ev : AllocEvent}
    (hsm : maxReq ≤ HasFineReallocCredit.smallMaxReq M)
    (hAlloc : ∀ r ≤ maxReq, HasFineReallocCredit.smallAllocCost M r ≤ stepCap)
    (hRealloc : ∀ n ≤ maxReq, HasFineReallocCredit.smallReallocCost M n ≤ stepCap)
    (hreq : eventStepReq ev ≤ maxReq) (hal : eventStepAlign ev ≤ 16) :
    HasFineReallocCredit.cumSmall (M.step ev st) ≤
      HasFineReallocCredit.cumSmall st + stepCap ∧
    HasFineReallocCredit.liveLarge (M.step ev st) ≤
      HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge (M.step ev st) ≤
      HasFineReallocCredit.peakLarge st := by
  cases ev with
  | free a s =>
    obtain ⟨hc, hl, hp⟩ := hM.freeNonInc a s st
    exact ⟨Nat.le_trans hc (Nat.le_add_right _ _), hl, hp⟩
  | alloc req =>
    simp only [eventStepReq] at hreq
    have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hsm
    obtain ⟨hc, hl, hp⟩ := hM.step_alloc_small_any st hle
    exact ⟨Nat.le_trans hc (Nat.add_le_add_left (hAlloc req hreq) _), hl, hp⟩
  | aligned al req =>
    simp only [eventStepReq, eventStepAlign] at hreq hal
    have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hsm
    obtain ⟨hc, hl, hp⟩ := hM.step_aligned_small_any st hal hle
    exact ⟨Nat.le_trans hc (Nat.add_le_add_left (hAlloc req hreq) _), hl, hp⟩
  | realloc al old new =>
    simp only [eventStepReq, eventStepAlign] at hreq hal
    have hnew_le : new ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hsm
    by_cases hold_le : old ≤ HasFineReallocCredit.smallMaxReq M
    · obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_small_any st hal hold_le hnew_le
      exact ⟨Nat.le_trans hc (Nat.add_le_add_left (hRealloc new hreq) _), hl, hp⟩
    · obtain ⟨hc, hl, hp⟩ :=
        hM.step_realloc_large_small_any st hal (Nat.lt_of_not_ge hold_le) hnew_le
      exact ⟨Nat.le_trans hc (Nat.add_le_add_left (hRealloc new hreq) _),
        Nat.le_trans hl (Nat.sub_le _ _), hp⟩

private theorem stepEvents_boundedCount_model_cap {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {maxReq stepCap : Nat}
    (hsm : maxReq ≤ HasFineReallocCredit.smallMaxReq M)
    (hAlloc : ∀ r ≤ maxReq, HasFineReallocCredit.smallAllocCost M r ≤ stepCap)
    (hRealloc : ∀ n ≤ maxReq, HasFineReallocCredit.smallReallocCost M n ≤ stepCap)
    (evs : List AllocEvent) :
    ∀ (maxNonFree : Nat) (st0 : M.σ),
      (nonFreeEvCount evs ≤ maxNonFree ∧
        ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      HasFineReallocCredit.cumSmall (M.stepEvents evs st0) ≤
        HasFineReallocCredit.cumSmall st0 + maxNonFree * stepCap ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st0) ≤
        HasFineReallocCredit.liveLarge st0 ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st0) ≤
        HasFineReallocCredit.peakLarge st0 := by
  induction evs with
  | nil =>
    intro _ st0 _
    simp only [AllocCostModel.stepEvents_nil]
    exact ⟨Nat.le_add_right _ _, Nat.le_refl _, Nat.le_refl _⟩
  | cons ev tl ih =>
    intro maxNonFree st0 ⟨hcnt, hall⟩
    have hall0 := hall ev List.mem_cons_self
    have hall_tl : ∀ e ∈ tl, eventStepReq e ≤ maxReq ∧ eventStepAlign e ≤ 16 :=
      fun e he => hall e (List.mem_cons_of_mem _ he)
    simp only [AllocCostModel.stepEvents_cons]
    by_cases hf : isFreeEv ev = true
    · simp only [nonFreeEvCount, hf, ↓reduceIte] at hcnt
      cases ev <;> try contradiction
      rename_i al sz
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.freeNonInc al sz st0
      obtain ⟨hc₂, hl₂, hp₂⟩ := ih maxNonFree (M.step (.free al sz) st0) ⟨hcnt, hall_tl⟩
      exact ⟨Nat.le_trans hc₂ (Nat.add_le_add_right hc₁ _),
        Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩
    · simp only [nonFreeEvCount, hf, Bool.false_eq_true, ↓reduceIte] at hcnt
      cases maxNonFree with
      | zero => omega
      | succ k =>
        rw [Nat.succ_mul]
        obtain ⟨hc₁, hl₁, hp₁⟩ := step_nonFree_model_cap hM st0 hsm hAlloc hRealloc hall0.1 hall0.2
        obtain ⟨hc₂, hl₂, hp₂⟩ :=
          ih k (M.step ev st0) ⟨Nat.le_of_succ_le_succ hcnt, hall_tl⟩
        have hc_add :
            HasFineReallocCredit.cumSmall (M.step ev st0) + k * stepCap ≤
              HasFineReallocCredit.cumSmall st0 + (k * stepCap + stepCap) := by
          have h1 := Nat.add_le_add_right hc₁ (k * stepCap)
          rw [Nat.add_assoc, Nat.add_comm stepCap (k * stepCap)] at h1
          exact h1
        exact ⟨Nat.le_trans hc₂ hc_add, Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩

/-- `PhaseCreditSpec` on `fineCostModel` for `BoundedCountEvs maxNonFree maxReq` with per-step ceiling `stepCap`.
-/
theorem boundedCount_fine_cap_phaseCreditSpec (maxNonFree maxReq stepCap : Nat)
    (hsm : maxReq ≤ 135167)
    (hAlloc : ∀ r ≤ maxReq, HasFineReallocCredit.smallAllocCost fineCostModel r ≤ stepCap)
    (hRealloc : ∀ n ≤ maxReq, HasFineReallocCredit.smallReallocCost fineCostModel n ≤ stepCap) :
    PhaseCreditSpec fineCostModel (BoundedCountEvs maxNonFree maxReq)
      (maxNonFree * stepCap) 0 0 maxReq where
  req_align _ h := h.2
  credit_le st0 {_} h := by
    have hsm' : maxReq ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]
      exact hsm
    obtain ⟨hc, hl, hp⟩ :=
      stepEvents_boundedCount_model_cap fineCostModel_modelHyps hsm' hAlloc hRealloc _ maxNonFree
        st0 ⟨nonFreeCount_eq_nonFreeEvCount _ ▸ h.1, h.2⟩
    exact ⟨hc, Nat.le_trans hl (Nat.le_add_right _ 0),
      Nat.le_trans hp (Nat.le_max_left _ _)⟩

theorem boundedCount_fine_2080_phaseCreditSpec :
    PhaseCreditSpec fineCostModel (BoundedCountEvs 8 2080) 83176 0 0 2080 := by
  have h := boundedCount_fine_cap_phaseCreditSpec 8 2080 10397 (by decide)
    (fun r hr => Nat.le_trans (smallAllocCost_le_9789_of_le_2560 (Nat.le_trans hr (by decide)))
      (by decide))
    (fun _ hn => smallReallocCost_le_10397_of_le_2080 hn)
  exact h.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 2080)

theorem boundedCount_fine_2400_phaseCreditSpec :
    PhaseCreditSpec fineCostModel (BoundedCountEvs 8 2400) 85736 0 0 2400 := by
  have h := boundedCount_fine_cap_phaseCreditSpec 8 2400 10717 (by decide)
    (fun r hr => Nat.le_trans (smallAllocCost_le_9789_of_le_2560 (Nat.le_trans hr (by decide)))
      (by decide))
    (fun _ hn => smallReallocCost_le_10717_of_le_2400 hn)
  exact h.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 2400)

/-- Per-event `cumSmall` charge on `fineCostModel` for small-class events (`≤ 135,167` bytes). -/
def fineSmallEventCost : AllocEvent → Nat
  | .free _ _ => 0
  | .alloc req => fineSmallAllocCost req
  | .aligned _ req => fineSmallAllocCost req
  | .realloc _ _ newSz => fineSmallReallocCost newSz

def fineSmallTraceCost : List AllocEvent → Nat
  | [] => 0
  | ev :: tl => fineSmallEventCost ev + fineSmallTraceCost tl

theorem fineSmallTraceCost_append (e₁ e₂ : List AllocEvent) :
    fineSmallTraceCost (e₁ ++ e₂) = fineSmallTraceCost e₁ + fineSmallTraceCost e₂ := by
  induction e₁ with
  | nil => simp [fineSmallTraceCost]
  | cons ev tl ih =>
    simp only [List.cons_append, fineSmallTraceCost, ih, Nat.add_assoc]

theorem fineSmallTraceCost_eq_zero_of_freeOnly {evs : List AllocEvent} (hf : FreeOnlyEvs evs) :
    fineSmallTraceCost evs = 0 := by
  induction evs with
  | nil => rfl
  | cons ev tl ih =>
    obtain ⟨al, sz, rfl⟩ := hf ev List.mem_cons_self
    simp only [fineSmallTraceCost, fineSmallEventCost, Nat.zero_add]
    exact ih (fun e he => hf e (List.mem_cons_of_mem _ he))

/-- Small-class trace envelope on `fineCostModel` bounding operation count by `maxOps`, cumulative cost by `cumCap`, and request size by `maxReq ≤ 135,167`.
-/
def FineSmallEvs (maxOps cumCap maxReq : Nat) (evs : List AllocEvent) : Prop :=
  nonFreeCount evs ≤ maxOps ∧
  fineSmallTraceCost evs ≤ cumCap ∧
  ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16

theorem FineSmallEvs.nil (maxOps cumCap maxReq : Nat) :
    FineSmallEvs maxOps cumCap maxReq [] :=
  ⟨Nat.zero_le _, Nat.zero_le _, (fun _ h => nomatch h)⟩

theorem FineSmallEvs.of_freeOnly (maxOps cumCap maxReq : Nat) {evs : List AllocEvent}
    (hf : FreeOnlyEvs evs) :
    FineSmallEvs maxOps cumCap maxReq evs := by
  refine ⟨Nat.le_trans (Nat.le_of_eq (nonFreeCount_eq_zero_of_freeOnly hf)) (Nat.zero_le _),
    Nat.le_trans (Nat.le_of_eq (fineSmallTraceCost_eq_zero_of_freeOnly hf)) (Nat.zero_le _),
    fun ev hev => ?_⟩
  obtain ⟨_, _, rfl⟩ := hf ev hev
  exact ⟨Nat.zero_le _, Nat.le_refl 16⟩

theorem FineSmallEvs.mono {o₁ o₂ c₁ c₂ r₁ r₂ : Nat} {evs : List AllocEvent}
    (ho : o₁ ≤ o₂) (hc : c₁ ≤ c₂) (hr : r₁ ≤ r₂)
    (h : FineSmallEvs o₁ c₁ r₁ evs) :
    FineSmallEvs o₂ c₂ r₂ evs :=
  ⟨Nat.le_trans h.1 ho, Nat.le_trans h.2.1 hc,
    fun ev hev => ⟨Nat.le_trans (h.2.2 ev hev).1 hr, (h.2.2 ev hev).2⟩⟩

theorem FineSmallEvs.append {o₁ o₂ c₁ c₂ r₁ r₂ : Nat} {e₁ e₂ : List AllocEvent}
    (h₁ : FineSmallEvs o₁ c₁ r₁ e₁) (h₂ : FineSmallEvs o₂ c₂ r₂ e₂) :
    FineSmallEvs (o₁ + o₂) (c₁ + c₂) (max r₁ r₂) (e₁ ++ e₂) := by
  refine ⟨by rw [nonFreeCount_append]; exact Nat.add_le_add h₁.1 h₂.1,
    by rw [fineSmallTraceCost_append]; exact Nat.add_le_add h₁.2.1 h₂.2.1,
    fun ev hev => ?_⟩
  rcases List.mem_append.mp hev with hm₁ | hm₂
  · exact ⟨Nat.le_trans (h₁.2.2 ev hm₁).1 (Nat.le_max_left r₁ r₂), (h₁.2.2 ev hm₁).2⟩
  · exact ⟨Nat.le_trans (h₂.2.2 ev hm₂).1 (Nat.le_max_right r₁ r₂), (h₂.2.2 ev hm₂).2⟩

theorem FineSmallEvs.rustAlloc {req al cap maxReq : Nat}
    (hal : al ≤ 16) (hreq : req ≤ maxReq)
    (hcost : HasFineReallocCredit.smallAllocCost fineCostModel req ≤ cap) :
    FineSmallEvs 1 cap maxReq (rustAllocEvents req al) := by
  unfold rustAllocEvents
  split
  · refine ⟨by simp [nonFreeCount], ?_, fun ev hev => ?_⟩
    · simp only [fineSmallTraceCost, fineSmallEventCost, Nat.add_zero]
      exact hcost
    · rw [List.mem_singleton] at hev
      subst hev
      exact ⟨hreq, Nat.le_refl 16⟩
  · refine ⟨by simp [nonFreeCount], ?_, fun ev hev => ?_⟩
    · simp only [fineSmallTraceCost, fineSmallEventCost, Nat.add_zero]
      exact hcost
    · rw [List.mem_singleton] at hev
      subst hev
      exact ⟨hreq, by simp only [eventStepAlign]; omega⟩

private theorem stepEvents_fineSmallEvs_model_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M)
    (hSmallMax : 135167 ≤ HasFineReallocCredit.smallMaxReq M)
    (hAllocLe : ∀ r, HasFineReallocCredit.smallAllocCost M r ≤ fineSmallAllocCost r)
    (hReallocLe : ∀ n, HasFineReallocCredit.smallReallocCost M n ≤ fineSmallReallocCost n)
    {maxReq : Nat} (hMax : maxReq ≤ 135167) :
    ∀ (evs : List AllocEvent) (maxOps cumCap : Nat) (st0 : M.σ),
      FineSmallEvs maxOps cumCap maxReq evs →
      HasFineReallocCredit.cumSmall (M.stepEvents evs st0) ≤
        HasFineReallocCredit.cumSmall st0 + cumCap ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st0) ≤
        HasFineReallocCredit.liveLarge st0 ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st0) ≤
        HasFineReallocCredit.peakLarge st0
  | [], _, _, st0, _ => by
    simp only [AllocCostModel.stepEvents_nil]
    exact ⟨Nat.le_add_right _ _, Nat.le_refl _, Nat.le_refl _⟩
  | .free al sz :: tl, maxOps, cumCap, st0, ⟨hcnt, hcost, hall⟩ => by
    simp only [AllocCostModel.stepEvents_cons]
    simp only [nonFreeCount, fineSmallTraceCost, fineSmallEventCost, Nat.zero_add] at hcnt hcost
    obtain ⟨hc₁, hl₁, hp₁⟩ := hM.freeNonInc al sz st0
    obtain ⟨hc₂, hl₂, hp₂⟩ :=
      stepEvents_fineSmallEvs_model_le hM hSmallMax hAllocLe hReallocLe hMax tl maxOps cumCap
        (M.step (.free al sz) st0) ⟨hcnt, hcost, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
    exact ⟨Nat.le_trans hc₂ (Nat.add_le_add_right hc₁ _),
      Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩
  | .alloc req :: tl, maxOps, cumCap, st0, ⟨hcnt, hcost, hall⟩ => by
    simp only [AllocCostModel.stepEvents_cons]
    simp only [nonFreeCount, fineSmallTraceCost, fineSmallEventCost] at hcnt hcost
    have hreq : req ≤ maxReq := (hall (.alloc req) List.mem_cons_self).1
    have hsm : req ≤ HasFineReallocCredit.smallMaxReq M :=
      Nat.le_trans (Nat.le_trans hreq hMax) hSmallMax
    obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_alloc_small_any st0 hsm
    have hc₁' : HasFineReallocCredit.cumSmall (M.step (.alloc req) st0) ≤
        HasFineReallocCredit.cumSmall st0 + fineSmallAllocCost req :=
      Nat.le_trans hc₁ (Nat.add_le_add_left (hAllocLe req) _)
    obtain ⟨hc₂, hl₂, hp₂⟩ :=
      stepEvents_fineSmallEvs_model_le hM hSmallMax hAllocLe hReallocLe hMax tl (maxOps - 1)
        (fineSmallTraceCost tl) (M.step (.alloc req) st0)
        ⟨by omega, Nat.le_refl _, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
    have hadd := Nat.le_trans hc₂ (Nat.add_le_add_right hc₁' (fineSmallTraceCost tl))
    rw [Nat.add_assoc] at hadd
    exact ⟨Nat.le_trans hadd (Nat.add_le_add_left hcost _),
      Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩
  | .aligned al req :: tl, maxOps, cumCap, st0, ⟨hcnt, hcost, hall⟩ => by
    simp only [AllocCostModel.stepEvents_cons]
    simp only [nonFreeCount, fineSmallTraceCost, fineSmallEventCost] at hcnt hcost
    obtain ⟨hreq, hal⟩ := hall (.aligned al req) List.mem_cons_self
    simp only [eventStepReq, eventStepAlign] at hreq hal
    have hsm : req ≤ HasFineReallocCredit.smallMaxReq M :=
      Nat.le_trans (Nat.le_trans hreq hMax) hSmallMax
    obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_aligned_small_any st0 hal hsm
    have hc₁' : HasFineReallocCredit.cumSmall (M.step (.aligned al req) st0) ≤
        HasFineReallocCredit.cumSmall st0 + fineSmallAllocCost req :=
      Nat.le_trans hc₁ (Nat.add_le_add_left (hAllocLe req) _)
    obtain ⟨hc₂, hl₂, hp₂⟩ :=
      stepEvents_fineSmallEvs_model_le hM hSmallMax hAllocLe hReallocLe hMax tl (maxOps - 1)
        (fineSmallTraceCost tl) (M.step (.aligned al req) st0)
        ⟨by omega, Nat.le_refl _, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
    have hadd := Nat.le_trans hc₂ (Nat.add_le_add_right hc₁' (fineSmallTraceCost tl))
    rw [Nat.add_assoc] at hadd
    exact ⟨Nat.le_trans hadd (Nat.add_le_add_left hcost _),
      Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩
  | .realloc al o n :: tl, maxOps, cumCap, st0, ⟨hcnt, hcost, hall⟩ => by
    simp only [AllocCostModel.stepEvents_cons]
    simp only [nonFreeCount, fineSmallTraceCost, fineSmallEventCost] at hcnt hcost
    obtain ⟨hn, hal⟩ := hall (.realloc al o n) List.mem_cons_self
    simp only [eventStepReq, eventStepAlign] at hn hal
    have hn_sm : n ≤ HasFineReallocCredit.smallMaxReq M :=
      Nat.le_trans (Nat.le_trans hn hMax) hSmallMax
    have hstep :
        HasFineReallocCredit.cumSmall (M.step (.realloc al o n) st0) ≤
          HasFineReallocCredit.cumSmall st0 + fineSmallReallocCost n ∧
        HasFineReallocCredit.liveLarge (M.step (.realloc al o n) st0) ≤
          HasFineReallocCredit.liveLarge st0 ∧
        HasFineReallocCredit.peakLarge (M.step (.realloc al o n) st0) ≤
          HasFineReallocCredit.peakLarge st0 := by
      by_cases ho_sm : o ≤ HasFineReallocCredit.smallMaxReq M
      · obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_small_any st0 hal ho_sm hn_sm
        exact ⟨Nat.le_trans hc (Nat.add_le_add_left (hReallocLe n) _), hl, hp⟩
      · obtain ⟨hc, hl, hp⟩ := hM.step_realloc_large_small_any st0 hal
          (Nat.lt_of_not_ge ho_sm) hn_sm
        exact ⟨Nat.le_trans hc (Nat.add_le_add_left (hReallocLe n) _),
          Nat.le_trans hl (Nat.sub_le _ _), hp⟩
    obtain ⟨hc₁, hl₁, hp₁⟩ := hstep
    obtain ⟨hc₂, hl₂, hp₂⟩ :=
      stepEvents_fineSmallEvs_model_le hM hSmallMax hAllocLe hReallocLe hMax tl (maxOps - 1)
        (fineSmallTraceCost tl) (M.step (.realloc al o n) st0)
        ⟨by omega, Nat.le_refl _, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
    have hadd := Nat.le_trans hc₂ (Nat.add_le_add_right hc₁ (fineSmallTraceCost tl))
    rw [Nat.add_assoc] at hadd
    exact ⟨Nat.le_trans hadd (Nat.add_le_add_left hcost _),
      Nat.le_trans hl₂ hl₁, Nat.le_trans hp₂ hp₁⟩

theorem fineSmallEvs_phaseCreditSpec (maxOps cumCap : Nat) {maxReq : Nat}
    (hMax : maxReq ≤ 135167) :
    PhaseCreditSpec fineCostModel (FineSmallEvs maxOps cumCap maxReq) cumCap 0 0 maxReq where
  req_align _ hE := hE.2.2
  credit_le st0 {evs} hE := by
    have hSmallMax : 135167 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
      rw [fineCostModel_smallMaxReq_eq]
    obtain ⟨hc, hl, hp⟩ :=
      stepEvents_fineSmallEvs_model_le fineCostModel_modelHyps hSmallMax
        (fun _ => Nat.le_refl _) (fun _ => Nat.le_refl _) hMax evs maxOps cumCap st0 hE
    exact ⟨hc, Nat.le_trans hl (Nat.le_add_right _ 0),
      Nat.le_trans hp (Nat.le_max_left _ _)⟩

/-! ## `nonFreeCount` Composition Lemmas -/

theorem nonFreeCount_boundedCount_le {maxNonFree maxReq : Nat} {evs : List AllocEvent}
    (h : BoundedCountEvs maxNonFree maxReq evs) :
    nonFreeCount evs ≤ maxNonFree :=
  h.1

theorem nonFreeCount_rustAlloc (req al : Nat) :
    nonFreeCount (rustAllocEvents req al) = 1 := by
  unfold rustAllocEvents
  split <;> rfl

theorem nonFreeCount_rustDealloc (req al : Nat) :
    nonFreeCount (rustDeallocEvents req al) = 0 := by
  unfold rustDeallocEvents
  rfl

theorem nonFreeCount_rustRealloc_le (old new al : Nat) :
    nonFreeCount (rustReallocEvents old new al) ≤ 1 := by
  unfold rustReallocEvents
  split <;> simp [nonFreeCount]

theorem nonFreeCount_sliceConcat2_le (n : Nat) :
    nonFreeCount (sliceConcat2Events n) ≤ 1 := by
  unfold sliceConcat2Events
  split
  · exact Nat.zero_le 1
  · rw [nonFreeCount_rustAlloc]

theorem nonFreeCount_seqEnv_le {E₁ E₂ : List AllocEvent → Prop} {k₁ k₂ : Nat}
    (h₁ : ∀ e, E₁ e → nonFreeCount e ≤ k₁)
    (h₂ : ∀ e, E₂ e → nonFreeCount e ≤ k₂)
    {evs : List AllocEvent} (h : SeqEnv E₁ E₂ evs) :
    nonFreeCount evs ≤ k₁ + k₂ := by
  rcases h with he₁ | ⟨e₁, e₂, rfl, he₁, he₂⟩
  · exact Nat.le_trans (h₁ evs he₁) (Nat.le_add_right k₁ k₂)
  · rw [nonFreeCount_append]
    exact Nat.add_le_add (h₁ e₁ he₁) (h₂ e₂ he₂)

theorem nonFreeCount_iterSeqEnv_le {α : Type} {Step : α → List AllocEvent → Prop}
    (k : α → Nat) (xs : List α)
    (hstep : ∀ x ∈ xs, ∀ e, Step x e → nonFreeCount e ≤ k x) :
    ∀ {evs : List AllocEvent}, IterSeqEnv Step xs evs → nonFreeCount evs ≤ (xs.map k).sum := by
  induction xs with
  | nil =>
    intro evs h
    subst h
    exact Nat.zero_le 0
  | cons x tl ih =>
    intro evs h
    simp only [List.map_cons, List.sum_cons]
    exact nonFreeCount_seqEnv_le (hstep x List.mem_cons_self)
      (fun _ he => ih (fun y hy => hstep y (List.mem_cons_of_mem x hy)) he) h

theorem nonFreeCount_iterSeqEnv_const_le {α : Type} {Step : α → List AllocEvent → Prop} {k : Nat}
    (xs : List α) (hstep : ∀ x ∈ xs, ∀ e, Step x e → nonFreeCount e ≤ k) :
    ∀ {evs : List AllocEvent}, IterSeqEnv Step xs evs → nonFreeCount evs ≤ xs.length * k := by
  intro evs h
  have hc := nonFreeCount_iterSeqEnv_le (fun _ => k) xs hstep h
  simpa using hc

/-! ## `Authenticator`, `encode_bytes`, and `<Poly>::compute_at` `fineCostModel` Specs -/

/-- `PhaseCreditSpec` on `fineCostModel` for `libcruxHmacSha256Events` (`Δcum = 5,559`, `Δlive = Δpeak = 0`).
-/
theorem libcruxHmacSha256_fine_phaseCreditSpec :
    PhaseCreditSpec fineCostModel (· = libcruxHmacSha256Events) 5559 0 0 64 := by
  have ha64 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 64 1) 1607 0 0 64 :=
    rustAlloc_fine_phaseCreditSpec (by decide) (by decide) (Nat.le_of_eq fineSmallAlloc_64)
  have hd64 : PhaseCreditSpec fineCostModel (· = rustDeallocEvents 64 1) 0 0 0 0 :=
    PhaseCreditSpec.rustDealloc_align16 fineCostModel (by decide)
  have ha32 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 32 1) 738 0 0 32 :=
    rustAlloc_fine_phaseCreditSpec (by decide) (by decide)
      (smallAllocCost_le_738_of_le_44 (by decide))
  have hseq :=
    ha64.concat (ha64.concat (ha64.concat (hd64.concat (hd64.concat (hd64.concat ha32)))))
  refine hseq.congr_mono ?_ (by decide) (by decide) (by decide) (by decide)
  intro evs hevs
  subst hevs
  simp only [libcruxHmacSha256Events, List.append_assoc, ConcatEnv]
  exact ⟨_, _, rfl, rfl, ⟨_, _, rfl, rfl, ⟨_, _, rfl, rfl, ⟨_, _, rfl, rfl,
    ⟨_, _, rfl, rfl, ⟨_, _, rfl, rfl, rfl⟩⟩⟩⟩⟩⟩

/-- `PhaseCreditSpec` on `fineCostModel` for `AuthMacHdrEnv` (`Δcum = 7,556`, `Δlive = Δpeak = 0`).
-/
theorem authMacHdr_fine_phaseCreditSpec :
    PhaseCreditSpec fineCostModel AuthMacHdrEnv 7556 0 0 105 := by
  have ha105 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 105 1) 1997 0 0 105 :=
    rustAlloc_fine_phaseCreditSpec (by decide) (by decide) (Nat.le_of_eq fineSmallAlloc_105)
  have h := (ha105.seq libcruxHmacSha256_fine_phaseCreditSpec).seq
    (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)
  exact h.mono (by decide) (by decide) (by decide) (by decide)

theorem authMacHdr_nonFreeCount_le {evs : List AllocEvent} (h : AuthMacHdrEnv evs) :
    nonFreeCount evs ≤ 5 := by
  have hc : nonFreeCount evs ≤ (1 + 4) + 0 :=
    nonFreeCount_seqEnv_le
      (fun _ hs => nonFreeCount_seqEnv_le
        (fun _ h1 => by subst h1; simp [nonFreeCount_rustAlloc])
        (fun _ h2 => by subst h2; decide) hs)
      (fun _ hf => Nat.le_of_eq (nonFreeCount_eq_zero_of_freeOnly hf)) h
  exact hc

theorem sliceConcat2_fine_phaseCreditSpec {n cap : Nat}
    (hn : n ≤ 135167)
    (hcost : HasFineReallocCredit.smallAllocCost fineCostModel n ≤ cap) :
    PhaseCreditSpec fineCostModel (· = sliceConcat2Events n) cap 0 0 n := by
  by_cases h0 : n = 0
  · subst h0
    exact (PhaseCreditSpec.nil fineCostModel).congr_mono
      (by intro _ h; simpa [sliceConcat2Events] using h)
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · have ha : PhaseCreditSpec fineCostModel (· = rustAllocEvents n 1) cap 0 0 n :=
      rustAlloc_fine_phaseCreditSpec (by decide) hn hcost
    exact ha.congr_mono
      (by intro _ h; simpa [sliceConcat2Events, h0] using h)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- `PhaseCreditSpec` on `fineCostModel` for `AuthUpdateEnv rkLen 32` when `rkLen ≤ 32` (`Δcum = 5,816`).
-/
theorem authUpdate_fine_32_phaseCreditSpec {rkLen : Nat} (hrk : rkLen ≤ 32) :
    PhaseCreditSpec fineCostModel (AuthUpdateEnv rkLen 32) 5816 0 0 64 := by
  have hsum : rkLen + 32 ≤ 64 := by omega
  have hs1 : PhaseCreditSpec fineCostModel (· = sliceConcat2Events (rkLen + 32))
      1607 0 0 (rkLen + 32) :=
    sliceConcat2_fine_phaseCreditSpec (Nat.le_trans hsum (by decide))
      (smallAllocCost_le_1607_of_le_72 (Nat.le_trans hsum (by decide)))
  have hs2 : PhaseCreditSpec fineCostModel (· = sliceConcat2Events 53) 1126 0 0 53 :=
    sliceConcat2_fine_phaseCreditSpec (by decide) (Nat.le_of_eq fineSmallAlloc_53)
  have hhkdf : PhaseCreditSpec fineCostModel (HkdfToVecEnv 64) 1607 0 0 64 :=
    rustAlloc_fine_phaseCreditSpec (by decide) (by decide) (Nat.le_of_eq fineSmallAlloc_64)
  have ha32 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 32 1) 738 0 0 32 :=
    rustAlloc_fine_phaseCreditSpec (by decide) (by decide)
      (smallAllocCost_le_738_of_le_44 (by decide))
  have h := hs1.seq (hs2.seq (hhkdf.seq (ha32.seq (ha32.seq
    (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)))))
  exact h.mono (by decide) (by decide) (by decide) (by omega)

theorem authUpdate_nonFreeCount_le {rkLen kLen : Nat} {evs : List AllocEvent}
    (h : AuthUpdateEnv rkLen kLen evs) :
    nonFreeCount evs ≤ 5 := by
  unfold AuthUpdateEnv at h
  have hc : nonFreeCount evs ≤ 1 + (1 + (1 + (1 + (1 + 0)))) :=
    nonFreeCount_seqEnv_le
      (fun _ hs => by subst hs; exact nonFreeCount_sliceConcat2_le _)
      (fun _ h2 => nonFreeCount_seqEnv_le
        (fun _ hs => by subst hs; exact nonFreeCount_sliceConcat2_le _)
        (fun _ h3 => nonFreeCount_seqEnv_le
          (fun _ hs => by unfold HkdfToVecEnv at hs; subst hs; rw [nonFreeCount_rustAlloc])
          (fun _ h4 => nonFreeCount_seqEnv_le
            (fun _ hs => by subst hs; rw [nonFreeCount_rustAlloc])
            (fun _ h5 => nonFreeCount_seqEnv_le
              (fun _ hs => by subst hs; rw [nonFreeCount_rustAlloc])
              (fun _ hf => Nat.le_of_eq (nonFreeCount_eq_zero_of_freeOnly hf)) h5) h4) h3) h2) h
  exact hc

private theorem iterConcatEnv_flatMap {α : Type} (f : α → List AllocEvent) :
    ∀ (xs : List α), IterConcatEnv (fun x evs => evs = f x) xs (xs.flatMap f)
  | [] => rfl
  | x :: xs => ⟨f x, xs.flatMap f, rfl, rfl, iterConcatEnv_flatMap f xs⟩

private theorem replicate_flatten_eq_flatMap (n : Nat) (evs₀ : List AllocEvent) :
    (List.replicate n evs₀).flatten = (List.replicate n ()).flatMap (fun _ => evs₀) := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.flatten_cons, List.flatMap_cons, ih]

private theorem replicate_flatten_zero_live_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M]
    (n : Nat) (evs₀ : List AllocEvent) {c r : Nat}
    (h₀ : PhaseCreditSpec M (· = evs₀) c 0 0 r) :
    PhaseCreditSpec M (· = (List.replicate n evs₀).flatten) (n * c) 0 0 r := by
  have hiter : PhaseCreditSpec M (fun x => x = (List.replicate n evs₀).flatten)
      ((List.replicate n ()).length * c) 0 0 r :=
    (PhaseCreditSpec.iter_zero_live (List.replicate n ()) (fun _ _ => h₀)).of_imp
      fun _ h => by
        rw [h, replicate_flatten_eq_flatMap]
        exact IterConcatEnv.toIterSeqEnv
          (iterConcatEnv_flatMap (fun _ : Unit => evs₀) (List.replicate n ()))
  simpa [List.length_replicate] using hiter

theorem encodeBytes_fine_96_phaseCreditSpec :
    PhaseCreditSpec fineCostModel (EncodeBytesEnv 96) 31952 0 0 96 := by
  unfold EncodeBytesEnv encodeBytesAllocEvents
  split
  · have hslot : PhaseCreditSpec fineCostModel (· = rustAllocEvents 96 2) 1997 0 0 96 :=
      rustAlloc_fine_phaseCreditSpec (by decide) (by decide) (Nat.le_of_eq fineSmallAlloc_96)
    exact (replicate_flatten_zero_live_phaseCreditSpec 16 (rustAllocEvents 96 2) hslot).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 96)
  · exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

theorem encodeBytes_fine_960_phaseCreditSpec :
    PhaseCreditSpec fineCostModel (EncodeBytesEnv 960) 56096 0 0 960 := by
  unfold EncodeBytesEnv encodeBytesAllocEvents
  split
  · have hslot : PhaseCreditSpec fineCostModel (· = rustAllocEvents 960 2) 3506 0 0 960 :=
      rustAlloc_fine_phaseCreditSpec (by decide) (by decide) (Nat.le_of_eq fineSmallAlloc_960)
    exact (replicate_flatten_zero_live_phaseCreditSpec 16 (rustAllocEvents 960 2) hslot).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 960)
  · exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

theorem encodeBytes_nonFreeCount_le (msgLen : Nat) {evs : List AllocEvent}
    (h : EncodeBytesEnv msgLen evs) :
    nonFreeCount evs ≤ 16 := by
  unfold EncodeBytesEnv encodeBytesAllocEvents at h
  subst h
  split
  · have hrep : ∀ k : Nat,
        nonFreeCount ((List.replicate k (rustAllocEvents msgLen 2)).flatten) = k := by
      intro k
      induction k with
      | zero => rfl
      | succ j ih =>
        simp only [List.replicate_succ, List.flatten_cons, nonFreeCount_append,
          nonFreeCount_rustAlloc, ih]
        omega
    rw [hrep 16]
  · exact Nat.zero_le 16

/-- `cumSmall` charge of `<Poly>::compute_at` on `.rodata` polynomial degree `n` (`8,513` at `n = 1`, `188` for `n ∈ {0, 2..6}`, `1,607` for `7 ≤ n ≤ 36`).
-/
def computeAtRodataCum (n : Nat) : Nat :=
  if n = 1 then 8513
  else if n ≤ 6 then 188
  else 1607

/-- Optional `<Poly>::compute_at` envelope in `PolysLoop` (`evs = []` on fast-prefix slots `j < i0`, `ComputeAtCallEnv n` on `j ≥ i0`).
-/
def ComputeAtOptEnv (n : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨ ComputeAtCallEnv n evs

theorem computeAtCall_fine_rodata_phaseCreditSpec {n : Nat} (hn : n ≤ 36) :
    PhaseCreditSpec fineCostModel (ComputeAtCallEnv n)
      (computeAtRodataCum n) 0 0 (max 8 (2 * n)) := by
  have halloc :
      PhaseCreditSpec fineCostModel (· = computeAtAllocEvents n)
        (computeAtRodataCum n) 0 0 (max 8 (2 * n)) := by
    unfold computeAtAllocEvents computeAtRodataCum
    by_cases h0 : n = 0
    · subst h0
      simp only [↓reduceIte]
      have ha8 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 8 2) 188 0 0 8 :=
        rustAlloc_fine_phaseCreditSpec (by decide) (by decide)
          (Nat.le_of_eq (smallAllocCost_eq_188_of_le_12 (by decide)))
      exact ha8.mono (Nat.le_refl 188) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
    · by_cases h1 : n = 1
      · subst h1
        simp only [↓reduceIte]
        have ha2 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 2 2) 188 0 0 2 :=
          rustAlloc_fine_phaseCreditSpec (by decide) (by decide)
            (Nat.le_of_eq (smallAllocCost_eq_188_of_le_12 (by decide)))
        have hre8 : PhaseCreditSpec fineCostModel (· = rustReallocEvents 2 8 2) 8325 0 0 8 :=
          rustRealloc_fine_phaseCreditSpec (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (Nat.le_of_eq fineSmallRealloc_8)
        refine (ha2.concat hre8).congr_mono ?_ (by decide) (by decide) (by decide) (by decide)
        intro evs hevs
        subst hevs
        exact ⟨rustAllocEvents 2 2, rustReallocEvents 2 8 2, rfl, rfl, rfl⟩
      · simp only [h0, h1, ↓reduceIte]
        by_cases h6 : n ≤ 6
        · simp only [h6, ↓reduceIte]
          have ha2n : PhaseCreditSpec fineCostModel (· = rustAllocEvents (2 * n) 2)
              188 0 0 (2 * n) :=
            rustAlloc_fine_phaseCreditSpec (by decide) (by omega)
              (Nat.le_of_eq (smallAllocCost_eq_188_of_le_12 (by omega)))
          exact ha2n.mono (Nat.le_refl 188) (Nat.le_refl 0) (Nat.le_refl 0)
            (Nat.le_max_right 8 (2 * n))
        · simp only [h6, ↓reduceIte]
          have ha2n : PhaseCreditSpec fineCostModel (· = rustAllocEvents (2 * n) 2)
              1607 0 0 (2 * n) :=
            rustAlloc_fine_phaseCreditSpec (by decide) (by omega)
              (smallAllocCost_le_1607_of_le_72 (by omega))
          exact ha2n.mono (Nat.le_refl 1607) (Nat.le_refl 0) (Nat.le_refl 0)
            (Nat.le_max_right 8 (2 * n))
  exact (halloc.seq (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)).mono
    (Nat.le_of_eq (Nat.add_zero _)) (Nat.le_refl 0) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩)

theorem computeAtOpt_fine_rodata_phaseCreditSpec {n : Nat} (hn : n ≤ 36) :
    PhaseCreditSpec fineCostModel (ComputeAtOptEnv n)
      (computeAtRodataCum n) 0 0 (max 8 (2 * n)) :=
  ((PhaseCreditSpec.nil fineCostModel).or (computeAtCall_fine_rodata_phaseCreditSpec hn)).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.le_refl 0) (Nat.le_refl 0)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

theorem computeAtCall_fine_640_phaseCreditSpec {n : Nat} (hn : n ≤ 640) :
    PhaseCreditSpec fineCostModel (ComputeAtCallEnv n) 9789 0 0 (max 8 (2 * n)) := by
  have halloc :
      PhaseCreditSpec fineCostModel (· = computeAtAllocEvents n) 9789 0 0 (max 8 (2 * n)) := by
    unfold computeAtAllocEvents
    by_cases h0 : n = 0
    · subst h0
      simp only [↓reduceIte]
      have ha8 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 8 2) 188 0 0 8 :=
        rustAlloc_fine_phaseCreditSpec (by decide) (by decide)
          (Nat.le_of_eq (smallAllocCost_eq_188_of_le_12 (by decide)))
      exact ha8.mono (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)
    · by_cases h1 : n = 1
      · subst h1
        simp only [↓reduceIte]
        have ha2 : PhaseCreditSpec fineCostModel (· = rustAllocEvents 2 2) 188 0 0 2 :=
          rustAlloc_fine_phaseCreditSpec (by decide) (by decide)
            (Nat.le_of_eq (smallAllocCost_eq_188_of_le_12 (by decide)))
        have hre8 : PhaseCreditSpec fineCostModel (· = rustReallocEvents 2 8 2) 8325 0 0 8 :=
          rustRealloc_fine_phaseCreditSpec (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (Nat.le_of_eq fineSmallRealloc_8)
        refine (ha2.concat hre8).congr_mono ?_ (by decide) (by decide) (by decide) (by decide)
        intro evs hevs
        subst hevs
        exact ⟨rustAllocEvents 2 2, rustReallocEvents 2 8 2, rfl, rfl, rfl⟩
      · simp only [h0, h1, ↓reduceIte]
        have ha2n : PhaseCreditSpec fineCostModel (· = rustAllocEvents (2 * n) 2)
            9789 0 0 (2 * n) :=
          rustAlloc_fine_phaseCreditSpec (by decide) (by omega)
            (smallAllocCost_le_9789_of_le_2560 (by omega))
        exact ha2n.mono (Nat.le_refl 9789) (Nat.le_refl 0) (Nat.le_refl 0)
          (Nat.le_max_right 8 (2 * n))
  exact (halloc.seq (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps)).mono
    (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.zero_le _⟩)

def computeAtOps (n : Nat) : Nat :=
  if n = 1 then 2 else 1

theorem computeAtCall_nonFreeCount_exact_le (n : Nat) {evs : List AllocEvent}
    (h : ComputeAtCallEnv n evs) :
    nonFreeCount evs ≤ computeAtOps n := by
  have hc : nonFreeCount evs ≤ computeAtOps n + 0 :=
    nonFreeCount_seqEnv_le
      (fun e he => by
        subst he
        unfold computeAtAllocEvents computeAtOps
        by_cases h0 : n = 0
        · simp [h0, nonFreeCount_rustAlloc]
        · by_cases h1 : n = 1
          · subst h1
            change nonFreeCount (rustAllocEvents 2 2 ++ rustReallocEvents 2 8 2) ≤ 2
            rw [nonFreeCount_append, nonFreeCount_rustAlloc]
            have hre := nonFreeCount_rustRealloc_le 2 8 2
            omega
          · simp [h0, h1, nonFreeCount_rustAlloc])
      (fun _ hf => Nat.le_of_eq (nonFreeCount_eq_zero_of_freeOnly hf)) h
  simpa using hc

theorem computeAtCall_nonFreeCount_le (n : Nat) {evs : List AllocEvent}
    (h : ComputeAtCallEnv n evs) :
    nonFreeCount evs ≤ 2 := by
  have hc := computeAtCall_nonFreeCount_exact_le n h
  unfold computeAtOps at hc
  split at hc <;> omega

theorem computeAtOpt_nonFreeCount_exact_le (n : Nat) {evs : List AllocEvent}
    (h : ComputeAtOptEnv n evs) :
    nonFreeCount evs ≤ computeAtOps n := by
  rcases h with rfl | hc
  · exact Nat.zero_le _
  · exact computeAtCall_nonFreeCount_exact_le n hc

end LibsignalBinary.Proofs.PeakBudget.SpqrSendTightBuckets
