/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Heap.Fine.ClientIntegration

/-!
# `fineCostModel` Instantiations, `FitsTrace`/`FitsEnv` Bridges, and Non-Vacuity

Companion lemmas to `SeqCreditKit` on `fineCostModel`:
1. `fineCostModel_freeNonInc` and `freeOnly_fineCostModel` (`FreeNonInc fineCostModel`).
2. Affine rate bounds (`fineCostModel_smallAff`, `fineCostModel_largeAff`,
   `fineCostModel_largeMetaCost_le_122`) and `fineCostModel_modelHyps : ModelHyps fineCostModel`.
3. Direct bridges from `PhaseCreditSpec fineCostModel` to `FitsTrace` and `FitsEnv`
   (`fitsTrace_fineCostModel_of_phaseCredit`, `fitsEnv_fineCostModel_of_phaseCredit`).
4. Concrete two-phase `SeqEnv` non-vacuity witness (`200,000` B `sc = 63` temporary alloc/free
   followed by a `1,024` B small allocation) proved inhabited and `FitsEnv` under `1 GiB`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas

open Arm64 ProofLib
open LibsignalBinary.Heap (
  AllocEvent BudgetLimits FitsTrace FitsEnv SeqEnv FreeOnlyEvs
  rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
)
open LibsignalBinary.Heap.Fine (
  FineBudget FineEvent FineScale FineStepBound
  finePeak63Bytes finePeak63Count
  fineCostModel fineCumSmall fineLiveLarge finePeakLarge toFineEvent
  stepAligned_small_credit
  stepRealloc_small_small_credit stepRealloc_small_large_credit stepRealloc_large_small_credit
)
open LibsignalBinary.Heap.Fine.ClientBounds (
  fineMaxGroupsOfCum fineMaxMetaAreasOfCum fineDynIvsOfCum fineStepReserveOfCum
  smallAllocCost_le_two_mul_add smallReallocCost_le_two_mul_add
  fineCostModel_largeCost_le fineCostModel_largeCost_eq fineCostModel_largeMetaCost_eq
  fineCostModel_smallMaxReq_eq
)
open LibsignalBinary.Heap.Fine.ClientIntegration (
  fitsTrace_fineCostModel_of_bounds_autoWf
  smallAllocCost_le_3506_of_kyber_range
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (
  ConcatEnv FreeNonInc ModelHyps PhaseCreditSpec DeallocCreditSpec
)

/-! ## 1. `FreeNonInc fineCostModel` & `FreeOnlyEvs` Specializations -/

private theorem max_max_sub (x y k : Nat) : max (max x y) (y - k) = max x y :=
  Nat.max_eq_left (Nat.le_trans (Nat.sub_le y k) (Nat.le_max_right x y))

private theorem max_max_self (x y : Nat) : max (max x y) y = max x y :=
  Nat.max_eq_left (Nat.le_max_right x y)

private theorem stepFree_cumSmall_eq (al sz : Nat) (b : FineBudget) :
    fineCumSmall (FineBudget.stepFree al sz b) = fineCumSmall b := by
  unfold FineBudget.stepFree
  dsimp only
  split
  · exact congrArg (fun x => b.cumSmallBytes + (122 * b.cumSmallGroupsS) / FineScale + 122 * x)
      (max_max_sub b.peak63Count b.live63Count 1)
  · exact congrArg (fun x => b.cumSmallBytes + (122 * b.cumSmallGroupsS) / FineScale + 122 * x)
      (max_max_self b.peak63Count b.live63Count)

private theorem stepFree_liveLarge_le (al sz : Nat) (b : FineBudget) :
    fineLiveLarge (FineBudget.stepFree al sz b) ≤ fineLiveLarge b := by
  unfold FineBudget.stepFree fineLiveLarge
  dsimp only
  split
  · exact Nat.sub_le _ _
  · exact Nat.le_refl _

private theorem stepFree_peakLarge_eq (al sz : Nat) (b : FineBudget) :
    finePeakLarge (FineBudget.stepFree al sz b) = finePeakLarge b := by
  unfold FineBudget.stepFree finePeakLarge finePeak63Bytes
  dsimp only
  split
  · exact max_max_sub b.peak63Bytes b.live63Bytes _
  · exact max_max_self b.peak63Bytes b.live63Bytes

/-- Discharges `FreeNonInc fineCostModel`: `FineBudget.stepFree al sz b` never raises
`cumSmall`, `liveLarge`, or `peakLarge` for any `al, sz : Nat` (including `al > 16`). -/
theorem fineCostModel_freeNonInc : FreeNonInc fineCostModel :=
  fun al sz b =>
    ⟨Nat.le_of_eq (stepFree_cumSmall_eq al sz b),
     stepFree_liveLarge_le al sz b,
     Nat.le_of_eq (stepFree_peakLarge_eq al sz b)⟩

/-- Concrete `PhaseCreditSpec` for bare `Heap.FreeOnlyEvs` on `fineCostModel`. -/
theorem freeOnly_fineCostModel :
    PhaseCreditSpec fineCostModel FreeOnlyEvs 0 0 0 0 :=
  PhaseCreditSpec.freeOnly fineCostModel_freeNonInc

/-- Concrete `DeallocCreditSpec` for bare `Heap.FreeOnlyEvs` on `fineCostModel`. -/
theorem deallocFreeOnly_fineCostModel :
    DeallocCreditSpec fineCostModel FreeOnlyEvs 0 :=
  DeallocCreditSpec.freeOnly fineCostModel_freeNonInc

/-! ## 2. `fineCostModel` Affine Rate Lemmas and `ModelHyps` -/

/-- Affine upper bound `≤ 2 * r + 9539` on `smallAllocCost` and `smallReallocCost` in `fineCostModel`. -/
theorem fineCostModel_smallAff :
    ∀ r ≤ HasFineReallocCredit.smallMaxReq fineCostModel,
      HasFineReallocCredit.smallAllocCost fineCostModel r ≤ 2 * r + 9539 ∧
      HasFineReallocCredit.smallReallocCost fineCostModel r ≤ 2 * r + 9539 :=
  fun r _ => ⟨smallAllocCost_le_two_mul_add r, smallReallocCost_le_two_mul_add r⟩

/-- Affine upper bound `≤ r + 8195` on `largeCost` (`sc = 63`) in `fineCostModel`. -/
theorem fineCostModel_largeAff :
    ∀ r, HasFineReallocCredit.smallMaxReq fineCostModel < r →
      HasFineReallocCredit.largeCost fineCostModel r ≤ r + 8195 :=
  fineCostModel_largeCost_le

/-- Upper bound `largeMetaCost fineCostModel ≤ 122`. -/
theorem fineCostModel_largeMetaCost_le_122 :
    HasFineReallocCredit.largeMetaCost fineCostModel ≤ 122 :=
  Nat.le_of_eq fineCostModel_largeMetaCost_eq

/-- Full `ModelHyps fineCostModel` instance. -/
theorem fineCostModel_modelHyps : ModelHyps fineCostModel where
  freeNonInc := fineCostModel_freeNonInc
  hSmallAff := fineCostModel_smallAff
  hLargeAff := fineCostModel_largeAff
  hMeta := fineCostModel_largeMetaCost_le_122
  step_alloc_small_any b hle := stepAligned_small_credit b (by decide) hle
  step_aligned_small_any b hal hle := stepAligned_small_credit b hal hle
  step_realloc_small_small_any b hal hold_le hnew_le :=
    stepRealloc_small_small_credit b hal hold_le hnew_le
  step_realloc_small_large_any b hal hold_le hnew_gt :=
    stepRealloc_small_large_credit b hal hold_le hnew_gt
  step_realloc_large_small_any b hal hold_gt hnew_le :=
    stepRealloc_large_small_credit b hal hold_gt hnew_le

/-! ## 3. One-Step `PhaseCreditSpec → FitsTrace / FitsEnv` Bridges on `fineCostModel` -/

/-- Lifts `PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq` (with `liveB ≤ peakB`)
directly to `FitsTrace fineCostModel lim (fineStepReserveOfCum maxReq 16 cumB) fullLog`. -/
theorem fitsTrace_fineCostModel_of_phaseCredit
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {cumB liveB peakB maxReq : Nat}
    (hSpec : PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq)
    (hlp : liveB ≤ peakB)
    (henf : lim.enforced = true)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq 16 cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq 16 cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq 16 cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq 16 cumB ≤ 2 ^ 48)
    {fullLog : List AllocEvent} (hEnv : Env fullLog) :
    FitsTrace fineCostModel lim (fineStepReserveOfCum maxReq 16 cumB) fullLog := by
  obtain ⟨hcum, hlive, hpeak⟩ := hSpec.evalLog_bounds hEnv
  refine fitsTrace_fineCostModel_of_bounds_autoWf
    (maxReq := maxReq) (maxAlign := 16) (cumB := cumB) (peakB := peakB)
    (fun ev hmem => ?_) henf hcum (Nat.le_trans hlive hlp) hpeak hram hva
  obtain ⟨hreq, hal⟩ := hSpec.req_align fullLog hEnv ev hmem
  exact ⟨hreq, by omega⟩

/-- Lifts `PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq` directly to initial-state
`FitsEnv fineCostModel lim fineCostModel.init Env` via `FitsEnv.of_subtrace_fitsTrace`. -/
theorem fitsEnv_fineCostModel_of_phaseCredit
    {lim : BudgetLimits} {Env : List AllocEvent → Prop}
    {cumB liveB peakB maxReq : Nat}
    (hSpec : PhaseCreditSpec fineCostModel Env cumB liveB peakB maxReq)
    (hlp : liveB ≤ peakB)
    (henf : lim.enforced = true)
    (hram : lim.staticBytes + (18686152 + cumB + peakB) +
      2 * fineStepReserveOfCum maxReq 16 cumB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes + (18686152 + cumB + peakB) +
      fineStepReserveOfCum maxReq 16 cumB +
      (lim.staticCount + fineDynIvsOfCum cumB + 16) *
        (fineStepReserveOfCum maxReq 16 cumB + PAGE_SIZE) +
      fineStepReserveOfCum maxReq 16 cumB ≤ 2 ^ 48) :
    FitsEnv fineCostModel lim fineCostModel.init Env := by
  intro evs hEnv
  have hFit := fitsTrace_fineCostModel_of_phaseCredit hSpec hlp henf hram hva hEnv
  have hSub : ∀ e, (· = evs) e → ∃ suf, evs = ([] : List AllocEvent) ++ e ++ suf := by
    rintro _ rfl
    exact ⟨[], by simp⟩
  exact FitsEnv.of_subtrace_fitsTrace hSub hFit evs rfl

/-! ## 4. Concrete Two-Phase `SeqEnv` Non-Vacuity Witness on `fineCostModel` -/

/-- Phase 1 of the non-vacuity witness: `sc = 63` `200,000` B temporary allocation (`> 135,167`)
followed in exact order by its matching deallocation. -/
def NonVacPhase1Env : List AllocEvent → Prop :=
  ConcatEnv (· = rustAllocEvents 200000 8) (· = rustDeallocEvents 200000 8)

/-- Phase 2 of the non-vacuity witness: `1,024` B small `LineWriter` allocation (`≤ 135,167`). -/
def NonVacPhase2Env : List AllocEvent → Prop :=
  (· = rustAllocEvents 1024 8)

/-- Concrete 2-phase `SeqEnv` witness (`Phase 1 ++ Phase 2` in exact call order). -/
def NonVacTwoPhaseEnv : List AllocEvent → Prop :=
  SeqEnv NonVacPhase1Env NonVacPhase2Env

/-- Concrete `1 GiB` (`physCap = 2 ^ 30`) `BudgetLimits` for the non-vacuity check. -/
def nonVacLimits : BudgetLimits where
  staticCount := 16
  staticBytes := 16 * 1024 * 1024
  physCap := 2 ^ 30
  enforced := true

/-- Non-vacuity witness trace inhabitation: `NonVacTwoPhaseEnv` admits the concrete 3-event trace
`[.alloc 200000, .free 8 200000, .alloc 1024]`. -/
theorem nonVacTwoPhaseEnv_inhabited :
    ∃ evs : List AllocEvent, NonVacTwoPhaseEnv evs ∧ evs.length = 3 := by
  refine ⟨rustAllocEvents 200000 8 ++ rustDeallocEvents 200000 8 ++ rustAllocEvents 1024 8, ?_, ?_⟩
  · exact SeqEnv.append (ConcatEnv.append rfl rfl) rfl
  · decide

/-- Concrete `PhaseCreditSpec` on `fineCostModel` for `NonVacTwoPhaseEnv`:
`Δcum = 3,628`, `Δlive = 0` (`200,000` B `sc = 63` allocation cancelled on `.free`),
`Δpeak = 208,195`, and `maxReq = 200,000`. -/
theorem nonVacTwoPhase_phaseCreditSpec :
    PhaseCreditSpec fineCostModel NonVacTwoPhaseEnv 3628 0 208195 200000 := by
  have hgt : HasFineReallocCredit.smallMaxReq fineCostModel < 200000 := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hle : 1024 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hp1_raw := PhaseCreditSpec.largeAllocFree_cancel fineCostModel (req := 200000) (al := 8)
    (by decide) hgt
  have hp1 : PhaseCreditSpec fineCostModel NonVacPhase1Env 122 0 208195 200000 := by
    refine hp1_raw.mono ?_ (Nat.le_refl 0) ?_ (Nat.le_refl 200000)
    · rw [fineCostModel_largeMetaCost_eq]
    · rw [fineCostModel_largeCost_eq]
  have hp2_raw := PhaseCreditSpec.rustAlloc_small fineCostModel (req := 1024) (al := 8)
    (by decide) (by decide) hle
  have hp2 : PhaseCreditSpec fineCostModel NonVacPhase2Env 3506 0 0 1024 :=
    hp2_raw.mono
      (smallAllocCost_le_3506_of_kyber_range (by decide) (by decide))
      (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 1024)
  exact (hp1.seq hp2).mono (by decide) (by decide) (by decide) (by decide)

/-- End-to-end `FitsEnv fineCostModel` discharge for `NonVacTwoPhaseEnv` under `nonVacLimits`
(`1 GiB` RAM cap). -/
theorem nonVacTwoPhase_fitsEnv :
    FitsEnv fineCostModel nonVacLimits fineCostModel.init NonVacTwoPhaseEnv := by
  have hstep : fineStepReserveOfCum 200000 16 3628 = 21704704 := by
    unfold fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum pageAlignUp PAGE_SIZE
    omega
  have hdyn : fineDynIvsOfCum 3628 = 316 := by
    unfold fineDynIvsOfCum fineMaxMetaAreasOfCum fineMaxGroupsOfCum
    omega
  have hsc : nonVacLimits.staticCount = 16 := rfl
  have hsb : nonVacLimits.staticBytes = 16 * 1024 * 1024 := rfl
  have hcap : nonVacLimits.physCap = 2 ^ 30 := rfl
  refine fitsEnv_fineCostModel_of_phaseCredit nonVacTwoPhase_phaseCreditSpec
    (by omega) rfl ?_ ?_
  · rw [hsb, hcap, hstep]
    omega
  · rw [hsc, hsb, hdyn, hstep]
    unfold MMAP_MIN_ADDR PAGE_SIZE
    omega

end LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
