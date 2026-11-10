/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3Defs

/-!
# Budget-Threaded `recordDeserializeOpenSpec_Q` and `RecordDeserializeEnv`

Defines the input-length-bounded deserialization allocation envelope `RecordDeserializeEnv bs`
(`DeserBoundedTotalEvs`), proves its `PhaseCreditSpec`, `1 GiB` physical RAM `FitsEnv` bound on
`fineCostModel` for inputs up to `2 MiB`, and non-vacuity witnesses, and defines parametric-envelope
`recordDeserializeOpenEnvSpec_Q` and canonical-envelope `recordDeserializeOpenSpec_Q`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DefsBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSessionApi (Session)
open CryptoVerification.LibsignalTripleRatchetRepr (SessionGhost)
open CryptoVerification.LibsignalPublicApiRepr (sessionRecordAt)
open CryptoVerification.E2E.Bin (BinCanonSession recordDeserializeStack)
open Symbolic.Swarm.TRREF.B3Defs (RecordCanonical_Q)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget FitsEnv
  rustAllocEvents rustReallocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
)
open LibsignalBinary.Heap.Fine (
  FineStepBound fineCostModel
)
open LibsignalBinary.Heap.Fine.ClientBounds (
  eventStepReq eventStepAlign
  fineMaxGroupsOfCum fineMaxMetaAreasOfCum fineDynIvsOfCum fineStepReserveOfCum
  fineCostModel_smallMaxReq_eq smallAllocCost_le_738_of_le_44
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (
  ModelHyps PhaseCreditSpec
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (
  fineCostModel_modelHyps fitsEnv_fineCostModel_of_phaseCredit nonVacLimits
)

/-! ## `DeserBoundedTotalEvs` and `RecordDeserializeEnv` -/

/-- Model-level small-bucket calibration for `DeserBoundedTotalEvs`, bundling
    `smallMaxReq M = 135167` and the `sc ≤ 2` (`r ≤ 44`) small-allocation weight cap `≤ 738`
    (discharged on `fineCostModel` by `fineCostModel_deserTinyHyps`). -/
structure DeserTinyHyps (M : AllocCostModel) [HasFineReallocCredit M] : Prop where
  smallMaxReq_eq : HasFineReallocCredit.smallMaxReq M = 135167
  tinyAlloc_le_738 : ∀ {r : Nat}, r ≤ 44 → HasFineReallocCredit.smallAllocCost M r ≤ 738

/-- Discharges `DeserTinyHyps` on `fineCostModel`. -/
theorem fineCostModel_deserTinyHyps : DeserTinyHyps fineCostModel where
  smallMaxReq_eq := fineCostModel_smallMaxReq_eq
  tinyAlloc_le_738 := smallAllocCost_le_738_of_le_44

/-- Indicator (`0` or `1`) for a tiny (`req ≤ 44`) fresh allocation event. -/
def tinyAllocStep : AllocEvent → Nat
  | .alloc req => if req ≤ 44 then 1 else 0
  | .aligned _ req => if req ≤ 44 then 1 else 0
  | .free _ _ => 0
  | .realloc _ _ _ => 0

/-- Indicator (`0` or `1`) for a non-tiny (`44 < req`) fresh allocation event. -/
def otherAllocStep : AllocEvent → Nat
  | .alloc req => if 44 < req then 1 else 0
  | .aligned _ req => if 44 < req then 1 else 0
  | .free _ _ => 0
  | .realloc _ _ _ => 0

/-- Indicator (`0` or `1`) for a `.realloc` event. -/
def reallocStep : AllocEvent → Nat
  | .realloc _ _ _ => 1
  | _ => 0

/-- Count of tiny (`req ≤ 44`) fresh allocations in `evs`. -/
def tinyAllocCount : List AllocEvent → Nat
  | [] => 0
  | ev :: evs => tinyAllocStep ev + tinyAllocCount evs

/-- Count of non-tiny (`44 < req`) fresh allocations in `evs`. -/
def otherAllocCount : List AllocEvent → Nat
  | [] => 0
  | ev :: evs => otherAllocStep ev + otherAllocCount evs

/-- Count of `.realloc` events in `evs`. -/
def reallocCount : List AllocEvent → Nat
  | [] => 0
  | ev :: evs => reallocStep ev + reallocCount evs

/-- Per-event small-class byte payload entering the `2 * r` slope of `cumSmall` (`0` on `req ≤ 44`
    fresh allocations covered by `tinyAlloc_le_738`, and `0` on `sc = 63` `> 135167` requests). -/
def deserSmallStepReq : AllocEvent → Nat
  | .alloc req => if 44 < req ∧ req ≤ 135167 then req else 0
  | .aligned _ req => if 44 < req ∧ req ≤ 135167 then req else 0
  | .free _ _ => 0
  | .realloc _ _ newSz => if newSz ≤ 135167 then newSz else 0

/-- Cumulative non-tiny small-class payload across `evs`. -/
def deserSmallTotalReq : List AllocEvent → Nat
  | [] => 0
  | ev :: evs => deserSmallStepReq ev + deserSmallTotalReq evs

/-- Cumulative step-request payload across `evs`. -/
def totalStepReq : List AllocEvent → Nat
  | [] => 0
  | ev :: evs => eventStepReq ev + totalStepReq evs

/-- Bounded deserialization allocation envelope tracking tiny (`≤ 44` B) key/seed allocations,
    larger fresh allocations, `.realloc` steps, small-class non-tiny bytes, total requested bytes,
    and per-step request/alignment bounds (`≤ maxReq`, `≤ 16`). -/
def DeserBoundedTotalEvs
    (maxTinyAllocs maxOtherAllocs maxReallocs maxSmallReq totalReq maxReq : Nat)
    (evs : List AllocEvent) : Prop :=
  tinyAllocCount evs ≤ maxTinyAllocs ∧
  otherAllocCount evs ≤ maxOtherAllocs ∧
  reallocCount evs ≤ maxReallocs ∧
  deserSmallTotalReq evs ≤ maxSmallReq ∧
  totalStepReq evs ≤ totalReq ∧
  ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16

/-- Input-length-bounded allocation envelope for `<SessionRecord>::deserialize` on canonical bytes
    `bs` (fitting under `1 GiB` RAM on `fineCostModel` for every `bs.length ≤ 2 MiB`). -/
def RecordDeserializeEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  DeserBoundedTotalEvs
    (min 12000 (bs.length / 24 + 64))
    64
    128
    (min (12 * bs.length + 4096) 2000000)
    (14 * bs.length + 4096)
    (6 * bs.length + 4096)
    evs

/-! ## `PhaseCreditSpec`, `1 GiB` `FitsEnv` bound, and non-vacuity witnesses -/

private theorem step_deser_credit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : DeserTinyHyps M) (ev : AllocEvent) (st : M.σ)
    (hal : eventStepAlign ev ≤ 16) :
    let st' := M.step ev st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st +
        (2 * deserSmallStepReq ev + 738 * tinyAllocStep ev +
          9539 * otherAllocStep ev + 9539 * reallocStep ev) ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st + 2 * eventStepReq ev ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + 2 * eventStepReq ev) := by
  cases ev with
  | free al sz =>
    obtain ⟨hc, hl, hp⟩ := hM.freeNonInc al sz st
    simp only [deserSmallStepReq, tinyAllocStep, otherAllocStep, reallocStep, eventStepReq]
    omega
  | alloc req =>
    simp only [deserSmallStepReq, tinyAllocStep, otherAllocStep, reallocStep, eventStepReq]
    by_cases h44 : req ≤ 44
    · have hgt44 : ¬ (44 < req) := by omega
      have hle : req ≤ HasFineReallocCredit.smallMaxReq M := by
        rw [hT.smallMaxReq_eq]; omega
      obtain ⟨hc, hl, hp⟩ := hM.step_alloc_small_any st hle
      have ht := hT.tinyAlloc_le_738 h44
      simp only [h44, hgt44, false_and, ↓reduceIte]
      omega
    · have hgt44 : 44 < req := by omega
      by_cases hle135 : req ≤ 135167
      · have hle : req ≤ HasFineReallocCredit.smallMaxReq M := by
          rw [hT.smallMaxReq_eq]; exact hle135
        obtain ⟨hc, hl, hp⟩ := hM.step_alloc_small_any st hle
        have hsa := hM.smallAlloc_le hle
        simp only [h44, hgt44, hle135, and_self, ↓reduceIte]
        omega
      · have hgt : HasFineReallocCredit.smallMaxReq M < req := by
          rw [hT.smallMaxReq_eq]; omega
        obtain ⟨hc, hl, hp⟩ := HasFineReallocCredit.step_alloc_large st hgt
        have hm := hM.meta_le
        have hla := hM.largeCost_le hgt
        simp only [h44, hgt44, hle135, and_false, ↓reduceIte]
        omega
  | aligned al req =>
    simp only [eventStepAlign] at hal
    simp only [deserSmallStepReq, tinyAllocStep, otherAllocStep, reallocStep, eventStepReq]
    by_cases h44 : req ≤ 44
    · have hgt44 : ¬ (44 < req) := by omega
      have hle : req ≤ HasFineReallocCredit.smallMaxReq M := by
        rw [hT.smallMaxReq_eq]; omega
      obtain ⟨hc, hl, hp⟩ := hM.step_aligned_small_any st hal hle
      have ht := hT.tinyAlloc_le_738 h44
      simp only [h44, hgt44, false_and, ↓reduceIte]
      omega
    · have hgt44 : 44 < req := by omega
      by_cases hle135 : req ≤ 135167
      · have hle : req ≤ HasFineReallocCredit.smallMaxReq M := by
          rw [hT.smallMaxReq_eq]; exact hle135
        obtain ⟨hc, hl, hp⟩ := hM.step_aligned_small_any st hal hle
        have hsa := hM.smallAlloc_le hle
        simp only [h44, hgt44, hle135, and_self, ↓reduceIte]
        omega
      · have hgt : HasFineReallocCredit.smallMaxReq M < req := by
          rw [hT.smallMaxReq_eq]; omega
        obtain ⟨hc, hl, hp⟩ := HasFineReallocCredit.step_aligned_large st hal hgt
        have hm := hM.meta_le
        have hla := hM.largeCost_le hgt
        simp only [h44, hgt44, hle135, and_false, ↓reduceIte]
        omega
  | realloc al old newSz =>
    simp only [eventStepAlign] at hal
    simp only [deserSmallStepReq, tinyAllocStep, otherAllocStep, reallocStep, eventStepReq]
    by_cases hold_le : old ≤ HasFineReallocCredit.smallMaxReq M
    · by_cases hnew135 : newSz ≤ 135167
      · have hnew_le : newSz ≤ HasFineReallocCredit.smallMaxReq M := by
          rw [hT.smallMaxReq_eq]; exact hnew135
        obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_small_any st hal hold_le hnew_le
        have hsr := hM.smallRealloc_le hnew_le
        simp only [hnew135, ↓reduceIte]
        omega
      · have hnew_gt : HasFineReallocCredit.smallMaxReq M < newSz := by
          rw [hT.smallMaxReq_eq]; omega
        obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_large_any st hal hold_le hnew_gt
        have hm := hM.meta_le
        have hla := hM.largeCost_le hnew_gt
        simp only [hnew135, ↓reduceIte]
        omega
    · have hold_gt : HasFineReallocCredit.smallMaxReq M < old := by omega
      by_cases hnew135 : newSz ≤ 135167
      · have hnew_le : newSz ≤ HasFineReallocCredit.smallMaxReq M := by
          rw [hT.smallMaxReq_eq]; exact hnew135
        obtain ⟨hc, hl, hp⟩ := hM.step_realloc_large_small_any st hal hold_gt hnew_le
        have hsr := hM.smallRealloc_le hnew_le
        simp only [hnew135, ↓reduceIte]
        omega
      · have hnew_gt : HasFineReallocCredit.smallMaxReq M < newSz := by
          rw [hT.smallMaxReq_eq]; omega
        obtain ⟨hc, hl, hp⟩ := HasFineReallocCredit.step_realloc_large_large st hal hold_gt hnew_gt
        have hm := hM.meta_le
        have hla := hM.largeCost_le hnew_gt
        simp only [hnew135, ↓reduceIte]
        omega

private theorem stepEvents_deser_credit {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : DeserTinyHyps M) :
    ∀ (evs : List AllocEvent) (st : M.σ),
      (∀ ev ∈ evs, eventStepAlign ev ≤ 16) →
      HasFineReallocCredit.cumSmall (M.stepEvents evs st) ≤
        HasFineReallocCredit.cumSmall st +
          (2 * deserSmallTotalReq evs + 738 * tinyAllocCount evs +
            9539 * otherAllocCount evs + 9539 * reallocCount evs) ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤
        HasFineReallocCredit.liveLarge st + 2 * totalStepReq evs ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤
        max (HasFineReallocCredit.peakLarge st)
          (HasFineReallocCredit.liveLarge st + 2 * totalStepReq evs)
  | [], st, _ => by
    simp only [AllocCostModel.stepEvents_nil, deserSmallTotalReq, tinyAllocCount,
      otherAllocCount, reallocCount, totalStepReq]
    omega
  | ev :: evs, st, hal => by
    simp only [AllocCostModel.stepEvents_cons, deserSmallTotalReq, tinyAllocCount,
      otherAllocCount, reallocCount, totalStepReq]
    obtain ⟨hc₁, hl₁, hp₁⟩ := step_deser_credit hM hT ev st (hal ev List.mem_cons_self)
    obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_deser_credit hM hT evs (M.step ev st)
      (fun e he => hal e (List.mem_cons_of_mem _ he))
    omega

/-- Parametric `PhaseCreditSpec` for `DeserBoundedTotalEvs`. -/
theorem deserBoundedTotalEvs_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : DeserTinyHyps M)
    (maxTinyAllocs maxOtherAllocs maxReallocs maxSmallReq totalReq maxReq : Nat) :
    PhaseCreditSpec M
      (DeserBoundedTotalEvs maxTinyAllocs maxOtherAllocs maxReallocs maxSmallReq totalReq maxReq)
      (2 * maxSmallReq + 738 * maxTinyAllocs + 9539 * maxOtherAllocs + 9539 * maxReallocs)
      (2 * totalReq)
      (2 * totalReq)
      maxReq where
  req_align _ hE := hE.2.2.2.2.2
  credit_le st0 {evs} hE := by
    obtain ⟨htiny, hother, hre, hsm, htot, hbounds⟩ := hE
    obtain ⟨hc, hl, hp⟩ := stepEvents_deser_credit hM hT evs st0
      (fun ev hev => (hbounds ev hev).2)
    omega

/-- Parametric `PhaseCreditSpec` for `RecordDeserializeEnv bs`. -/
theorem recordDeserializeEnv_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : DeserTinyHyps M) (bs : List (BitVec 8)) :
    PhaseCreditSpec M (RecordDeserializeEnv bs)
      (2 * min (12 * bs.length + 4096) 2000000 +
        738 * min 12000 (bs.length / 24 + 64) +
        9539 * 64 + 9539 * 128)
      (2 * (14 * bs.length + 4096))
      (2 * (14 * bs.length + 4096))
      (6 * bs.length + 4096) :=
  deserBoundedTotalEvs_phaseCreditSpec hM hT _ _ _ _ _ _

/-- Any serialized record `bs` up to `2 MiB` (`2 * 1024 * 1024` bytes) satisfies
    `FitsEnv fineCostModel nonVacLimits fineCostModel.init (RecordDeserializeEnv bs)`
    under a `1 GiB` (`2 ^ 30`) physical RAM cap (`≈ 466.6 MiB < 1 GiB`). -/
theorem recordDeserializeEnv_fitsEnv_of_len_le (bs : List (BitVec 8))
    (hlen : bs.length ≤ 2 * 1024 * 1024) :
    FitsEnv fineCostModel nonVacLimits fineCostModel.init (RecordDeserializeEnv bs) := by
  have hSpec : PhaseCreditSpec fineCostModel (RecordDeserializeEnv bs)
      14687488 58728448 58728448 12587008 :=
    (recordDeserializeEnv_phaseCreditSpec fineCostModel_modelHyps
      fineCostModel_deserTinyHyps bs).mono
      (by omega) (by omega) (by omega) (by omega)
  refine fitsEnv_fineCostModel_of_phaseCredit hSpec (by decide) rfl ?_ ?_
  · unfold nonVacLimits fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum pageAlignUp
      PAGE_SIZE
    decide
  · unfold nonVacLimits fineStepReserveOfCum FineStepBound fineMaxMetaAreasOfCum fineDynIvsOfCum
      fineMaxGroupsOfCum pageAlignUp MMAP_MIN_ADDR PAGE_SIZE
    decide

/-- Non-empty 3-event trace exercising tiny key allocation (`33` B), `Vec<Chain>` initial
    allocation (`416` B), and `Vec<Chain>` reallocation (`416 → 832` B) inside
    `RecordDeserializeEnv bs` for every `bs`. -/
theorem recordDeserializeEnv_inhabited (bs : List (BitVec 8)) :
    RecordDeserializeEnv bs
      (rustAllocEvents 33 1 ++ rustAllocEvents 416 8 ++ rustReallocEvents 416 832 8) := by
  have hevs :
      rustAllocEvents 33 1 ++ rustAllocEvents 416 8 ++ rustReallocEvents 416 832 8 =
        [.alloc 33, .alloc 416, .realloc 8 416 832] := by
    decide
  rw [hevs]
  unfold RecordDeserializeEnv DeserBoundedTotalEvs
  have h1 : tinyAllocCount [.alloc 33, .alloc 416, .realloc 8 416 832] = 1 := by decide
  have h2 : otherAllocCount [.alloc 33, .alloc 416, .realloc 8 416 832] = 1 := by decide
  have h3 : reallocCount [.alloc 33, .alloc 416, .realloc 8 416 832] = 1 := by decide
  have h4 : deserSmallTotalReq [.alloc 33, .alloc 416, .realloc 8 416 832] = 1248 := by decide
  have h5 : totalStepReq [.alloc 33, .alloc 416, .realloc 8 416 832] = 1281 := by decide
  rw [h1, h2, h3, h4, h5]
  refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
  intro ev hev
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
  rcases hev with rfl | rfl | rfl <;> simp only [eventStepReq, eventStepAlign] <;> omega

/-- Non-vacuity witness for `RecordDeserializeEnv` on a concrete non-empty `128`-byte input slice
under `nonVacLimits` (`1 GiB` RAM cap, `enforced = true`). -/
theorem recordDeserializeEnv_fitsEnv_witness :
    FitsEnv fineCostModel nonVacLimits fineCostModel.init
      (RecordDeserializeEnv (List.replicate 128 0#8)) :=
  recordDeserializeEnv_fitsEnv_of_len_le (List.replicate 128 0#8)
    (by rw [List.length_replicate]; decide)

/-! ## Parametric-envelope and canonical-envelope `recordDeserializeOpenSpec_Q` -/

/-- Parametric-envelope budget-threaded `recordDeserializeOpenSpec_Q` (`onPanic = ⌜False⌝`,
    `onOom = ⌜False⌝`). -/
def recordDeserializeOpenEnvSpec_Q (Q : List (BitVec 8) → Prop)
    (Env : List (BitVec 8) → Session (List (BitVec 8)) → List AllocEvent → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × List (BitVec 8) × BitVec 64 × Session (List (BitVec 8))) × M.σ) where
  pre := fun ((ptr, bs, out, sess), st) s =>
    ⌜s.readReg64 .x0 = ptr ∧ (s.readReg64 .x1).toNat = bs.length ∧
      s.readReg64 .x8 = out ∧ RecordCanonical_Q Q bs sess ∧
      FitsEnv M lim st (Env bs sess)⌝ ∗
      (ptr ↦ₛ bs) ∗ memRegion out 0x170 ∗ A.pool lim st s ∗
      stackAt s.sp recordDeserializeStack
  post := fun ((ptr, bs, out, sess), st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env bs sess evs⌝ ∗ (ptr ↦ₛ bs) ∗
        (∃∗ G : SessionGhost, ⌜BinCanonSession G sess⌝ ∗
          sessionRecordAt A.repAlloc out ⟨0#64, 8#64, some G⟩ ⟨some sess⟩) ∗
        A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp recordDeserializeStack

/-- Budget-threaded `recordDeserializeOpenSpec_Q` specialized to `RecordDeserializeEnv`. -/
abbrev recordDeserializeOpenSpec_Q (Q : List (BitVec 8) → Prop)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × List (BitVec 8) × BitVec 64 × Session (List (BitVec 8))) × M.σ) :=
  recordDeserializeOpenEnvSpec_Q Q (fun bs _ => RecordDeserializeEnv bs) M A lim

end LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DefsBudget
