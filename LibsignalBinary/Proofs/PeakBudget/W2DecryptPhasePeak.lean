/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptLeavesPeak
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCmkDhPeak
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak

/-!
# W2 `message_decrypt` `PhaseCreditSpec` and `DeallocCreditSpec` Combinators

Lifts symbolic `[HasFineReallocCredit M]` step bounds into `PhaseCreditSpec M` and `DeallocCreditSpec M`
combinators for W2 `message_decrypt`: bounded event-list envelopes (`BoundedNonFreeEvs`, `BoundedLenEvs`),
Segments `S3`/`S4`/`S7`/`S8`/`S9`, multi-buffer `SessionClone` deallocation cancellation, and the
`≤ n`-session `TrialLoopEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak

open LibsignalBinary.Heap (
  AllocCostModel AllocEvent SeqEnv FreeOnlyEvs
  rustAllocEvents rustDeallocEvents rustReallocEvents
)
open LibsignalBinary.Heap.Fine.ClientBounds (
  eventStepReq eventStepAlign
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
  stepEvents_rustAlloc_small stepEvents_rustAlloc_large
  stepEvents_rustDealloc_small stepEvents_rustDealloc_large
  stepEvents_rustRealloc_small_small stepEvents_rustRealloc_small_large
  stepEvents_rustRealloc_large_large
)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (
  ConcatEnv IterSeqEnv IterConcatEnv
  FreeNonInc ModelHyps PhaseCreditSpec DeallocCreditSpec
)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptLeavesPeak (
  singleAllocCum singleAllocLarge
)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCmkDhPeak (
  growOne104Evs v104Live v104GrowStepCum
  stepEvents_growOne104_zero stepEvents_growOne104_pos
  stepEvents_dhCommitStep12_small stepEvents_dhCommitStep3_smallCap
  v104TowerCum2048 v104CapSeq v104TowerPeak
  cmkJumpListEvs cmkJumpFinalIdx stepEvents_cmk_jump_list_le_2000
)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak (
  computeMacEvs stepEvents_computeMac_small
  vmacEvs stepEvents_vmac_small
  s7CoreEvs stepEvents_s7Core_small
  optDeallocListEvs optDeallocListLarge stepEvents_optDeallocList_cancel
)

/-! ## 1. Bounded Event-List `PhaseCreditSpec` -/

theorem req_align_rustAlloc_le {req al maxReq : Nat} (hreq : req ≤ maxReq) (hal : al ≤ 16) :
    ∀ ev ∈ rustAllocEvents req al, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  unfold rustAllocEvents
  split <;> intro ev hev <;> rw [List.mem_singleton] at hev <;> subst hev <;>
    simp only [eventStepReq, eventStepAlign] <;> omega

theorem req_align_rustDealloc_le (req al maxReq : Nat) :
    ∀ ev ∈ rustDeallocEvents req al, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  intro ev hev
  unfold rustDeallocEvents at hev
  rw [List.mem_singleton] at hev
  subst hev
  exact ⟨Nat.zero_le maxReq, Nat.le_refl 16⟩

theorem req_align_rustRealloc_le {old new al maxReq : Nat}
    (hal : al ≤ 16) (hal_new : al ≤ new) (hnew : new ≤ maxReq) :
    ∀ ev ∈ rustReallocEvents old new al, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  unfold rustReallocEvents
  simp only [hal, hal_new, and_self, ↓reduceIte]
  intro ev hev
  rw [List.mem_singleton] at hev
  subst hev
  exact ⟨hnew, hal⟩

def isNonFreeEv : AllocEvent → Bool
  | .free _ _ => false
  | _ => true

/-- Envelope of event lists of total length `≤ maxLen` containing at most `k` non-`.free` events,
with per-event `eventStepReq ≤ maxReq`, `eventStepAlign ≤ 16`. -/
def BoundedNonFreeEvs (k maxLen maxReq : Nat) (evs : List AllocEvent) : Prop :=
  evs.length ≤ maxLen ∧
  (evs.filter isNonFreeEv).length ≤ k ∧
  ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16

/-- Envelope of event lists of total length `≤ k` with `eventStepReq ≤ maxReq`, `eventStepAlign ≤ 16`. -/
def BoundedLenEvs (k maxReq : Nat) (evs : List AllocEvent) : Prop :=
  evs.length ≤ k ∧
  ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16

theorem BoundedLenEvs.toBoundedNonFreeEvs {k maxReq : Nat} {evs : List AllocEvent}
    (h : BoundedLenEvs k maxReq evs) :
    BoundedNonFreeEvs k k maxReq evs :=
  ⟨h.1, Nat.le_trans (List.length_filter_le isNonFreeEv evs) h.1, h.2⟩

theorem step_small_or_free_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {ev : AllocEvent} {maxReq : Nat} (st : M.σ)
    (hsmall : maxReq ≤ HasFineReallocCredit.smallMaxReq M)
    (hreq : eventStepReq ev ≤ maxReq) (hal : eventStepAlign ev ≤ 16) :
    let st' := M.step ev st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st +
        (if isNonFreeEv ev then 2 * maxReq + 9539 else 0) ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  cases ev with
  | free al sz =>
    simp only [isNonFreeEv]
    obtain ⟨hc, hl, hp⟩ := hM.freeNonInc al sz st
    exact ⟨by omega, hl, hp⟩
  | alloc req =>
    simp only [isNonFreeEv, ↓reduceIte, eventStepReq] at hreq ⊢
    have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hsmall
    obtain ⟨hc, hl, hp⟩ := hM.step_alloc_small_any st hle
    have hsa := hM.smallAlloc_le hle
    exact ⟨by omega, hl, hp⟩
  | aligned al req =>
    simp only [isNonFreeEv, ↓reduceIte, eventStepReq, eventStepAlign] at hreq hal ⊢
    have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hsmall
    obtain ⟨hc, hl, hp⟩ := hM.step_aligned_small_any st hal hle
    have hsa := hM.smallAlloc_le hle
    exact ⟨by omega, hl, hp⟩
  | realloc al old new =>
    simp only [isNonFreeEv, ↓reduceIte, eventStepReq, eventStepAlign] at hreq hal ⊢
    have hnew_le : new ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hsmall
    have hsr := hM.smallRealloc_le hnew_le
    by_cases hold_le : old ≤ HasFineReallocCredit.smallMaxReq M
    · obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_small_any st hal hold_le hnew_le
      exact ⟨by omega, hl, hp⟩
    · have hold_gt : HasFineReallocCredit.smallMaxReq M < old := by omega
      obtain ⟨hc, hl, hp⟩ := hM.step_realloc_large_small_any st hal hold_gt hnew_le
      exact ⟨by omega, by omega, hp⟩

private theorem stepEvents_boundedNonFree_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {maxReq : Nat} (hsmall : maxReq ≤ HasFineReallocCredit.smallMaxReq M) :
    ∀ (evs : List AllocEvent) (st : M.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      let st' := M.stepEvents evs st
      HasFineReallocCredit.cumSmall st' ≤
        HasFineReallocCredit.cumSmall st +
          (evs.filter isNonFreeEv).length * (2 * maxReq + 9539) ∧
      HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
      HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st
  | [], st, _ => by
    simp only [AllocCostModel.stepEvents_nil, List.filter_nil, List.length_nil,
      Nat.zero_mul, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | ev :: rest, st, hall => by
    obtain ⟨hreq, hal⟩ := hall ev List.mem_cons_self
    obtain ⟨hc1, hl1, hp1⟩ := step_small_or_free_aff hM st hsmall hreq hal
    obtain ⟨hc2, hl2, hp2⟩ := stepEvents_boundedNonFree_small hM hsmall rest (M.step ev st)
      (fun e he => hall e (List.mem_cons_of_mem ev he))
    simp only [AllocCostModel.stepEvents_cons, List.filter_cons]
    cases hnf : isNonFreeEv ev
    · simp only [hnf, Bool.false_eq_true, ↓reduceIte] at hc1 ⊢
      exact ⟨by omega, by omega, by omega⟩
    · simp only [hnf, ↓reduceIte, List.length_cons] at hc1 ⊢
      have hmul : ((rest.filter isNonFreeEv).length + 1) * (2 * maxReq + 9539) =
          (rest.filter isNonFreeEv).length * (2 * maxReq + 9539) + (2 * maxReq + 9539) :=
        Nat.succ_mul _ _
      exact ⟨by omega, by omega, by omega⟩

theorem phaseCreditSpec_boundedNonFree_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {k maxLen maxReq : Nat}
    (hsmall : maxReq ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (BoundedNonFreeEvs k maxLen maxReq)
      (k * (2 * maxReq + 9539)) 0 0 maxReq where
  req_align _ h := h.2.2
  credit_le st0 {evs} h := by
    obtain ⟨hc, hl, hp⟩ := stepEvents_boundedNonFree_small hM hsmall evs st0 h.2.2
    have hmul : (evs.filter isNonFreeEv).length * (2 * maxReq + 9539) ≤
        k * (2 * maxReq + 9539) :=
      Nat.mul_le_mul_right _ h.2.1
    omega

theorem phaseCreditSpec_boundedLen_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {k maxReq : Nat}
    (hsmall : maxReq ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (BoundedLenEvs k maxReq)
      (k * (2 * maxReq + 9539)) 0 0 maxReq :=
  (phaseCreditSpec_boundedNonFree_small hM hsmall).of_imp fun _ =>
    BoundedLenEvs.toBoundedNonFreeEvs

private theorem stepEvents_boundedNonFree_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {maxReq : Nat} :
    ∀ (evs : List AllocEvent) (st : M.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16) →
      let n := (evs.filter isNonFreeEv).length
      let st' := M.stepEvents evs st
      HasFineReallocCredit.cumSmall st' ≤
        HasFineReallocCredit.cumSmall st + n * (2 * maxReq + 9539) ∧
      HasFineReallocCredit.liveLarge st' ≤
        HasFineReallocCredit.liveLarge st + n * (maxReq + 8195) ∧
      HasFineReallocCredit.peakLarge st' ≤
        max (HasFineReallocCredit.peakLarge st)
          (HasFineReallocCredit.liveLarge st + n * (maxReq + 8195))
  | [], st, _ => by
    simp only [AllocCostModel.stepEvents_nil, List.filter_nil, List.length_nil,
      Nat.zero_mul, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _⟩
  | ev :: rest, st, hall => by
    obtain ⟨hreq, hal⟩ := hall ev List.mem_cons_self
    simp only [AllocCostModel.stepEvents_cons, List.filter_cons]
    cases hnf : isNonFreeEv ev
    · cases ev with
      | free al sz =>
        simp only [↓reduceIte, Bool.false_eq_true]
        obtain ⟨hc1, hl1, hp1⟩ := hM.freeNonInc al sz st
        obtain ⟨hc2, hl2, hp2⟩ := stepEvents_boundedNonFree_aff hM rest (M.step (.free al sz) st)
          (fun e he => hall e (List.mem_cons_of_mem _ he))
        exact ⟨by omega, by omega, by omega⟩
      | alloc _ | aligned _ _ | realloc _ _ _ =>
        simp [isNonFreeEv] at hnf
    · simp only [↓reduceIte, List.length_cons]
      obtain ⟨hc1, hl1, hp1⟩ := hM.step_nonFree_aff st hreq hal
      obtain ⟨hc2, hl2, hp2⟩ := stepEvents_boundedNonFree_aff hM rest (M.step ev st)
        (fun e he => hall e (List.mem_cons_of_mem ev he))
      have hmul1 : ((rest.filter isNonFreeEv).length + 1) * (2 * maxReq + 9539) =
          (rest.filter isNonFreeEv).length * (2 * maxReq + 9539) + (2 * maxReq + 9539) :=
        Nat.succ_mul _ _
      have hmul2 : ((rest.filter isNonFreeEv).length + 1) * (maxReq + 8195) =
          (rest.filter isNonFreeEv).length * (maxReq + 8195) + (maxReq + 8195) :=
        Nat.succ_mul _ _
      exact ⟨by omega, by omega, by omega⟩

theorem phaseCreditSpec_boundedNonFree_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (k maxLen maxReq : Nat) :
    PhaseCreditSpec M (BoundedNonFreeEvs k maxLen maxReq)
      (k * (2 * maxReq + 9539))
      (k * (maxReq + 8195))
      (k * (maxReq + 8195))
      maxReq where
  req_align _ h := h.2.2
  credit_le st0 {evs} h := by
    obtain ⟨hc, hl, hp⟩ := stepEvents_boundedNonFree_aff hM evs st0 h.2.2
    have hcmul : (evs.filter isNonFreeEv).length * (2 * maxReq + 9539) ≤
        k * (2 * maxReq + 9539) := Nat.mul_le_mul_right _ h.2.1
    have hlmul : (evs.filter isNonFreeEv).length * (maxReq + 8195) ≤
        k * (maxReq + 8195) := Nat.mul_le_mul_right _ h.2.1
    omega

theorem phaseCreditSpec_boundedLen_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (k maxReq : Nat) :
    PhaseCreditSpec M (BoundedLenEvs k maxReq)
      (k * (2 * maxReq + 9539))
      (k * (maxReq + 8195))
      (k * (maxReq + 8195))
      maxReq :=
  (phaseCreditSpec_boundedNonFree_aff hM k k maxReq).of_imp fun _ =>
    BoundedLenEvs.toBoundedNonFreeEvs

/-- Bounded W2 Segment 9 `apply_to_session_state` envelope (`≤ 6` small `≤ 34 B` allocations
surrounded by `.free` events). -/
def TrApplyBoundedEnv : List AllocEvent → Prop :=
  SeqEnv FreeOnlyEvs (SeqEnv (BoundedLenEvs 6 34) FreeOnlyEvs)

theorem phaseCreditSpec_trApplyBounded {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hsmall34 : 34 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M TrApplyBoundedEnv (6 * (2 * 34 + 9539)) 0 0 34 := by
  have hf := PhaseCreditSpec.freeOnly_of_hyps hM
  have hb := phaseCreditSpec_boundedLen_small hM (k := 6) hsmall34
  simpa [TrApplyBoundedEnv] using hf.seq (hb.seq hf)

/-! ## 2. W2 Segments `S3`, `S4`, `S7`, `S8` as `PhaseCreditSpec M` -/

def dhCommitStep12Evs : List AllocEvent :=
  rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++ rustAllocEvents 32 1

theorem phaseCreditSpec_dhCommitStep12 (M : AllocCostModel) [HasFineReallocCredit M]
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = dhCommitStep12Evs)
      (2 * HasFineReallocCredit.smallAllocCost M 33 +
        HasFineReallocCredit.smallAllocCost M 32)
      0 0 33 where
  req_align := by
    rintro _ rfl ev hev
    unfold dhCommitStep12Evs at hev
    simp only [List.mem_append] at hev
    rcases hev with (he | he) | he
    · exact req_align_rustAlloc_le (Nat.le_refl 33) (by decide) ev he
    · exact req_align_rustAlloc_le (Nat.le_refl 33) (by decide) ev he
    · exact req_align_rustAlloc_le (by decide) (by decide) ev he
  credit_le := by
    rintro st0 _ rfl
    unfold dhCommitStep12Evs
    obtain ⟨hc, hl, hp⟩ := stepEvents_dhCommitStep12_small M st0 h33
    omega

def dhCommitStep3Evs (cap : Nat) (needGrow : Bool) : List AllocEvent :=
  (if needGrow then growOne104Evs cap else []) ++ rustDeallocEvents 33 1

theorem req_align_growOne104 {c maxOldCap : Nat} (hc : c ≤ maxOldCap) :
    ∀ ev ∈ growOne104Evs c,
      eventStepReq ev ≤ max 416 (104 * (2 * maxOldCap)) ∧ eventStepAlign ev ≤ 16 := by
  unfold growOne104Evs
  split
  · exact req_align_rustAlloc_le (Nat.le_max_left _ _) (by decide)
  · rename_i hne
    have hpos : 0 < c := Nat.pos_of_ne_zero hne
    have hnew : 104 * (2 * c) ≤ max 416 (104 * (2 * maxOldCap)) :=
      Nat.le_trans (by omega) (Nat.le_max_right 416 _)
    exact req_align_rustRealloc_le (by decide) (by omega) hnew

theorem phaseCreditSpec_dhCommitStep3_smallCap (M : AllocCostModel) [HasFineReallocCredit M]
    {cap : Nat} {needGrow : Bool}
    (hcap_small : 104 * max 4 (2 * cap) ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = dhCommitStep3Evs cap needGrow)
      (if needGrow then v104GrowStepCum M cap else 0)
      0 0 (max 416 (104 * (2 * cap))) where
  req_align := by
    rintro _ rfl ev hev
    unfold dhCommitStep3Evs at hev
    simp only [List.mem_append] at hev
    rcases hev with he | he
    · split at he
      · exact req_align_growOne104 (Nat.le_refl cap) ev he
      · nomatch he
    · exact req_align_rustDealloc_le 33 1 _ ev he
  credit_le := by
    rintro st0 _ rfl
    unfold dhCommitStep3Evs
    obtain ⟨hc, hl, hp⟩ := stepEvents_dhCommitStep3_smallCap M (cap := cap)
      (needGrow := needGrow) st0 hcap_small
    omega

private theorem le_cmkJumpFinalIdx : ∀ (jumps : List (Bool × Bool)) (k : Nat),
    k ≤ cmkJumpFinalIdx k jumps
  | [], k => Nat.le_refl k
  | (needGrow, _) :: rest, k => by
    simp only [cmkJumpFinalIdx]
    have h := le_cmkJumpFinalIdx rest (if needGrow then k + 1 else k)
    cases needGrow
    · simpa using h
    · simp only [↓reduceIte] at h ⊢
      omega

private theorem v104CapSeq_le_1024 {k : Nat} (hk : k ≤ 9) : v104CapSeq k ≤ 1024 := by
  cases k with
  | zero => simp [v104CapSeq]
  | succ j =>
    simp only [v104CapSeq]
    have hj : j ≤ 8 := by omega
    have hp : 2 ^ j ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hj
    omega

theorem req_align_cmkJumpList :
    ∀ (jumps : List (Bool × Bool)) (k : Nat),
      cmkJumpFinalIdx k jumps ≤ 10 →
      ∀ ev ∈ cmkJumpListEvs k jumps,
        eventStepReq ev ≤ 212992 ∧ eventStepAlign ev ≤ 16
  | [], _, _, ev, hev => nomatch hev
  | (needGrow, needEvictFree) :: rest, k, hkf, ev, hev => by
    simp only [cmkJumpListEvs, List.mem_append] at hev
    simp only [cmkJumpFinalIdx] at hkf
    rcases hev with ((he | he) | he) | he
    · exact req_align_rustAlloc_le (by decide) (by decide) ev he
    · cases needGrow
      · simp only [Bool.false_eq_true, ↓reduceIte] at he
        nomatch he
      · simp only [↓reduceIte] at he hkf
        have hk1 : k + 1 ≤ cmkJumpFinalIdx (k + 1) rest := le_cmkJumpFinalIdx rest (k + 1)
        have hk9 : k ≤ 9 := by omega
        obtain ⟨hr, ha⟩ := req_align_growOne104 (v104CapSeq_le_1024 hk9) ev he
        exact ⟨Nat.le_trans hr (by decide), ha⟩
    · cases needEvictFree
      · simp only [Bool.false_eq_true, ↓reduceIte] at he
        nomatch he
      · simp only [↓reduceIte] at he
        exact req_align_rustDealloc_le 33 1 212992 ev he
    · exact req_align_cmkJumpList rest (if needGrow then k + 1 else k) hkf ev he

/-- `PhaseCreditSpec` for the `CMK ≤ 2000` tower jump-list (`cap₀ = 0` → `≤ 2048`). -/
theorem phaseCreditSpec_cmkJumpList_tower (M : AllocCostModel) [HasFineReallocCredit M]
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M)
    (jumps : List (Bool × Bool))
    (hlen : jumps.length ≤ 2000)
    (hkf : cmkJumpFinalIdx 0 jumps ≤ 10) :
    PhaseCreditSpec M (· = cmkJumpListEvs 0 jumps)
      (2000 * HasFineReallocCredit.smallAllocCost M 33 + v104TowerCum2048 M)
      (v104TowerPeak M 10)
      (v104TowerPeak M 10)
      212992 where
  req_align := by
    rintro _ rfl
    exact req_align_cmkJumpList jumps 0 hkf
  credit_le := by
    rintro st0 _ rfl
    exact stepEvents_cmk_jump_list_le_2000 M h33 st0 hlen rfl hkf

theorem v104Live_le_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (c : Nat) :
    v104Live M c ≤ 104 * c + 8195 := by
  unfold v104Live
  split
  · exact Nat.zero_le _
  · rename_i hnot
    have hgt : HasFineReallocCredit.smallMaxReq M < 104 * c := Nat.lt_of_not_ge hnot
    exact hM.largeCost_le hgt

theorem v104GrowStepCum_le_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (c : Nat) :
    v104GrowStepCum M c ≤ 2 * (104 * (if c = 0 then 4 else 2 * c)) + 9539 := by
  unfold v104GrowStepCum singleAllocCum
  have hm := hM.meta_le
  by_cases hc0 : c = 0
  · subst hc0
    simp only [↓reduceIte]
    split
    · rename_i hle
      exact hM.smallAlloc_le hle
    · omega
  · simp only [hc0, ↓reduceIte]
    split
    · rename_i hle
      exact hM.smallRealloc_le hle
    · omega

/-- First-step `growOne104Evs c₀` bound from an arbitrary pre-state `st0`, crediting the new capacity
`c₁ = if c₀ = 0 then 4 else 2 * c₀` so subsequent doublings cancel telescopically. -/
theorem stepEvents_growOne104_first (M : AllocCostModel) [HasFineReallocCredit M]
    {L₀ : Nat} (c₀ : Nat) (st0 : M.σ)
    (hlive : HasFineReallocCredit.liveLarge st0 ≤ L₀) :
    let c₁ := if c₀ = 0 then 4 else 2 * c₀
    let st1 := M.stepEvents (growOne104Evs c₀) st0
    HasFineReallocCredit.cumSmall st1 ≤
      HasFineReallocCredit.cumSmall st0 + v104GrowStepCum M c₀ ∧
    HasFineReallocCredit.liveLarge st1 ≤ L₀ + v104Live M c₁ ∧
    HasFineReallocCredit.peakLarge st1 ≤
      max (HasFineReallocCredit.peakLarge st0) (L₀ + v104Live M c₁) := by
  by_cases hc0 : c₀ = 0
  · subst hc0
    exact stepEvents_growOne104_zero M st0 hlive
  · have hc_pos : 0 < c₀ := Nat.pos_of_ne_zero hc0
    dsimp only
    simp only [hc0, ↓reduceIte]
    unfold growOne104Evs v104GrowStepCum v104Live
    simp only [hc0, ↓reduceIte]
    by_cases hold_le : 104 * c₀ ≤ HasFineReallocCredit.smallMaxReq M
    · by_cases hnew_le : 104 * (2 * c₀) ≤ HasFineReallocCredit.smallMaxReq M
      · simp only [hnew_le, ↓reduceIte]
        obtain ⟨hc, hl, hp⟩ := stepEvents_rustRealloc_small_small M
          (old := 104 * c₀) (new := 104 * (2 * c₀)) (al := 8) st0
          (by decide) (by omega) (by omega) hold_le (by omega) hnew_le
        exact ⟨hc, by omega, by omega⟩
      · have hnew_gt : HasFineReallocCredit.smallMaxReq M < 104 * (2 * c₀) := Nat.lt_of_not_ge hnew_le
        simp only [hnew_le, ↓reduceIte]
        obtain ⟨hc, hl, hp⟩ := stepEvents_rustRealloc_small_large M
          (old := 104 * c₀) (new := 104 * (2 * c₀)) (al := 8) st0
          (by decide) (by omega) (by omega) hold_le hnew_gt
        exact ⟨hc, by omega, by omega⟩
    · have hold_gt : HasFineReallocCredit.smallMaxReq M < 104 * c₀ := Nat.lt_of_not_ge hold_le
      have hnew_gt : HasFineReallocCredit.smallMaxReq M < 104 * (2 * c₀) := by omega
      have hnew_not_le : ¬ (104 * (2 * c₀) ≤ HasFineReallocCredit.smallMaxReq M) := by omega
      simp only [hnew_not_le, ↓reduceIte]
      obtain ⟨hc, hl, hp⟩ := stepEvents_rustRealloc_large_large M
        (old := 104 * c₀) (new := 104 * (2 * c₀)) (al := 8) st0
        (by decide) (by omega) hold_gt hnew_gt
      exact ⟨hc, by omega, by omega⟩

/-- `Vec<104>` doubling chain starting from an arbitrary initial capacity `c₀`, with every growth at `c ≤ maxOldCap`.
-/
def DoublingChainLe (maxOldCap : Nat) : List Nat → Prop
  | [] => True
  | [c] => c ≤ maxOldCap
  | c₁ :: c₂ :: rest =>
    c₁ ≤ maxOldCap ∧ c₂ = (if c₁ = 0 then 4 else 2 * c₁) ∧ DoublingChainLe maxOldCap (c₂ :: rest)

private def DoublingTailPred (maxOldCap c_cur : Nat) : List Nat → Prop
  | [] => True
  | c_next :: rest => c_next = c_cur ∧ DoublingChainLe maxOldCap (c_next :: rest)

def doublingChain104Evs : List Nat → List AllocEvent
  | [] => []
  | c :: rest => growOne104Evs c ++ doublingChain104Evs rest

private theorem stepEvents_doublingTail104 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {maxOldCap L₀ : Nat} :
    ∀ (rest : List Nat) (c_cur : Nat) (st : M.σ),
      0 < c_cur →
      c_cur ≤ max 4 (2 * maxOldCap) →
      DoublingTailPred maxOldCap c_cur rest →
      HasFineReallocCredit.liveLarge st ≤ L₀ + v104Live M c_cur →
      let st' := M.stepEvents (doublingChain104Evs rest) st
      HasFineReallocCredit.cumSmall st' ≤
        HasFineReallocCredit.cumSmall st +
          rest.length * (2 * (104 * max 4 (2 * maxOldCap)) + 9539) ∧
      HasFineReallocCredit.liveLarge st' ≤
        L₀ + (104 * max 4 (2 * maxOldCap) + 8195) ∧
      HasFineReallocCredit.peakLarge st' ≤
        max (HasFineReallocCredit.peakLarge st)
          (L₀ + (104 * maxOldCap + 8195) + (104 * max 4 (2 * maxOldCap) + 8195))
  | [], c_cur, st, _, hcur_le, _, hlive => by
    simp only [doublingChain104Evs, AllocCostModel.stepEvents_nil, List.length_nil,
      Nat.zero_mul, Nat.add_zero]
    have haff := v104Live_le_aff hM c_cur
    exact ⟨Nat.le_refl _, by omega, Nat.le_max_left _ _⟩
  | [c], c_cur, st, hcur_pos, _, hchain, hlive => by
    dsimp only [DoublingTailPred, DoublingChainLe] at hchain
    obtain ⟨rfl, hc_le⟩ := hchain
    simp only [doublingChain104Evs, List.length_singleton, Nat.one_mul, List.append_nil]
    obtain ⟨hc1, hl1, hp1⟩ := stepEvents_growOne104_pos M st hcur_pos hlive
    have hcum_aff := v104GrowStepCum_le_aff hM c
    have hc_nz : c ≠ 0 := Nat.ne_of_gt hcur_pos
    simp only [hc_nz, ↓reduceIte] at hcum_aff
    have hlive_old := v104Live_le_aff hM c
    have hlive_new := v104Live_le_aff hM (2 * c)
    have h2c_le : 2 * c ≤ max 4 (2 * maxOldCap) :=
      Nat.le_trans (by omega) (Nat.le_max_right 4 (2 * maxOldCap))
    exact ⟨by omega, by omega, by omega⟩
  | c₁ :: c₂ :: rest, c_cur, st, hcur_pos, _, hchain, hlive => by
    dsimp only [DoublingTailPred, DoublingChainLe] at hchain
    obtain ⟨rfl, hc1_le, hc2_eq, hrest⟩ := hchain
    have hc1_nz : c₁ ≠ 0 := Nat.ne_of_gt hcur_pos
    simp only [hc1_nz, ↓reduceIte] at hc2_eq
    dsimp only
    rw [show doublingChain104Evs (c₁ :: c₂ :: rest) =
          growOne104Evs c₁ ++ doublingChain104Evs (c₂ :: rest) from rfl,
        show (c₁ :: c₂ :: rest).length = (c₂ :: rest).length + 1 from rfl,
        M.stepEvents_append]
    obtain ⟨hc1, hl1, hp1⟩ := stepEvents_growOne104_pos M st hcur_pos hlive
    have hc2_pos : 0 < c₂ := by omega
    have hc2_le : c₂ ≤ max 4 (2 * maxOldCap) :=
      Nat.le_trans (by omega) (Nat.le_max_right 4 (2 * maxOldCap))
    rw [← hc2_eq] at hl1
    obtain ⟨hc2, hl2, hp2⟩ := stepEvents_doublingTail104 hM (c₂ :: rest) c₂
      (M.stepEvents (growOne104Evs c₁) st) hc2_pos hc2_le ⟨rfl, hrest⟩ hl1
    have hcum_aff := v104GrowStepCum_le_aff hM c₁
    simp only [hc1_nz, ↓reduceIte] at hcum_aff
    have hlive_old := v104Live_le_aff hM c₁
    have hlive_new := v104Live_le_aff hM (2 * c₁)
    have h2c1_le : 2 * c₁ ≤ max 4 (2 * maxOldCap) := hc2_eq ▸ hc2_le
    have hmul : ((c₂ :: rest).length + 1) * (2 * (104 * max 4 (2 * maxOldCap)) + 9539) =
        (c₂ :: rest).length * (2 * (104 * max 4 (2 * maxOldCap)) + 9539) +
          (2 * (104 * max 4 (2 * maxOldCap)) + 9539) :=
      Nat.succ_mul _ _
    exact ⟨by omega, hl2, by omega⟩

/-- `PhaseCreditSpec` for any `Vec<104>` doubling chain `caps` (`caps.length ≤ maxSteps`, `DoublingChainLe maxOldCap caps`).
-/
theorem phaseCreditSpec_doublingChain104 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (maxSteps maxOldCap : Nat) :
    PhaseCreditSpec M
      (fun evs => ∃ caps : List Nat,
        caps.length ≤ maxSteps ∧ DoublingChainLe maxOldCap caps ∧ evs = doublingChain104Evs caps)
      (maxSteps * (2 * (104 * max 4 (2 * maxOldCap)) + 9539))
      (104 * max 4 (2 * maxOldCap) + 8195)
      ((104 * maxOldCap + 8195) + (104 * max 4 (2 * maxOldCap) + 8195))
      (max 416 (104 * (2 * maxOldCap))) where
  req_align := by
    rintro _ ⟨caps, -, hchain, rfl⟩ ev hev
    induction caps with
    | nil => nomatch hev
    | cons c rest ih =>
      simp only [doublingChain104Evs, List.mem_append] at hev
      have hc_le : c ≤ maxOldCap := by
        cases rest with
        | nil => exact hchain
        | cons c₂ r => exact hchain.1
      rcases hev with he | he
      · exact req_align_growOne104 hc_le ev he
      · cases rest with
        | nil => nomatch he
        | cons c₂ r => exact ih hchain.2.2 he
  credit_le := by
    rintro st0 _ ⟨caps, hlen, hchain, rfl⟩
    cases caps with
    | nil =>
      simp only [doublingChain104Evs, AllocCostModel.stepEvents_nil]
      omega
    | cons c₀ rest =>
      simp only [doublingChain104Evs]
      rw [M.stepEvents_append]
      have hc0_le : c₀ ≤ maxOldCap := by
        cases rest with
        | nil => simpa [DoublingChainLe] using hchain
        | cons _ _ => exact hchain.1
      have hc1_pos : 0 < (if c₀ = 0 then 4 else 2 * c₀) := by split <;> omega
      have hc1_le : (if c₀ = 0 then 4 else 2 * c₀) ≤ max 4 (2 * maxOldCap) := by split <;> omega
      obtain ⟨hc1, hl1, hp1⟩ := stepEvents_growOne104_first M c₀ st0 (Nat.le_refl _)
      have htail_cond : DoublingTailPred maxOldCap (if c₀ = 0 then 4 else 2 * c₀) rest := by
        cases rest with
        | nil => trivial
        | cons c₂ r => exact ⟨hchain.2.1, hchain.2.2⟩
      obtain ⟨hc2, hl2, hp2⟩ := stepEvents_doublingTail104 hM rest
        (if c₀ = 0 then 4 else 2 * c₀)
        (M.stepEvents (growOne104Evs c₀) st0) hc1_pos hc1_le htail_cond hl1
      have hcum0 := v104GrowStepCum_le_aff hM c₀
      have hlive1 := v104Live_le_aff hM (if c₀ = 0 then 4 else 2 * c₀)
      have hlen_succ : (1 + rest.length) * (2 * (104 * max 4 (2 * maxOldCap)) + 9539) ≤
          maxSteps * (2 * (104 * max 4 (2 * maxOldCap)) + 9539) := by
        simp only [List.length_cons] at hlen
        exact Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at hlen_succ
      exact ⟨by omega, hl2, by omega⟩

theorem phaseCreditSpec_computeMac (M : AllocCostModel) [HasFineReallocCredit M]
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = computeMacEvs)
      (2 * HasFineReallocCredit.smallAllocCost M 33) 0 0 33 where
  req_align := by
    rintro _ rfl ev hev
    unfold computeMacEvs at hev
    simp only [List.mem_append] at hev
    rcases hev with ((he | he) | he | he)
    · exact req_align_rustAlloc_le (Nat.le_refl 33) (by decide) ev he
    · exact req_align_rustDealloc_le 33 1 33 ev he
    · exact req_align_rustAlloc_le (Nat.le_refl 33) (by decide) ev he
    · exact req_align_rustDealloc_le 33 1 33 ev he
  credit_le := by
    rintro st0 _ rfl
    obtain ⟨hc, hl, hp⟩ := stepEvents_computeMac_small M st0 h33
    omega

theorem phaseCreditSpec_vmac (M : AllocCostModel) [HasFineReallocCredit M]
    (withAddr : Bool) (h36 : 36 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = vmacEvs withAddr)
      (2 * HasFineReallocCredit.smallAllocCost M 33 +
        HasFineReallocCredit.smallAllocCost M 36)
      0 0 36 where
  req_align := by
    rintro _ rfl ev hev
    unfold vmacEvs at hev
    cases withAddr
    · simp only [Bool.false_eq_true, ↓reduceIte] at hev
      obtain ⟨hr, ha⟩ := (phaseCreditSpec_computeMac M (by omega)).req_align _ rfl ev hev
      exact ⟨by omega, ha⟩
    · simp only [↓reduceIte, List.mem_append] at hev
      rcases hev with he | (he | he)
      · obtain ⟨hr, ha⟩ := (phaseCreditSpec_computeMac M (by omega)).req_align _ rfl ev he
        exact ⟨by omega, ha⟩
      · exact req_align_rustAlloc_le (Nat.le_refl 36) (by decide) ev he
      · exact req_align_rustDealloc_le 36 1 36 ev he
  credit_le := by
    rintro st0 _ rfl
    obtain ⟨hc, hl, hp⟩ := stepEvents_vmac_small M withAddr st0 h36
    omega

theorem phaseCreditSpec_s7Core (M : AllocCostModel) [HasFineReallocCredit M]
    (withAddr errAlloc : Bool) (h36 : 36 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = s7CoreEvs withAddr errAlloc)
      (2 * HasFineReallocCredit.smallAllocCost M 33 +
        HasFineReallocCredit.smallAllocCost M 36 +
        HasFineReallocCredit.smallAllocCost M 23)
      0 0 36 where
  req_align := by
    rintro _ rfl ev hev
    unfold s7CoreEvs at hev
    simp only [List.mem_append] at hev
    rcases hev with he | he
    · exact (phaseCreditSpec_vmac M withAddr h36).req_align _ rfl ev he
    · cases errAlloc
      · simp only [Bool.false_eq_true, ↓reduceIte] at he
        nomatch he
      · simp only [↓reduceIte] at he
        exact req_align_rustAlloc_le (by decide) (by decide) ev he
  credit_le := by
    rintro st0 _ rfl
    obtain ⟨hc, hl, hp⟩ := stepEvents_s7Core_small M withAddr errAlloc st0 h36
    omega

/-- Event-shape predicate for W2 Segment 8 `AesDecCtEnv ctLen` (`[]`, `alloc`, or `alloc ++ dealloc`).
-/
def AesDecCtShape (ctLen : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  evs = rustAllocEvents ctLen 1 ∨
  evs = rustAllocEvents ctLen 1 ++ rustDeallocEvents ctLen 1

theorem phaseCreditSpec_aesDecCt {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {ctLen maxCt : Nat} (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec M (AesDecCtShape ctLen)
      (2 * maxCt + 9539) (maxCt + 8195) (maxCt + 8195) maxCt := by
  have hnil : PhaseCreditSpec M (· = [])
      (2 * maxCt + 9539) (maxCt + 8195) (maxCt + 8195) maxCt :=
    (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have halloc : PhaseCreditSpec M (· = rustAllocEvents ctLen 1)
      (2 * maxCt + 9539) (maxCt + 8195) (maxCt + 8195) maxCt :=
    (PhaseCreditSpec.rustAlloc_aff hM (req := ctLen) (al := 1) (by decide)).mono
      (by omega) (by omega) (by omega) hct
  have hcancel : PhaseCreditSpec M
      (ConcatEnv (· = rustAllocEvents ctLen 1) (· = rustDeallocEvents ctLen 1))
      (2 * maxCt + 9539) (maxCt + 8195) (maxCt + 8195) maxCt :=
    (PhaseCreditSpec.tempAllocFree_aff hM (req := ctLen) (al := 1) (by decide)).mono
      (by omega) (Nat.zero_le _) (by omega) hct
  refine ((hnil.or (halloc.or hcancel)).of_imp ?_).mono
    (by omega) (by omega) (by omega) (by omega)
  rintro evs (rfl | rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨rustAllocEvents ctLen 1, rustDeallocEvents ctLen 1, rfl, rfl, rfl⟩)

/-- Error-branch `PhaseCreditSpec` for `AesDecCtEnv` (`Δlive = 0`). -/
theorem phaseCreditSpec_aesDecCt_err {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {ctLen maxCt : Nat} (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec M
      (fun evs => evs = [] ∨ evs = rustAllocEvents ctLen 1 ++ rustDeallocEvents ctLen 1)
      (2 * maxCt + 9539) 0 (maxCt + 8195) maxCt := by
  have hnil : PhaseCreditSpec M (· = []) (2 * maxCt + 9539) 0 (maxCt + 8195) maxCt :=
    (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.zero_le _) (Nat.zero_le _)
  have hcancel : PhaseCreditSpec M
      (ConcatEnv (· = rustAllocEvents ctLen 1) (· = rustDeallocEvents ctLen 1))
      (2 * maxCt + 9539) 0 (maxCt + 8195) maxCt :=
    (PhaseCreditSpec.tempAllocFree_aff hM (req := ctLen) (al := 1) (by decide)).mono
      (by omega) (Nat.le_refl 0) (by omega) hct
  refine ((hnil.or hcancel).of_imp ?_).mono (by omega) (by omega) (by omega) (by omega)
  rintro evs (rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr ⟨rustAllocEvents ctLen 1, rustDeallocEvents ctLen 1, rfl, rfl, rfl⟩

/-! ## 3. `SessionClone` `DeallocCreditSpec` and `TrialLoopEnv` -/

theorem DeallocCreditSpec.opt_free_singleAllocLarge (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (hal : al ≤ 16) :
    DeallocCreditSpec M
      (· = if req = 0 then [] else rustDeallocEvents req al)
      (if req = 0 then 0 else singleAllocLarge M req) := by
  by_cases h0 : req = 0
  · subst h0
    simpa using DeallocCreditSpec.nil M
  · simp only [h0, ↓reduceIte, singleAllocLarge]
    by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
    · simp only [hle, ↓reduceIte]
      exact DeallocCreditSpec.free_small M hal hle
    · have hgt : HasFineReallocCredit.smallMaxReq M < req := Nat.lt_of_not_ge hle
      simp only [hle, ↓reduceIte]
      exact DeallocCreditSpec.free_large M hal hgt

/-- `DeallocCreditSpec` for `optDeallocListEvs pairs` (`align ≤ 16`), crediting `optDeallocListLarge M pairs`.
-/
theorem DeallocCreditSpec.optDeallocList (M : AllocCostModel) [HasFineReallocCredit M]
    (pairs : List (Nat × Nat)) (hal_all : ∀ p ∈ pairs, p.2 ≤ 16) :
    DeallocCreditSpec M (· = optDeallocListEvs pairs) (optDeallocListLarge M pairs) where
  req_align := by
    rintro _ rfl ev hev
    induction pairs with
    | nil => nomatch hev
    | cons p rest ih =>
      rcases p with ⟨req, al⟩
      simp only [optDeallocListEvs, List.mem_append] at hev
      rcases hev with he | he
      · split at he
        · nomatch he
        · exact req_align_rustDealloc_le req al 0 ev he
      · exact ih (fun q hq => hal_all q (List.mem_cons_of_mem _ hq)) he
  credit_sub := by
    rintro st0 _ rfl
    have hlive : HasFineReallocCredit.liveLarge st0 ≤
        (HasFineReallocCredit.liveLarge st0 - optDeallocListLarge M pairs) +
          optDeallocListLarge M pairs := by omega
    exact stepEvents_optDeallocList_cancel M pairs st0 hal_all hlive

/-- Completed failed-trial combinator (`Clone ++ TdFail ++ DropClone`), restoring `Δlive = 0`. -/
theorem phaseCreditSpec_failedTrial_done {M : AllocCostModel} [HasFineReallocCredit M]
    {CloneEnv TdFailEnv DropCloneEnv : List AllocEvent → Prop}
    {cClone lClone pClone rClone cTd lMut pTd rTd : Nat}
    (hClone : PhaseCreditSpec M CloneEnv cClone lClone pClone rClone)
    (hTdFail : PhaseCreditSpec M TdFailEnv cTd lMut pTd rTd)
    (hDrop : DeallocCreditSpec M DropCloneEnv (lClone + lMut)) :
    PhaseCreditSpec M
      (ConcatEnv (ConcatEnv CloneEnv TdFailEnv) DropCloneEnv)
      (cClone + cTd) 0 (max pClone (lClone + pTd)) (max rClone rTd) := by
  have h12 :
      PhaseCreditSpec M (ConcatEnv CloneEnv TdFailEnv)
        (cClone + cTd) (0 + (lClone + lMut)) (max pClone (lClone + pTd)) (max rClone rTd) := by
    simpa [Nat.zero_add] using hClone.concat hTdFail
  exact h12.concat_dealloc_cancel hDrop

/-- Trial-decrypt loop envelope (`≤ n` sessions): each iteration either halts early (`HaltStep x`) or
completes `DoneStep x` (`Δlive = 0` after `DropClone`) and continues to the remaining trials, ending in `FinalEnv`.
-/
def TrialLoopEnv {α : Type}
    (HaltStep DoneStep : α → List AllocEvent → Prop)
    (FinalEnv : List AllocEvent → Prop) : List α → List AllocEvent → Prop
  | [], evs => FinalEnv evs
  | x :: xs, evs => HaltStep x evs ∨ ConcatEnv (DoneStep x) (TrialLoopEnv HaltStep DoneStep FinalEnv xs) evs

/-- `PhaseCreditSpec` for `TrialLoopEnv` across `xs` failed session trials (`xs.length + 1 ≤ n`) followed by `FinalEnv`.
-/
theorem phaseCreditSpec_trialLoop {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    {HaltStep DoneStep : α → List AllocEvent → Prop}
    {FinalEnv : List AllocEvent → Prop}
    {n cFail lHalt pFail rFail cFinal lFinal pFinal rFinal : Nat}
    (xs : List α) (hlen : xs.length + 1 ≤ n)
    (hHalt : ∀ x ∈ xs, PhaseCreditSpec M (HaltStep x) cFail lHalt pFail rFail)
    (hDone : ∀ x ∈ xs, PhaseCreditSpec M (DoneStep x) cFail 0 pFail rFail)
    (hFinal : PhaseCreditSpec M FinalEnv cFinal lFinal pFinal rFinal) :
    PhaseCreditSpec M (TrialLoopEnv HaltStep DoneStep FinalEnv xs)
      ((n - 1) * cFail + cFinal)
      (max lHalt lFinal)
      (max pFail pFinal)
      (max rFail rFinal) := by
  suffices hrec : ∀ ys : List α,
      (∀ x ∈ ys, PhaseCreditSpec M (HaltStep x) cFail lHalt pFail rFail) →
      (∀ x ∈ ys, PhaseCreditSpec M (DoneStep x) cFail 0 pFail rFail) →
      PhaseCreditSpec M (TrialLoopEnv HaltStep DoneStep FinalEnv ys)
        (ys.length * cFail + cFinal)
        (max lHalt lFinal)
        (max pFail pFinal)
        (max rFail rFinal) by
    have h := hrec xs hHalt hDone
    have hmul : xs.length * cFail ≤ (n - 1) * cFail :=
      Nat.mul_le_mul_right cFail (by omega)
    exact h.mono (by omega) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  intro ys hH hD
  induction ys with
  | nil =>
    simp only [TrialLoopEnv, List.length_nil, Nat.zero_mul, Nat.zero_add]
    exact hFinal.mono (Nat.le_refl _) (Nat.le_max_right _ _)
      (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  | cons y rest ih =>
    have hyH := hH y List.mem_cons_self
    have hyD := hD y List.mem_cons_self
    have hrest := ih
      (fun z hz => hH z (List.mem_cons_of_mem y hz))
      (fun z hz => hD z (List.mem_cons_of_mem y hz))
    have hcat := hyD.concat hrest
    have hor := hyH.or hcat
    refine (hor.of_imp (fun _ h => h)).mono ?_ ?_ ?_ ?_
    · rw [List.length_cons, Nat.succ_mul]; omega
    · omega
    · omega
    · omega

end LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak
