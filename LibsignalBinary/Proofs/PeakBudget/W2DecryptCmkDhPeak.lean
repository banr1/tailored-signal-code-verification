/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptLeavesPeak

/-!
# `Vec<104>` Doubling, `consume_message_key`, and `create_chain` Helpers for W2

Symbolic `[HasFineReallocCredit M]` cumulative and peak bounds for W2 `message_decrypt`:
`Vec<104>` (`align = 8`, `stride = 104`) capacity-doubling steps with `L → L` `realloc` cancellation,
`consume_message_key` (`≤ 2,000` forward jumps), and `dh_ratchet_step` / `create_chain` (`cap ≤ 5`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W2DecryptCmkDhPeak

open LibsignalBinary.Heap (
  AllocCostModel AllocEvent rustAllocEvents rustDeallocEvents rustReallocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
  stepEvents_rustAlloc_small
  stepEvents_rustRealloc_large_large stepEvents_rustRealloc_small_large
  stepEvents_rustRealloc_small_small
)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptLeavesPeak (
  singleAllocCum singleAllocLarge
  stepEvents_rustAlloc_any stepEvents_rustAlloc_dealloc_cancel stepEvents_rustDealloc_noninc
)

/-! ## 1. `Vec<104>` Capacity-Doubling Event Shape and Charges -/

/-- Events emitted by `<RawVec<Chain/MessageKey>>::grow_one` (`stride = 104`, `align = 8`) at capacity `cap`.
-/
def growOne104Evs (cap : Nat) : List AllocEvent :=
  if cap = 0 then
    rustAllocEvents 416 8
  else
    rustReallocEvents (104 * cap) (104 * (2 * cap)) 8

/-- Live `sc = 63` large-buffer weight of a `Vec<104>` buffer at capacity `cap`. -/
def v104Live (M : AllocCostModel) [HasFineReallocCredit M] (cap : Nat) : Nat :=
  if 104 * cap ≤ HasFineReallocCredit.smallMaxReq M then
    0
  else
    HasFineReallocCredit.largeCost M (104 * cap)

/-- Step `cumSmall` charge of `growOne104Evs cap`. -/
def v104GrowStepCum (M : AllocCostModel) [HasFineReallocCredit M] (cap : Nat) : Nat :=
  if cap = 0 then
    singleAllocCum M 416
  else if 104 * (2 * cap) ≤ HasFineReallocCredit.smallMaxReq M then
    HasFineReallocCredit.smallReallocCost M (104 * (2 * cap))
  else
    HasFineReallocCredit.largeMetaCost M

theorem v104Live_zero (M : AllocCostModel) [HasFineReallocCredit M] :
    v104Live M 0 = 0 := by
  simp [v104Live]

theorem v104Live_eq_zero_of_le (M : AllocCostModel) [HasFineReallocCredit M]
    {cap : Nat} (hle : 104 * cap ≤ HasFineReallocCredit.smallMaxReq M) :
    v104Live M cap = 0 := by
  simp [v104Live, hle]

theorem stepEvents_growOne104_zero (M : AllocCostModel) [HasFineReallocCredit M]
    {L₀ : Nat} (st : M.σ)
    (hlive : HasFineReallocCredit.liveLarge st ≤ L₀) :
    let st' := M.stepEvents (growOne104Evs 0) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + v104GrowStepCum M 0 ∧
    HasFineReallocCredit.liveLarge st' ≤ L₀ + v104Live M 4 ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st) (L₀ + v104Live M 4) := by
  unfold growOne104Evs v104GrowStepCum
  simp only [↓reduceIte]
  rcases stepEvents_rustAlloc_any M (req := 416) (al := 8) st (by decide) (by decide) with
    ⟨hc, hl, hp⟩
  have hv4 : singleAllocLarge M 416 = v104Live M 4 := rfl
  rw [hv4] at hl hp
  exact ⟨hc, by omega, by omega⟩

/-- Credit step for `growOne104Evs cap` (`0 < cap`), cancelling `v104Live M cap` in `L → L` and recording transient overlap.
-/
theorem stepEvents_growOne104_pos (M : AllocCostModel) [HasFineReallocCredit M]
    {cap L₀ : Nat} (st : M.σ) (hpos : 0 < cap)
    (hlive : HasFineReallocCredit.liveLarge st ≤ L₀ + v104Live M cap) :
    let st' := M.stepEvents (growOne104Evs cap) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + v104GrowStepCum M cap ∧
    HasFineReallocCredit.liveLarge st' ≤ L₀ + v104Live M (2 * cap) ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (L₀ + v104Live M cap + v104Live M (2 * cap)) := by
  have hnz : cap ≠ 0 := Nat.ne_of_gt hpos
  unfold growOne104Evs v104GrowStepCum
  simp only [hnz, ↓reduceIte]
  have hal : (8 : Nat) ≤ 16 := by decide
  have hal_new : 8 ≤ 104 * (2 * cap) := by omega
  have hold_pos : 0 < 104 * cap := by omega
  have hnew_pos : 0 < 104 * (2 * cap) := by omega
  by_cases hnew_s : 104 * (2 * cap) ≤ HasFineReallocCredit.smallMaxReq M
  · have hold_s : 104 * cap ≤ HasFineReallocCredit.smallMaxReq M := by omega
    rcases stepEvents_rustRealloc_small_small M (old := 104 * cap) (new := 104 * (2 * cap))
        (al := 8) st hal hal_new hold_pos hold_s hnew_pos hnew_s with ⟨hc, hl, hp⟩
    simp only [v104Live, hold_s, hnew_s, ↓reduceIte, Nat.add_zero] at hlive ⊢
    exact ⟨hc, by omega, by omega⟩
  · have hnew_l : HasFineReallocCredit.smallMaxReq M < 104 * (2 * cap) := Nat.lt_of_not_ge hnew_s
    by_cases hold_s : 104 * cap ≤ HasFineReallocCredit.smallMaxReq M
    · rcases stepEvents_rustRealloc_small_large M (old := 104 * cap) (new := 104 * (2 * cap))
          (al := 8) st hal hal_new hold_pos hold_s hnew_l with ⟨hc, hl, hp⟩
      simp only [v104Live, hold_s, hnew_s, ↓reduceIte, Nat.add_zero] at hlive ⊢
      exact ⟨hc, by omega, by omega⟩
    · have hold_l : HasFineReallocCredit.smallMaxReq M < 104 * cap := Nat.lt_of_not_ge hold_s
      rcases stepEvents_rustRealloc_large_large M (old := 104 * cap) (new := 104 * (2 * cap))
          (al := 8) st hal hal_new hold_l hnew_l with ⟨hc, hl, hp⟩
      simp only [v104Live, hold_s, hnew_s, ↓reduceIte] at hlive ⊢
      exact ⟨hc, by omega, by omega⟩

/-! ## 2. `dhCommitStep12` and `dhCommitStep3` (`create_chain ≤ 5`) Bounds -/

theorem stepEvents_dhCommitStep12_small (M : AllocCostModel) [HasFineReallocCredit M]
    (st : M.σ) (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M) :
    let evs := rustAllocEvents 33 1 ++ rustAllocEvents 33 1 ++ rustAllocEvents 32 1
    let st' := M.stepEvents evs st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st +
        (2 * HasFineReallocCredit.smallAllocCost M 33 + HasFineReallocCredit.smallAllocCost M 32) ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  dsimp only
  rw [M.stepEvents_append, M.stepEvents_append]
  have h32 : 32 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  rcases stepEvents_rustAlloc_small M (req := 33) (al := 1) st (by decide) (by decide) h33 with
    ⟨hc1, hl1, hp1⟩
  rcases stepEvents_rustAlloc_small M (req := 33) (al := 1)
      (M.stepEvents (rustAllocEvents 33 1) st) (by decide) (by decide) h33 with ⟨hc2, hl2, hp2⟩
  rcases stepEvents_rustAlloc_small M (req := 32) (al := 1)
      (M.stepEvents (rustAllocEvents 33 1) (M.stepEvents (rustAllocEvents 33 1) st))
      (by decide) (by decide) h32 with ⟨hc3, hl3, hp3⟩
  exact ⟨by omega, by omega, by omega⟩

theorem stepEvents_alloc33_and_dealloc33 (M : AllocCostModel) [HasFineReallocCredit M]
    (st : M.σ) :
    let st' := M.stepEvents (rustAllocEvents 33 1 ++ rustDeallocEvents 33 1) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + singleAllocCum M 33 ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + singleAllocLarge M 33) :=
  stepEvents_rustAlloc_dealloc_cancel M (req := 33) (al := 1) st (by decide) (by decide)

/-- Credit bound for `dhCommitStep3Events cap needGrow` in the small-capacity regime (`104 * max 4 (2 * cap) ≤ smallMaxReq M`).
-/
theorem stepEvents_dhCommitStep3_smallCap (M : AllocCostModel) [HasFineReallocCredit M]
    {cap : Nat} {needGrow : Bool} (st : M.σ)
    (hcap_small : 104 * max 4 (2 * cap) ≤ HasFineReallocCredit.smallMaxReq M) :
    let evs := (if needGrow then growOne104Evs cap else []) ++ rustDeallocEvents 33 1
    let st' := M.stepEvents evs st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + (if needGrow then v104GrowStepCum M cap else 0) ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  dsimp only
  rw [M.stepEvents_append]
  cases needGrow
  · simp only [Bool.false_eq_true, ↓reduceIte, AllocCostModel.stepEvents_nil, Nat.add_zero]
    exact stepEvents_rustDealloc_noninc M (req := 33) (al := 1) st (by decide)
  · simp only [↓reduceIte]
    by_cases h0 : cap = 0
    · subst h0
      have h416 : 416 ≤ HasFineReallocCredit.smallMaxReq M := by omega
      have hcum0 : v104GrowStepCum M 0 = HasFineReallocCredit.smallAllocCost M 416 := by
        simp [v104GrowStepCum, singleAllocCum, h416]
      unfold growOne104Evs
      simp only [↓reduceIte]
      rcases stepEvents_rustAlloc_small M (req := 416) (al := 8) st
          (by decide) (by decide) h416 with ⟨hc1, hl1, hp1⟩
      rcases stepEvents_rustDealloc_noninc M (req := 33) (al := 1)
          (M.stepEvents (rustAllocEvents 416 8) st) (by decide) with ⟨hc2, hl2, hp2⟩
      rw [hcum0]
      exact ⟨by omega, by omega, by omega⟩
    · have hpos : 0 < cap := Nat.pos_of_ne_zero h0
      have hold_s : 104 * cap ≤ HasFineReallocCredit.smallMaxReq M := by omega
      have hnew_s : 104 * (2 * cap) ≤ HasFineReallocCredit.smallMaxReq M := by omega
      have hcum_pos : v104GrowStepCum M cap =
          HasFineReallocCredit.smallReallocCost M (104 * (2 * cap)) := by
        simp [v104GrowStepCum, h0, hnew_s]
      unfold growOne104Evs
      simp only [h0, ↓reduceIte]
      rcases stepEvents_rustRealloc_small_small M (old := 104 * cap) (new := 104 * (2 * cap))
          (al := 8) st (by decide) (by omega) (by omega) hold_s (by omega) hnew_s with
        ⟨hc1, hl1, hp1⟩
      rcases stepEvents_rustDealloc_noninc M (req := 33) (al := 1)
          (M.stepEvents (rustReallocEvents (104 * cap) (104 * (2 * cap)) 8) st) (by decide) with
        ⟨hc2, hl2, hp2⟩
      rw [hcum_pos]
      exact ⟨by omega, by omega, by omega⟩

/-! ## 3. `consume_message_key` Doubling Tower (`0 → ... → 2048`) -/

/-- Cumulative `cumSmall` bound for the `Vec<104>` doubling tower from `0` to `2048`. -/
def v104TowerCum2048 (M : AllocCostModel) [HasFineReallocCredit M] : Nat :=
  v104GrowStepCum M 0 +
  v104GrowStepCum M 4 +
  v104GrowStepCum M 8 +
  v104GrowStepCum M 16 +
  v104GrowStepCum M 32 +
  v104GrowStepCum M 64 +
  v104GrowStepCum M 128 +
  v104GrowStepCum M 256 +
  v104GrowStepCum M 512 +
  v104GrowStepCum M 1024

def v104CapSeq : Nat → Nat
  | 0 => 0
  | j + 1 => 4 * 2 ^ j

def v104TowerCum (M : AllocCostModel) [HasFineReallocCredit M] : Nat → Nat
  | 0 => 0
  | k + 1 => v104TowerCum M k + v104GrowStepCum M (v104CapSeq k)

def v104TowerPeak (M : AllocCostModel) [HasFineReallocCredit M] : Nat → Nat
  | 0 => 0
  | 1 => v104Live M 4
  | k + 2 => max (v104TowerPeak M (k + 1))
      (v104Live M (4 * 2 ^ k) + v104Live M (4 * 2 ^ (k + 1)))

theorem v104TowerCum_ten_eq (M : AllocCostModel) [HasFineReallocCredit M] :
    v104TowerCum M 10 = v104TowerCum2048 M := by
  simp only [v104TowerCum, v104CapSeq, v104TowerCum2048, Nat.reducePow, Nat.reduceMul]
  omega

theorem v104Live_le_towerPeak (M : AllocCostModel) [HasFineReallocCredit M] :
    ∀ k : Nat, v104Live M (v104CapSeq k) ≤ v104TowerPeak M k
  | 0 => by simp [v104CapSeq, v104Live_zero, v104TowerPeak]
  | 1 => Nat.le_refl _
  | k + 2 => by
    dsimp only [v104CapSeq, v104TowerPeak]
    omega

theorem v104TowerCum_mono (M : AllocCostModel) [HasFineReallocCredit M]
    {j k : Nat} (hjk : j ≤ k) :
    v104TowerCum M j ≤ v104TowerCum M k := by
  induction hjk with
  | refl => exact Nat.le_refl _
  | step _ ih => dsimp only [v104TowerCum]; omega

theorem v104TowerPeak_mono (M : AllocCostModel) [HasFineReallocCredit M]
    {j k : Nat} (hjk : j ≤ k) :
    v104TowerPeak M j ≤ v104TowerPeak M k := by
  induction hjk with
  | refl => exact Nat.le_refl _
  | @step m hjm ih =>
    cases m with
    | zero =>
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hjm
      subst hj0
      dsimp only [v104TowerPeak]
      omega
    | succ m' => dsimp only [v104TowerPeak]; omega

theorem stepEvents_growOne104_tower_step (M : AllocCostModel) [HasFineReallocCredit M]
    (k : Nat) {L₀ C₀ P₀ : Nat} (st : M.σ)
    (hcum : HasFineReallocCredit.cumSmall st ≤ C₀ + v104TowerCum M k)
    (hlive : HasFineReallocCredit.liveLarge st ≤ L₀ + v104Live M (v104CapSeq k))
    (hpeak : HasFineReallocCredit.peakLarge st ≤ max P₀ (L₀ + v104TowerPeak M k)) :
    let st' := M.stepEvents (growOne104Evs (v104CapSeq k)) st
    HasFineReallocCredit.cumSmall st' ≤ C₀ + v104TowerCum M (k + 1) ∧
    HasFineReallocCredit.liveLarge st' ≤ L₀ + v104Live M (v104CapSeq (k + 1)) ∧
    HasFineReallocCredit.peakLarge st' ≤ max P₀ (L₀ + v104TowerPeak M (k + 1)) := by
  cases k with
  | zero =>
    dsimp only [v104CapSeq, v104TowerCum, v104TowerPeak] at hcum hlive hpeak ⊢
    rw [v104Live_zero, Nat.add_zero] at hlive
    rcases stepEvents_growOne104_zero M st hlive with ⟨hc, hl, hp⟩
    exact ⟨by omega, hl, by omega⟩
  | succ k' =>
    have hpow : 0 < 2 ^ k' := Nat.two_pow_pos k'
    have hpos : 0 < 4 * 2 ^ k' := by omega
    have h2 : 2 * (4 * 2 ^ k') = 4 * 2 ^ (k' + 1) := by
      rw [Nat.pow_succ]
      omega
    dsimp only [v104CapSeq, v104TowerCum, v104TowerPeak] at hcum hlive hpeak ⊢
    rcases stepEvents_growOne104_pos M (cap := 4 * 2 ^ k') (L₀ := L₀) st hpos hlive with
      ⟨hc, hl, hp⟩
    rw [h2] at hl hp
    exact ⟨by omega, hl, by omega⟩

/-- Single forward-jump step in `consume_message_key` (`33` B seed alloc, optional `Vec<104>` grow, optional `33` B evict free).
-/
theorem stepEvents_cmk_jump_step (M : AllocCostModel) [HasFineReallocCredit M]
    (k : Nat) {needGrow needEvictFree : Bool} {L₀ C₀ P₀ : Nat} (st : M.σ)
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M)
    (hcum : HasFineReallocCredit.cumSmall st ≤ C₀ + v104TowerCum M k)
    (hlive : HasFineReallocCredit.liveLarge st ≤ L₀ + v104Live M (v104CapSeq k))
    (hpeak : HasFineReallocCredit.peakLarge st ≤ max P₀ (L₀ + v104TowerPeak M k)) :
    let evs :=
      rustAllocEvents 33 1 ++
      (if needGrow then growOne104Evs (v104CapSeq k) else []) ++
      (if needEvictFree then rustDeallocEvents 33 1 else [])
    let k' := if needGrow then k + 1 else k
    let st' := M.stepEvents evs st
    HasFineReallocCredit.cumSmall st' ≤
      (C₀ + HasFineReallocCredit.smallAllocCost M 33) + v104TowerCum M k' ∧
    HasFineReallocCredit.liveLarge st' ≤ L₀ + v104Live M (v104CapSeq k') ∧
    HasFineReallocCredit.peakLarge st' ≤ max P₀ (L₀ + v104TowerPeak M k') := by
  dsimp only
  rw [M.stepEvents_append, M.stepEvents_append]
  rcases stepEvents_rustAlloc_small M (req := 33) (al := 1) st (by decide) (by decide) h33 with
    ⟨hcA, hlA, hpA⟩
  have hcumA : HasFineReallocCredit.cumSmall (M.stepEvents (rustAllocEvents 33 1) st) ≤
      (C₀ + HasFineReallocCredit.smallAllocCost M 33) + v104TowerCum M k := by omega
  have hliveA : HasFineReallocCredit.liveLarge (M.stepEvents (rustAllocEvents 33 1) st) ≤
      L₀ + v104Live M (v104CapSeq k) := by omega
  have hpeakA : HasFineReallocCredit.peakLarge (M.stepEvents (rustAllocEvents 33 1) st) ≤
      max P₀ (L₀ + v104TowerPeak M k) := by omega
  cases needGrow
  · simp only [Bool.false_eq_true, ↓reduceIte, AllocCostModel.stepEvents_nil]
    cases needEvictFree
    · simp only [Bool.false_eq_true, ↓reduceIte, AllocCostModel.stepEvents_nil]
      exact ⟨hcumA, hliveA, hpeakA⟩
    · simp only [↓reduceIte]
      rcases stepEvents_rustDealloc_noninc M (req := 33) (al := 1)
          (M.stepEvents (rustAllocEvents 33 1) st) (by decide) with ⟨hcF, hlF, hpF⟩
      exact ⟨by omega, by omega, by omega⟩
  · simp only [↓reduceIte]
    rcases stepEvents_growOne104_tower_step M k (M.stepEvents (rustAllocEvents 33 1) st)
        hcumA hliveA hpeakA with ⟨hcG, hlG, hpG⟩
    cases needEvictFree
    · simp only [Bool.false_eq_true, ↓reduceIte, AllocCostModel.stepEvents_nil]
      exact ⟨hcG, hlG, hpG⟩
    · simp only [↓reduceIte]
      rcases stepEvents_rustDealloc_noninc M (req := 33) (al := 1)
          (M.stepEvents (growOne104Evs (v104CapSeq k)) (M.stepEvents (rustAllocEvents 33 1) st))
          (by decide) with ⟨hcF, hlF, hpF⟩
      exact ⟨by omega, by omega, by omega⟩

/-- Event sequence of a multi-step `consume_message_key` forward-jump trace starting at tower
    capacity index `k`. -/
def cmkJumpListEvs : Nat → List (Bool × Bool) → List AllocEvent
  | _, [] => []
  | k, (needGrow, needEvictFree) :: rest =>
    (rustAllocEvents 33 1 ++
      (if needGrow then growOne104Evs (v104CapSeq k) else []) ++
      (if needEvictFree then rustDeallocEvents 33 1 else [])) ++
    cmkJumpListEvs (if needGrow then k + 1 else k) rest

/-- Final tower index after executing `jumps` starting from index `k`. -/
def cmkJumpFinalIdx : Nat → List (Bool × Bool) → Nat
  | k, [] => k
  | k, (needGrow, _) :: rest => cmkJumpFinalIdx (if needGrow then k + 1 else k) rest

theorem stepEvents_cmk_jump_list (M : AllocCostModel) [HasFineReallocCredit M]
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M) :
    ∀ (jumps : List (Bool × Bool)) (k : Nat) {L₀ C₀ P₀ : Nat} (st : M.σ),
      HasFineReallocCredit.cumSmall st ≤ C₀ + v104TowerCum M k →
      HasFineReallocCredit.liveLarge st ≤ L₀ + v104Live M (v104CapSeq k) →
      HasFineReallocCredit.peakLarge st ≤ max P₀ (L₀ + v104TowerPeak M k) →
      let k' := cmkJumpFinalIdx k jumps
      let st' := M.stepEvents (cmkJumpListEvs k jumps) st
      HasFineReallocCredit.cumSmall st' ≤
        (C₀ + jumps.length * HasFineReallocCredit.smallAllocCost M 33) + v104TowerCum M k' ∧
      HasFineReallocCredit.liveLarge st' ≤ L₀ + v104Live M (v104CapSeq k') ∧
      HasFineReallocCredit.peakLarge st' ≤ max P₀ (L₀ + v104TowerPeak M k')
  | [], k, _, _, _, st, hcum, hlive, hpeak => by
    simp only [cmkJumpFinalIdx, cmkJumpListEvs, AllocCostModel.stepEvents_nil,
      List.length_nil, Nat.zero_mul, Nat.add_zero]
    exact ⟨hcum, hlive, hpeak⟩
  | (needGrow, needEvictFree) :: rest, k, L₀, C₀, P₀, st, hcum, hlive, hpeak => by
    dsimp only [cmkJumpListEvs, cmkJumpFinalIdx]
    rw [M.stepEvents_append]
    rcases stepEvents_cmk_jump_step M k (needGrow := needGrow) (needEvictFree := needEvictFree)
        st h33 hcum hlive hpeak with ⟨hc1, hl1, hp1⟩
    rcases stepEvents_cmk_jump_list M h33 rest (if needGrow then k + 1 else k)
        (L₀ := L₀) (C₀ := C₀ + HasFineReallocCredit.smallAllocCost M 33) (P₀ := P₀)
        _ hc1 hl1 hp1 with ⟨hc2, hl2, hp2⟩
    have hmul :
        (C₀ + HasFineReallocCredit.smallAllocCost M 33) +
          rest.length * HasFineReallocCredit.smallAllocCost M 33 =
        C₀ + ((needGrow, needEvictFree) :: rest).length *
          HasFineReallocCredit.smallAllocCost M 33 := by
      simp only [List.length_cons, Nat.succ_mul]
      omega
    rw [hmul] at hc2
    exact ⟨hc2, hl2, hp2⟩

/-- Closed-form bound for `cmkJumpListEvs` up to `2,000` jumps and final tower index `≤ 10` (`cap ≤ 2048`).
-/
theorem stepEvents_cmk_jump_list_le_2000 (M : AllocCostModel) [HasFineReallocCredit M]
    (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M)
    {jumps : List (Bool × Bool)} {k : Nat} (st0 : M.σ)
    (hlen : jumps.length ≤ 2000)
    (hk0 : k = 0)
    (hkf : cmkJumpFinalIdx k jumps ≤ 10) :
    let st' := M.stepEvents (cmkJumpListEvs k jumps) st0
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st0 +
        (2000 * HasFineReallocCredit.smallAllocCost M 33 + v104TowerCum2048 M) ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st0 + v104TowerPeak M 10 ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st0)
        (HasFineReallocCredit.liveLarge st0 + v104TowerPeak M 10) := by
  subst hk0
  have hcum0 : HasFineReallocCredit.cumSmall st0 ≤
      HasFineReallocCredit.cumSmall st0 + v104TowerCum M 0 := by
    simp [v104TowerCum]
  have hlive0 : HasFineReallocCredit.liveLarge st0 ≤
      HasFineReallocCredit.liveLarge st0 + v104Live M (v104CapSeq 0) := by
    simp [v104CapSeq, v104Live_zero]
  have hpeak0 : HasFineReallocCredit.peakLarge st0 ≤
      max (HasFineReallocCredit.peakLarge st0)
        (HasFineReallocCredit.liveLarge st0 + v104TowerPeak M 0) := by
    simp only [v104TowerPeak, Nat.add_zero]
    exact Nat.le_max_left _ _
  rcases stepEvents_cmk_jump_list M h33 jumps 0 st0 hcum0 hlive0 hpeak0 with ⟨hc, hl, hp⟩
  have hmc : v104TowerCum M (cmkJumpFinalIdx 0 jumps) ≤ v104TowerCum2048 M := by
    rw [← v104TowerCum_ten_eq]
    exact v104TowerCum_mono M hkf
  have hmp : v104TowerPeak M (cmkJumpFinalIdx 0 jumps) ≤ v104TowerPeak M 10 :=
    v104TowerPeak_mono M hkf
  have hml : v104Live M (v104CapSeq (cmkJumpFinalIdx 0 jumps)) ≤ v104TowerPeak M 10 :=
    Nat.le_trans (v104Live_le_towerPeak M _) hmp
  have hjmul : jumps.length * HasFineReallocCredit.smallAllocCost M 33 ≤
      2000 * HasFineReallocCredit.smallAllocCost M 33 :=
    Nat.mul_le_mul_right _ hlen
  exact ⟨by omega, by omega, by omega⟩

end LibsignalBinary.Proofs.PeakBudget.W2DecryptCmkDhPeak
