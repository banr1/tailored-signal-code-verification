/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.VecGrowCreditHelpers
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.LayoutBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PureBudget
public import LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget

/-!
# Parametric `Vec` Growth and Realloc-Credit Lemmas

Proves `HasFineReallocCredit` and `PhaseCreditSpec` recurrences and closed-form `ModelHyps M` affine
bounds for `RawVec` and `VecDeque` doubling ladders, concrete `Vec<T>` element strides, and
super-doubling `do_reserve` / `prost::encoding::bytes::merge` overwrite chains.
-/

@[expose] public section

namespace LibsignalBinary.Proofs.PeakBudget.VecGrowCredit

set_option autoImplicit false

open CryptoVerification.LibsignalProtoCodec (WireType mergeBytes)
open CryptoVerification.LibsignalSpqrV1 (GrowOneCall SortedSetPt)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost (BytesMergeGhost)
open CryptoVerification.SignalSession.Cli (GrowOneDirGhost)
open CryptoVerification.SpqrV1.ChainProofs (VecDequeGrowGhost chainEpochAlign chainEpochSize)
open CryptoVerification.SpqrV1.Poly.AddChunk (AddChunkGhost)
open LibsignalBinary.Heap
  (AllocEvent AllocCostModel SeqEnv rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepReq eventStepAlign)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (rawVecNewCap rawVecGrowEvents RawVecGrowEnv rawVecGrowEnv_events
   GrowOneU8Env GrowOneU8Env_iff_rawVecGrowEnv GrowOneVecU8Env)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (IterSeqEnv IterConcatEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.VecGrowCreditHelpers
  (IsSuperDoubling headOrZero lastOrZero
   doublingCap_mono doublingCap_pos rawVecGrowEnv_req_align
   rawVecLargeLive_le_maxLiveOfSteps rawVecStepPeak_le_peakOfSteps
   growOrReallocEvents_req_align rustAllocEvents_req_align rustDeallocEvents_req_align
   stepEvents_rustAlloc_credit stepEvents_alloc_dealloc_credit
   stepEvents_alloc_growOrRealloc_dealloc_credit stepEvents_growOrRealloc_delta
   allocLargeLive_le_affine allocStepCum_le_affine growOrReallocStepCum_amortized)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
  (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
  (growOne104Events GrowOne104Env)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.LayoutBudget
  (GrowOneDirBytesEnv)
open LibsignalBinary.Proofs.SignalSession.Cli.Dir.Put.PureBudget
  (GrowOneDirEnv)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
  (vecDequeGrowEvents VecDequeGrowEnv)
open LibsignalBinary.Proofs.SpqrV1.Poly.AddChunk.DefsBudget
  (growOnePtEvents AddChunkSlotEnv AddChunkSlotsEnv AddChunkEnv)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (finishGrowEvents doReserveEvents DoReserveEnv)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
  (GrowOneSpeEnv growOneSpeEvents_eq_of_env)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (doReserveClearEvents bytesMergeEventsCore BytesMergeEnv)

/-! ## 1. Realloc-Credit Primitives and Standalone `PhaseCreditSpec` -/

export VecGrowCreditHelpers
  (allocLargeLive allocStepCum reallocStepCum growOrReallocEvents growOrReallocStepCum)

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
        (L_base + allocLargeLive M oldReq + allocLargeLive M newReq) :=
  VecGrowCreditHelpers.stepEvents_rustRealloc_any_credit M st hal hold_pos hnew_pos hlive

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
        (L_base + allocLargeLive M oldReq + allocLargeLive M newReq) :=
  VecGrowCreditHelpers.stepEvents_growOrRealloc_credit M st hal hnew_pos hlive

theorem phaseCreditSpec_growOrRealloc (M : AllocCostModel) [HasFineReallocCredit M]
    {oldReq newReq align : Nat} (hal : align ≤ 16) (hnew_pos : 0 < newReq) :
    PhaseCreditSpec M (· = growOrReallocEvents oldReq newReq align)
      (growOrReallocStepCum M oldReq newReq align)
      (allocLargeLive M newReq - allocLargeLive M oldReq)
      (allocLargeLive M newReq)
      newReq where
  req_align := by
    rintro _ rfl
    exact growOrReallocEvents_req_align hal
  credit_le := by
    rintro st0 _ rfl
    exact stepEvents_growOrRealloc_delta M st0 hal hnew_pos

/-! ## 2. Parametric `RawVec` Doubling Ladder and Affine Bounds -/

export VecGrowCreditHelpers (doublingCap doublingSteps doublingCapsFrom doublingCaps)
export VecGrowCreditHelpers
  (rawVecLargeLive rawVecStepCum rawVecCumOfSteps rawVecMaxLiveOfSteps rawVecPeakOfSteps)

theorem doublingCap_doublingSteps_ge {minCap : Nat} (hmin : 0 < minCap) (targetCap : Nat) :
    targetCap ≤ doublingCap minCap (doublingSteps minCap targetCap) :=
  VecGrowCreditHelpers.doublingCap_doublingSteps_ge hmin targetCap

theorem doublingCap_doublingSteps_le {minCap : Nat} (hmin : 0 < minCap) {targetCap : Nat}
    (ht : 0 < targetCap) :
    doublingCap minCap (doublingSteps minCap targetCap) ≤ max minCap (2 * targetCap - 2) :=
  VecGrowCreditHelpers.doublingCap_doublingSteps_le hmin ht

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
          rawVecLargeLive M elemSz (doublingCap minCap (j + 1))) :=
  VecGrowCreditHelpers.stepEvents_rawVecGrow_credit M st helem hmin hal hcap hEnv hlive

theorem rawVecCumOfSteps_le_affine {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (elemSz minCap align k : Nat) :
    rawVecCumOfSteps M elemSz minCap align k ≤
      4 * min (doublingCap minCap k * elemSz) (HasFineReallocCredit.smallMaxReq M) + 9539 * k :=
  VecGrowCreditHelpers.rawVecCumOfSteps_le_affine M
    (fun _ hr => hM.smallAlloc_le hr) (fun _ hr => hM.smallRealloc_le hr) hM.meta_le
    elemSz minCap align k

theorem rawVecLargeLive_le_affine {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (elemSz cap : Nat) :
    rawVecLargeLive M elemSz cap ≤
      if cap * elemSz ≤ HasFineReallocCredit.smallMaxReq M then 0
      else cap * elemSz + 8195 :=
  VecGrowCreditHelpers.rawVecLargeLive_le_affine M (fun _ hr => hM.largeCost_le hr) elemSz cap

theorem rawVecMaxLiveOfSteps_le_affine {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (elemSz minCap k : Nat) :
    rawVecMaxLiveOfSteps M elemSz minCap k ≤
      if doublingCap minCap k * elemSz ≤ HasFineReallocCredit.smallMaxReq M then 0
      else doublingCap minCap k * elemSz + 8195 :=
  VecGrowCreditHelpers.rawVecMaxLiveOfSteps_le_affine M
    (fun _ hr => hM.largeCost_le hr) elemSz minCap k

theorem rawVecPeakOfSteps_le_affine {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (elemSz minCap k : Nat) :
    rawVecPeakOfSteps M elemSz minCap k ≤
      if doublingCap minCap k * elemSz ≤ HasFineReallocCredit.smallMaxReq M then 0
      else (3 * (doublingCap minCap k * elemSz)) / 2 + 16390 :=
  VecGrowCreditHelpers.rawVecPeakOfSteps_le_affine M
    (fun _ hr => hM.largeCost_le hr) elemSz minCap k

private def rawVecCumFrom (M : AllocCostModel) [HasFineReallocCredit M]
    (elemSz minCap align j : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    rawVecStepCum M elemSz minCap align j + rawVecCumFrom M elemSz minCap align (j + 1) n

private theorem rawVecCumOfSteps_add_cumFrom (M : AllocCostModel) [HasFineReallocCredit M]
    (elemSz minCap align : Nat) :
    ∀ (n j : Nat),
      rawVecCumOfSteps M elemSz minCap align j + rawVecCumFrom M elemSz minCap align j n =
        rawVecCumOfSteps M elemSz minCap align (j + n)
  | 0, j => by simp [rawVecCumFrom]
  | n + 1, j => by
    have ih := rawVecCumOfSteps_add_cumFrom M elemSz minCap align n (j + 1)
    have hidx : j + 1 + n = j + (n + 1) := by omega
    simp only [rawVecCumFrom]
    calc
      rawVecCumOfSteps M elemSz minCap align j +
          (rawVecStepCum M elemSz minCap align j +
            rawVecCumFrom M elemSz minCap align (j + 1) n) =
        rawVecCumOfSteps M elemSz minCap align (j + 1) +
          rawVecCumFrom M elemSz minCap align (j + 1) n := by
        simp only [rawVecCumOfSteps, VecGrowCreditHelpers.rawVecCumOfSteps]
        omega
      _ = rawVecCumOfSteps M elemSz minCap align (j + 1 + n) := ih
      _ = rawVecCumOfSteps M elemSz minCap align (j + (n + 1)) := by rw [hidx]

private theorem rawVecCumFrom_zero_eq (M : AllocCostModel) [HasFineReallocCredit M]
    (elemSz minCap align k : Nat) :
    rawVecCumFrom M elemSz minCap align 0 k = rawVecCumOfSteps M elemSz minCap align k := by
  have h := rawVecCumOfSteps_add_cumFrom M elemSz minCap align k 0
  simpa [rawVecCumOfSteps, VecGrowCreditHelpers.rawVecCumOfSteps] using h

private theorem iterSeq_rawVecGrow_from_aux (M : AllocCostModel) [HasFineReallocCredit M]
    {elemSz minCap align : Nat} {Step : BitVec 64 → List AllocEvent → Prop}
    (helem : 0 < elemSz) (hmin : 0 < minCap) (hal : align ≤ 16)
    (hStep : ∀ (c : BitVec 64) (evs : List AllocEvent),
      Step c evs → RawVecGrowEnv elemSz minCap align ⟨0#64, c, 0#64, []⟩ evs) :
    ∀ (n j : Nat) {evs : List AllocEvent},
      doublingCap minCap (j + n) < 2 ^ 64 →
      IterSeqEnv Step (doublingCapsFrom minCap j n) evs →
      (∀ ev ∈ evs,
        eventStepReq ev ≤ doublingCap minCap (j + n) * elemSz ∧ eventStepAlign ev ≤ 16) ∧
      (∀ (st : M.σ) (L_base : Nat),
        HasFineReallocCredit.liveLarge st ≤
          L_base + rawVecLargeLive M elemSz (doublingCap minCap j) →
        HasFineReallocCredit.cumSmall (M.stepEvents evs st) ≤
          HasFineReallocCredit.cumSmall st + rawVecCumFrom M elemSz minCap align j n ∧
        HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤
          L_base + rawVecMaxLiveOfSteps M elemSz minCap (j + n) ∧
        HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤
          max (HasFineReallocCredit.peakLarge st)
            (L_base + rawVecPeakOfSteps M elemSz minCap (j + n)))
  | 0, j, evs, _, hIter => by
    simp only [doublingCapsFrom, IterSeqEnv] at hIter
    subst hIter
    refine ⟨(fun _ h => nomatch h), fun st L_base hlive => ?_⟩
    simp only [AllocCostModel.stepEvents_nil, rawVecCumFrom, Nat.add_zero]
    have hmax := rawVecLargeLive_le_maxLiveOfSteps M elemSz minCap j
    exact ⟨Nat.le_refl _, by omega, Nat.le_max_left _ _⟩
  | n + 1, j, evs, hfit, hIter => by
    simp only [doublingCapsFrom, VecGrowCreditHelpers.doublingCapsFrom, IterSeqEnv] at hIter
    have hj_le : doublingCap minCap j ≤ doublingCap minCap (j + (n + 1)) :=
      doublingCap_mono minCap (by omega)
    have hj1_le : doublingCap minCap (j + 1) ≤ doublingCap minCap (j + (n + 1)) :=
      doublingCap_mono minCap (by omega)
    have htoNat : (BitVec.ofNat 64 (doublingCap minCap j)).toNat = doublingCap minCap j := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hidx : j + 1 + n = j + (n + 1) := by omega
    rcases hIter with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
    · have hEnv1 := hStep _ _ h1
      refine ⟨fun ev hev => ?_, fun st L_base hlive => ?_⟩
      · obtain ⟨hr, ha⟩ := rawVecGrowEnv_req_align helem hmin hal htoNat hEnv1 ev hev
        exact ⟨Nat.le_trans hr (Nat.mul_le_mul_right elemSz hj1_le), ha⟩
      · obtain ⟨hc, hl, hp⟩ := stepEvents_rawVecGrow_credit M st helem hmin hal htoNat hEnv1 hlive
        have hlive_max :
            rawVecLargeLive M elemSz (doublingCap minCap (j + 1)) ≤
              rawVecMaxLiveOfSteps M elemSz minCap (j + (n + 1)) :=
          Nat.le_trans (rawVecLargeLive_le_maxLiveOfSteps M elemSz minCap (j + 1))
            (VecGrowCreditHelpers.rawVecMaxLiveOfSteps_mono M elemSz minCap (by omega))
        have hpeak_max :
            rawVecLargeLive M elemSz (doublingCap minCap j) +
                rawVecLargeLive M elemSz (doublingCap minCap (j + 1)) ≤
              rawVecPeakOfSteps M elemSz minCap (j + (n + 1)) :=
          rawVecStepPeak_le_peakOfSteps M elemSz minCap (by omega)
        simp only [rawVecCumFrom]
        exact ⟨by omega, by omega, by omega⟩
    · have hEnv1 := hStep _ _ h1
      have hfit' : doublingCap minCap (j + 1 + n) < 2 ^ 64 := by rw [hidx]; exact hfit
      obtain ⟨hreq2, hcred2⟩ :=
        iterSeq_rawVecGrow_from_aux M helem hmin hal hStep n (j + 1) hfit' h2
      refine ⟨fun ev hev => ?_, fun st L_base hlive => ?_⟩
      · rcases List.mem_append.mp hev with he1 | he2
        · obtain ⟨hr, ha⟩ := rawVecGrowEnv_req_align helem hmin hal htoNat hEnv1 ev he1
          exact ⟨Nat.le_trans hr (Nat.mul_le_mul_right elemSz hj1_le), ha⟩
        · obtain ⟨hr, ha⟩ := hreq2 ev he2
          rw [hidx] at hr
          exact ⟨hr, ha⟩
      · rw [AllocCostModel.stepEvents_append]
        obtain ⟨hc1, hl1, hp1⟩ :=
          stepEvents_rawVecGrow_credit M st helem hmin hal htoNat hEnv1 hlive
        obtain ⟨hc2, hl2, hp2⟩ := hcred2 (M.stepEvents evs₁ st) L_base hl1
        have hpeak1 :
            rawVecLargeLive M elemSz (doublingCap minCap j) +
                rawVecLargeLive M elemSz (doublingCap minCap (j + 1)) ≤
              rawVecPeakOfSteps M elemSz minCap (j + (n + 1)) :=
          rawVecStepPeak_le_peakOfSteps M elemSz minCap (by omega)
        rw [hidx] at hl2 hp2
        simp only [rawVecCumFrom]
        exact ⟨by omega, hl2, by omega⟩

/-- Telescoping `PhaseCreditSpec` for an `IterSeqEnv` chain over `doublingCaps minCap k`
(`0 → minCap → 2 * minCap → … → doublingCap minCap k`), cancelling intermediate `sc = 63`
buffers at every `realloc` step and handling early prefix exits. -/
theorem phaseCreditSpec_rawVecGrow_chain (M : AllocCostModel) [HasFineReallocCredit M]
    {elemSz minCap align k : Nat} {Step : BitVec 64 → List AllocEvent → Prop}
    (helem : 0 < elemSz) (hmin : 0 < minCap) (hal : align ≤ 16)
    (hfit : doublingCap minCap k < 2 ^ 64)
    (hStep : ∀ (c : BitVec 64) (evs : List AllocEvent),
      Step c evs → RawVecGrowEnv elemSz minCap align ⟨0#64, c, 0#64, []⟩ evs) :
    PhaseCreditSpec M (IterSeqEnv Step (doublingCaps minCap k))
      (rawVecCumOfSteps M elemSz minCap align k)
      (rawVecMaxLiveOfSteps M elemSz minCap k)
      (rawVecPeakOfSteps M elemSz minCap k)
      (doublingCap minCap k * elemSz) where
  req_align evs hIter := by
    have hfit0 : doublingCap minCap (0 + k) < 2 ^ 64 := by simpa using hfit
    simpa using (iterSeq_rawVecGrow_from_aux M helem hmin hal hStep k 0 hfit0 hIter).1
  credit_le st0 {_} hIter := by
    have hfit0 : doublingCap minCap (0 + k) < 2 ^ 64 := by simpa using hfit
    have hcred := (iterSeq_rawVecGrow_from_aux M helem hmin hal hStep k 0 hfit0 hIter).2
      st0 (HasFineReallocCredit.liveLarge st0) (Nat.le_add_right _ _)
    rw [rawVecCumFrom_zero_eq] at hcred
    simpa using hcred

private theorem rawVecCumOfSteps_mono (M : AllocCostModel) [HasFineReallocCredit M]
    (elemSz minCap align : Nat) {m k : Nat} (hmk : m ≤ k) :
    rawVecCumOfSteps M elemSz minCap align m ≤ rawVecCumOfSteps M elemSz minCap align k := by
  induction hmk with
  | refl => exact Nat.le_refl _
  | @step r _ ih =>
    simp only [rawVecCumOfSteps]
    exact Nat.le_trans ih (Nat.le_add_right _ _)

theorem phaseCreditSpec_rawVecGrow_prefix (M : AllocCostModel) [HasFineReallocCredit M]
    {elemSz minCap align m k : Nat} {Step : BitVec 64 → List AllocEvent → Prop}
    (helem : 0 < elemSz) (hmin : 0 < minCap) (hal : align ≤ 16)
    (hmk : m ≤ k) (hfit : doublingCap minCap k < 2 ^ 64)
    (hStep : ∀ (c : BitVec 64) (evs : List AllocEvent),
      Step c evs → RawVecGrowEnv elemSz minCap align ⟨0#64, c, 0#64, []⟩ evs) :
    PhaseCreditSpec M (IterSeqEnv Step (doublingCaps minCap m))
      (rawVecCumOfSteps M elemSz minCap align k)
      (rawVecMaxLiveOfSteps M elemSz minCap k)
      (rawVecPeakOfSteps M elemSz minCap k)
      (doublingCap minCap k * elemSz) := by
  have hm_le : doublingCap minCap m ≤ doublingCap minCap k := doublingCap_mono minCap hmk
  exact (phaseCreditSpec_rawVecGrow_chain M helem hmin hal (by omega) hStep).mono
    (rawVecCumOfSteps_mono M elemSz minCap align hmk)
    (VecGrowCreditHelpers.rawVecMaxLiveOfSteps_mono M elemSz minCap hmk)
    (VecGrowCreditHelpers.rawVecPeakOfSteps_mono M elemSz minCap hmk)
    (Nat.mul_le_mul_right elemSz hm_le)

private theorem iterConcat_rawVecGrow_from_aux (M : AllocCostModel) [HasFineReallocCredit M]
    {elemSz minCap align : Nat} {Step : BitVec 64 → List AllocEvent → Prop}
    (helem : 0 < elemSz) (hmin : 0 < minCap) (hal : align ≤ 16)
    (hStep : ∀ (c : BitVec 64) (evs : List AllocEvent),
      Step c evs → RawVecGrowEnv elemSz minCap align ⟨0#64, c, 0#64, []⟩ evs) :
    ∀ (n j : Nat) {evs : List AllocEvent},
      doublingCap minCap (j + n) < 2 ^ 64 →
      IterConcatEnv Step (doublingCapsFrom minCap j n) evs →
      ∀ (st : M.σ) (L_base : Nat),
        HasFineReallocCredit.liveLarge st ≤
          L_base + rawVecLargeLive M elemSz (doublingCap minCap j) →
        HasFineReallocCredit.cumSmall (M.stepEvents evs st) ≤
          HasFineReallocCredit.cumSmall st + rawVecCumFrom M elemSz minCap align j n ∧
        HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤
          L_base + rawVecLargeLive M elemSz (doublingCap minCap (j + n)) ∧
        HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤
          max (HasFineReallocCredit.peakLarge st)
            (L_base + rawVecPeakOfSteps M elemSz minCap (j + n))
  | 0, j, evs, _, hIter => by
    simp only [doublingCapsFrom, VecGrowCreditHelpers.doublingCapsFrom, IterConcatEnv] at hIter
    subst hIter
    intro st L_base hlive
    simp only [AllocCostModel.stepEvents_nil, rawVecCumFrom, Nat.add_zero]
    exact ⟨Nat.le_refl _, hlive, Nat.le_max_left _ _⟩
  | n + 1, j, evs, hfit, hIter => by
    obtain ⟨evs₁, evs₂, rfl, h1, h2⟩ := hIter
    intro st L_base hlive
    have hj_le : doublingCap minCap j ≤ doublingCap minCap (j + (n + 1)) :=
      doublingCap_mono minCap (by omega)
    have htoNat : (BitVec.ofNat 64 (doublingCap minCap j)).toNat = doublingCap minCap j := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hidx : j + 1 + n = j + (n + 1) := by omega
    have hfit' : doublingCap minCap (j + 1 + n) < 2 ^ 64 := by rw [hidx]; exact hfit
    rw [AllocCostModel.stepEvents_append]
    obtain ⟨hc1, hl1, hp1⟩ :=
      stepEvents_rawVecGrow_credit M st helem hmin hal htoNat (hStep _ _ h1) hlive
    obtain ⟨hc2, hl2, hp2⟩ :=
      iterConcat_rawVecGrow_from_aux M helem hmin hal hStep n (j + 1) hfit' h2 _ L_base hl1
    have hpeak1 :
        rawVecLargeLive M elemSz (doublingCap minCap j) +
            rawVecLargeLive M elemSz (doublingCap minCap (j + 1)) ≤
          rawVecPeakOfSteps M elemSz minCap (j + (n + 1)) :=
      rawVecStepPeak_le_peakOfSteps M elemSz minCap (by omega)
    rw [hidx] at hl2 hp2
    simp only [rawVecCumFrom]
    exact ⟨by omega, hl2, by omega⟩

/-- Exact-endpoint `PhaseCreditSpec` for a completed `k`-step `IterConcatEnv` chain, tightening `Δlive` to `rawVecLargeLive M elemSz (doublingCap minCap k)`.
-/
theorem phaseCreditSpec_rawVecGrow_concatChain (M : AllocCostModel) [HasFineReallocCredit M]
    {elemSz minCap align k : Nat} {Step : BitVec 64 → List AllocEvent → Prop}
    (helem : 0 < elemSz) (hmin : 0 < minCap) (hal : align ≤ 16)
    (hfit : doublingCap minCap k < 2 ^ 64)
    (hStep : ∀ (c : BitVec 64) (evs : List AllocEvent),
      Step c evs → RawVecGrowEnv elemSz minCap align ⟨0#64, c, 0#64, []⟩ evs) :
    PhaseCreditSpec M (IterConcatEnv Step (doublingCaps minCap k))
      (rawVecCumOfSteps M elemSz minCap align k)
      (rawVecLargeLive M elemSz (doublingCap minCap k))
      (rawVecPeakOfSteps M elemSz minCap k)
      (doublingCap minCap k * elemSz) where
  req_align evs hIter :=
    (phaseCreditSpec_rawVecGrow_chain M helem hmin hal hfit hStep).req_align
      evs (IterConcatEnv.toIterSeqEnv hIter)
  credit_le st0 {_} hIter := by
    have hfit0 : doublingCap minCap (0 + k) < 2 ^ 64 := by simpa using hfit
    have hcred := iterConcat_rawVecGrow_from_aux M helem hmin hal hStep k 0 hfit0 hIter
      st0 (HasFineReallocCredit.liveLarge st0) (Nat.le_add_right _ _)
    rw [rawVecCumFrom_zero_eq] at hcred
    simpa using hcred

/-! ## 3. Concrete Element-Stride Specializations -/

theorem stepEvents_growOneVecU8_credit (M : AllocCostModel) [HasFineReallocCredit M]
    {j L_base : Nat} {x : GrowOneCall} {evs : List AllocEvent} (st : M.σ)
    (hcap : x.cap.toNat = doublingCap 4 j)
    (hEnv : GrowOneVecU8Env x evs)
    (hlive : HasFineReallocCredit.liveLarge st ≤
      L_base + rawVecLargeLive M 24 (doublingCap 4 j)) :
    let st' := M.stepEvents evs st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + rawVecStepCum M 24 4 8 j ∧
    HasFineReallocCredit.liveLarge st' ≤
      L_base + rawVecLargeLive M 24 (doublingCap 4 (j + 1)) ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (L_base + rawVecLargeLive M 24 (doublingCap 4 j) +
          rawVecLargeLive M 24 (doublingCap 4 (j + 1))) :=
  stepEvents_rawVecGrow_credit M st (by decide) (by decide) (by decide) hcap hEnv hlive

theorem phaseCreditSpec_growOneVecU8_chain (M : AllocCostModel) [HasFineReallocCredit M]
    {k : Nat} {Step : BitVec 64 → List AllocEvent → Prop}
    (hfit : doublingCap 4 k < 2 ^ 64)
    (hStep : ∀ (c : BitVec 64) (evs : List AllocEvent),
      Step c evs → GrowOneVecU8Env ⟨0#64, c, 0#64, []⟩ evs) :
    PhaseCreditSpec M (IterSeqEnv Step (doublingCaps 4 k))
      (rawVecCumOfSteps M 24 4 8 k)
      (rawVecMaxLiveOfSteps M 24 4 k)
      (rawVecPeakOfSteps M 24 4 k)
      (doublingCap 4 k * 24) :=
  phaseCreditSpec_rawVecGrow_chain M (by decide) (by decide) (by decide) hfit hStep

theorem stepEvents_growOneU8_credit (M : AllocCostModel) [HasFineReallocCredit M]
    {j L_base : Nat} {x : GrowOneCall} {evs : List AllocEvent} (st : M.σ)
    (hcap : x.cap.toNat = doublingCap 8 j)
    (hEnv : GrowOneU8Env x evs)
    (hlive : HasFineReallocCredit.liveLarge st ≤
      L_base + rawVecLargeLive M 1 (doublingCap 8 j)) :
    let st' := M.stepEvents evs st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + rawVecStepCum M 1 8 1 j ∧
    HasFineReallocCredit.liveLarge st' ≤
      L_base + rawVecLargeLive M 1 (doublingCap 8 (j + 1)) ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (L_base + rawVecLargeLive M 1 (doublingCap 8 j) +
          rawVecLargeLive M 1 (doublingCap 8 (j + 1))) :=
  stepEvents_rawVecGrow_credit M st (by decide) (by decide) (by decide) hcap
    ((GrowOneU8Env_iff_rawVecGrowEnv x evs).mp hEnv) hlive

theorem phaseCreditSpec_growOneU8_chain (M : AllocCostModel) [HasFineReallocCredit M]
    {k : Nat} {Step : BitVec 64 → List AllocEvent → Prop}
    (hfit : doublingCap 8 k < 2 ^ 64)
    (hStep : ∀ (c : BitVec 64) (evs : List AllocEvent),
      Step c evs → GrowOneU8Env ⟨0#64, c, 0#64, []⟩ evs) :
    PhaseCreditSpec M (IterSeqEnv Step (doublingCaps 8 k))
      (rawVecCumOfSteps M 1 8 1 k)
      (rawVecMaxLiveOfSteps M 1 8 k)
      (rawVecPeakOfSteps M 1 8 k)
      (doublingCap 8 k * 1) :=
  phaseCreditSpec_rawVecGrow_chain M (by decide) (by decide) (by decide) hfit
    (fun c evs h => (GrowOneU8Env_iff_rawVecGrowEnv _ evs).mp (hStep c evs h))

theorem growOne104Events_eq_rawVecGrowEvents (cap : BitVec 64) :
    growOne104Events cap = rawVecGrowEvents 104 4 8 cap := by
  unfold growOne104Events finishGrowEvents rawVecGrowEvents rawVecNewCap
  by_cases h : cap = 0#64
  · subst h; rfl
  · have hne : cap.toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq h0)
    simp [h, hne]

theorem stepEvents_growOne104_credit (M : AllocCostModel) [HasFineReallocCredit M]
    {j L_base : Nat} {cap : BitVec 64} {evs : List AllocEvent} (st : M.σ)
    (hcap : cap.toNat = doublingCap 4 j)
    (hEnv : GrowOne104Env cap evs)
    (hlive : HasFineReallocCredit.liveLarge st ≤
      L_base + rawVecLargeLive M 104 (doublingCap 4 j)) :
    let st' := M.stepEvents evs st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + rawVecStepCum M 104 4 8 j ∧
    HasFineReallocCredit.liveLarge st' ≤
      L_base + rawVecLargeLive M 104 (doublingCap 4 (j + 1)) ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (L_base + rawVecLargeLive M 104 (doublingCap 4 j) +
          rawVecLargeLive M 104 (doublingCap 4 (j + 1))) := by
  have hRaw : RawVecGrowEnv 104 4 8 ⟨0#64, cap, 0#64, []⟩ evs := by
    unfold GrowOne104Env at hEnv
    rw [hEnv, growOne104Events_eq_rawVecGrowEvents]
    exact rawVecGrowEnv_events 104 4 8 ⟨0#64, cap, 0#64, []⟩
  exact stepEvents_rawVecGrow_credit M st (by decide) (by decide) (by decide) hcap hRaw hlive

theorem phaseCreditSpec_growOne104_chain (M : AllocCostModel) [HasFineReallocCredit M]
    {k : Nat} (hfit : doublingCap 4 k < 2 ^ 64) :
    PhaseCreditSpec M (IterSeqEnv GrowOne104Env (doublingCaps 4 k))
      (rawVecCumOfSteps M 104 4 8 k)
      (rawVecMaxLiveOfSteps M 104 4 k)
      (rawVecPeakOfSteps M 104 4 k)
      (doublingCap 4 k * 104) :=
  phaseCreditSpec_rawVecGrow_chain M (by decide) (by decide) (by decide) hfit
    (fun c evs h => by
      unfold GrowOne104Env at h
      rw [h, growOne104Events_eq_rawVecGrowEvents]
      exact rawVecGrowEnv_events 104 4 8 ⟨0#64, c, 0#64, []⟩)

theorem stepEvents_growOneDir_credit (M : AllocCostModel) [HasFineReallocCredit M]
    {j L_base : Nat} {x : GrowOneDirGhost} {evs : List AllocEvent} (st : M.σ)
    (hcap : x.cap.toNat = doublingCap 4 j)
    (hEnv : GrowOneDirEnv x evs)
    (hlive : HasFineReallocCredit.liveLarge st ≤
      L_base + rawVecLargeLive M 48 (doublingCap 4 j)) :
    let st' := M.stepEvents evs st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + rawVecStepCum M 48 4 8 j ∧
    HasFineReallocCredit.liveLarge st' ≤
      L_base + rawVecLargeLive M 48 (doublingCap 4 (j + 1)) ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (L_base + rawVecLargeLive M 48 (doublingCap 4 j) +
          rawVecLargeLive M 48 (doublingCap 4 (j + 1))) := by
  have hRaw : RawVecGrowEnv 48 4 8 ⟨0#64, x.cap, 0#64, []⟩ evs := by
    unfold GrowOneDirEnv at hEnv
    rw [hEnv]
    exact rawVecGrowEnv_events 48 4 8 ⟨0#64, x.cap, 0#64, []⟩
  exact stepEvents_rawVecGrow_credit M st (by decide) (by decide) (by decide) hcap hRaw hlive

theorem phaseCreditSpec_growOneDir_chain (M : AllocCostModel) [HasFineReallocCredit M]
    {k : Nat} (hfit : doublingCap 4 k < 2 ^ 64) :
    PhaseCreditSpec M (IterSeqEnv GrowOneDirBytesEnv (doublingCaps 4 k))
      (rawVecCumOfSteps M 48 4 8 k)
      (rawVecMaxLiveOfSteps M 48 4 k)
      (rawVecPeakOfSteps M 48 4 k)
      (doublingCap 4 k * 48) :=
  phaseCreditSpec_rawVecGrow_chain M (by decide) (by decide) (by decide) hfit
    (fun c evs h => by
      unfold GrowOneDirBytesEnv at h
      rw [h]
      exact rawVecGrowEnv_events 48 4 8 ⟨0#64, c, 0#64, []⟩)

theorem stepEvents_growOneSpe_credit (M : AllocCostModel) [HasFineReallocCredit M]
    {j L_base : Nat} {cap : BitVec 64} {evs : List AllocEvent} (st : M.σ)
    (hcap : cap.toNat = doublingCap 4 j)
    (hEnv : GrowOneSpeEnv cap evs)
    (hlive : HasFineReallocCredit.liveLarge st ≤
      L_base + rawVecLargeLive M 48 (doublingCap 4 j)) :
    let st' := M.stepEvents evs st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + rawVecStepCum M 48 4 8 j ∧
    HasFineReallocCredit.liveLarge st' ≤
      L_base + rawVecLargeLive M 48 (doublingCap 4 (j + 1)) ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (L_base + rawVecLargeLive M 48 (doublingCap 4 j) +
          rawVecLargeLive M 48 (doublingCap 4 (j + 1))) := by
  have hRaw : RawVecGrowEnv 48 4 8 ⟨0#64, cap, 0#64, []⟩ evs := by
    rw [growOneSpeEvents_eq_of_env hEnv]
    exact rawVecGrowEnv_events 48 4 8 ⟨0#64, cap, 0#64, []⟩
  exact stepEvents_rawVecGrow_credit M st (by decide) (by decide) (by decide) hcap hRaw hlive

theorem growOnePtEvents_eq_rawVecGrowEvents {len : Nat} (hlen : len < 2 ^ 64) :
    growOnePtEvents len = rawVecGrowEvents 4 4 2 (BitVec.ofNat 64 len) := by
  unfold growOnePtEvents rawVecGrowEvents rawVecNewCap
  have htoNat : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen]
  by_cases h0 : len = 0
  · subst h0; rfl
  · have hne : BitVec.ofNat 64 len ≠ 0#64 := by
      intro heq
      have ht := congrArg BitVec.toNat heq
      simp [htoNat] at ht
      exact h0 ht
    simp only [h0, hne, ↓reduceIte, htoNat]
    rw [Nat.mul_comm 4 len, Nat.mul_comm 4 (max (2 * len) 4)]

theorem stepEvents_growOnePt_credit (M : AllocCostModel) [HasFineReallocCredit M]
    {j L_base : Nat} (st : M.σ) (hfit : doublingCap 4 j < 2 ^ 64)
    (hlive : HasFineReallocCredit.liveLarge st ≤
      L_base + rawVecLargeLive M 4 (doublingCap 4 j)) :
    let st' := M.stepEvents (growOnePtEvents (doublingCap 4 j)) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + rawVecStepCum M 4 4 2 j ∧
    HasFineReallocCredit.liveLarge st' ≤
      L_base + rawVecLargeLive M 4 (doublingCap 4 (j + 1)) ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (L_base + rawVecLargeLive M 4 (doublingCap 4 j) +
          rawVecLargeLive M 4 (doublingCap 4 (j + 1))) := by
  rw [growOnePtEvents_eq_rawVecGrowEvents hfit]
  have htoNat : (BitVec.ofNat 64 (doublingCap 4 j)).toNat = doublingCap 4 j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
  exact stepEvents_rawVecGrow_credit M st (by decide) (by decide) (by decide) htoNat
    (rawVecGrowEnv_events 4 4 2 ⟨0#64, BitVec.ofNat 64 (doublingCap 4 j), 0#64, []⟩) hlive

theorem phaseCreditSpec_growOnePt_chain (M : AllocCostModel) [HasFineReallocCredit M]
    {k : Nat} (hfit : doublingCap 4 k < 2 ^ 64) :
    PhaseCreditSpec M
      (IterSeqEnv (fun c evs => evs = growOnePtEvents c.toNat) (doublingCaps 4 k))
      (rawVecCumOfSteps M 4 4 2 k)
      (rawVecMaxLiveOfSteps M 4 4 k)
      (rawVecPeakOfSteps M 4 4 k)
      (doublingCap 4 k * 4) :=
  phaseCreditSpec_rawVecGrow_chain M (by decide) (by decide) (by decide) hfit
    (fun c evs h => by
      rw [h, growOnePtEvents_eq_rawVecGrowEvents c.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact rawVecGrowEnv_events 4 4 2 ⟨0#64, c, 0#64, []⟩)

/-- `PhaseCreditSpec` for `<PolyDecoder as Decoder>::add_chunk` (`AddChunkEnv x`) when each slot has `s.vec.length ≤ maxPts` in the small-allocation regime.
-/
theorem phaseCreditSpec_addChunk {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {x : AddChunkGhost} {maxPts : Nat}
    (hpts : ∀ s ∈ x.dec.pts, s.vec.length ≤ maxPts)
    (hsmall : 4 * max (2 * maxPts) 4 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (AddChunkEnv x)
      ((2 * (4 * max (2 * maxPts) 4) + 9539) * x.dec.pts.length)
      0 0
      (4 * max (2 * maxPts) 4) := by
  unfold AddChunkEnv
  generalize x.dec.pts = pts at hpts ⊢
  induction pts with
  | nil =>
    simpa [AddChunkSlotsEnv] using
      (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | cons s rest ih =>
    have hs_len : s.vec.length ≤ maxPts := hpts s List.mem_cons_self
    have hnew_le : 4 * max (2 * s.vec.length) 4 ≤ 4 * max (2 * maxPts) 4 := by omega
    have hnew_pos : 0 < 4 * max (2 * s.vec.length) 4 := by omega
    have hnew_small : 4 * max (2 * s.vec.length) 4 ≤ HasFineReallocCredit.smallMaxReq M :=
      Nat.le_trans hnew_le hsmall
    have heq_events :
        growOnePtEvents s.vec.length =
          growOrReallocEvents (4 * s.vec.length) (4 * max (2 * s.vec.length) 4) 2 := by
      unfold growOnePtEvents growOrReallocEvents
      by_cases h0 : s.vec.length = 0
      · simp [h0]
      · have hmul : 4 * s.vec.length ≠ 0 := by omega
        simp [h0, hmul]
    have hSlotGrow :
        PhaseCreditSpec M (· = growOnePtEvents s.vec.length)
          (2 * (4 * max (2 * maxPts) 4) + 9539) 0 0 (4 * max (2 * maxPts) 4) := by
      rw [heq_events]
      refine (phaseCreditSpec_growOrRealloc M (by decide) hnew_pos).mono ?_ ?_ ?_ hnew_le
      · have haff := VecGrowCreditHelpers.growOrReallocStepCum_le_affine M
          (fun _ hr => hM.smallAlloc_le hr) (fun _ hr => hM.smallRealloc_le hr) hM.meta_le
          (4 * s.vec.length) (4 * max (2 * s.vec.length) 4) 2
        simp only [hnew_small, ↓reduceIte] at haff
        omega
      · rw [VecGrowCreditHelpers.allocLargeLive_of_le M hnew_small]
        omega
      · rw [VecGrowCreditHelpers.allocLargeLive_of_le M hnew_small]
    have hSlot :
        PhaseCreditSpec M (AddChunkSlotEnv s)
          (2 * (4 * max (2 * maxPts) 4) + 9539) 0 0 (4 * max (2 * maxPts) 4) := by
      unfold AddChunkSlotEnv
      simpa using (PhaseCreditSpec.nil M).or hSlotGrow
    have hRest := ih (fun t ht => hpts t (List.mem_cons_of_mem s ht))
    have hSeq := hSlot.seq hRest
    simpa [AddChunkSlotsEnv, List.length_cons, Nat.mul_succ, Nat.add_comm] using hSeq

theorem vecDequeGrowEvents_eq_rawVecGrowEvents (cap : BitVec 64) :
    vecDequeGrowEvents cap = rawVecGrowEvents chainEpochSize 4 chainEpochAlign cap := by
  rfl

theorem stepEvents_vecDequeGrow_credit (M : AllocCostModel) [HasFineReallocCredit M]
    {j L_base : Nat} {x : VecDequeGrowGhost} {evs : List AllocEvent} (st : M.σ)
    (hcap : x.cap.toNat = doublingCap 4 j)
    (hEnv : VecDequeGrowEnv x evs)
    (hlive : HasFineReallocCredit.liveLarge st ≤
      L_base + rawVecLargeLive M chainEpochSize (doublingCap 4 j)) :
    let st' := M.stepEvents evs st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st +
        rawVecStepCum M chainEpochSize 4 chainEpochAlign j ∧
    HasFineReallocCredit.liveLarge st' ≤
      L_base + rawVecLargeLive M chainEpochSize (doublingCap 4 (j + 1)) ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (L_base + rawVecLargeLive M chainEpochSize (doublingCap 4 j) +
          rawVecLargeLive M chainEpochSize (doublingCap 4 (j + 1))) := by
  have hRaw : RawVecGrowEnv chainEpochSize 4 chainEpochAlign ⟨0#64, x.cap, 0#64, []⟩ evs := by
    unfold VecDequeGrowEnv at hEnv
    rw [hEnv, vecDequeGrowEvents_eq_rawVecGrowEvents]
    exact rawVecGrowEnv_events chainEpochSize 4 chainEpochAlign _
  exact stepEvents_rawVecGrow_credit M st (by decide) (by decide) (by decide) hcap hRaw hlive

theorem phaseCreditSpec_vecDequeGrow_chain (M : AllocCostModel) [HasFineReallocCredit M]
    {k : Nat} {Step : BitVec 64 → List AllocEvent → Prop}
    (hfit : doublingCap 4 k < 2 ^ 64)
    (hStep : ∀ (c : BitVec 64) (evs : List AllocEvent),
      Step c evs → evs = vecDequeGrowEvents c) :
    PhaseCreditSpec M (IterSeqEnv Step (doublingCaps 4 k))
      (rawVecCumOfSteps M chainEpochSize 4 chainEpochAlign k)
      (rawVecMaxLiveOfSteps M chainEpochSize 4 k)
      (rawVecPeakOfSteps M chainEpochSize 4 k)
      (doublingCap 4 k * chainEpochSize) :=
  phaseCreditSpec_rawVecGrow_chain M (by decide) (by decide) (by decide) hfit
    (fun c evs h => by
      rw [hStep c evs h, vecDequeGrowEvents_eq_rawVecGrowEvents]
      exact rawVecGrowEnv_events chainEpochSize 4 chainEpochAlign _)

/-! ## 4. Super-Doubling `do_reserve` and `bytes::merge` Overwrite Credit -/

theorem super_doubling_sum_le {cs : List Nat} {capMax : Nat}
    (h : IsSuperDoubling cs) (hlast : lastOrZero cs ≤ capMax) :
    cs.sum ≤ 2 * capMax :=
  VecGrowCreditHelpers.super_doubling_sum_le h hlast

theorem doReserveEvents_eq_growOrReallocEvents (x : DoReserveCall) :
    doReserveEvents x =
      growOrReallocEvents x.cap.toNat (reserveCap x.cap.toNat x.bs.length x.additional) 1 := by
  unfold doReserveEvents growOrReallocEvents
  dsimp only [TripleRatchet.Alloc.DefsBudget.reserveCap]
  by_cases h0 : x.cap = 0#64
  · simp [h0]
  · have hne : x.cap.toNat ≠ 0 := fun ht => h0 (BitVec.eq_of_toNat_eq ht)
    simp [h0, hne]

/-- Realloc-credit transition for `DoReserveEnv x`, cancelling `allocLargeLive M x.cap.toNat` out of `liveLarge`.
-/
theorem stepEvents_doReserve_credit (M : AllocCostModel) [HasFineReallocCredit M]
    {L_base : Nat} {x : DoReserveCall} {evs : List AllocEvent} (st : M.σ)
    (hEnv : DoReserveEnv x evs)
    (hlive : HasFineReallocCredit.liveLarge st ≤ L_base + allocLargeLive M x.cap.toNat) :
    let newCap := reserveCap x.cap.toNat x.bs.length x.additional
    let st' := M.stepEvents evs st
    2 * x.cap.toNat ≤ newCap ∧
    8 ≤ newCap ∧
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + growOrReallocStepCum M x.cap.toNat newCap 1 ∧
    HasFineReallocCredit.liveLarge st' ≤ L_base + allocLargeLive M newCap ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (L_base + allocLargeLive M x.cap.toNat + allocLargeLive M newCap) := by
  intro newCap st'
  have h2 : 2 * x.cap.toNat ≤ newCap := by dsimp [newCap, reserveCap]; omega
  have h8 : 8 ≤ newCap := by dsimp [newCap, reserveCap]; omega
  have hcred :
      HasFineReallocCredit.cumSmall st' ≤
        HasFineReallocCredit.cumSmall st + growOrReallocStepCum M x.cap.toNat newCap 1 ∧
      HasFineReallocCredit.liveLarge st' ≤ L_base + allocLargeLive M newCap ∧
      HasFineReallocCredit.peakLarge st' ≤
        max (HasFineReallocCredit.peakLarge st)
          (L_base + allocLargeLive M x.cap.toNat + allocLargeLive M newCap) := by
    dsimp [st']
    unfold DoReserveEnv at hEnv
    rw [hEnv, doReserveEvents_eq_growOrReallocEvents]
    exact stepEvents_growOrRealloc_credit M st (by decide) (by omega) hlive
  exact ⟨h2, h8, hcred⟩

/-- Updated capacity of a `Vec<u8>` after `doReserveClearEvents cap vLen` / `bytes::merge`. -/
def bytesMergeOutCap (cap vLen : Nat) : Nat :=
  if vLen ≤ cap then cap else reserveCap cap 0 vLen

/-- Single-step `cumSmall` charge of `doReserveClearEvents cap vLen`. -/
def doReserveClearStepCum (M : AllocCostModel) [HasFineReallocCredit M]
    (cap vLen : Nat) : Nat :=
  if vLen ≤ cap then 0 else growOrReallocStepCum M cap (reserveCap cap 0 vLen) 1

/-- Single-step `cumSmall` charge of `bytesMergeEventsCore` on a `some (v, _)` step (`vLen = v.length`). -/
def bytesMergeOkStepCum (M : AllocCostModel) [HasFineReallocCredit M]
    (cap vLen : Nat) : Nat :=
  if vLen = 0 then 0 else allocStepCum M vLen + doReserveClearStepCum M cap vLen

theorem bytesMergeOutCap_le_of_wire {cap vLen maxWire : Nat}
    (hcap : cap ≤ max (2 * maxWire) 8) (hv : vLen ≤ maxWire) :
    bytesMergeOutCap cap vLen ≤ max (2 * maxWire) 8 := by
  unfold bytesMergeOutCap
  split
  · exact hcap
  · dsimp [reserveCap]
    omega

theorem stepEvents_doReserveClear_credit (M : AllocCostModel) [HasFineReallocCredit M]
    {cap vLen L_base : Nat} (st : M.σ)
    (hlive : HasFineReallocCredit.liveLarge st ≤ L_base + allocLargeLive M cap) :
    let outCap := bytesMergeOutCap cap vLen
    let st' := M.stepEvents (doReserveClearEvents cap vLen) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + doReserveClearStepCum M cap vLen ∧
    HasFineReallocCredit.liveLarge st' ≤ L_base + allocLargeLive M outCap ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (L_base + allocLargeLive M cap + allocLargeLive M outCap) := by
  intro outCap st'
  by_cases hle : vLen ≤ cap
  · simp only [st', outCap, doReserveClearEvents, bytesMergeOutCap, doReserveClearStepCum,
      hle, ↓reduceIte, AllocCostModel.stepEvents_nil, Nat.add_zero]
    exact ⟨Nat.le_refl _, hlive, Nat.le_max_left _ _⟩
  · have heq : doReserveClearEvents cap vLen =
        growOrReallocEvents cap (reserveCap cap 0 vLen) 1 := by
      unfold doReserveClearEvents growOrReallocEvents
      simp [hle]
    have hout : outCap = reserveCap cap 0 vLen := by simp [outCap, bytesMergeOutCap, hle]
    have hcum : doReserveClearStepCum M cap vLen =
        growOrReallocStepCum M cap (reserveCap cap 0 vLen) 1 := by
      simp [doReserveClearStepCum, hle]
    have hpos : 0 < reserveCap cap 0 vLen := by dsimp [reserveCap]; omega
    dsimp [st']
    rw [heq, hout, hcum]
    exact stepEvents_growOrRealloc_credit M st (by decide) hpos hlive

theorem bytesMergeEventsCore_req_align (wt : WireType) (valCap : BitVec 64)
    (bs : List (BitVec 8)) :
    ∀ ev ∈ bytesMergeEventsCore wt valCap bs,
      (match mergeBytes wt bs with
       | none => eventStepReq ev ≤ 72
       | some (v, _) =>
         eventStepReq ev ≤ max v.length (bytesMergeOutCap valCap.toNat v.length)) ∧
      eventStepAlign ev ≤ 16 := by
  unfold bytesMergeEventsCore
  cases hmb : mergeBytes wt bs with
  | none =>
    intro ev hev
    exact rustAllocEvents_req_align (by decide) ev hev
  | some vr =>
    rcases vr with ⟨v, rest⟩
    by_cases hv0 : v.length = 0
    · simp only [hv0, ↓reduceIte]
      intro _ hev; nomatch hev
    · simp only [hv0, ↓reduceIte]
      intro ev hev
      rcases List.mem_append.mp hev with h12 | h3
      · rcases List.mem_append.mp h12 with h1 | h2
        · obtain ⟨hr, ha⟩ := rustAllocEvents_req_align (by decide) ev h1
          exact ⟨Nat.le_trans hr (Nat.le_max_left _ _), ha⟩
        · unfold doReserveClearEvents at h2
          by_cases hle : v.length ≤ valCap.toNat
          · simp [hle] at h2
          · have heq :
                (if valCap.toNat = 0 then rustAllocEvents (reserveCap valCap.toNat 0 v.length) 1
                 else rustReallocEvents valCap.toNat (reserveCap valCap.toNat 0 v.length) 1) =
                growOrReallocEvents valCap.toNat (reserveCap valCap.toNat 0 v.length) 1 := rfl
            simp only [hle, ↓reduceIte, heq] at h2
            obtain ⟨hr, ha⟩ := growOrReallocEvents_req_align (by decide) ev h2
            have hout : bytesMergeOutCap valCap.toNat v.length =
                reserveCap valCap.toNat 0 v.length := by simp [bytesMergeOutCap, hle]
            rw [← hout] at hr
            exact ⟨Nat.le_trans hr (Nat.le_max_right _ _), ha⟩
      · obtain ⟨hr, ha⟩ := rustDeallocEvents_req_align v.length 1 ev h3
        exact ⟨by omega, ha⟩

/-- Credit transition for `bytesMergeEventsCore wt valCap bs` (`BytesMergeEnv`): on `some (v, rest)`,
cancels both `allocLargeLive M valCap.toNat` (`realloc`) and `allocLargeLive M v.length` (`.free`)
out of `liveLarge`. -/
theorem stepEvents_bytesMergeEventsCore_credit (M : AllocCostModel) [HasFineReallocCredit M]
    {L_base : Nat} (wt : WireType) (valCap : BitVec 64) (bs : List (BitVec 8)) (st : M.σ)
    (hlive : HasFineReallocCredit.liveLarge st ≤ L_base + allocLargeLive M valCap.toNat) :
    let st' := M.stepEvents (bytesMergeEventsCore wt valCap bs) st
    match mergeBytes wt bs with
    | none =>
      HasFineReallocCredit.cumSmall st' ≤
        HasFineReallocCredit.cumSmall st + allocStepCum M 72 ∧
      HasFineReallocCredit.liveLarge st' ≤
        L_base + allocLargeLive M valCap.toNat + allocLargeLive M 72 ∧
      HasFineReallocCredit.peakLarge st' ≤
        max (HasFineReallocCredit.peakLarge st)
          (L_base + allocLargeLive M valCap.toNat + allocLargeLive M 72)
    | some (v, _) =>
      let outCap := bytesMergeOutCap valCap.toNat v.length
      HasFineReallocCredit.cumSmall st' ≤
        HasFineReallocCredit.cumSmall st + bytesMergeOkStepCum M valCap.toNat v.length ∧
      HasFineReallocCredit.liveLarge st' ≤ L_base + allocLargeLive M outCap ∧
      HasFineReallocCredit.peakLarge st' ≤
        max (HasFineReallocCredit.peakLarge st)
          (L_base + allocLargeLive M v.length +
            allocLargeLive M valCap.toNat + allocLargeLive M outCap) := by
  intro st'
  dsimp [st']
  unfold bytesMergeEventsCore
  cases hmb : mergeBytes wt bs with
  | none =>
    simp only []
    obtain ⟨hc, hl, hp⟩ :=
      stepEvents_rustAlloc_credit M (req := 72) (align := 8) st (by decide) (by decide)
    exact ⟨hc, by omega, by omega⟩
  | some vr =>
    rcases vr with ⟨v, rest⟩
    dsimp only []
    by_cases hv0 : v.length = 0
    · have hout : bytesMergeOutCap valCap.toNat v.length = valCap.toNat := by
        simp [bytesMergeOutCap, hv0]
      rw [hout]
      simp only [hv0, ↓reduceIte, AllocCostModel.stepEvents_nil, bytesMergeOkStepCum,
        Nat.add_zero]
      exact ⟨Nat.le_refl _, hlive, Nat.le_max_left _ _⟩
    · have hv_pos : 0 < v.length := Nat.pos_of_ne_zero hv0
      by_cases hle : v.length ≤ valCap.toNat
      · have hclr : doReserveClearEvents valCap.toNat v.length = [] := by
          simp [doReserveClearEvents, hle]
        have hout : bytesMergeOutCap valCap.toNat v.length = valCap.toNat := by
          simp [bytesMergeOutCap, hle]
        have hcum : bytesMergeOkStepCum M valCap.toNat v.length = allocStepCum M v.length := by
          simp [bytesMergeOkStepCum, doReserveClearStepCum, hv0, hle]
        simp only [hv0, ↓reduceIte, hclr, List.append_nil, hout, hcum]
        obtain ⟨hc, hl, hp⟩ :=
          stepEvents_alloc_dealloc_credit M (tmpReq := v.length) (align := 1)
            st (by decide) hv_pos hlive
        exact ⟨hc, hl, by omega⟩
      · have hclr : doReserveClearEvents valCap.toNat v.length =
            growOrReallocEvents valCap.toNat (reserveCap valCap.toNat 0 v.length) 1 := by
          unfold doReserveClearEvents growOrReallocEvents
          simp [hle]
        have hout : bytesMergeOutCap valCap.toNat v.length =
            reserveCap valCap.toNat 0 v.length := by simp [bytesMergeOutCap, hle]
        have hcum : bytesMergeOkStepCum M valCap.toNat v.length =
            allocStepCum M v.length +
              growOrReallocStepCum M valCap.toNat (reserveCap valCap.toNat 0 v.length) 1 := by
          simp [bytesMergeOkStepCum, doReserveClearStepCum, hv0, hle]
        have hpos_out : 0 < reserveCap valCap.toNat 0 v.length := by dsimp [reserveCap]; omega
        simp only [hv0, ↓reduceIte, hclr, hout, hcum]
        obtain ⟨hc, hl, hp⟩ := stepEvents_alloc_growOrRealloc_dealloc_credit M
          (tmpReq := v.length) (oldCap := valCap.toNat)
          (newCap := reserveCap valCap.toNat 0 v.length)
          (alignTmp := 1) (alignBuf := 1) st (by decide) (by decide)
          hv_pos hpos_out hlive
        exact ⟨by omega, hl, hp⟩

/-- Capacity-threaded sequence of `BytesMergeGhost` calls overwriting a single `Vec<u8>` buffer
on wire slices whose individual field payloads have length `≤ maxWire`. -/
inductive BytesMergeChainOk : Nat → List BytesMergeGhost → Nat → Prop where
  | nil (cap maxWire : Nat) : BytesMergeChainOk cap [] maxWire
  | err {cap maxWire : Nat} (x : BytesMergeGhost) :
      mergeBytes x.wt x.bs = none →
      x.valCap.toNat = cap →
      BytesMergeChainOk cap [x] maxWire
  | ok {cap maxWire : Nat} (x : BytesMergeGhost) (v rest : List (BitVec 8))
      (xs : List BytesMergeGhost) :
      mergeBytes x.wt x.bs = some (v, rest) →
      x.valCap.toNat = cap →
      v.length ≤ maxWire →
      BytesMergeChainOk (bytesMergeOutCap cap v.length) xs maxWire →
      BytesMergeChainOk cap (x :: xs) maxWire

/-- Total merged payload bytes across a list of `BytesMergeGhost` calls. -/
def bytesMergePayloadSum : List BytesMergeGhost → Nat
  | [] => 0
  | x :: xs =>
    (match mergeBytes x.wt x.bs with
     | none => 0
     | some (v, _) => v.length) + bytesMergePayloadSum xs

/-- Affine upper bound on `allocLargeLive M req` under `ModelHyps M`. -/
def largeLiveBound (M : AllocCostModel) [HasFineReallocCredit M] (req : Nat) : Nat :=
  if req ≤ HasFineReallocCredit.smallMaxReq M then 0 else req + 8195

private theorem bytesMergeOkStepCum_amortized {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (cap vLen : Nat) :
    let S := HasFineReallocCredit.smallMaxReq M
    let outCap := bytesMergeOutCap cap vLen
    bytesMergeOkStepCum M cap vLen + 4 * min cap S ≤
      4 * min outCap S + (2 * vLen + 19078) := by
  intro S outCap
  by_cases hv0 : vLen = 0
  · have hout : outCap = cap := by simp [outCap, bytesMergeOutCap, hv0]
    simp only [bytesMergeOkStepCum, hv0, ↓reduceIte, hout]
    omega
  · have halloc := allocStepCum_le_affine M (fun _ hr => hM.smallAlloc_le hr) hM.meta_le vLen
    have halloc' : allocStepCum M vLen ≤ 2 * vLen + 9539 := by split at halloc <;> omega
    by_cases hle : vLen ≤ cap
    · have hout : outCap = cap := by simp [outCap, bytesMergeOutCap, hle]
      simp only [bytesMergeOkStepCum, doReserveClearStepCum, hv0, hle, ↓reduceIte, hout]
      omega
    · have hout : outCap = reserveCap cap 0 vLen := by simp [outCap, bytesMergeOutCap, hle]
      have h2 : 2 * cap ≤ outCap := by rw [hout]; dsimp [reserveCap]; omega
      have hgrow := growOrReallocStepCum_amortized M
        (fun _ hr => hM.smallAlloc_le hr) (fun _ hr => hM.smallRealloc_le hr) hM.meta_le
        (align := 1) h2
      simp only [bytesMergeOkStepCum, doReserveClearStepCum, hv0, hle, ↓reduceIte]
      rw [← hout]
      dsimp [S] at *
      omega

private theorem largeLiveBound_mono (M : AllocCostModel) [HasFineReallocCredit M]
    {a b : Nat} (hab : a ≤ b) :
    largeLiveBound M a ≤ largeLiveBound M b := by
  unfold largeLiveBound
  split <;> split <;> omega

private theorem allocLargeLive_le_largeLiveBound {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (req : Nat) :
    allocLargeLive M req ≤ largeLiveBound M req :=
  allocLargeLive_le_affine M (fun _ hr => hM.largeCost_le hr) req

private theorem iterSeq_bytesMerge_overwrite_aux {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {cap maxWire : Nat} {xs : List BytesMergeGhost}
    (hChain : BytesMergeChainOk cap xs maxWire) :
    let S := HasFineReallocCredit.smallMaxReq M
    let maxOut := max (2 * maxWire) 8
    ∀ {evs : List AllocEvent},
      cap ≤ maxOut →
      IterSeqEnv BytesMergeEnv xs evs →
      (∀ ev ∈ evs, eventStepReq ev ≤ max maxOut 72 ∧ eventStepAlign ev ≤ 16) ∧
      (∀ (st : M.σ) (L_base : Nat),
        HasFineReallocCredit.liveLarge st ≤ L_base + allocLargeLive M cap →
        HasFineReallocCredit.cumSmall (M.stepEvents evs st) ≤
          HasFineReallocCredit.cumSmall st +
            (4 * min maxOut S - 4 * min cap S) +
            2 * bytesMergePayloadSum xs + 19078 * xs.length ∧
        HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤
          L_base + largeLiveBound M maxOut + allocLargeLive M 72 ∧
        HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤
          max (HasFineReallocCredit.peakLarge st)
            (L_base + largeLiveBound M maxWire +
              2 * largeLiveBound M maxOut + allocLargeLive M 72)) := by
  induction hChain with
  | nil cap maxWire =>
    intro S maxOut evs hcap hIter
    simp only [IterSeqEnv] at hIter
    subst hIter
    refine ⟨(fun _ h => nomatch h), fun st L_base hlive => ?_⟩
    simp only [AllocCostModel.stepEvents_nil, bytesMergePayloadSum, List.length_nil]
    have hlive_cap : allocLargeLive M cap ≤ largeLiveBound M maxOut :=
      Nat.le_trans (allocLargeLive_le_largeLiveBound hM cap) (largeLiveBound_mono M hcap)
    exact ⟨by omega, by omega, Nat.le_max_left _ _⟩
  | @err cap maxWire x hmb hxcap =>
    intro S maxOut evs hcap hIter
    simp only [IterSeqEnv] at hIter
    have hevs : evs = bytesMergeEventsCore x.wt x.valCap x.bs ∨ evs = [] := by
      rcases hIter with h1 | ⟨e₁, e₂, rfl, h1, rfl⟩
      · exact Or.inl h1
      · rw [List.append_nil]; exact Or.inl h1
    rcases hevs with rfl | rfl
    · refine ⟨fun ev hev => ?_, fun st L_base hlive => ?_⟩
      · obtain ⟨hr, ha⟩ := bytesMergeEventsCore_req_align x.wt x.valCap x.bs ev hev
        rw [hmb] at hr
        exact ⟨Nat.le_trans hr (Nat.le_max_right _ _), ha⟩
      · have hlive_x : HasFineReallocCredit.liveLarge st ≤
            L_base + allocLargeLive M x.valCap.toNat := by simpa [hxcap] using hlive
        have hcred := stepEvents_bytesMergeEventsCore_credit M x.wt x.valCap x.bs st hlive_x
        rw [hmb, hxcap] at hcred
        obtain ⟨hc, hl, hp⟩ := hcred
        have hc72 := allocStepCum_le_affine M (fun _ hr => hM.smallAlloc_le hr) hM.meta_le 72
        have hc72' : allocStepCum M 72 ≤ 19078 := by split at hc72 <;> omega
        have hlive_cap : allocLargeLive M cap ≤ largeLiveBound M maxOut :=
          Nat.le_trans (allocLargeLive_le_largeLiveBound hM cap) (largeLiveBound_mono M hcap)
        simp only [bytesMergePayloadSum, hmb, List.length_singleton]
        exact ⟨by omega, by omega, by omega⟩
    · refine ⟨(fun _ h => nomatch h), fun st L_base hlive => ?_⟩
      simp only [AllocCostModel.stepEvents_nil, bytesMergePayloadSum, hmb, List.length_singleton]
      have hlive_cap : allocLargeLive M cap ≤ largeLiveBound M maxOut :=
        Nat.le_trans (allocLargeLive_le_largeLiveBound hM cap) (largeLiveBound_mono M hcap)
      exact ⟨by omega, by omega, Nat.le_max_left _ _⟩
  | @ok cap maxWire x v rest xs hmb hxcap hv hrest ih =>
    intro S maxOut evs hcap hIter
    simp only [IterSeqEnv] at hIter
    let outCap := bytesMergeOutCap cap v.length
    have hout_le : outCap ≤ maxOut := bytesMergeOutCap_le_of_wire hcap hv
    have hmin_cap : min cap S ≤ min maxOut S := by omega
    have hmin_out : min outCap S ≤ min maxOut S := by omega
    have hamort := bytesMergeOkStepCum_amortized hM cap v.length
    have hv_bound : allocLargeLive M v.length ≤ largeLiveBound M maxWire :=
      Nat.le_trans (allocLargeLive_le_largeLiveBound hM v.length) (largeLiveBound_mono M hv)
    have hcap_bound : allocLargeLive M cap ≤ largeLiveBound M maxOut :=
      Nat.le_trans (allocLargeLive_le_largeLiveBound hM cap) (largeLiveBound_mono M hcap)
    have hout_bound : allocLargeLive M outCap ≤ largeLiveBound M maxOut :=
      Nat.le_trans (allocLargeLive_le_largeLiveBound hM outCap) (largeLiveBound_mono M hout_le)
    rcases hIter with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
    · unfold BytesMergeEnv at h1
      subst h1
      refine ⟨fun ev hev => ?_, fun st L_base hlive => ?_⟩
      · obtain ⟨hr, ha⟩ := bytesMergeEventsCore_req_align x.wt x.valCap x.bs ev hev
        rw [hmb, hxcap] at hr
        have hmax_le : max v.length outCap ≤ max maxOut 72 := by
          have hv_maxOut : v.length ≤ maxOut := by dsimp [maxOut]; omega
          omega
        exact ⟨Nat.le_trans hr hmax_le, ha⟩
      · have hlive_x : HasFineReallocCredit.liveLarge st ≤
            L_base + allocLargeLive M x.valCap.toNat := by simpa [hxcap] using hlive
        have hcred := stepEvents_bytesMergeEventsCore_credit M x.wt x.valCap x.bs st hlive_x
        rw [hmb, hxcap] at hcred
        obtain ⟨hc, hl, hp⟩ := hcred
        simp only [bytesMergePayloadSum, hmb, List.length_cons]
        dsimp [S, outCap] at *
        exact ⟨by omega, by omega, by omega⟩
    · unfold BytesMergeEnv at h1
      subst h1
      obtain ⟨hreq2, hcred2⟩ := ih hout_le h2
      refine ⟨fun ev hev => ?_, fun st L_base hlive => ?_⟩
      · rcases List.mem_append.mp hev with he1 | he2
        · obtain ⟨hr, ha⟩ := bytesMergeEventsCore_req_align x.wt x.valCap x.bs ev he1
          rw [hmb, hxcap] at hr
          have hmax_le : max v.length outCap ≤ max maxOut 72 := by
            have hv_maxOut : v.length ≤ maxOut := by dsimp [maxOut]; omega
            omega
          exact ⟨Nat.le_trans hr hmax_le, ha⟩
        · exact hreq2 ev he2
      · rw [AllocCostModel.stepEvents_append]
        have hlive_x : HasFineReallocCredit.liveLarge st ≤
            L_base + allocLargeLive M x.valCap.toNat := by simpa [hxcap] using hlive
        have hcred1 := stepEvents_bytesMergeEventsCore_credit M x.wt x.valCap x.bs st hlive_x
        rw [hmb, hxcap] at hcred1
        obtain ⟨hc1, hl1, hp1⟩ := hcred1
        obtain ⟨hc2, hl2, hp2⟩ := hcred2 _ L_base hl1
        simp only [bytesMergePayloadSum, hmb, List.length_cons]
        dsimp [S, outCap, maxOut] at *
        exact ⟨by omega, hl2, by omega⟩

/-- `PhaseCreditSpec` for a `BytesMergeChainOk 0 xs maxWire` sequence of `prost::encoding::bytes::merge`
overwrites on a single `Vec<u8>` field, bounding `Δlive` by a single `max (2 * maxWire) 8` buffer
(plus optional 72-byte error box) regardless of overwrite count. -/
theorem phaseCreditSpec_bytesMerge_overwrite_seq {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {maxWire : Nat} {xs : List BytesMergeGhost}
    (hChain : BytesMergeChainOk 0 xs maxWire) :
    let maxOut := max (2 * maxWire) 8
    PhaseCreditSpec M (IterSeqEnv BytesMergeEnv xs)
      (4 * min maxOut (HasFineReallocCredit.smallMaxReq M) +
        2 * bytesMergePayloadSum xs + 19078 * xs.length)
      (largeLiveBound M maxOut + allocLargeLive M 72)
      (largeLiveBound M maxWire + 2 * largeLiveBound M maxOut + allocLargeLive M 72)
      (max maxOut 72) := by
  dsimp only []
  refine
    { req_align := fun evs hIter =>
        (iterSeq_bytesMerge_overwrite_aux hM hChain (Nat.zero_le _) hIter).1
      credit_le := fun st0 {_} hIter => ?_ }
  obtain ⟨hc, hl, hp⟩ := (iterSeq_bytesMerge_overwrite_aux hM hChain (Nat.zero_le _) hIter).2
    st0 (HasFineReallocCredit.liveLarge st0) (Nat.le_add_right _ _)
  have hmin0 : min 0 (HasFineReallocCredit.smallMaxReq M) = 0 := Nat.zero_min _
  rw [hmin0] at hc
  exact ⟨by omega, by omega, by omega⟩

end LibsignalBinary.Proofs.PeakBudget.VecGrowCredit
