/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec

/-!
# Tight `738` B/Seed `fineCostModel` Bounds for W2/W4 Segment 4

Tightens W2/W4 `try_decrypt` Segment 4 (`consume_message_key` `33`-B message-key seed allocations,
`BoundedFreshEvs`, `W2Seg4CmkTightEnv`, and `cmkJumpListEvs`) on `fineCostModel` to `738` B per seed
(`2,000 × 738 = 1,476,000` B), with `maxSeeds`-parametric variants (`W2Seg4CmkSeedsEnv`) and
`PhaseGroupSpec` companions.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Message MlKem PqRatchetState States V1Recv V1State VersionNegotiationPB spqrAuthApi
   spqrPolyApi)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall ChainNewGhost ChainRecvKeyGhost)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open LibsignalBinary.Heap (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_smallMaxReq_eq smallAllocCost_le_738_of_le_44)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
  (BoundedFreshEvs W2Seg4CmkTightEnv W2TryDecryptTightEnv aesDecCtShape_groupSpec
   boundedFreshEvs_le_44_fine_groupSpec boundedNonFreeEvs_groupSpec doublingChain104Evs_groupSpec
   trApplyBoundedEnv_groupSpec w2AesDecErrEnv_groupSpec w2Seg3DhCommitEnv_fine_groupSpec
   w2Seg4CmkFineGrpS w2Seg7MacEnv_fine_groupSpec)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (PhaseGroupSpec nonFreeCount nonFreeCount_nil)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_freeNonInc fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (optLargeCost)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightBranches
  (SpqrRecvC07TightEnv SpqrRecvTightDomain)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightRecvKey (KeyHistorySmallOrReserved)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightSpec
  (StatesRecvTightCreditSpec spqrRecvParts_c07_phaseCreditSpec_tight
   spqrRecvParts_c07_phaseCreditSpec_tight_c09a spqrRecvParts_c07_phaseCreditSpec_tight_uncondHist)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptCmkDhPeak
  (cmkJumpFinalIdx cmkJumpListEvs v104GrowStepCum v104TowerCum2048 v104TowerPeak)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
  (W2AesDecErrEnv W2Seg3DhCommitEnv W2Seg7MacEnv phaseCreditSpec_aesDecCt_err_fine_tight
   phaseCreditSpec_aesDecCt_fine_tight phaseCreditSpec_boundedNonFree_fine_256
   phaseCreditSpec_doublingChain104_fine_tight w2CmkChainTightLive w2CmkChainTightPeak
   w2Seg3DhCommit_fine_phaseCreditSpec_tight w2Seg7Mac_fine_phaseCreditSpec_tight
   w2TryDecryptMaxReq w2TryDecryptTightCum w2TryDecryptTightLive w2TryDecryptTightPeak)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPhasePeak
  (AesDecCtShape BoundedNonFreeEvs DoublingChainLe TrApplyBoundedEnv doublingChain104Evs
   phaseCreditSpec_cmkJumpList_tower phaseCreditSpec_trApplyBounded)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)

/-! ## 1. `BoundedFreshEvs` (`req ≤ 44`) `PhaseCreditSpec` -/

private theorem or_freeOnly {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E : List AllocEvent → Prop} {c l p r : Nat}
    (h : PhaseCreditSpec M E c l p r) :
    PhaseCreditSpec M (fun evs => FreeOnlyEvs evs ∨ E evs) c l p r :=
  ((PhaseCreditSpec.freeOnly_of_hyps hM).or h).mono
    (by omega) (by omega) (by omega) (by omega)

private theorem seq_zero_left {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {c₁ r₁ c₂ l₂ p₂ r₂ : Nat}
    (h₁ : PhaseCreditSpec M E₁ c₁ 0 0 r₁)
    (h₂ : PhaseCreditSpec M E₂ c₂ l₂ p₂ r₂) :
    PhaseCreditSpec M (SeqEnv E₁ E₂) (c₁ + c₂) l₂ p₂ (max r₁ r₂) :=
  (h₁.seq h₂).mono (Nat.le_refl _) (by omega) (by omega) (Nat.le_refl _)

private theorem seq_freeOnly_right_zero_live {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {E : List AllocEvent → Prop} {c p r : Nat}
    (h : PhaseCreditSpec M E c 0 p r) :
    PhaseCreditSpec M (SeqEnv E FreeOnlyEvs) c 0 p r :=
  (h.seq (PhaseCreditSpec.freeOnly_of_hyps hM)).mono
    (by omega) (by omega) (by omega) (by omega)

private theorem seq_zero_right_eq_peak {M : AllocCostModel} [HasFineReallocCredit M]
    {E₁ E₂ : List AllocEvent → Prop} {c₁ l₁ r₁ c₂ r₂ : Nat}
    (h₁ : PhaseCreditSpec M E₁ c₁ l₁ l₁ r₁)
    (h₂ : PhaseCreditSpec M E₂ c₂ 0 0 r₂) :
    PhaseCreditSpec M (SeqEnv E₁ E₂) (c₁ + c₂) l₁ l₁ (max r₁ r₂) :=
  (h₁.seq h₂).mono (Nat.le_refl _) (by omega) (by omega) (Nat.le_refl _)

private theorem stepEvents_boundedFresh_le_44 :
    ∀ (evs : List AllocEvent) (st0 : fineCostModel.σ),
      (∀ ev ∈ evs, eventStepReq ev ≤ 44 ∧ eventStepAlign ev ≤ 16) →
      (∀ ev ∈ evs, ∀ al o n, ev ≠ .realloc al o n) →
      let st' := fineCostModel.stepEvents evs st0
      HasFineReallocCredit.cumSmall st' ≤
        HasFineReallocCredit.cumSmall st0 + nonFreeCount evs * 738 ∧
      HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st0 ∧
      HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st0
  | [], st0, _, _ => by
      simp only [AllocCostModel.stepEvents_nil, nonFreeCount_nil, Nat.zero_mul, Nat.add_zero]
      exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | ev :: rest, st0, hreq, hnr => by
      have hrest_req : ∀ e ∈ rest, eventStepReq e ≤ 44 ∧ eventStepAlign e ≤ 16 :=
        fun e he => hreq e (List.mem_cons_of_mem _ he)
      have hrest_nr : ∀ e ∈ rest, ∀ al o n, e ≠ .realloc al o n :=
        fun e he => hnr e (List.mem_cons_of_mem _ he)
      have hev := hreq ev List.mem_cons_self
      cases ev with
      | free al sz =>
          obtain ⟨hc1, hl1, hp1⟩ := fineCostModel_freeNonInc al sz st0
          obtain ⟨hc2, hl2, hp2⟩ :=
            stepEvents_boundedFresh_le_44 rest (fineCostModel.step (.free al sz) st0)
              hrest_req hrest_nr
          simp only [AllocCostModel.stepEvents_cons, nonFreeCount]
          exact ⟨Nat.le_trans hc2 (Nat.add_le_add_right hc1 _),
            Nat.le_trans hl2 hl1, Nat.le_trans hp2 hp1⟩
      | alloc req =>
          have hle44 : req ≤ 44 := by simpa [eventStepReq] using hev.1
          have hsm : req ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
            rw [fineCostModel_smallMaxReq_eq]; exact Nat.le_trans hle44 (by decide)
          obtain ⟨hc1, hl1, hp1⟩ := fineCostModel_modelHyps.step_alloc_small_any st0 hsm
          have hw := smallAllocCost_le_738_of_le_44 hle44
          obtain ⟨hc2, hl2, hp2⟩ :=
            stepEvents_boundedFresh_le_44 rest (fineCostModel.step (.alloc req) st0)
              hrest_req hrest_nr
          simp only [AllocCostModel.stepEvents_cons, nonFreeCount]
          have hmul : (nonFreeCount rest + 1) * 738 = 738 + nonFreeCount rest * 738 := by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
          refine ⟨?_, Nat.le_trans hl2 hl1, Nat.le_trans hp2 hp1⟩
          rw [hmul, ← Nat.add_assoc]
          exact Nat.le_trans hc2
            (Nat.add_le_add_right (Nat.le_trans hc1 (Nat.add_le_add_left hw _)) _)
      | aligned al req =>
          have hle44 : req ≤ 44 := by simpa [eventStepReq] using hev.1
          have hal16 : al ≤ 16 := by simpa [eventStepAlign] using hev.2
          have hsm : req ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
            rw [fineCostModel_smallMaxReq_eq]; exact Nat.le_trans hle44 (by decide)
          obtain ⟨hc1, hl1, hp1⟩ := fineCostModel_modelHyps.step_aligned_small_any st0 hal16 hsm
          have hw := smallAllocCost_le_738_of_le_44 hle44
          obtain ⟨hc2, hl2, hp2⟩ :=
            stepEvents_boundedFresh_le_44 rest (fineCostModel.step (.aligned al req) st0)
              hrest_req hrest_nr
          simp only [AllocCostModel.stepEvents_cons, nonFreeCount]
          have hmul : (nonFreeCount rest + 1) * 738 = 738 + nonFreeCount rest * 738 := by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
          refine ⟨?_, Nat.le_trans hl2 hl1, Nat.le_trans hp2 hp1⟩
          rw [hmul, ← Nat.add_assoc]
          exact Nat.le_trans hc2
            (Nat.add_le_add_right (Nat.le_trans hc1 (Nat.add_le_add_left hw _)) _)
      | realloc al o n =>
          exact False.elim (hnr (.realloc al o n) List.mem_cons_self al o n rfl)

/-- `PhaseCreditSpec fineCostModel` for `BoundedFreshEvs k maxLen maxReq` when `maxReq ≤ 44` (`k * 738` B, `0` live, `0` peak).
-/
theorem phaseCreditSpec_boundedFresh_fine_44
    {k maxLen maxReq : Nat} (hmr : maxReq ≤ 44) :
    PhaseCreditSpec fineCostModel (BoundedFreshEvs k maxLen maxReq)
      (k * 738) 0 0 maxReq where
  req_align _ := fun ⟨_, _, hb, _⟩ => hb
  credit_le st0 {evs} := fun ⟨_, hnf, hb, hnr⟩ => by
    have hreq : ∀ ev ∈ evs, eventStepReq ev ≤ 44 ∧ eventStepAlign ev ≤ 16 :=
      fun ev hev => ⟨Nat.le_trans (hb ev hev).1 hmr, (hb ev hev).2⟩
    obtain ⟨hc, hl, hp⟩ := stepEvents_boundedFresh_le_44 evs st0 hreq hnr
    have hmul : nonFreeCount evs * 738 ≤ k * 738 :=
      Nat.mul_le_mul_right 738 hnf
    exact ⟨Nat.le_trans hc (Nat.add_le_add_left hmul _),
      by simpa using hl,
      Nat.le_trans hp (Nat.le_max_left _ _)⟩

/-! ## 2. W2/W4 Segment 4 `738` B/Seed Bounds -/

/-- Fresh-seed W2/W4 Segment 4 envelope parameterized by `maxSeeds`. -/
def W2Seg4CmkSeedsEnv (maxSeeds : Nat) (caps : List Nat) (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    SeqEnv (BoundedFreshEvs maxSeeds (2 * maxSeeds) 33)
      (SeqEnv (· = doublingChain104Evs caps) FreeOnlyEvs) evs

theorem w2Seg4CmkSeedsEnv_2000_eq (caps : List Nat) :
    W2Seg4CmkSeedsEnv 2000 caps = W2Seg4CmkTightEnv caps :=
  rfl

/-- Tight `fineCostModel` `PhaseCreditSpec` for `W2Seg4CmkSeedsEnv maxSeeds caps`. -/
theorem w2Seg4CmkSeeds_fine_phaseCreditSpec
    {maxSeeds : Nat} {caps : List Nat} {maxSteps maxOldCap : Nat}
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps) :
    PhaseCreditSpec fineCostModel (W2Seg4CmkSeedsEnv maxSeeds caps)
      (maxSeeds * 738 + maxSteps * 143484)
      (w2CmkChainTightLive maxOldCap)
      (w2CmkChainTightPeak maxOldCap)
      (max 416 (104 * (2 * maxOldCap))) := by
  have hFree := PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps
  have hSeeds : PhaseCreditSpec fineCostModel (BoundedFreshEvs maxSeeds (2 * maxSeeds) 33)
      (maxSeeds * 738) 0 0 33 :=
    phaseCreditSpec_boundedFresh_fine_44 (by decide)
  have hGrow : PhaseCreditSpec fineCostModel (· = doublingChain104Evs caps)
      (maxSteps * 143484)
      (w2CmkChainTightLive maxOldCap)
      (w2CmkChainTightPeak maxOldCap)
      (max 416 (104 * (2 * maxOldCap))) :=
    (phaseCreditSpec_doublingChain104_fine_tight maxSteps maxOldCap).of_imp
      fun _ h => ⟨caps, hlen, hchain, h⟩
  have hlp : w2CmkChainTightLive maxOldCap ≤ w2CmkChainTightPeak maxOldCap :=
    Nat.le_add_left _ _
  have hGrowFree : PhaseCreditSpec fineCostModel (SeqEnv (· = doublingChain104Evs caps) FreeOnlyEvs)
      (maxSteps * 143484)
      (w2CmkChainTightLive maxOldCap)
      (w2CmkChainTightPeak maxOldCap)
      (max 416 (104 * (2 * maxOldCap))) :=
    (hGrow.seq hFree).mono
      (Nat.le_of_eq (Nat.add_zero _))
      (Nat.le_of_eq (Nat.add_zero _))
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_trans (Nat.le_of_eq (Nat.add_zero _)) hlp⟩)
      (Nat.max_eq_left (Nat.zero_le _)).le
  exact (or_freeOnly fineCostModel_modelHyps (seq_zero_left hSeeds hGrowFree)).mono
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    (by generalize 104 * (2 * maxOldCap) = r; omega)

/-- Tightens `W2Seg4CmkTightEnv caps` (`≤ 2,000` `33`-B seeds) on `fineCostModel` to `1,476,000 + maxSteps * 143,484` B.
-/
theorem w2Seg4CmkTight_fine_phaseCreditSpec_seeds738
    {caps : List Nat} {maxSteps maxOldCap : Nat}
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps) :
    PhaseCreditSpec fineCostModel (W2Seg4CmkTightEnv caps)
      (1476000 + maxSteps * 143484)
      (w2CmkChainTightLive maxOldCap)
      (w2CmkChainTightPeak maxOldCap)
      (max 416 (104 * (2 * maxOldCap))) := by
  simpa [w2Seg4CmkSeedsEnv_2000_eq] using
    w2Seg4CmkSeeds_fine_phaseCreditSpec (maxSeeds := 2000) hlen hchain

theorem phaseCreditSpec_cmkJumpList_tower_seeds738
    (jumps : List (Bool × Bool))
    (hlen : jumps.length ≤ 2000)
    (hkf : cmkJumpFinalIdx 0 jumps ≤ 10) :
    PhaseCreditSpec fineCostModel (· = cmkJumpListEvs 0 jumps)
      (1476000 + v104TowerCum2048 fineCostModel)
      (v104TowerPeak fineCostModel 10)
      (v104TowerPeak fineCostModel 10)
      212992 := by
  have h33 : 33 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hc33 := smallAllocCost_le_738_of_le_44 (req := 33) (by decide)
  have hmul : 2000 * HasFineReallocCredit.smallAllocCost fineCostModel 33 ≤ 1476000 :=
    Nat.le_trans (Nat.mul_le_mul_left 2000 hc33) (by decide)
  exact (phaseCreditSpec_cmkJumpList_tower fineCostModel h33 jumps hlen hkf).mono
    (Nat.add_le_add_right hmul _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

theorem w2Seg4CmkSeedsEnv_fine_groupSpec {maxSeeds : Nat} {caps : List Nat} {maxSteps : Nat}
    (hcaps : caps.length ≤ maxSteps) :
    PhaseGroupSpec fineCostModel (W2Seg4CmkSeedsEnv maxSeeds caps)
      (maxSeeds * 16659 + maxSteps * (3 * FineScale)) := by
  unfold W2Seg4CmkSeedsEnv
  have h1 := @boundedFreshEvs_le_44_fine_groupSpec maxSeeds (2 * maxSeeds) 33 (by omega)
  have h2 := (doublingChain104Evs_groupSpec fineCostModel caps).mono
    (Nat.mul_le_mul_right (3 * FineScale) hcaps)
  have hok := (h1.seq (h2.seq (PhaseGroupSpec.freeOnly fineCostModel))).mono
    (by rw [Nat.add_zero])
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hok).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

/-! ## 3. Full `try_decrypt` and Failed-Trial Envelopes and Bounds -/

/-- Failed-trial counterpart of `CliGroupBounds.W2TryDecryptTightEnv`. -/
def W2TryDecryptFailTightEnv (dhCap : Nat) (needGrow : Bool) (caps : List Nat)
    (SpqrStepEnv : List AllocEvent → Prop) (withAddr errAlloc : Bool) (ctLen : Nat)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    SeqEnv (BoundedNonFreeEvs 6 16 160)
      (SeqEnv (W2Seg3DhCommitEnv dhCap needGrow)
        (SeqEnv (W2Seg4CmkTightEnv caps)
          (SeqEnv SpqrStepEnv
            (SeqEnv (W2Seg7MacEnv withAddr errAlloc)
              (SeqEnv (W2AesDecErrEnv ctLen) FreeOnlyEvs))))) evs

/-- `maxSeeds`-parameterized `W2TryDecrypt` envelope. -/
def W2TryDecryptSeedsEnv (maxSeeds dhCap : Nat) (needGrow : Bool) (caps : List Nat)
    (SpqrStepEnv : List AllocEvent → Prop) (withAddr errAlloc : Bool) (ctLen : Nat)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    SeqEnv (BoundedNonFreeEvs 6 16 160)
      (SeqEnv (W2Seg3DhCommitEnv dhCap needGrow)
        (SeqEnv (W2Seg4CmkSeedsEnv maxSeeds caps)
          (SeqEnv SpqrStepEnv
            (SeqEnv (W2Seg7MacEnv withAddr errAlloc)
              (SeqEnv (AesDecCtShape ctLen)
                (SeqEnv TrApplyBoundedEnv FreeOnlyEvs)))))) evs

/-- `maxSeeds`-parameterized failed-trial `W2TryDecrypt` envelope. -/
def W2TryDecryptFailSeedsEnv (maxSeeds dhCap : Nat) (needGrow : Bool) (caps : List Nat)
    (SpqrStepEnv : List AllocEvent → Prop) (withAddr errAlloc : Bool) (ctLen : Nat)
    (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨
    SeqEnv (BoundedNonFreeEvs 6 16 160)
      (SeqEnv (W2Seg3DhCommitEnv dhCap needGrow)
        (SeqEnv (W2Seg4CmkSeedsEnv maxSeeds caps)
          (SeqEnv SpqrStepEnv
            (SeqEnv (W2Seg7MacEnv withAddr errAlloc)
              (SeqEnv (W2AesDecErrEnv ctLen) FreeOnlyEvs))))) evs

theorem w2TryDecryptSeedsEnv_2000_eq (dhCap : Nat) (needGrow : Bool) (caps : List Nat)
    (SpqrStepEnv : List AllocEvent → Prop) (withAddr errAlloc : Bool) (ctLen : Nat) :
    W2TryDecryptSeedsEnv 2000 dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen =
      W2TryDecryptTightEnv dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen :=
  rfl

theorem w2TryDecryptFailSeedsEnv_2000_eq (dhCap : Nat) (needGrow : Bool) (caps : List Nat)
    (SpqrStepEnv : List AllocEvent → Prop) (withAddr errAlloc : Bool) (ctLen : Nat) :
    W2TryDecryptFailSeedsEnv 2000 dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen =
      W2TryDecryptFailTightEnv dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen :=
  rfl

def w2TryDecryptGenSeeds738Cum (maxSeeds dhCap : Nat) (needGrow : Bool) (maxSteps c_spqr : Nat) :
    Nat :=
  58734 +
    (2214 + (if needGrow then v104GrowStepCum fineCostModel dhCap else 0)) +
    (maxSeeds * 738 + maxSteps * 143484) +
    c_spqr +
    2702 +
    143484 +
    57642

/-- Tight `fineCostModel` `Δcum` for `W2TryDecryptTightEnv` and `W2TryDecryptFailTightEnv`. -/
def w2TryDecryptSeeds738Cum (dhCap : Nat) (needGrow : Bool) (maxSteps c_spqr : Nat) : Nat :=
  w2TryDecryptGenSeeds738Cum 2000 dhCap needGrow maxSteps c_spqr

theorem w2TryDecryptSeeds738Cum_add_eq
    (dhCap : Nat) (needGrow : Bool) (maxSteps c_spqr : Nat) :
    w2TryDecryptSeeds738Cum dhCap needGrow maxSteps c_spqr + 17734000 =
      w2TryDecryptTightCum dhCap needGrow maxSteps c_spqr := by
  unfold w2TryDecryptSeeds738Cum w2TryDecryptGenSeeds738Cum w2TryDecryptTightCum
  omega

theorem w2TryDecrypt_genSeeds_fine_phaseCreditSpec
    {maxSeeds dhCap : Nat} {needGrow : Bool} {caps : List Nat}
    {SpqrStepEnv : List AllocEvent → Prop} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap c_spqr l_spqr p_spqr r_spqr maxCt : Nat}
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hSpqr : PhaseCreditSpec fineCostModel SpqrStepEnv c_spqr l_spqr p_spqr r_spqr)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptSeedsEnv maxSeeds dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen)
      (w2TryDecryptGenSeeds738Cum maxSeeds dhCap needGrow maxSteps c_spqr)
      (w2TryDecryptTightLive maxOldCap l_spqr maxCt)
      (w2TryDecryptTightPeak maxOldCap l_spqr p_spqr maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap r_spqr maxCt) := by
  have h34 : 34 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have hS1 : PhaseCreditSpec fineCostModel (BoundedNonFreeEvs 6 16 160) 58734 0 0 160 :=
    (phaseCreditSpec_boundedNonFree_fine_256 6 16 160 (by decide)).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 160)
  have hS3 := w2Seg3DhCommit_fine_phaseCreditSpec_tight (dhCap := dhCap) (needGrow := needGrow) hDhSmall
  have hS4 := w2Seg4CmkSeeds_fine_phaseCreditSpec (maxSeeds := maxSeeds) hlen hchain
  have hS7 := w2Seg7Mac_fine_phaseCreditSpec_tight withAddr errAlloc
  have hS8 := phaseCreditSpec_aesDecCt_fine_tight hct
  have hS9 : PhaseCreditSpec fineCostModel (SeqEnv TrApplyBoundedEnv FreeOnlyEvs) 57642 0 0 34 :=
    (seq_freeOnly_right_zero_live fineCostModel_modelHyps
      (phaseCreditSpec_trApplyBounded fineCostModel_modelHyps h34)).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 34)
  have h89 := seq_zero_right_eq_peak hS8 hS9
  have h79 := seq_zero_left hS7 h89
  have h59 := hSpqr.seq h79
  have h49 := hS4.seq h59
  have h39 := seq_zero_left hS3 h49
  have h19 := seq_zero_left hS1 h39
  unfold w2TryDecryptGenSeeds738Cum w2TryDecryptTightLive w2TryDecryptTightPeak w2TryDecryptMaxReq
  refine (or_freeOnly fineCostModel_modelHyps h19).mono ?_ ?_ (Nat.le_refl _) ?_
  · simp only [Nat.add_assoc]; exact Nat.le_refl _
  · simp only [Nat.add_assoc]; exact Nat.le_refl _
  · generalize max 416 (104 * (2 * dhCap)) = r3
    generalize max 416 (104 * (2 * maxOldCap)) = r4
    omega

theorem w2TryDecryptFail_genSeeds_fine_phaseCreditSpec
    {maxSeeds dhCap : Nat} {needGrow : Bool} {caps : List Nat}
    {SpqrStepEnv : List AllocEvent → Prop} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap c_spqr l_spqr p_spqr r_spqr maxCt : Nat}
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hSpqr : PhaseCreditSpec fineCostModel SpqrStepEnv c_spqr l_spqr p_spqr r_spqr)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptFailSeedsEnv maxSeeds dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen)
      (w2TryDecryptGenSeeds738Cum maxSeeds dhCap needGrow maxSteps c_spqr)
      (w2CmkChainTightLive maxOldCap + l_spqr)
      (w2TryDecryptTightPeak maxOldCap l_spqr p_spqr maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap r_spqr maxCt) := by
  have hS1 : PhaseCreditSpec fineCostModel (BoundedNonFreeEvs 6 16 160) 58734 0 0 160 :=
    (phaseCreditSpec_boundedNonFree_fine_256 6 16 160 (by decide)).mono
      (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 160)
  have hS3 := w2Seg3DhCommit_fine_phaseCreditSpec_tight (dhCap := dhCap) (needGrow := needGrow) hDhSmall
  have hS4 := w2Seg4CmkSeeds_fine_phaseCreditSpec (maxSeeds := maxSeeds) hlen hchain
  have hS7 := w2Seg7Mac_fine_phaseCreditSpec_tight withAddr errAlloc
  have hS8 := seq_freeOnly_right_zero_live fineCostModel_modelHyps
    (phaseCreditSpec_aesDecCt_err_fine_tight hct)
  have h78 := seq_zero_left hS7 hS8
  have h58 := hSpqr.seq h78
  have h48 := hS4.seq h58
  have h38 := seq_zero_left hS3 h48
  have h18 := seq_zero_left hS1 h38
  have hcum_assoc : ∀ a b c d e f : Nat, a + (b + (c + (d + (e + f)))) = a + b + c + d + e + f :=
    fun _ _ _ _ _ _ => by simp only [Nat.add_assoc]
  unfold w2TryDecryptGenSeeds738Cum w2TryDecryptTightPeak w2TryDecryptMaxReq
  refine (or_freeOnly fineCostModel_modelHyps h18).mono ?_ ?_ (Nat.le_refl _) (Nat.le_refl _)
  · rw [hcum_assoc]; exact Nat.le_add_right _ _
  · simp only [Nat.add_zero]; exact Nat.le_refl _

/-- `PhaseCreditSpec fineCostModel` for `W2TryDecryptTightEnv` charging `738` B per Segment 4 seed.
-/
theorem w2TryDecrypt_fine_phaseCreditSpec_seeds738
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat}
    {SpqrStepEnv : List AllocEvent → Prop} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap c_spqr l_spqr p_spqr r_spqr maxCt : Nat}
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hSpqr : PhaseCreditSpec fineCostModel SpqrStepEnv c_spqr l_spqr p_spqr r_spqr)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen)
      (w2TryDecryptSeeds738Cum dhCap needGrow maxSteps c_spqr)
      (w2TryDecryptTightLive maxOldCap l_spqr maxCt)
      (w2TryDecryptTightPeak maxOldCap l_spqr p_spqr maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap r_spqr maxCt) :=
  w2TryDecrypt_genSeeds_fine_phaseCreditSpec (maxSeeds := 2000) hDhSmall hlen hchain hSpqr hct

/-- Failed-trial `PhaseCreditSpec fineCostModel` for `W2TryDecryptFailTightEnv`. -/
theorem w2TryDecryptFail_fine_phaseCreditSpec_seeds738
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat}
    {SpqrStepEnv : List AllocEvent → Prop} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap c_spqr l_spqr p_spqr r_spqr maxCt : Nat}
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hSpqr : PhaseCreditSpec fineCostModel SpqrStepEnv c_spqr l_spqr p_spqr r_spqr)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptFailTightEnv dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen)
      (w2TryDecryptSeeds738Cum dhCap needGrow maxSteps c_spqr)
      (w2CmkChainTightLive maxOldCap + l_spqr)
      (w2TryDecryptTightPeak maxOldCap l_spqr p_spqr maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap r_spqr maxCt) :=
  w2TryDecryptFail_genSeeds_fine_phaseCreditSpec (maxSeeds := 2000) hDhSmall hlen hchain hSpqr hct

theorem w2TryDecryptSeedsEnv_fine_groupSpec
    (maxSeeds dhCap : Nat) (needGrow : Bool) {caps : List Nat} {maxSteps g_spqr : Nat}
    {SpqrStepEnv : List AllocEvent → Prop} (withAddr errAlloc : Bool) (ctLen : Nat)
    (hcaps : caps.length ≤ maxSteps)
    (hspqr : PhaseGroupSpec fineCostModel SpqrStepEnv g_spqr) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptSeedsEnv maxSeeds dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen)
      (42 * FineScale + 6 * 16659 + 11056 +
        (maxSeeds * 16659 + maxSteps * (3 * FineScale)) + g_spqr) := by
  unfold W2TryDecryptSeedsEnv
  have hs1 := boundedNonFreeEvs_groupSpec fineCostModel 6 16 160
  have hs3 := w2Seg3DhCommitEnv_fine_groupSpec dhCap needGrow
  have hs4 := w2Seg4CmkSeedsEnv_fine_groupSpec (maxSeeds := maxSeeds) hcaps
  have hs7 := w2Seg7MacEnv_fine_groupSpec withAddr errAlloc
  have hs8 := aesDecCtShape_groupSpec fineCostModel ctLen
  have hs9 := trApplyBoundedEnv_groupSpec fineCostModel
  have hok := hs1.seq (hs3.seq (hs4.seq (hspqr.seq
    (hs7.seq (hs8.seq (hs9.seq (PhaseGroupSpec.freeOnly fineCostModel)))))))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hok).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, by omega⟩)

theorem w2TryDecryptFailTightEnv_fine_groupSpec
    (dhCap : Nat) (needGrow : Bool) {caps : List Nat} {maxSteps g_spqr : Nat}
    {SpqrStepEnv : List AllocEvent → Prop} (withAddr errAlloc : Bool) (ctLen : Nat)
    (hcaps : caps.length ≤ maxSteps)
    (hspqr : PhaseGroupSpec fineCostModel SpqrStepEnv g_spqr) :
    PhaseGroupSpec fineCostModel
      (W2TryDecryptFailTightEnv dhCap needGrow caps SpqrStepEnv withAddr errAlloc ctLen)
      (24 * FineScale + 6 * 16659 + 11056 + w2Seg4CmkFineGrpS maxSteps + g_spqr) := by
  unfold W2TryDecryptFailTightEnv w2Seg4CmkFineGrpS
  have hs1 := boundedNonFreeEvs_groupSpec fineCostModel 6 16 160
  have hs3 := w2Seg3DhCommitEnv_fine_groupSpec dhCap needGrow
  have hs4 := w2Seg4CmkSeedsEnv_fine_groupSpec (maxSeeds := 2000) hcaps
  have hs7 := w2Seg7MacEnv_fine_groupSpec withAddr errAlloc
  have hs8 := w2AesDecErrEnv_groupSpec fineCostModel ctLen
  have hok := hs1.seq (hs3.seq (hs4.seq (hspqr.seq
    (hs7.seq (hs8.seq (PhaseGroupSpec.freeOnly fineCostModel))))))
  exact ((PhaseGroupSpec.freeOnly fineCostModel).or hok).mono
    (Nat.max_le.mpr ⟨Nat.zero_le _, by omega⟩)

/-! ## 4. Concrete SPQR `recv` Instantiations -/

/-- SPQR `recv` instantiation of `w2TryDecrypt_fine_phaseCreditSpec_seeds738` under `KeyHistorySmallOrReserved xRk`.
-/
theorem w2TryDecrypt_spqrC07_phaseCreditSpec_seeds738
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (hcRecv : cRecv ≤ 1910199)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptSeeds738Cum dhCap needGrow maxSteps 23313687)
      (w2TryDecryptTightLive maxOldCap 294391 maxCt)
      (w2TryDecryptTightPeak maxOldCap 294391 294391 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap (max rRecv 286196) maxCt) :=
  w2TryDecrypt_fine_phaseCreditSpec_seeds738 hDhSmall hlen hchain
    (spqrRecvParts_c07_phaseCreditSpec_tight F K C09a hcRecv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist)
    hct

theorem w2TryDecrypt_spqrC07_c09a_phaseCreditSpec_seeds738
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv 1647247 rRecv)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptSeeds738Cum dhCap needGrow maxSteps 23313687)
      (w2TryDecryptTightLive maxOldCap 294391 maxCt)
      (w2TryDecryptTightPeak maxOldCap 294391 294391 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap (max rRecv 286196) maxCt) :=
  w2TryDecrypt_fine_phaseCreditSpec_seeds738 hDhSmall hlen hchain
    (spqrRecvParts_c07_phaseCreditSpec_tight_c09a F K C09a
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist)
    hct

theorem w2TryDecryptFail_spqrC07_phaseCreditSpec_seeds738
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (hcRecv : cRecv ≤ 1910199)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hHist : KeyHistorySmallOrReserved xRk)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptFailTightEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptSeeds738Cum dhCap needGrow maxSteps 23313687)
      (w2CmkChainTightLive maxOldCap + 294391)
      (w2TryDecryptTightPeak maxOldCap 294391 294391 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap (max rRecv 286196) maxCt) :=
  w2TryDecryptFail_fine_phaseCreditSpec_seeds738 hDhSmall hlen hchain
    (spqrRecvParts_c07_phaseCreditSpec_tight F K C09a hcRecv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom hHist)
    hct

/-- Unconditional-history SPQR `recv` instantiation of `w2TryDecrypt_fine_phaseCreditSpec_seeds738`.
-/
theorem w2TryDecrypt_spqrC07_uncondHist_phaseCreditSpec_seeds738
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (hcRecv : cRecv ≤ 1900660)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptTightEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptSeeds738Cum dhCap needGrow maxSteps 23313687)
      (w2TryDecryptTightLive maxOldCap 605066 maxCt)
      (w2TryDecryptTightPeak maxOldCap 605066 621350 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap (max rRecv 302480) maxCt) :=
  w2TryDecrypt_fine_phaseCreditSpec_seeds738 hDhSmall hlen hchain
    (spqrRecvParts_c07_phaseCreditSpec_tight_uncondHist F K C09a hcRecv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom)
    hct

theorem w2TryDecryptFail_spqrC07_uncondHist_phaseCreditSpec_seeds738
    (F : ShaCompress) (K : MlKem)
    {StatesRecvEnv : States spqrPolyApi (spqrAuthApi F) → Message spqrPolyApi →
      List AllocEvent → Prop}
    {cRecv rRecv : Nat}
    (C09a : StatesRecvTightCreditSpec F StatesRecvEnv cRecv rRecv)
    (hcRecv : cRecv ≤ 1900660)
    {dhCap : Nat} {needGrow : Bool} {caps : List Nat} {withAddr errAlloc : Bool}
    {ctLen maxSteps maxOldCap maxCt : Nat}
    (stBytes : Bytes)
    (pre_pb : PqRatchetState) (vn : VersionNegotiationPB) (pb : V1State)
    (st0 : States spqrPolyApi (spqrAuthApi F)) (sckaMsg : Message spqrPolyApi)
    (v : V1Recv spqrPolyApi (spqrAuthApi F))
    (xInit : InitInnerGhost) (xNew : ChainNewGhost)
    (xAdd : ChainAddEpochGhost) (xRk : ChainRecvKeyGhost)
    (xSInto : StatesIntoPbGhost F) (xCInto : ChainIntoPbCall)
    (hDhSmall : 104 * max 4 (2 * dhCap) ≤ HasFineReallocCredit.smallMaxReq fineCostModel)
    (hlen : caps.length ≤ maxSteps)
    (hchain : DoublingChainLe maxOldCap caps)
    (hDom : SpqrRecvTightDomain F K stBytes xAdd xRk)
    (hct : ctLen ≤ maxCt) :
    PhaseCreditSpec fineCostModel
      (W2TryDecryptFailTightEnv dhCap needGrow caps
        (SpqrRecvC07TightEnv F K StatesRecvEnv
          stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto)
        withAddr errAlloc ctLen)
      (w2TryDecryptSeeds738Cum dhCap needGrow maxSteps 23313687)
      (w2CmkChainTightLive maxOldCap + 605066)
      (w2TryDecryptTightPeak maxOldCap 605066 621350 maxCt)
      (w2TryDecryptMaxReq dhCap maxOldCap (max rRecv 302480) maxCt) :=
  w2TryDecryptFail_fine_phaseCreditSpec_seeds738 hDhSmall hlen hchain
    (spqrRecvParts_c07_phaseCreditSpec_tight_uncondHist F K C09a hcRecv
      stBytes pre_pb vn pb st0 sckaMsg v xInit xNew xAdd xRk xSInto xCInto hDom)
    hct

end LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738
