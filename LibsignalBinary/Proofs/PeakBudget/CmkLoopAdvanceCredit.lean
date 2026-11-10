/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyTrapPlacedBudget
public import LibsignalBinary.Proofs.PeakBudget.CliGroupBounds
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
public import LibsignalBinary.Proofs.PeakBudget.VecGrowCreditHelpers
public import LibsignalBinary.Proofs.PeakBudget.W2Seg4CmkSeeds738

/-!
# `CmkLoopAdvanceEvs`, `CmkStepEnv`, and `CmkSeg4Env` Credit and Group Specifications

State-threaded `fineCostModel` `PhaseCreditSpec` and `PhaseGroupSpec` bounds for the Segment-4
`consume_message_key` envelopes (`CmkLoopAdvanceEvs`, `CmkStepEnv` / `tryDecryptCmkStepEnv`, and
`CmkSeg4Env FmtWriteEnv` / `tryDecryptCmkSeg4Env FmtWriteEnv`):
- Requires only `len0 ≤ maxMessageKeys` (`2000`) with no hypothesis on `cap0 : BitVec 64`,
  bounding `Vec<104>` growth across arbitrary `n` to at most `10` doubling steps.
- Discharges telescopic `sc = 63` `realloc` cancellation (`Δlive = 424,195` B, `Δpeak = 640,390` B,
  `maxReq = 416,000` B) and amortized `cumSmall` (`(n + 2) * 738 + 636,058` B).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.CmkLoopAdvanceCredit

open CryptoGames.LibsignalSession
  (ChainKey PublicKey RatchetState TripleRatchet maxMessageKeys)
open CryptoVerification.LibsignalTripleRatchet (TrGhost TryDecryptGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (FineScale fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_smallMaxReq_eq smallAllocCost_le_738_of_le_44)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.ConsumeMsgKeyTrapPlacedBudget
  (CmkSeg4Env CmkStepEnv)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget
  (CmkEpilogueEvs CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.ConsumeMessageKey.DefsBudget (GrowOneEnv)
open LibsignalBinary.Proofs.PeakBudget.CliGroupBounds (fine_rustAlloc_le_44)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
  (tryDecryptCmkSeg4Env tryDecryptCmkStepEnv)
open LibsignalBinary.Proofs.PeakBudget.GroupCreditKit
  (HasFineGroupCredit NonFreeBound PhaseGroupSpec nonFreeCount_rustAllocEvents
   nonFreeCount_rustReallocEvents)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (PhaseCreditSpec stepEvents_freeOnly_le)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
  (fineCostModel_freeNonInc fineCostModel_modelHyps fineCostModel_smallAff freeOnly_fineCostModel)
open LibsignalBinary.Proofs.PeakBudget.SerCloneStorePeakSpec (optLargeCost_fine_mono)
open LibsignalBinary.Proofs.PeakBudget.SessionCloneCredit (optLargeCost)
open LibsignalBinary.Proofs.PeakBudget.VecGrowCreditHelpers
  (allocLargeLive growOrReallocEvents growOrReallocEvents_req_align growOrReallocStepCum
   growOrReallocStepCum_amortized rustAllocEvents_req_align stepEvents_growOrRealloc_credit
   stepEvents_growOrRealloc_delta)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptPeakSpec
  (w2CmkChainTightLive w2CmkChainTightPeak)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)

/-! ## 1. Doubling-Step Budget & Amortized Potential Helpers -/

private theorem cmkr1_maxMessageKeys_eq : maxMessageKeys = 2000 := rfl

private theorem cmkr1_nextLen_le {len : Nat} (hlen : len ≤ 2000) :
    (if maxMessageKeys ≤ len then maxMessageKeys else len + 1) ≤ 2000 := by
  rw [cmkr1_maxMessageKeys_eq]
  split <;> omega

private def cmkr1_stepsTo2000 : Nat → Nat
  | 0 => 10
  | c + 1 =>
    if 2000 < c + 1 then 0
    else 1 + cmkr1_stepsTo2000 (2 * (c + 1))
termination_by c => 2001 - c

private theorem cmkr1_stepsTo2000_gt {c : Nat} (hgt : 2000 < c) :
    cmkr1_stepsTo2000 c = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
  rw [cmkr1_stepsTo2000]
  simp only [hgt, ↓reduceIte]

private theorem cmkr1_stepsTo2000_pos_le {c : Nat} (hc_pos : 0 < c) (hc_le : c ≤ 2000) :
    cmkr1_stepsTo2000 (2 * c) + 1 = cmkr1_stepsTo2000 c := by
  obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
  rw [cmkr1_stepsTo2000]
  have hnot : ¬ (2000 < m + 1) := Nat.not_lt.mpr hc_le
  simp only [hnot, ↓reduceIte, Nat.add_comm 1]

private theorem cmkr1_stepsTo2000_step_le {c b : Nat} (hc_pos : 0 < c)
    (h2 : cmkr1_stepsTo2000 (2 * c) ≤ b) :
    cmkr1_stepsTo2000 c ≤ b + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
  rw [cmkr1_stepsTo2000]
  split
  · exact Nat.zero_le _
  · omega

private theorem cmkr1_stepsTo2000_le_nine {c : Nat} (hc4 : 4 ≤ c) :
    cmkr1_stepsTo2000 c ≤ 9 := by
  have h0 : cmkr1_stepsTo2000 (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * c))))))))) ≤ 0 :=
    Nat.le_of_eq (cmkr1_stepsTo2000_gt (by omega))
  have h1 := cmkr1_stepsTo2000_step_le (by omega) h0
  have h2 := cmkr1_stepsTo2000_step_le (by omega) h1
  have h3 := cmkr1_stepsTo2000_step_le (by omega) h2
  have h4 := cmkr1_stepsTo2000_step_le (by omega) h3
  have h5 := cmkr1_stepsTo2000_step_le (by omega) h4
  have h6 := cmkr1_stepsTo2000_step_le (by omega) h5
  have h7 := cmkr1_stepsTo2000_step_le (by omega) h6
  have h8 := cmkr1_stepsTo2000_step_le (by omega) h7
  exact cmkr1_stepsTo2000_step_le (by omega) h8

private def cmkr1_growBudget (grown : Bool) (c : Nat) : Nat :=
  if grown then cmkr1_stepsTo2000 c else 10

private def cmkr1_remPot (S : Nat) (grown : Bool) (c : Nat) : Nat :=
  if grown then 4 * (S - min (104 * c) S) else 4 * S

private theorem cmkr1_pot_step_false {S oldReq newReq sc : Nat}
    (ham : sc + 4 * min oldReq S ≤ 4 * min newReq S + 9539) :
    sc + 4 * (S - min newReq S) ≤ 4 * S + 9539 := by
  have hmin : min newReq S ≤ S := Nat.min_le_right newReq S
  omega

private theorem cmkr1_pot_step_true {S oldReq newReq sc : Nat}
    (ham : sc + 4 * min oldReq S ≤ 4 * min newReq S + 9539) :
    sc + 4 * (S - min newReq S) ≤ 4 * (S - min oldReq S) + 9539 := by
  have hm1 : min oldReq S ≤ S := Nat.min_le_right oldReq S
  have hm2 : min newReq S ≤ S := Nat.min_le_right newReq S
  omega

/-! ## 2. `GrowOneEnv`, `32`/`36`-B Small Allocations, and `CmkEpilogueEvs` Primitives -/

private theorem cmkr1_growOneEnv_eq {cap : BitVec 64} {evs : List AllocEvent}
    (h : GrowOneEnv cap evs) :
    evs = growOrReallocEvents (104 * cap.toNat) (104 * max (2 * cap.toNat) 4) 8 := by
  unfold GrowOneEnv at h
  unfold growOrReallocEvents
  rcases h with ⟨rfl, rfl⟩ | ⟨hne, rfl⟩
  · simp
  · have hcnz : cap.toNat ≠ 0 := fun hz => hne (BitVec.eq_of_toNat_eq hz)
    have hmul_nz : 104 * cap.toNat ≠ 0 := by omega
    simp only [hmul_nz, ↓reduceIte, Nat.mul_comm cap.toNat 104,
      Nat.mul_comm (max (2 * cap.toNat) 4) 104]

private theorem cmkr1_growOneEnv_req_align {cap : BitVec 64} {evs : List AllocEvent}
    (h : GrowOneEnv cap evs) (hc_le : cap.toNat ≤ 2000) :
    ∀ ev ∈ evs, eventStepReq ev ≤ 416000 ∧ eventStepAlign ev ≤ 16 := by
  rw [cmkr1_growOneEnv_eq h]
  intro ev hev
  obtain ⟨hreq, hal⟩ := growOrReallocEvents_req_align (by decide : (8 : Nat) ≤ 16) ev hev
  have hnew_le : 104 * max (2 * cap.toNat) 4 ≤ 416000 := by omega
  exact ⟨Nat.le_trans hreq hnew_le, hal⟩

private theorem cmkr1_growOneEnv_amortized (cap : BitVec 64) :
    let oldReq := 104 * cap.toNat
    let newReq := 104 * max (2 * cap.toNat) 4
    growOrReallocStepCum fineCostModel oldReq newReq 8 +
      4 * min oldReq (HasFineReallocCredit.smallMaxReq fineCostModel) ≤
      4 * min newReq (HasFineReallocCredit.smallMaxReq fineCostModel) + 9539 := by
  refine growOrReallocStepCum_amortized fineCostModel
    (fun r hr => (fineCostModel_smallAff r hr).1)
    (fun r hr => (fineCostModel_smallAff r hr).2)
    fineCostModel_modelHyps.hMeta ?_
  omega

private theorem cmkr1_stepEvents_alloc_le_44 {sz al : Nat} (st : fineCostModel.σ)
    (hal : al ≤ 16) (hsz : sz ≤ 44) :
    let st' := fineCostModel.stepEvents (rustAllocEvents sz al) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st + 738 ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  have hsm : sz ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]
    exact Nat.le_trans hsz (by decide)
  have hw := smallAllocCost_le_738_of_le_44 hsz
  unfold rustAllocEvents
  split
  · dsimp only
    rw [AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
    obtain ⟨hc, hl, hp⟩ := fineCostModel_modelHyps.step_alloc_small_any st hsm
    exact ⟨Nat.le_trans hc (Nat.add_le_add_left hw _), hl, hp⟩
  · dsimp only
    rw [AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
    have hal8 : max al 8 ≤ 16 := by omega
    obtain ⟨hc, hl, hp⟩ := fineCostModel_modelHyps.step_aligned_small_any st hal8 hsm
    exact ⟨Nat.le_trans hc (Nat.add_le_add_left hw _), hl, hp⟩

private theorem cmkr1_freeOnly_of_pop {cond : Prop} [Decidable cond] {evs : List AllocEvent}
    (h : if cond then FreeOnlyEvs evs else evs = []) :
    FreeOnlyEvs evs := by
  split at h
  · exact h
  · subst h
    intro ev hev
    nomatch hev

private theorem cmkr1_epilogue_req_align {isPanic : Bool} {evs : List AllocEvent}
    (h : CmkEpilogueEvs isPanic evs) :
    ∀ ev ∈ evs, eventStepReq ev ≤ 32 ∧ eventStepAlign ev ≤ 16 := by
  unfold CmkEpilogueEvs at h
  cases isPanic
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨evs_ck, hck, rfl⟩ := h
    intro ev hev
    rw [List.mem_append, List.mem_append] at hev
    rcases hev with (hev1 | hev2) | hev3
    · exact rustAllocEvents_req_align (by decide : (1 : Nat) ≤ 16) ev hev1
    · obtain ⟨hreq, hal⟩ := freeOnly_fineCostModel.req_align evs_ck hck ev hev2
      exact ⟨Nat.le_trans hreq (Nat.zero_le 32), hal⟩
    · exact rustAllocEvents_req_align (by decide : (1 : Nat) ≤ 16) ev hev3
  · simp only [↓reduceIte] at h
    subst h
    intro ev hev
    nomatch hev

private theorem cmkr1_stepEvents_epilogue {isPanic : Bool} {evs : List AllocEvent}
    (st : fineCostModel.σ) (h : CmkEpilogueEvs isPanic evs) :
    let st' := fineCostModel.stepEvents evs st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st + 2 * 738 ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  unfold CmkEpilogueEvs at h
  cases isPanic
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨evs_ck, hck, rfl⟩ := h
    dsimp only
    simp only [AllocCostModel.stepEvents_append]
    obtain ⟨hc1, hl1, hp1⟩ :=
      cmkr1_stepEvents_alloc_le_44 (sz := 32) (al := 1) st (by decide) (by decide)
    obtain ⟨hc2, hl2, hp2⟩ :=
      stepEvents_freeOnly_le fineCostModel_freeNonInc hck
        (fineCostModel.stepEvents (rustAllocEvents 32 1) st)
    obtain ⟨hc3, hl3, hp3⟩ :=
      cmkr1_stepEvents_alloc_le_44 (sz := 32) (al := 1)
        (fineCostModel.stepEvents evs_ck (fineCostModel.stepEvents (rustAllocEvents 32 1) st))
        (by decide) (by decide)
    exact ⟨by omega, Nat.le_trans hl3 (Nat.le_trans hl2 hl1),
      Nat.le_trans hp3 (Nat.le_trans hp2 hp1)⟩
  · simp only [↓reduceIte] at h
    subst h
    simp only [AllocCostModel.stepEvents_nil]
    exact ⟨Nat.le_add_right _ _, Nat.le_refl _, Nat.le_refl _⟩

/-- Tight `fineCostModel` `PhaseCreditSpec` for `CmkEpilogueEvs isPanic`. -/
theorem cmkEpilogueEvs_fine_phaseCreditSpec (isPanic : Bool) :
    PhaseCreditSpec fineCostModel (CmkEpilogueEvs isPanic)
      (if isPanic then 0 else 1476) 0 0 (if isPanic then 0 else 32) where
  req_align evs h ev hev := by
    cases isPanic
    · exact cmkr1_epilogue_req_align h ev hev
    · unfold CmkEpilogueEvs at h
      simp only [↓reduceIte] at h
      subst h
      nomatch hev
  credit_le st0 {evs} h := by
    cases isPanic
    · obtain ⟨hc, hl, hp⟩ := cmkr1_stepEvents_epilogue st0 h
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact ⟨hc, hl, Nat.le_trans hp (Nat.le_max_left _ _)⟩
    · unfold CmkEpilogueEvs at h
      simp only [↓reduceIte] at h
      subst h
      simp only [↓reduceIte, AllocCostModel.stepEvents_nil, Nat.add_zero]
      exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _⟩

/-- Exact `fineCostModel` `PhaseGroupSpec` for `CmkEpilogueEvs isPanic` (`≤ 2 × 16,659` scaled units). -/
theorem cmkEpilogueEvs_fine_groupSpec (isPanic : Bool) :
    PhaseGroupSpec fineCostModel (CmkEpilogueEvs isPanic)
      (if isPanic then 0 else 2 * 16659) where
  groups_le st0 {evs} h := by
    unfold CmkEpilogueEvs at h
    cases isPanic
    · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨evs_ck, hck, rfl⟩ := h
      simp only [AllocCostModel.stepEvents_append]
      have ha := fine_rustAlloc_le_44 (sz := 32) (al := 1) (by decide) (by decide)
      have hb1 := ha.groups_le st0 rfl
      have hb2 := (PhaseGroupSpec.freeOnly fineCostModel).groups_le
        (fineCostModel.stepEvents (rustAllocEvents 32 1) st0) hck
      have hb3 := ha.groups_le
        (fineCostModel.stepEvents evs_ck (fineCostModel.stepEvents (rustAllocEvents 32 1) st0)) rfl
      omega
    · simp only [↓reduceIte] at h ⊢
      subst h
      simp

/-! ## 3. Direct State-Threaded Induction on `CmkLoopAdvanceEvs` -/

private theorem cmkr1_loop_req_align :
    ∀ {n : Nat} {cap : BitVec 64} {len : Nat} {isPanic : Bool} {evs : List AllocEvent},
      CmkLoopAdvanceEvs n cap len isPanic evs →
      len ≤ 2000 →
      ∀ ev ∈ evs, eventStepReq ev ≤ 416000 ∧ eventStepAlign ev ≤ 16
  | 0, _, _, _, _, .done hepi, _ => fun ev hev => by
      obtain ⟨hreq, hal⟩ := cmkr1_epilogue_req_align hepi ev hev
      exact ⟨Nat.le_trans hreq (by decide : 32 ≤ 416000), hal⟩
  | _ + 1, cap, len, _, _, .step hgrow hpop hrest, hlen => fun ev hev => by
      have hlen' := cmkr1_nextLen_le hlen
      have hpop_fo := cmkr1_freeOnly_of_pop hpop
      rw [List.mem_append, List.mem_append, List.mem_append] at hev
      rcases hev with ((hev_a | hev_g) | hev_p) | hev_r
      · obtain ⟨hreq, hal⟩ := rustAllocEvents_req_align (by decide : (1 : Nat) ≤ 16) ev hev_a
        exact ⟨Nat.le_trans hreq (by decide : 32 ≤ 416000), hal⟩
      · by_cases hgc : len = cap.toNat
        · simp only [hgc, ↓reduceIte] at hgrow
          have hc_le : cap.toNat ≤ 2000 := by omega
          exact cmkr1_growOneEnv_req_align hgrow hc_le ev hev_g
        · simp only [hgc, ↓reduceIte] at hgrow
          subst hgrow
          nomatch hev_g
      · obtain ⟨hreq, hal⟩ := freeOnly_fineCostModel.req_align _ hpop_fo ev hev_p
        exact ⟨Nat.le_trans hreq (Nat.zero_le 416000), hal⟩
      · exact cmkr1_loop_req_align hrest hlen' ev hev_r

private def cmkr1_loopLiveInv (L₀ : Nat) (grown : Bool) (c : Nat) (st : fineCostModel.σ) : Prop :=
  if grown then
    4 ≤ c ∧ c ≤ 4000 ∧
      HasFineReallocCredit.liveLarge st ≤ L₀ + optLargeCost fineCostModel (104 * c)
  else
    HasFineReallocCredit.liveLarge st ≤ L₀

private theorem cmkr1_loopLiveInv_mono_st {L₀ : Nat} {grown : Bool} {c : Nat}
    {st st' : fineCostModel.σ}
    (hinv : cmkr1_loopLiveInv L₀ grown c st)
    (hl : HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st) :
    cmkr1_loopLiveInv L₀ grown c st' := by
  unfold cmkr1_loopLiveInv at hinv ⊢
  cases grown
  · exact Nat.le_trans hl hinv
  · simp only [↓reduceIte] at hinv ⊢
    exact ⟨hinv.1, hinv.2.1, Nat.le_trans hl hinv.2.2⟩

private theorem cmkr1_max_peak_step_first {P₀ L₀ c' : Nat} {st_a st_g : fineCostModel.σ}
    (hpk_a : HasFineReallocCredit.peakLarge st_a ≤ max P₀ (L₀ + w2CmkChainTightPeak 2000))
    (hl_a : HasFineReallocCredit.liveLarge st_a ≤ L₀)
    (hc'_le : c' ≤ 4000)
    (hp_g : HasFineReallocCredit.peakLarge st_g ≤
      max (HasFineReallocCredit.peakLarge st_a)
        (HasFineReallocCredit.liveLarge st_a + allocLargeLive fineCostModel (104 * c'))) :
    HasFineReallocCredit.peakLarge st_g ≤ max P₀ (L₀ + w2CmkChainTightPeak 2000) := by
  have h1 : allocLargeLive fineCostModel (104 * c') ≤ w2CmkChainTightLive 2000 := by
    change optLargeCost fineCostModel (104 * c') ≤
      optLargeCost fineCostModel (104 * max 4 (2 * 2000))
    exact optLargeCost_fine_mono (Nat.mul_le_mul_left 104
      (Nat.le_trans hc'_le (by decide : 4000 ≤ max 4 (2 * 2000))))
  have h2 : w2CmkChainTightLive 2000 ≤ w2CmkChainTightPeak 2000 :=
    Nat.le_add_left _ _
  have hrhs : HasFineReallocCredit.liveLarge st_a + allocLargeLive fineCostModel (104 * c') ≤
      max P₀ (L₀ + w2CmkChainTightPeak 2000) :=
    Nat.le_trans (Nat.add_le_add hl_a (Nat.le_trans h1 h2)) (Nat.le_max_right _ _)
  exact Nat.le_trans hp_g (Nat.max_le.mpr ⟨hpk_a, hrhs⟩)

private theorem cmkr1_max_peak_step_next {P₀ L₀ c c' : Nat} {st_a st_g : fineCostModel.σ}
    (hpk_a : HasFineReallocCredit.peakLarge st_a ≤ max P₀ (L₀ + w2CmkChainTightPeak 2000))
    (hc_le : c ≤ 2000) (hc'_le : c' ≤ 4000)
    (hp_g : HasFineReallocCredit.peakLarge st_g ≤
      max (HasFineReallocCredit.peakLarge st_a)
        (L₀ + allocLargeLive fineCostModel (104 * c) + allocLargeLive fineCostModel (104 * c'))) :
    HasFineReallocCredit.peakLarge st_g ≤ max P₀ (L₀ + w2CmkChainTightPeak 2000) := by
  have hold : allocLargeLive fineCostModel (104 * c) ≤ optLargeCost fineCostModel (104 * 2000) :=
    optLargeCost_fine_mono (Nat.mul_le_mul_left 104 hc_le)
  have hnew : allocLargeLive fineCostModel (104 * c') ≤
      optLargeCost fineCostModel (104 * max 4 (2 * 2000)) :=
    optLargeCost_fine_mono (Nat.mul_le_mul_left 104
      (Nat.le_trans hc'_le (by decide : 4000 ≤ max 4 (2 * 2000))))
  have hsum : L₀ + allocLargeLive fineCostModel (104 * c) + allocLargeLive fineCostModel (104 * c') ≤
      L₀ + w2CmkChainTightPeak 2000 := by
    unfold w2CmkChainTightPeak
    rw [Nat.add_assoc]
    exact Nat.add_le_add_left (Nat.add_le_add hold hnew) L₀
  exact Nat.le_trans hp_g (Nat.max_le.mpr ⟨hpk_a, Nat.le_trans hsum (Nat.le_max_right _ _)⟩)

private theorem cmkr1_combine_step_cum {c0 ca cg cr n pot' pot bud' bud sc : Nat}
    (ha : ca ≤ c0 + 738)
    (hg : cg ≤ ca + sc)
    (hr : cr ≤ cg + ((n + 2) * 738 + pot' + bud' * 9539))
    (hpot : sc + pot' ≤ pot + 9539)
    (hbud : bud' + 1 ≤ bud) :
    cr ≤ c0 + ((n + 1 + 2) * 738 + pot + bud * 9539) := by
  have hbmul : (bud' + 1) * 9539 ≤ bud * 9539 := Nat.mul_le_mul_right 9539 hbud
  rw [Nat.add_mul, Nat.one_mul] at hbmul
  have hnmul : (n + 1 + 2) * 738 = (n + 2) * 738 + 738 := by
    have h1 : n + 1 + 2 = (n + 2) + 1 := by omega
    rw [h1, Nat.add_mul, Nat.one_mul]
  rw [hnmul]
  omega

private theorem cmkr1_combine_nogrow_cum {c0 ca cr n pot bud : Nat}
    (ha : ca ≤ c0 + 738)
    (hr : cr ≤ ca + ((n + 2) * 738 + pot + bud * 9539)) :
    cr ≤ c0 + ((n + 1 + 2) * 738 + pot + bud * 9539) := by
  have hnmul : (n + 1 + 2) * 738 = (n + 2) * 738 + 738 := by
    have h1 : n + 1 + 2 = (n + 2) + 1 := by omega
    rw [h1, Nat.add_mul, Nat.one_mul]
  rw [hnmul]
  omega

private theorem cmkr1_loop_credit {L₀ P₀ : Nat} :
    ∀ {n : Nat} {cap : BitVec 64} {len : Nat} {isPanic : Bool} {evs : List AllocEvent},
      CmkLoopAdvanceEvs n cap len isPanic evs →
      ∀ (grown : Bool) (st : fineCostModel.σ),
      len ≤ 2000 →
      cmkr1_loopLiveInv L₀ grown cap.toNat st →
      HasFineReallocCredit.peakLarge st ≤ max P₀ (L₀ + w2CmkChainTightPeak 2000) →
      let S := HasFineReallocCredit.smallMaxReq fineCostModel
      let st' := fineCostModel.stepEvents evs st
      HasFineReallocCredit.cumSmall st' ≤
        HasFineReallocCredit.cumSmall st +
          ((n + 2) * 738 + cmkr1_remPot S grown cap.toNat +
            cmkr1_growBudget grown cap.toNat * 9539) ∧
      HasFineReallocCredit.liveLarge st' ≤ L₀ + w2CmkChainTightLive 2000 ∧
      HasFineReallocCredit.peakLarge st' ≤ max P₀ (L₀ + w2CmkChainTightPeak 2000)
  | 0, cap, _, _, evs, .done hepi, grown, st, _, hinv, hpk => by
      dsimp only
      obtain ⟨hc, hl, hp⟩ := cmkr1_stepEvents_epilogue st hepi
      have hc_bound : HasFineReallocCredit.cumSmall (fineCostModel.stepEvents evs st) ≤
          HasFineReallocCredit.cumSmall st +
            ((0 + 2) * 738 +
              cmkr1_remPot (HasFineReallocCredit.smallMaxReq fineCostModel) grown cap.toNat +
              cmkr1_growBudget grown cap.toNat * 9539) :=
        Nat.le_trans hc (Nat.add_le_add_left (Nat.le_trans (Nat.le_add_right _ _)
          (Nat.le_add_right _ _)) _)
      have hl_bound : HasFineReallocCredit.liveLarge (fineCostModel.stepEvents evs st) ≤
          L₀ + w2CmkChainTightLive 2000 := by
        unfold cmkr1_loopLiveInv at hinv
        cases grown
        · exact Nat.le_trans hl (Nat.le_trans hinv (Nat.le_add_right L₀ _))
        · simp only [↓reduceIte] at hinv
          have hm : optLargeCost fineCostModel (104 * cap.toNat) ≤ w2CmkChainTightLive 2000 :=
            optLargeCost_fine_mono (Nat.mul_le_mul_left 104
              (Nat.le_trans hinv.2.1 (by decide : 4000 ≤ max 4 (2 * 2000))))
          exact Nat.le_trans hl (Nat.le_trans hinv.2.2 (Nat.add_le_add_left hm L₀))
      exact ⟨hc_bound, hl_bound, Nat.le_trans hp hpk⟩
  | n + 1, cap, len, _, _, .step (evs_grow := evs_grow) (evs_pop := evs_pop) hgrow hpop hrest,
      grown, st, hlen, hinv, hpk => by
      dsimp only
      simp only [AllocCostModel.stepEvents_append]
      have hlen' := cmkr1_nextLen_le hlen
      have hpop_fo := cmkr1_freeOnly_of_pop hpop
      obtain ⟨hca, hla, hpa⟩ :=
        cmkr1_stepEvents_alloc_le_44 (sz := 32) (al := 1) st (by decide) (by decide)
      have hinv_a := cmkr1_loopLiveInv_mono_st hinv hla
      have hpk_a := Nat.le_trans hpa hpk
      by_cases hgc : len = cap.toNat
      · simp only [hgc, ↓reduceIte] at hgrow hrest
        have hc_le : cap.toNat ≤ 2000 := by omega
        let c' := max (2 * cap.toNat) 4
        have hc'4 : 4 ≤ c' := Nat.le_max_right _ _
        have hc'_le : c' ≤ 4000 := by dsimp [c']; omega
        have hnew_pos : 0 < 104 * c' := by omega
        have hevs_g : _ = growOrReallocEvents (104 * cap.toNat) (104 * c') 8 :=
          cmkr1_growOneEnv_eq hgrow
        let cap' := BitVec.ofNat 64 c'
        have hcap'_toNat : cap'.toNat = c' := by
          dsimp [cap']
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hc'_le (by decide))]
        have ham := cmkr1_growOneEnv_amortized cap
        let st_a := fineCostModel.stepEvents (rustAllocEvents 32 1) st
        let st_g := fineCostModel.stepEvents (growOrReallocEvents (104 * cap.toNat) (104 * c') 8) st_a
        rw [hevs_g]
        have hstep_g :
            HasFineReallocCredit.cumSmall st_g ≤
              HasFineReallocCredit.cumSmall st_a +
                growOrReallocStepCum fineCostModel (104 * cap.toNat) (104 * c') 8 ∧
            cmkr1_loopLiveInv L₀ true c' st_g ∧
            HasFineReallocCredit.peakLarge st_g ≤ max P₀ (L₀ + w2CmkChainTightPeak 2000) ∧
            growOrReallocStepCum fineCostModel (104 * cap.toNat) (104 * c') 8 +
              cmkr1_remPot (HasFineReallocCredit.smallMaxReq fineCostModel) true c' ≤
              cmkr1_remPot (HasFineReallocCredit.smallMaxReq fineCostModel) grown cap.toNat + 9539 ∧
            cmkr1_growBudget true c' + 1 ≤ cmkr1_growBudget grown cap.toNat := by
          cases grown
          · unfold cmkr1_loopLiveInv at hinv_a
            obtain ⟨hcg, hlg, hpg⟩ :=
              stepEvents_growOrRealloc_delta fineCostModel
                (oldReq := 104 * cap.toNat) (newReq := 104 * c') (align := 8)
                st_a (by decide) hnew_pos
            have hlg' : HasFineReallocCredit.liveLarge st_g ≤
                L₀ + optLargeCost fineCostModel (104 * c') := by
              have hsub : allocLargeLive fineCostModel (104 * c') -
                  allocLargeLive fineCostModel (104 * cap.toNat) ≤
                  optLargeCost fineCostModel (104 * c') := Nat.sub_le _ _
              exact Nat.le_trans hlg (Nat.add_le_add hinv_a hsub)
            have hpg' := cmkr1_max_peak_step_first hpk_a hinv_a hc'_le hpg
            have hpot := cmkr1_pot_step_false ham
            have hbud : cmkr1_stepsTo2000 c' + 1 ≤ 10 :=
              Nat.add_le_add_right (cmkr1_stepsTo2000_le_nine hc'4) 1
            exact ⟨hcg, ⟨hc'4, hc'_le, hlg'⟩, hpg', hpot, hbud⟩
          · unfold cmkr1_loopLiveInv at hinv_a
            simp only [↓reduceIte] at hinv_a
            obtain ⟨hc4_old, _, hlive_old⟩ := hinv_a
            obtain ⟨hcg, hlg, hpg⟩ :=
              stepEvents_growOrRealloc_credit fineCostModel
                (oldReq := 104 * cap.toNat) (newReq := 104 * c') (align := 8) (L_base := L₀)
                st_a (by decide) hnew_pos hlive_old
            have hpg' := cmkr1_max_peak_step_next hpk_a hc_le hc'_le hpg
            have hpot := cmkr1_pot_step_true ham
            have hc'_eq_2c : c' = 2 * cap.toNat := by dsimp [c']; omega
            have hbud : cmkr1_stepsTo2000 c' + 1 ≤ cmkr1_stepsTo2000 cap.toNat :=
              Nat.le_of_eq (hc'_eq_2c ▸ cmkr1_stepsTo2000_pos_le (by omega) hc_le)
            exact ⟨hcg, ⟨hc'4, hc'_le, hlg⟩, hpg', hpot, hbud⟩
        obtain ⟨hcg, hinv_g, hpg, hpot, hbud⟩ := hstep_g
        obtain ⟨hcp, hlp, hpp⟩ := stepEvents_freeOnly_le fineCostModel_freeNonInc hpop_fo st_g
        have hinv_p : cmkr1_loopLiveInv L₀ true cap'.toNat
            (fineCostModel.stepEvents evs_pop st_g) := by
          rw [hcap'_toNat]
          exact cmkr1_loopLiveInv_mono_st hinv_g hlp
        obtain ⟨hcr, hlr, hpr⟩ :=
          cmkr1_loop_credit hrest true (fineCostModel.stepEvents evs_pop st_g)
            (cmkr1_nextLen_le hc_le) hinv_p (Nat.le_trans hpp hpg)
        rw [hcap'_toNat] at hcr
        refine ⟨?_, hlr, hpr⟩
        exact cmkr1_combine_step_cum hca (Nat.le_trans hcp hcg) hcr hpot hbud
      · simp only [hgc, ↓reduceIte] at hgrow hrest
        subst hgrow
        simp only [AllocCostModel.stepEvents_nil]
        let st_a := fineCostModel.stepEvents (rustAllocEvents 32 1) st
        obtain ⟨hcp, hlp, hpp⟩ := stepEvents_freeOnly_le fineCostModel_freeNonInc hpop_fo st_a
        have hinv_p := cmkr1_loopLiveInv_mono_st hinv_a hlp
        obtain ⟨hcr, hlr, hpr⟩ :=
          cmkr1_loop_credit hrest grown (fineCostModel.stepEvents evs_pop st_a)
            hlen' hinv_p (Nat.le_trans hpp hpk_a)
        exact ⟨cmkr1_combine_nogrow_cum hca
          (Nat.le_trans hcr (Nat.add_le_add_right hcp _)), hlr, hpr⟩

/-! ## 4. `PhaseGroupSpec` Induction on `CmkLoopAdvanceEvs` -/

private theorem cmkr1_growOneEnv_groupSpec (cap : BitVec 64) :
    PhaseGroupSpec fineCostModel (GrowOneEnv cap) (3 * FineScale) := by
  have hnf : NonFreeBound (GrowOneEnv cap) 1 := by
    rintro _ (⟨_, rfl⟩ | ⟨_, rfl⟩)
    · rw [nonFreeCount_rustAllocEvents]
    · rw [nonFreeCount_rustReallocEvents]
  simpa [Nat.mul_one] using PhaseGroupSpec.of_nonFreeBound fineCostModel hnf

private theorem cmkr1_combine_step_grp {g0 ga gg gr n bud' bud gGrow : Nat}
    (ha : ga ≤ g0 + 16659)
    (hg : gg ≤ ga + gGrow)
    (hr : gr ≤ gg + ((n + 2) * 16659 + bud' * gGrow))
    (hbud : bud' + 1 ≤ bud) :
    gr ≤ g0 + ((n + 1 + 2) * 16659 + bud * gGrow) := by
  have hbmul : (bud' + 1) * gGrow ≤ bud * gGrow := Nat.mul_le_mul_right gGrow hbud
  rw [Nat.add_mul, Nat.one_mul] at hbmul
  have hnmul : (n + 1 + 2) * 16659 = (n + 2) * 16659 + 16659 := by
    have h1 : n + 1 + 2 = (n + 2) + 1 := by omega
    rw [h1, Nat.add_mul, Nat.one_mul]
  rw [hnmul]
  omega

private theorem cmkr1_combine_nogrow_grp {g0 ga gr n bud gGrow : Nat}
    (ha : ga ≤ g0 + 16659)
    (hr : gr ≤ ga + ((n + 2) * 16659 + bud * gGrow)) :
    gr ≤ g0 + ((n + 1 + 2) * 16659 + bud * gGrow) := by
  have hnmul : (n + 1 + 2) * 16659 = (n + 2) * 16659 + 16659 := by
    have h1 : n + 1 + 2 = (n + 2) + 1 := by omega
    rw [h1, Nat.add_mul, Nat.one_mul]
  rw [hnmul]
  omega

private theorem cmkr1_loop_groups :
    ∀ {n : Nat} {cap : BitVec 64} {len : Nat} {isPanic : Bool} {evs : List AllocEvent},
      CmkLoopAdvanceEvs n cap len isPanic evs →
      ∀ (grown : Bool) (st : fineCostModel.σ),
      len ≤ 2000 →
      (grown = true → 4 ≤ cap.toNat) →
      HasFineGroupCredit.groupsScaled (fineCostModel.stepEvents evs st) ≤
        HasFineGroupCredit.groupsScaled st +
          ((n + 2) * 16659 + cmkr1_growBudget grown cap.toNat * (3 * FineScale))
  | 0, cap, _, isPanic, _, .done hepi, grown, st, _, _ => by
      have hg := (cmkEpilogueEvs_fine_groupSpec isPanic).groups_le st hepi
      have hle : (if isPanic then 0 else 2 * 16659) ≤
          (0 + 2) * 16659 + cmkr1_growBudget grown cap.toNat * (3 * FineScale) := by
        cases isPanic
        · exact Nat.le_add_right (2 * 16659) _
        · exact Nat.zero_le _
      exact Nat.le_trans hg (Nat.add_le_add_left hle _)
  | n + 1, cap, len, _, _, .step (evs_grow := evs_grow) (evs_pop := evs_pop) hgrow hpop hrest,
      grown, st, hlen, hcap4 => by
      simp only [AllocCostModel.stepEvents_append]
      have hlen' := cmkr1_nextLen_le hlen
      have hpop_fo := cmkr1_freeOnly_of_pop hpop
      have ha := (fine_rustAlloc_le_44 (sz := 32) (al := 1) (by decide) (by decide)).groups_le st rfl
      let st_a := fineCostModel.stepEvents (rustAllocEvents 32 1) st
      by_cases hgc : len = cap.toNat
      · simp only [hgc, ↓reduceIte] at hgrow hrest
        have hc_le : cap.toNat ≤ 2000 := by omega
        let c' := max (2 * cap.toNat) 4
        have hc'4 : 4 ≤ c' := Nat.le_max_right _ _
        have hc'_le : c' ≤ 4000 := by dsimp [c']; omega
        let cap' := BitVec.ofNat 64 c'
        have hcap'_toNat : cap'.toNat = c' := by
          dsimp [cap']
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hc'_le (by decide))]
        have hg := (cmkr1_growOneEnv_groupSpec cap).groups_le st_a hgrow
        let st_g := fineCostModel.stepEvents evs_grow st_a
        have hp := (PhaseGroupSpec.freeOnly fineCostModel).groups_le st_g hpop_fo
        rw [Nat.add_zero] at hp
        have hbud : cmkr1_growBudget true c' + 1 ≤ cmkr1_growBudget grown cap.toNat := by
          cases grown
          · exact Nat.add_le_add_right (cmkr1_stepsTo2000_le_nine hc'4) 1
          · have hc4 := hcap4 rfl
            have hc'_eq : c' = 2 * cap.toNat := by dsimp [c']; omega
            show cmkr1_stepsTo2000 c' + 1 ≤ cmkr1_stepsTo2000 cap.toNat
            exact Nat.le_of_eq (hc'_eq ▸ cmkr1_stepsTo2000_pos_le (by omega) hc_le)
        have hr := cmkr1_loop_groups hrest true (fineCostModel.stepEvents evs_pop st_g)
          (cmkr1_nextLen_le hc_le) (fun _ => by rw [hcap'_toNat]; exact hc'4)
        rw [hcap'_toNat] at hr
        exact cmkr1_combine_step_grp ha (Nat.le_trans hp hg) hr hbud
      · simp only [hgc, ↓reduceIte] at hgrow hrest
        subst hgrow
        simp only [AllocCostModel.stepEvents_nil]
        have hp := (PhaseGroupSpec.freeOnly fineCostModel).groups_le st_a hpop_fo
        rw [Nat.add_zero] at hp
        have hr := cmkr1_loop_groups hrest grown (fineCostModel.stepEvents evs_pop st_a) hlen' hcap4
        exact cmkr1_combine_nogrow_grp ha (Nat.le_trans hr (Nat.add_le_add_right hp _))

/-! ## 5. Top-Level `CmkLoopAdvanceEvs` Credit & Group Specifications -/

/-- Tight amortized `PhaseCreditSpec` for `CmkLoopAdvanceEvs n cap0 len0 isPanic` (`len0 ≤ 2000`,
any `cap0 : BitVec 64`): charges `636,058` B (`4 × 135,167 + 10 × 9,539`) across all `Vec<104>`
doubling steps plus `(n + 2) × 738` B for `32`-B message-key/chain-key seeds. -/
theorem cmkLoopAdvanceEvs_fine_phaseCreditSpec_tight
    (n : Nat) (cap0 : BitVec 64) {len0 : Nat} (isPanic : Bool)
    (hlen0 : len0 ≤ maxMessageKeys) :
    PhaseCreditSpec fineCostModel (CmkLoopAdvanceEvs n cap0 len0 isPanic)
      ((n + 2) * 738 + 636058)
      (w2CmkChainTightLive 2000)
      (w2CmkChainTightPeak 2000)
      416000 where
  req_align _ hloop := cmkr1_loop_req_align hloop (cmkr1_maxMessageKeys_eq ▸ hlen0)
  credit_le st0 {_} hloop := by
    obtain ⟨hc, hl, hp⟩ :=
      cmkr1_loop_credit (L₀ := HasFineReallocCredit.liveLarge st0)
        (P₀ := HasFineReallocCredit.peakLarge st0)
        hloop false st0 (cmkr1_maxMessageKeys_eq ▸ hlen0)
        (Nat.le_refl _) (Nat.le_max_left _ _)
    have hpot_eq :
        cmkr1_remPot (HasFineReallocCredit.smallMaxReq fineCostModel) false cap0.toNat +
          cmkr1_growBudget false cap0.toNat * 9539 = 636058 := by
      unfold cmkr1_remPot cmkr1_growBudget
      rw [fineCostModel_smallMaxReq_eq]
      simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Nat.add_assoc ((n + 2) * 738), hpot_eq] at hc
    exact ⟨hc, hl, hp⟩

/-- Core `PhaseCreditSpec` for `CmkLoopAdvanceEvs n cap0 len0 isPanic` (`n` parametric, any
`cap0 : BitVec 64`, `len0 ≤ maxMessageKeys` = `2000`). -/
theorem cmkLoopAdvanceEvs_fine_phaseCreditSpec
    (n : Nat) (cap0 : BitVec 64) {len0 : Nat} (isPanic : Bool)
    (hlen0 : len0 ≤ maxMessageKeys) :
    PhaseCreditSpec fineCostModel (CmkLoopAdvanceEvs n cap0 len0 isPanic)
      ((n + 2) * 738 + 11 * 143484)
      (w2CmkChainTightLive 2000)
      (w2CmkChainTightPeak 2000)
      416000 :=
  (cmkLoopAdvanceEvs_fine_phaseCreditSpec_tight n cap0 isPanic hlen0).mono
    (Nat.add_le_add_left (by decide : 636058 ≤ 11 * 143484) _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- Tight `10`-grow `PhaseGroupSpec` for `CmkLoopAdvanceEvs n cap0 len0 isPanic` (`len0 ≤ 2000`,
any `cap0 : BitVec 64`). -/
theorem cmkLoopAdvanceEvs_fine_groupSpec_tight
    (n : Nat) (cap0 : BitVec 64) {len0 : Nat} (isPanic : Bool)
    (hlen0 : len0 ≤ maxMessageKeys) :
    PhaseGroupSpec fineCostModel (CmkLoopAdvanceEvs n cap0 len0 isPanic)
      ((n + 2) * 16659 + 10 * (3 * FineScale)) where
  groups_le st0 {_} hloop :=
    cmkr1_loop_groups hloop false st0 (cmkr1_maxMessageKeys_eq ▸ hlen0) (fun h => nomatch h)

/-- Core `PhaseGroupSpec` for `CmkLoopAdvanceEvs n cap0 len0 isPanic` (`n` parametric, any
`cap0 : BitVec 64`, `len0 ≤ maxMessageKeys` = `2000`). -/
theorem cmkLoopAdvanceEvs_fine_groupSpec
    (n : Nat) (cap0 : BitVec 64) {len0 : Nat} (isPanic : Bool)
    (hlen0 : len0 ≤ maxMessageKeys) :
    PhaseGroupSpec fineCostModel (CmkLoopAdvanceEvs n cap0 len0 isPanic)
      ((n + 2) * 16659 + 11 * (3 * FineScale)) :=
  (cmkLoopAdvanceEvs_fine_groupSpec_tight n cap0 isPanic hlen0).mono
    (Nat.add_le_add_left
      (Nat.mul_le_mul_right (3 * FineScale) (by decide : 10 ≤ 11)) _)

/-! ## 6. `CmkStepEnv` and `CmkSeg4Env` Wrappers -/

private theorem cmkr1_chain_len_le (r : RatchetState) (ci : Nat)
    (hchains : ∀ c ∈ r.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    (r.receiverChains[ci]?.map (·.messageKeys.length)).getD 0 ≤ maxMessageKeys := by
  cases hci : r.receiverChains[ci]? with
  | none => exact Nat.zero_le _
  | some ch =>
    simp only [Option.map_some, Option.getD_some]
    exact hchains ch (List.mem_of_getElem? hci)

private theorem cmkr1_alloc_small_phaseCredit {sz maxJumps growCum : Nat} (hsz : sz ≤ 44) :
    PhaseCreditSpec fineCostModel (· = rustAllocEvents sz 1)
      ((maxJumps + 2) * 738 + growCum)
      (w2CmkChainTightLive 2000)
      (w2CmkChainTightPeak 2000)
      416000 where
  req_align := by
    rintro _ rfl ev hev
    obtain ⟨hreq, hal⟩ := rustAllocEvents_req_align (by decide : (1 : Nat) ≤ 16) ev hev
    exact ⟨Nat.le_trans hreq (Nat.le_trans hsz (by decide : 44 ≤ 416000)), hal⟩
  credit_le := by
    rintro st0 _ rfl
    obtain ⟨hc, hl, hp⟩ := cmkr1_stepEvents_alloc_le_44 (al := 1) st0 (by decide) hsz
    have h738 : 738 ≤ (maxJumps + 2) * 738 + growCum := by
      have h2 : 1 * 738 ≤ (maxJumps + 2) * 738 :=
        Nat.mul_le_mul_right 738 (by omega)
      exact Nat.le_trans h2 (Nat.le_add_right _ _)
    exact ⟨Nat.le_trans hc (Nat.add_le_add_left h738 _),
      Nat.le_trans hl (Nat.le_add_right _ _),
      Nat.le_trans hp (Nat.le_max_left _ _)⟩

private theorem cmkr1_cmkStepEnv_cases
    (msgCounter : BitVec 32) (senderRatchetKey : PublicKey)
    (trG : TrGhost) (r : RatchetState) (ck : ChainKey) :
    CmkStepEnv msgCounter senderRatchetKey trG r ck = FreeOnlyEvs ∨
    CmkStepEnv msgCounter senderRatchetKey trG r ck = (· = []) ∨
    CmkStepEnv msgCounter senderRatchetKey trG r ck =
      (fun evs => evs = [] ∨ evs = rustAllocEvents 32 1) ∨
    CmkStepEnv msgCounter senderRatchetKey trG r ck = (· = rustAllocEvents 36 1) ∨
    ∃ ci : Nat, r.findReceiverChainIndex senderRatchetKey = some ci ∧
      (msgCounter - ck.index).toNat ≤ r.maxForwardJumps ∧
      CmkStepEnv msgCounter senderRatchetKey trG r ck =
        CmkLoopAdvanceEvs (msgCounter - ck.index).toNat
          ((trG.ratchet.chains[ci]?.map (·.mkCap)).getD 0#64)
          ((r.receiverChains[ci]?.map (·.messageKeys.length)).getD 0)
          (msgCounter == BitVec.allOnes 32) := by
  by_cases h1 : msgCounter < ck.index
  · exact Or.inl (funext fun evs => by unfold CmkStepEnv; simp only [h1, ↓reduceIte])
  · by_cases h2 : (msgCounter - ck.index).toNat ≤ r.maxForwardJumps
    · cases hfind : r.findReceiverChainIndex senderRatchetKey with
      | none =>
        by_cases h3 : ck.index < msgCounter
        · exact Or.inr (Or.inr (Or.inl (funext fun evs => by
            unfold CmkStepEnv; simp only [h1, h2, hfind, h3, ↓reduceIte])))
        · exact Or.inr (Or.inl (funext fun evs => by
            unfold CmkStepEnv; simp only [h1, h2, hfind, h3, ↓reduceIte]))
      | some ci =>
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ci, rfl, h2, funext fun evs => by
          unfold CmkStepEnv; simp only [h1, h2, hfind, ↓reduceIte]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (funext fun evs => by
        unfold CmkStepEnv; simp only [h1, h2, ↓reduceIte]))))

/-- Tight amortized `PhaseCreditSpec` for `ConsumeMsgKeyTrapPlacedBudget.CmkStepEnv`
(`r.maxForwardJumps ≤ maxJumps`). -/
theorem cmkStepEnv_fine_phaseCreditSpec_tight
    {maxJumps : Nat} (msgCounter : BitVec 32) (senderRatchetKey : PublicKey)
    (trG : TrGhost) (r : RatchetState) (ck : ChainKey)
    (hjumps : r.maxForwardJumps ≤ maxJumps)
    (hchains : ∀ c ∈ r.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    PhaseCreditSpec fineCostModel
      (CmkStepEnv msgCounter senderRatchetKey trG r ck)
      ((maxJumps + 2) * 738 + 636058)
      (w2CmkChainTightLive 2000)
      (w2CmkChainTightPeak 2000)
      416000 := by
  rcases cmkr1_cmkStepEnv_cases msgCounter senderRatchetKey trG r ck with
    hEq | hEq | hEq | hEq | ⟨ci, _, hj_le, hEq⟩ <;> rw [hEq]
  · exact freeOnly_fineCostModel.mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · exact (PhaseCreditSpec.nil fineCostModel).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · have hnil : PhaseCreditSpec fineCostModel (· = [])
        ((maxJumps + 2) * 738 + 636058)
        (w2CmkChainTightLive 2000) (w2CmkChainTightPeak 2000) 416000 :=
      (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    have ha32 := cmkr1_alloc_small_phaseCredit (sz := 32)
      (maxJumps := maxJumps) (growCum := 636058) (by decide)
    exact (hnil.or ha32).mono
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
  · exact cmkr1_alloc_small_phaseCredit (sz := 36)
      (maxJumps := maxJumps) (growCum := 636058) (by decide)
  · have hn_le : (msgCounter - ck.index).toNat ≤ maxJumps := Nat.le_trans hj_le hjumps
    exact (cmkLoopAdvanceEvs_fine_phaseCreditSpec_tight
      (msgCounter - ck.index).toNat
      ((trG.ratchet.chains[ci]?.map (·.mkCap)).getD 0#64)
      (msgCounter == BitVec.allOnes 32)
      (cmkr1_chain_len_le r ci hchains)).mono
      (Nat.add_le_add_right (Nat.mul_le_mul_right 738 (Nat.add_le_add_right hn_le 2)) _)
      (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- `PhaseCreditSpec` for `ConsumeMsgKeyTrapPlacedBudget.CmkStepEnv` (`r.maxForwardJumps ≤ maxJumps`). -/
theorem cmkStepEnv_fine_phaseCreditSpec
    {maxJumps : Nat} (msgCounter : BitVec 32) (senderRatchetKey : PublicKey)
    (trG : TrGhost) (r : RatchetState) (ck : ChainKey)
    (hjumps : r.maxForwardJumps ≤ maxJumps)
    (hchains : ∀ c ∈ r.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    PhaseCreditSpec fineCostModel
      (CmkStepEnv msgCounter senderRatchetKey trG r ck)
      ((maxJumps + 2) * 738 + 11 * 143484)
      (w2CmkChainTightLive 2000)
      (w2CmkChainTightPeak 2000)
      416000 :=
  (cmkStepEnv_fine_phaseCreditSpec_tight msgCounter senderRatchetKey trG r ck hjumps hchains).mono
    (Nat.add_le_add_left (by decide : 636058 ≤ 11 * 143484) _)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

/-- Tight `10`-grow `PhaseGroupSpec` for `ConsumeMsgKeyTrapPlacedBudget.CmkStepEnv`
(`r.maxForwardJumps ≤ maxJumps`). -/
theorem cmkStepEnv_fine_groupSpec_tight
    {maxJumps : Nat} (msgCounter : BitVec 32) (senderRatchetKey : PublicKey)
    (trG : TrGhost) (r : RatchetState) (ck : ChainKey)
    (hjumps : r.maxForwardJumps ≤ maxJumps)
    (hchains : ∀ c ∈ r.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    PhaseGroupSpec fineCostModel
      (CmkStepEnv msgCounter senderRatchetKey trG r ck)
      ((maxJumps + 2) * 16659 + 10 * (3 * FineScale)) := by
  have h16659 : 16659 ≤ (maxJumps + 2) * 16659 + 10 * (3 * FineScale) :=
    Nat.le_trans (Nat.mul_le_mul_right 16659 (by omega : 1 ≤ maxJumps + 2)) (Nat.le_add_right _ _)
  rcases cmkr1_cmkStepEnv_cases msgCounter senderRatchetKey trG r ck with
    hEq | hEq | hEq | hEq | ⟨ci, _, hj_le, hEq⟩ <;> rw [hEq]
  · exact (PhaseGroupSpec.freeOnly fineCostModel).mono (Nat.zero_le _)
  · exact (PhaseGroupSpec.nil fineCostModel).mono (Nat.zero_le _)
  · have hnil := (PhaseGroupSpec.nil fineCostModel).mono
      (Nat.zero_le ((maxJumps + 2) * 16659 + 10 * (3 * FineScale)))
    have ha32 := (fine_rustAlloc_le_44 (sz := 32) (al := 1) (by decide) (by decide)).mono h16659
    exact (hnil.or ha32).mono (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_refl _⟩)
  · exact (fine_rustAlloc_le_44 (sz := 36) (al := 1) (by decide) (by decide)).mono h16659
  · have hn_le : (msgCounter - ck.index).toNat ≤ maxJumps := Nat.le_trans hj_le hjumps
    exact (cmkLoopAdvanceEvs_fine_groupSpec_tight
      (msgCounter - ck.index).toNat
      ((trG.ratchet.chains[ci]?.map (·.mkCap)).getD 0#64)
      (msgCounter == BitVec.allOnes 32)
      (cmkr1_chain_len_le r ci hchains)).mono
      (Nat.add_le_add_right (Nat.mul_le_mul_right 16659 (Nat.add_le_add_right hn_le 2)) _)

/-- `PhaseGroupSpec` for `ConsumeMsgKeyTrapPlacedBudget.CmkStepEnv` (`r.maxForwardJumps ≤ maxJumps`). -/
theorem cmkStepEnv_fine_groupSpec
    {maxJumps : Nat} (msgCounter : BitVec 32) (senderRatchetKey : PublicKey)
    (trG : TrGhost) (r : RatchetState) (ck : ChainKey)
    (hjumps : r.maxForwardJumps ≤ maxJumps)
    (hchains : ∀ c ∈ r.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    PhaseGroupSpec fineCostModel
      (CmkStepEnv msgCounter senderRatchetKey trG r ck)
      ((maxJumps + 2) * 16659 + 11 * (3 * FineScale)) :=
  (cmkStepEnv_fine_groupSpec_tight msgCounter senderRatchetKey trG r ck hjumps hchains).mono
    (Nat.add_le_add_left
      (Nat.mul_le_mul_right (3 * FineScale) (by decide : 10 ≤ 11)) _)

theorem tryDecryptCmkStepEnv_fine_phaseCreditSpec_tight
    {maxJumps : Nat} (msgCounter : BitVec 32) (senderRatchetKey : PublicKey)
    (trG : TrGhost) (r : RatchetState) (ck : ChainKey)
    (hjumps : r.maxForwardJumps ≤ maxJumps)
    (hchains : ∀ c ∈ r.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    PhaseCreditSpec fineCostModel
      (tryDecryptCmkStepEnv msgCounter senderRatchetKey trG r ck)
      ((maxJumps + 2) * 738 + 636058)
      (w2CmkChainTightLive 2000)
      (w2CmkChainTightPeak 2000)
      416000 :=
  cmkStepEnv_fine_phaseCreditSpec_tight msgCounter senderRatchetKey trG r ck hjumps hchains

theorem tryDecryptCmkStepEnv_fine_phaseCreditSpec
    {maxJumps : Nat} (msgCounter : BitVec 32) (senderRatchetKey : PublicKey)
    (trG : TrGhost) (r : RatchetState) (ck : ChainKey)
    (hjumps : r.maxForwardJumps ≤ maxJumps)
    (hchains : ∀ c ∈ r.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    PhaseCreditSpec fineCostModel
      (tryDecryptCmkStepEnv msgCounter senderRatchetKey trG r ck)
      ((maxJumps + 2) * 738 + 11 * 143484)
      (w2CmkChainTightLive 2000)
      (w2CmkChainTightPeak 2000)
      416000 :=
  cmkStepEnv_fine_phaseCreditSpec msgCounter senderRatchetKey trG r ck hjumps hchains

theorem tryDecryptCmkStepEnv_fine_groupSpec_tight
    {maxJumps : Nat} (msgCounter : BitVec 32) (senderRatchetKey : PublicKey)
    (trG : TrGhost) (r : RatchetState) (ck : ChainKey)
    (hjumps : r.maxForwardJumps ≤ maxJumps)
    (hchains : ∀ c ∈ r.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    PhaseGroupSpec fineCostModel
      (tryDecryptCmkStepEnv msgCounter senderRatchetKey trG r ck)
      ((maxJumps + 2) * 16659 + 10 * (3 * FineScale)) :=
  cmkStepEnv_fine_groupSpec_tight msgCounter senderRatchetKey trG r ck hjumps hchains

theorem tryDecryptCmkStepEnv_fine_groupSpec
    {maxJumps : Nat} (msgCounter : BitVec 32) (senderRatchetKey : PublicKey)
    (trG : TrGhost) (r : RatchetState) (ck : ChainKey)
    (hjumps : r.maxForwardJumps ≤ maxJumps)
    (hchains : ∀ c ∈ r.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    PhaseGroupSpec fineCostModel
      (tryDecryptCmkStepEnv msgCounter senderRatchetKey trG r ck)
      ((maxJumps + 2) * 16659 + 11 * (3 * FineScale)) :=
  cmkStepEnv_fine_groupSpec msgCounter senderRatchetKey trG r ck hjumps hchains

private theorem cmkr1_seg4_credit_wrap {E : List AllocEvent → Prop} {c : Nat}
    (h : PhaseCreditSpec fineCostModel E c (w2CmkChainTightLive 2000) (w2CmkChainTightPeak 2000) 416000) :
    PhaseCreditSpec fineCostModel (SeqEnv FmtWriteEnv (SeqEnv E FreeOnlyEvs))
      c (w2CmkChainTightLive 2000) (w2CmkChainTightPeak 2000) 416000 := by
  have hfmt : PhaseCreditSpec fineCostModel FmtWriteEnv 0 0 0 0 := PhaseCreditSpec.nil fineCostModel
  have hlp : w2CmkChainTightLive 2000 ≤ w2CmkChainTightPeak 2000 := Nat.le_add_left _ _
  have h1 : PhaseCreditSpec fineCostModel (SeqEnv E FreeOnlyEvs)
      c (w2CmkChainTightLive 2000) (w2CmkChainTightPeak 2000) 416000 :=
    (h.seq freeOnly_fineCostModel).mono
      (Nat.le_of_eq (Nat.add_zero c))
      (Nat.le_of_eq (Nat.add_zero _))
      (Nat.max_le.mpr ⟨Nat.le_refl _, Nat.le_trans (Nat.le_of_eq (Nat.add_zero _)) hlp⟩)
      (Nat.max_eq_left (Nat.zero_le _)).le
  exact (hfmt.seq h1).mono
    (Nat.le_of_eq (Nat.zero_add c))
    (Nat.le_of_eq (Nat.zero_add _))
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_of_eq (Nat.zero_add _)⟩)
    (Nat.max_eq_right (Nat.zero_le _)).le

private theorem cmkr1_seg4_group_wrap {E : List AllocEvent → Prop} {g : Nat}
    (h : PhaseGroupSpec fineCostModel E g) :
    PhaseGroupSpec fineCostModel (SeqEnv FmtWriteEnv (SeqEnv E FreeOnlyEvs)) g := by
  have hfmt : PhaseGroupSpec fineCostModel FmtWriteEnv 0 := PhaseGroupSpec.nil fineCostModel
  have h1 := (h.seq (PhaseGroupSpec.freeOnly fineCostModel)).mono (Nat.le_of_eq (Nat.add_zero g))
  exact (hfmt.seq h1).mono (Nat.le_of_eq (Nat.zero_add g))

/-- Tight amortized Segment-4 `PhaseCreditSpec` for `CmkSeg4Env FmtWriteEnv` (`s4DefaultEnv`). -/
theorem cmkSeg4Env_fine_phaseCreditSpec_tight
    {maxJumps : Nat} (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (ck : ChainKey)
    (hjumps : tr.ratchet.maxForwardJumps ≤ maxJumps)
    (hchains : ∀ c ∈ tr.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    PhaseCreditSpec fineCostModel (CmkSeg4Env FmtWriteEnv x trG tr ck)
      ((maxJumps + 2) * 738 + 636058)
      (w2CmkChainTightLive 2000)
      (w2CmkChainTightPeak 2000)
      416000 :=
  cmkr1_seg4_credit_wrap
    (cmkStepEnv_fine_phaseCreditSpec_tight x.msg.counter x.msg.senderRatchetKey trG tr.ratchet ck
      hjumps hchains)

/-- Segment-4 `PhaseCreditSpec` for `CmkSeg4Env FmtWriteEnv` (`s4DefaultEnv`, matching `s4DefaultEnv`
and `DecPkD2cSlotOkLinked.tryDecryptCmkSeg4Env FmtWriteEnv`). -/
theorem cmkSeg4Env_fine_phaseCreditSpec
    {maxJumps : Nat} (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (ck : ChainKey)
    (hjumps : tr.ratchet.maxForwardJumps ≤ maxJumps)
    (hchains : ∀ c ∈ tr.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    PhaseCreditSpec fineCostModel (CmkSeg4Env FmtWriteEnv x trG tr ck)
      ((maxJumps + 2) * 738 + 11 * 143484)
      (w2CmkChainTightLive 2000)
      (w2CmkChainTightPeak 2000)
      416000 :=
  cmkr1_seg4_credit_wrap
    (cmkStepEnv_fine_phaseCreditSpec x.msg.counter x.msg.senderRatchetKey trG tr.ratchet ck
      hjumps hchains)

/-- Tight `10`-grow Segment-4 `PhaseGroupSpec` for `CmkSeg4Env FmtWriteEnv` (`s4DefaultEnv`). -/
theorem cmkSeg4Env_fine_groupSpec_tight
    {maxJumps : Nat} (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (ck : ChainKey)
    (hjumps : tr.ratchet.maxForwardJumps ≤ maxJumps)
    (hchains : ∀ c ∈ tr.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    PhaseGroupSpec fineCostModel (CmkSeg4Env FmtWriteEnv x trG tr ck)
      ((maxJumps + 2) * 16659 + 10 * (3 * FineScale)) :=
  cmkr1_seg4_group_wrap
    (cmkStepEnv_fine_groupSpec_tight x.msg.counter x.msg.senderRatchetKey trG tr.ratchet ck
      hjumps hchains)

/-- Segment-4 `PhaseGroupSpec` for `CmkSeg4Env FmtWriteEnv` (`s4DefaultEnv`). -/
theorem cmkSeg4Env_fine_groupSpec
    {maxJumps : Nat} (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (ck : ChainKey)
    (hjumps : tr.ratchet.maxForwardJumps ≤ maxJumps)
    (hchains : ∀ c ∈ tr.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    PhaseGroupSpec fineCostModel (CmkSeg4Env FmtWriteEnv x trG tr ck)
      ((maxJumps + 2) * 16659 + 11 * (3 * FineScale)) :=
  cmkr1_seg4_group_wrap
    (cmkStepEnv_fine_groupSpec x.msg.counter x.msg.senderRatchetKey trG tr.ratchet ck
      hjumps hchains)

theorem tryDecryptCmkSeg4Env_fine_phaseCreditSpec_tight
    {maxJumps : Nat} (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (ck : ChainKey)
    (hjumps : tr.ratchet.maxForwardJumps ≤ maxJumps)
    (hchains : ∀ c ∈ tr.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    PhaseCreditSpec fineCostModel (tryDecryptCmkSeg4Env FmtWriteEnv x trG tr ck)
      ((maxJumps + 2) * 738 + 636058)
      (w2CmkChainTightLive 2000)
      (w2CmkChainTightPeak 2000)
      416000 :=
  cmkSeg4Env_fine_phaseCreditSpec_tight x trG tr ck hjumps hchains

theorem tryDecryptCmkSeg4Env_fine_phaseCreditSpec
    {maxJumps : Nat} (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (ck : ChainKey)
    (hjumps : tr.ratchet.maxForwardJumps ≤ maxJumps)
    (hchains : ∀ c ∈ tr.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    PhaseCreditSpec fineCostModel (tryDecryptCmkSeg4Env FmtWriteEnv x trG tr ck)
      ((maxJumps + 2) * 738 + 11 * 143484)
      (w2CmkChainTightLive 2000)
      (w2CmkChainTightPeak 2000)
      416000 :=
  cmkSeg4Env_fine_phaseCreditSpec x trG tr ck hjumps hchains

theorem tryDecryptCmkSeg4Env_fine_groupSpec_tight
    {maxJumps : Nat} (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (ck : ChainKey)
    (hjumps : tr.ratchet.maxForwardJumps ≤ maxJumps)
    (hchains : ∀ c ∈ tr.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    PhaseGroupSpec fineCostModel (tryDecryptCmkSeg4Env FmtWriteEnv x trG tr ck)
      ((maxJumps + 2) * 16659 + 10 * (3 * FineScale)) :=
  cmkSeg4Env_fine_groupSpec_tight x trG tr ck hjumps hchains

theorem tryDecryptCmkSeg4Env_fine_groupSpec
    {maxJumps : Nat} (x : TryDecryptGhost) (trG : TrGhost)
    (tr : TripleRatchet (List (BitVec 8))) (ck : ChainKey)
    (hjumps : tr.ratchet.maxForwardJumps ≤ maxJumps)
    (hchains : ∀ c ∈ tr.ratchet.receiverChains, c.messageKeys.length ≤ maxMessageKeys) :
    PhaseGroupSpec fineCostModel (tryDecryptCmkSeg4Env FmtWriteEnv x trG tr ck)
      ((maxJumps + 2) * 16659 + 11 * (3 * FineScale)) :=
  cmkSeg4Env_fine_groupSpec x trG tr ck hjumps hchains

/-! ## 7. Closed `25,000`-Jump Constants and Non-Vacuity Witness -/

/-- Closed `Δcum` at `maxJumps = 25,000` (`tight`: `19,087,534` B; `11 * 143,484`: `20,029,800` B). -/
def cmkLoop25000TightCum : Nat := 19087534
def cmkLoop25000Cum : Nat := 20029800
def cmkLoop25000Live : Nat := 424195
def cmkLoop25000Peak : Nat := 640390
def cmkLoop25000MaxReq : Nat := 416000
def cmkLoop25000TightGrpS : Nat := 418474398
def cmkLoop25000GrpS : Nat := 418671006

theorem cmkLoop25000_constants_eq :
    (25000 + 2) * 738 + 636058 = cmkLoop25000TightCum ∧
    (25000 + 2) * 738 + 11 * 143484 = cmkLoop25000Cum ∧
    w2CmkChainTightLive 2000 = cmkLoop25000Live ∧
    w2CmkChainTightPeak 2000 = cmkLoop25000Peak ∧
    (25000 + 2) * 16659 + 10 * (3 * FineScale) = cmkLoop25000TightGrpS ∧
    (25000 + 2) * 16659 + 11 * (3 * FineScale) = cmkLoop25000GrpS := by
  decide

/-- Concrete allocating non-vacuity witness at the exact-fit `len0 = 2000, cap0 = 2000#64` edge case
(`realloc 8 208000 416000` firing before `evs_pop`, followed by non-panic `CmkEpilogueEvs`). -/
theorem cmkLoopAdvanceEvs_exactFit2000_nonvacuous :
    ∃ evs : List AllocEvent,
      evs ≠ [] ∧
      CmkLoopAdvanceEvs 1 2000#64 2000 false evs := by
  let evs_grow := rustReallocEvents (2000 * 104) (4000 * 104) 8
  let evs_epi := rustAllocEvents 32 1 ++ ([] : List AllocEvent) ++ rustAllocEvents 32 1
  refine ⟨rustAllocEvents 32 1 ++ evs_grow ++ [] ++ evs_epi, ?_, ?_⟩
  · unfold rustAllocEvents
    decide
  · refine CmkLoopAdvanceEvs.step ?_ ?_ (CmkLoopAdvanceEvs.done ?_)
    · change GrowOneEnv 2000#64 evs_grow
      exact Or.inr ⟨by decide, rfl⟩
    · change FreeOnlyEvs []
      intro ev hev
      nomatch hev
    · unfold CmkEpilogueEvs
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨[], (fun _ hev => nomatch hev), rfl⟩

end LibsignalBinary.Proofs.PeakBudget.CmkLoopAdvanceCredit
