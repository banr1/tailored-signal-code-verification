/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrLeafCodecCredit
public import LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakHelpers

/-!
# Small-Class and `fineCostModel` Leaf/Chain Credit Helpers for `spqr::recv`

Proves zero-live-growth (`Δlive = Δpeak = 0`) `PhaseCreditSpec` bounds for `SpqrBoundedEvs` below
`smallMaxReq M` (`InitInnerEnv`, `StatesIntoPbEnv`) and tight `fineCostModel` credit bounds for
`NextKeyInternalEnv`, `ChainNewEnv`, `ChainFromEnv`, `ChainAddEpochEnv`, `ChainIntoPbEnv`, and
`PqRatchetStateEncodeToVecEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightHelpers

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1
  (Bytes Chain ChainPB Epoch HkdfFn PqRatchetState V1State VersionNegotiationPB)
open CryptoVerification.SpqrV1.ChainProofs
  (ChainAddEpochGhost ChainIntoPbCall chainEpochAlign chainEpochSize)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (pqRatchetStatePBEncodedLen)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.StateSize (rawV1State)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine (fineCostModel)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_largeCost_eq fineCostModel_largeMetaCost_eq
   fineCostModel_smallMaxReq_eq smallAllocCost_le_1997_of_le_108 smallAllocCost_le_738_of_le_44
   smallAllocCost_le_add_26365 smallAllocCost_le_two_mul_add)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
  (HasFineReallocCredit stepEvents_rustAlloc_large stepEvents_rustAlloc_small
   stepEvents_rustRealloc_small_small)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ConcatEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit (eventStepReq_le_reqBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrPolyBounds (v1StateEncodeRaw_len_le)
open LibsignalBinary.Proofs.PeakBudget.SpqrRecvPeakHelpers
  (chainNew_phaseCreditSpec_exact nextKeyInternalReq nextKeyInternal_phaseCreditSpec
   vecDequeGrowMaxReq)
open LibsignalBinary.Proofs.SpqrV1.Chain.AddEpochHelpersBudget
  (ChainAddEpochEnv chainAddEpochEvents)
open LibsignalBinary.Proofs.SpqrV1.Chain.DefsBudget
  (ChainNewEnv NextKeyInternalEnv vecDequeGrowEvents)
open LibsignalBinary.Proofs.SpqrV1.Chain.IntoPbHelpersBudget (ChainIntoPbEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget (PqRatchetStateEncodeToVecEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget
  (ChainFromEnv ChainFromVersionNegotiationEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (InitInnerEnv SpqrBoundedEvs StatesIntoPbEnv nonFreeCount)

/-! ## Small-Class `SpqrBoundedEvs` (`Δlive = 0`, `Δpeak = 0`) -/

private theorem nat_max_le_max_local {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) :
    max a b ≤ max c d :=
  Nat.max_le.mpr ⟨Nat.le_trans h1 (Nat.le_max_left c d), Nat.le_trans h2 (Nat.le_max_right c d)⟩

private theorem req_align_of_spqrBounded {maxReq : Nat} {ev : AllocEvent}
    (h : ev.withinMaxAlloc ∧ ev.reqBytes ≤ maxReq ∧
      (∀ al r, ev = .aligned al r → al ≤ 16) ∧
      (∀ al o n, ev = .realloc al o n → al ≤ 16)) :
    eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  obtain ⟨_, hreq, ha, hre⟩ := h
  refine ⟨Nat.le_trans (eventStepReq_le_reqBytes ev) hreq, ?_⟩
  cases ev with
  | alloc _ => exact Nat.le_refl 16
  | aligned al r => exact ha al r rfl
  | free _ _ => exact Nat.le_refl 16
  | realloc al o n => exact hre al o n rfl

private theorem stepEvents_spqrBoundedEvs_small_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {maxReq : Nat} (hSmall : maxReq ≤ HasFineReallocCredit.smallMaxReq M) :
    ∀ (evs : List AllocEvent) (maxAllocs : Nat) (st0 : M.σ),
      SpqrBoundedEvs maxAllocs maxReq evs →
      HasFineReallocCredit.cumSmall (M.stepEvents evs st0) ≤
        HasFineReallocCredit.cumSmall st0 + maxAllocs * (2 * maxReq + 9539) ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st0) ≤
        HasFineReallocCredit.liveLarge st0 ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st0) ≤
        max (HasFineReallocCredit.peakLarge st0) (HasFineReallocCredit.liveLarge st0)
  | [], _, st0, _ => by
    simp only [AllocCostModel.stepEvents_nil]
    exact ⟨by omega, Nat.le_refl _, Nat.le_max_left _ _⟩
  | .free al sz :: tl, maxAllocs, st0, ⟨hcnt, hall⟩ => by
    simp only [AllocCostModel.stepEvents_cons]
    have htl : SpqrBoundedEvs maxAllocs maxReq tl :=
      ⟨hcnt, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
    obtain ⟨hc₁, hl₁, hp₁⟩ := hM.freeNonInc al sz st0
    obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrBoundedEvs_small_le hM hSmall tl maxAllocs
      (M.step (.free al sz) st0) htl
    omega
  | .alloc req :: tl, maxAllocs, st0, ⟨hcnt, hall⟩ => by
    simp only [nonFreeCount] at hcnt
    cases maxAllocs with
    | zero => omega
    | succ m =>
      simp only [AllocCostModel.stepEvents_cons]
      have hc_step : (m + 1) * (2 * maxReq + 9539) = m * (2 * maxReq + 9539) + (2 * maxReq + 9539) :=
        Nat.succ_mul m _
      obtain ⟨hreq, _⟩ := req_align_of_spqrBounded (hall (.alloc req) List.mem_cons_self)
      have hreq_le : req ≤ maxReq := hreq
      have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq_le hSmall
      have htl : SpqrBoundedEvs m maxReq tl :=
        ⟨by omega, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_alloc_small_any st0 hle
      have hsa := hM.smallAlloc_le hle
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrBoundedEvs_small_le hM hSmall tl m
        (M.step (.alloc req) st0) htl
      rw [hc_step]
      exact ⟨by omega, by omega, by omega⟩
  | .aligned al req :: tl, maxAllocs, st0, ⟨hcnt, hall⟩ => by
    simp only [nonFreeCount] at hcnt
    cases maxAllocs with
    | zero => omega
    | succ m =>
      simp only [AllocCostModel.stepEvents_cons]
      have hc_step : (m + 1) * (2 * maxReq + 9539) = m * (2 * maxReq + 9539) + (2 * maxReq + 9539) :=
        Nat.succ_mul m _
      obtain ⟨hreq, hal⟩ := req_align_of_spqrBounded (hall (.aligned al req) List.mem_cons_self)
      have hreq_le : req ≤ maxReq := hreq
      have hal16 : al ≤ 16 := hal
      have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq_le hSmall
      have htl : SpqrBoundedEvs m maxReq tl :=
        ⟨by omega, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_aligned_small_any st0 hal16 hle
      have hsa := hM.smallAlloc_le hle
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrBoundedEvs_small_le hM hSmall tl m
        (M.step (.aligned al req) st0) htl
      rw [hc_step]
      exact ⟨by omega, by omega, by omega⟩
  | .realloc al o n :: tl, maxAllocs, st0, ⟨hcnt, hall⟩ => by
    simp only [nonFreeCount] at hcnt
    cases maxAllocs with
    | zero => omega
    | succ m =>
      simp only [AllocCostModel.stepEvents_cons]
      have hc_step : (m + 1) * (2 * maxReq + 9539) = m * (2 * maxReq + 9539) + (2 * maxReq + 9539) :=
        Nat.succ_mul m _
      obtain ⟨hreq, hal⟩ := req_align_of_spqrBounded (hall (.realloc al o n) List.mem_cons_self)
      have hn_max : n ≤ maxReq := hreq
      have hal16 : al ≤ 16 := hal
      have hn : n ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hn_max hSmall
      have hsr := hM.smallRealloc_le hn
      have htl : SpqrBoundedEvs m maxReq tl :=
        ⟨by omega, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
      rw [hc_step]
      by_cases ho : o ≤ HasFineReallocCredit.smallMaxReq M
      · obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_realloc_small_small_any st0 hal16 ho hn
        obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrBoundedEvs_small_le hM hSmall tl m
          (M.step (.realloc al o n) st0) htl
        exact ⟨by omega, by omega, by omega⟩
      · have ho' : HasFineReallocCredit.smallMaxReq M < o := by omega
        obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_realloc_large_small_any st0 hal16 ho' hn
        obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrBoundedEvs_small_le hM hSmall tl m
          (M.step (.realloc al o n) st0) htl
        exact ⟨by omega, by omega, by omega⟩

/-- When `maxReq ≤ smallMaxReq M`, `SpqrBoundedEvs maxAllocs maxReq` stays in small classes (`Δlive = Δpeak = 0`).
-/
theorem spqrBoundedEvs_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (maxAllocs : Nat) {maxReq : Nat}
    (hSmall : maxReq ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (SpqrBoundedEvs maxAllocs maxReq)
      (maxAllocs * (2 * maxReq + 9539)) 0 0 maxReq where
  req_align _ hE ev hev := req_align_of_spqrBounded (hE.2 ev hev)
  credit_le st0 {evs} hE := by
    obtain ⟨hc, hl, hp⟩ := stepEvents_spqrBoundedEvs_small_le hM hSmall evs maxAllocs st0 hE
    exact ⟨hc, by omega, by omega⟩

/-- Small-class `PhaseCreditSpec` for `InitInnerEnv F x` when `2 * authCap + 2048 ≤ smallMaxReq M`.
-/
theorem initInner_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress) (x : InitInnerGhost) {authCap : Nat}
    (hauth : x.authKey.length ≤ authCap)
    (hSmall : 2 * authCap + 2048 ≤ HasFineReallocCredit.smallMaxReq M) :
    let R := 2 * authCap + 2048
    PhaseCreditSpec M (InitInnerEnv F x) (96 * (2 * R + 9539)) 0 0 R := by
  intro R
  unfold InitInnerEnv
  cases x.v with
  | v0 =>
    exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | v1 =>
    have hR : 2 * x.authKey.length + 2048 ≤ R := by dsimp only [R]; omega
    exact (spqrBoundedEvs_small_phaseCreditSpec hM 96 hSmall).of_imp
      fun _ hevs => SpqrBoundedEvs.mono (Nat.le_refl 96) hR hevs

theorem initInner_fine_phaseCreditSpec_32 (F : ShaCompress) (x : InitInnerGhost)
    (hauth : x.authKey.length ≤ 32) :
    PhaseCreditSpec fineCostModel (InitInnerEnv F x) 1321248 0 0 2112 :=
  (initInner_small_phaseCreditSpec fineCostModel_modelHyps F x hauth
    (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
    (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

/-- Small-class `PhaseCreditSpec` for `StatesIntoPbEnv x` when `2 * v1Cap + 1824 ≤ smallMaxReq M`.
-/
theorem statesIntoPb_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {F : ShaCompress} (x : StatesIntoPbGhost F) {v1Cap : Nat}
    (hv1 : rawV1State x.st.into_pb ≤ v1Cap)
    (hSmall : 2 * v1Cap + 1824 ≤ HasFineReallocCredit.smallMaxReq M) :
    let R := 2 * v1Cap + 1824
    PhaseCreditSpec M (StatesIntoPbEnv x) (64 * (2 * R + 9539)) 0 0 R := by
  intro R
  have hlen := v1StateEncodeRaw_len_le x.st.into_pb
  have hR : 2 * (V1State.encodeRaw x.st.into_pb).length + 1024 ≤ R := by dsimp only [R]; omega
  exact (spqrBoundedEvs_small_phaseCreditSpec hM 64 hSmall).of_imp
    fun _ hevs => SpqrBoundedEvs.mono (Nat.le_refl 64) hR hevs

theorem statesIntoPb_fine_phaseCreditSpec_49856 {F : ShaCompress} (x : StatesIntoPbGhost F)
    (hv1 : rawV1State x.st.into_pb ≤ 49856) :
    PhaseCreditSpec fineCostModel (StatesIntoPbEnv x) 13607104 0 0 101536 :=
  (statesIntoPb_small_phaseCreditSpec fineCostModel_modelHyps x hv1
    (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
    (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

/-! ## Tight `fineCostModel` Leaf and Chain Credit Specs -/

theorem req_align_rustAlloc_local {req al : Nat} (hal : al ≤ 16) :
    ∀ ev ∈ rustAllocEvents req al, eventStepReq ev ≤ req ∧ eventStepAlign ev ≤ 16 := by
  unfold rustAllocEvents
  split <;> intro ev hev <;> rw [List.mem_singleton] at hev <;> subst hev <;>
    simp only [eventStepReq, eventStepAlign] <;> omega

theorem req_align_rustRealloc_local {old new al : Nat} (hal : al ≤ 16) (hal_new : al ≤ new) :
    ∀ ev ∈ rustReallocEvents old new al, eventStepReq ev ≤ new ∧ eventStepAlign ev ≤ 16 := by
  unfold rustReallocEvents
  simp only [hal, hal_new, and_self, ↓reduceIte]
  intro ev hev
  rw [List.mem_singleton] at hev
  subst hev
  exact ⟨Nat.le_refl new, hal⟩

/-- `PhaseCreditSpec` for `NextKeyInternalEnv` on `fineCostModel` (`nextKeyInternalReq = 35 ≤ 44`, `Δcum = 738`, `Δlive = Δpeak = 0`).
-/
theorem nextKeyInternal_fine_phaseCreditSpec :
    PhaseCreditSpec fineCostModel NextKeyInternalEnv 738 0 0 nextKeyInternalReq := by
  have hSmall : nextKeyInternalReq ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have h738 : HasFineReallocCredit.smallAllocCost fineCostModel nextKeyInternalReq ≤ 738 :=
    smallAllocCost_le_738_of_le_44 (by decide)
  exact (nextKeyInternal_phaseCreditSpec hSmall).mono
    h738 (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl _)

/-- `PhaseCreditSpec` for `ChainNewEnv` on `fineCostModel` (`Δcum = 16,643`, `Δlive = Δpeak = 0`, `maxReq = 448`).
-/
theorem chainNew_fine_phaseCreditSpec :
    PhaseCreditSpec fineCostModel ChainNewEnv 16643 0 0 448 := by
  have hSmall448 : 448 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have h72 : HasFineReallocCredit.smallAllocCost fineCostModel 72 ≤ 1997 :=
    smallAllocCost_le_1997_of_le_108 (by decide)
  have h32 : HasFineReallocCredit.smallAllocCost fineCostModel 32 ≤ 738 :=
    smallAllocCost_le_738_of_le_44 (by decide)
  have h448 : HasFineReallocCredit.smallAllocCost fineCostModel 448 ≤ 10435 := by
    have := smallAllocCost_le_two_mul_add 448; omega
  exact (chainNew_phaseCreditSpec_exact hSmall448).mono
    (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 448)

private theorem chainFromNewEvents_fine_phaseCreditSpec :
    PhaseCreditSpec fineCostModel
      (· = LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget.chainNewEvents)
      16643 0 0 448 := by
  have h72s : 72 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have h32s : 32 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have h448s : 448 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have ha72 := PhaseCreditSpec.rustAlloc_small fineCostModel (req := 72) (al := 1)
    (by decide) (by decide) h72s
  have ha32 := PhaseCreditSpec.rustAlloc_small fineCostModel (req := 32) (al := 1)
    (by decide) (by decide) h32s
  have ha448 := PhaseCreditSpec.rustAlloc_small fineCostModel (req := 448) (al := 8)
    (by decide) (by decide) h448s
  have hc72 := smallAllocCost_le_1997_of_le_108 (req := 72) (by decide)
  have hc32 := smallAllocCost_le_738_of_le_44 (req := 32) (by decide)
  have hc448 := smallAllocCost_le_two_mul_add 448
  have h6 := ((((ha72.concat ha32).concat ha72).concat ha32).concat ha448).concat ha32
  refine h6.congr_mono ?_ (by omega) (by omega) (by omega) (by decide)
  intro evs hE
  rw [hE]
  unfold LibsignalBinary.Proofs.SpqrV1.Top.ChainFrom.DefsBudget.chainNewEvents
  exact ConcatEnv.append
    (ConcatEnv.append
      (ConcatEnv.append
        (ConcatEnv.append (ConcatEnv.append rfl rfl) rfl) rfl) rfl) rfl

theorem chainFrom_fine_phaseCreditSpec (pb : Option ChainPB) (vn : Option VersionNegotiationPB) :
    PhaseCreditSpec fineCostModel (ChainFromEnv pb vn) 16643 0 0 448 := by
  cases pb with
  | some _ =>
    exact (PhaseCreditSpec.freeOnly_of_hyps fineCostModel_modelHyps).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | none =>
    cases vn with
    | none =>
      exact (PhaseCreditSpec.nil fineCostModel).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    | some v =>
      change PhaseCreditSpec fineCostModel (ChainFromVersionNegotiationEnv v) 16643 0 0 448
      unfold ChainFromVersionNegotiationEnv
      split
      · exact chainFromNewEvents_fine_phaseCreditSpec
      · exact (PhaseCreditSpec.nil fineCostModel).mono
          (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)

theorem vecDequeGrow_small_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    {cap : BitVec 64} {capBound : Nat}
    (hcap : cap.toNat ≤ capBound)
    (hSmall : vecDequeGrowMaxReq capBound ≤ HasFineReallocCredit.smallMaxReq M) :
    let reqB := vecDequeGrowMaxReq capBound
    PhaseCreditSpec M (· = vecDequeGrowEvents cap) (2 * reqB + 9539) 0 0 reqB := by
  intro reqB
  have hreq_align : ∀ ev ∈ vecDequeGrowEvents cap,
      eventStepReq ev ≤ reqB ∧ eventStepAlign ev ≤ 16 := by
    intro ev hev
    unfold vecDequeGrowEvents at hev
    by_cases hc : cap = 0#64
    · rw [ite_eq_left hc] at hev
      obtain ⟨hr, ha⟩ := req_align_rustAlloc_local (al := chainEpochAlign) (by decide) ev hev
      have h448 : 4 * chainEpochSize ≤ reqB := by
        unfold reqB vecDequeGrowMaxReq chainEpochSize; omega
      exact ⟨Nat.le_trans hr h448, ha⟩
    · rw [ite_eq_right hc] at hev
      have hal_new : chainEpochAlign ≤ max (2 * cap.toNat) 4 * chainEpochSize := by
        unfold chainEpochAlign chainEpochSize; omega
      obtain ⟨hr, ha⟩ := req_align_rustRealloc_local (al := chainEpochAlign) (by decide) hal_new ev hev
      have hnew : max (2 * cap.toNat) 4 * chainEpochSize ≤ reqB := by
        unfold reqB vecDequeGrowMaxReq chainEpochSize; omega
      exact ⟨Nat.le_trans hr hnew, ha⟩
  refine
    { req_align := fun _ hE ev hev => by rw [hE] at hev; exact hreq_align ev hev
      credit_le := ?_ }
  rintro st0 _ rfl
  unfold vecDequeGrowEvents
  by_cases hc : cap = 0#64
  · rw [ite_eq_left hc]
    have h448 : 4 * chainEpochSize ≤ reqB := by
      unfold reqB vecDequeGrowMaxReq chainEpochSize; omega
    have h448_sm : 4 * chainEpochSize ≤ HasFineReallocCredit.smallMaxReq M :=
      Nat.le_trans h448 hSmall
    obtain ⟨hc1, hl1, hp1⟩ := stepEvents_rustAlloc_small M
      (req := 4 * chainEpochSize) (al := chainEpochAlign) st0 (by decide) (by decide) h448_sm
    have hsa := hM.smallAlloc_le h448_sm
    omega
  · rw [ite_eq_right hc]
    have hpos_cap : 0 < cap.toNat := by
      by_contra h0
      apply hc
      have h0' : cap.toNat = (0#64).toNat := by change cap.toNat = 0; omega
      exact BitVec.eq_of_toNat_eq h0'
    set oldSz := cap.toNat * chainEpochSize
    set newSz := max (2 * cap.toNat) 4 * chainEpochSize
    have hal_new : chainEpochAlign ≤ newSz := by
      unfold newSz chainEpochAlign chainEpochSize; omega
    have hnew_le : newSz ≤ reqB := by
      unfold newSz reqB vecDequeGrowMaxReq chainEpochSize; omega
    have hnew_sm : newSz ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hnew_le hSmall
    have hold_le : oldSz ≤ newSz := by
      unfold oldSz newSz chainEpochSize; omega
    have hold_sm : oldSz ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hold_le hnew_sm
    have hold_pos : 0 < oldSz := by unfold oldSz chainEpochSize; omega
    have hnew_pos : 0 < newSz := by unfold newSz chainEpochSize; omega
    obtain ⟨hc1, hl1, hp1⟩ := stepEvents_rustRealloc_small_small M
      (old := oldSz) (new := newSz) (al := chainEpochAlign) st0
      (by decide) hal_new hold_pos hold_sm hnew_pos hnew_sm
    have hsr := hM.smallRealloc_le hnew_sm
    omega

/-- Small-class `fineCostModel` `PhaseCreditSpec` for `ChainAddEpochEnv` when `vecDequeGrowMaxReq lenBound ≤ 135,167`.
-/
theorem chainAddEpoch_small_fine_phaseCreditSpec
    (hkdf : HkdfFn) (x : ChainAddEpochGhost) {lenBound : Nat}
    (hlen : x.self.links.length ≤ lenBound)
    (hSmall : vecDequeGrowMaxReq lenBound ≤ HasFineReallocCredit.smallMaxReq fineCostModel) :
    let reqB := vecDequeGrowMaxReq lenBound
    PhaseCreditSpec fineCostModel (ChainAddEpochEnv hkdf x) (2 * reqB + 15747) 0 0 reqB := by
  intro reqB
  have h32s : 32 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have h72s : 72 ≤ HasFineReallocCredit.smallMaxReq fineCostModel := by
    rw [fineCostModel_smallMaxReq_eq]; decide
  have ha32 := PhaseCreditSpec.rustAlloc_small fineCostModel (req := 32) (al := 1)
    (by decide) (by decide) h32s
  have ha72 := PhaseCreditSpec.rustAlloc_small fineCostModel (req := 72) (al := 1)
    (by decide) (by decide) h72s
  have hc32 := smallAllocCost_le_738_of_le_44 (req := 32) (by decide)
  have hc72 := smallAllocCost_le_1997_of_le_108 (req := 72) (by decide)
  have hd_nr : PhaseCreditSpec fineCostModel
      (· = if x.G.nextRoot.cap = 0#64 then [] else rustDeallocEvents x.G.nextRoot.cap.toNat 1)
      0 0 0 0 := by
    split
    · exact PhaseCreditSpec.nil fineCostModel
    · exact PhaseCreditSpec.rustDealloc_align16 fineCostModel (by decide)
  have hd_es : PhaseCreditSpec fineCostModel
      (· = if x.esPin.cap = 0#64 then [] else rustDeallocEvents x.esPin.cap.toNat 1)
      0 0 0 0 := by
    split
    · exact PhaseCreditSpec.nil fineCostModel
    · exact PhaseCreditSpec.rustDealloc_align16 fineCostModel (by decide)
  have hgrow_opt : PhaseCreditSpec fineCostModel
      (· = if x.self.links.length = x.G.linksCap.toNat then vecDequeGrowEvents x.G.linksCap else [])
      (2 * reqB + 9539) 0 0 reqB := by
    split
    · next heq =>
      exact vecDequeGrow_small_phaseCreditSpec fineCostModel_modelHyps
        (Nat.le_trans (Nat.le_of_eq heq.symm) hlen) hSmall
    · exact (PhaseCreditSpec.nil fineCostModel).mono (by omega) (by omega) (by omega) (by omega)
  have hreq_ge72 : 72 ≤ reqB := by
    unfold reqB vecDequeGrowMaxReq chainEpochSize; omega
  have hok_seq :=
    (((((((ha32.concat hd_nr).concat ha72).concat ha32).concat ha72).concat ha32).concat hgrow_opt).concat hd_es)
  have hok : PhaseCreditSpec fineCostModel (· = chainAddEpochEvents x)
      (2 * reqB + 15747) 0 0 reqB := by
    refine hok_seq.congr_mono ?_ (by omega) (by omega) (by omega) (by omega)
    intro evs hE
    rw [hE]
    unfold chainAddEpochEvents
    exact ConcatEnv.append
      (ConcatEnv.append
        (ConcatEnv.append
          (ConcatEnv.append
            (ConcatEnv.append
              (ConcatEnv.append
                (ConcatEnv.append rfl rfl) rfl) rfl) rfl) rfl) rfl) rfl
  unfold ChainAddEpochEnv
  split
  · exact (PhaseCreditSpec.nil fineCostModel).mono (by omega) (by omega) (by omega) (by omega)
  · exact hok

theorem chainAddEpoch_fine_phaseCreditSpec_4 (hkdf : HkdfFn) (x : ChainAddEpochGhost)
    (hlen : x.self.links.length ≤ 4) :
    PhaseCreditSpec fineCostModel (ChainAddEpochEnv hkdf x) 17539 0 0 896 :=
  (chainAddEpoch_small_fine_phaseCreditSpec hkdf x hlen
    (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
    (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

/-- Small-class `PhaseCreditSpec` for `<Chain>::into_pb` when `x.chain.links.length * 112 ≤ B ≤ smallMaxReq M`.
-/
theorem chainIntoPb_small_phaseCreditSpec
    {M : AllocCostModel} [HasFineReallocCredit M] (hM : ModelHyps M)
    (x : ChainIntoPbCall) {B : Nat}
    (hlen : x.chain.links.length * 112 ≤ B)
    (hSmall : B ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (ChainIntoPbEnv x) (2 * B + 9539) 0 0 B := by
  by_cases hempty : x.chain.links = []
  · exact ((PhaseCreditSpec.freeOnly_of_hyps hM).of_imp fun evs hE => by
      simp only [ChainIntoPbEnv, hempty, ↓reduceIte] at hE
      exact hE).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  · have hpos_len : 0 < x.chain.links.length := List.length_pos_iff.mpr hempty
    have hpos : 0 < x.chain.links.length * 112 := by omega
    have hle_sm : x.chain.links.length * 112 ≤ HasFineReallocCredit.smallMaxReq M :=
      Nat.le_trans hlen hSmall
    have halloc := PhaseCreditSpec.rustAlloc_small M
      (req := x.chain.links.length * 112) (al := 8) (by decide) hpos hle_sm
    have hsa := hM.smallAlloc_le hle_sm
    have hcat := halloc.concat (PhaseCreditSpec.freeOnly_of_hyps hM)
    have hcat' : PhaseCreditSpec M (ChainIntoPbEnv x)
        (HasFineReallocCredit.smallAllocCost M (x.chain.links.length * 112) + 0)
        (0 + 0) (max 0 (0 + 0)) (max (x.chain.links.length * 112) 0) :=
      hcat.of_imp fun evs hE => by
        simp only [ChainIntoPbEnv, hempty, ↓reduceIte] at hE
        obtain ⟨ef, hf, heq⟩ := hE
        exact ⟨rustAllocEvents (x.chain.links.length * 112) 8, ef, heq, rfl, hf⟩
    exact hcat'.mono (by omega) (by omega) (by omega) (by omega)

theorem chainIntoPb_fine_phaseCreditSpec_4 (x : ChainIntoPbCall)
    (hlen : x.chain.links.length ≤ 4) :
    PhaseCreditSpec fineCostModel (ChainIntoPbEnv x) 10435 0 0 448 :=
  (chainIntoPb_small_phaseCreditSpec fineCostModel_modelHyps x (B := 448)
    (by omega) (by rw [fineCostModel_smallMaxReq_eq]; decide)).mono
    (by decide) (Nat.le_refl 0) (Nat.le_refl 0) (by decide)

/-- `<Chain>::recv_key` preserves `links.length`. -/
theorem chainRecvKey_links_length_eq {hkdf : HkdfFn} {c c' : Chain} {epoch : Epoch}
    {index : BitVec 32} {out : Bytes}
    (h : c.recvKey hkdf epoch index = .ok (c', out)) :
    c'.links.length = c.links.length := by
  unfold Chain.recvKey at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; rfl
  · rcases heidx : CryptoVerification.LibsignalSpqrV1.ChainResult.ofError (c.epochIdx epoch) with
      _ | epochIndex
    · simp [heidx, Bind.bind, Except.bind] at h
    · simp only [heidx, Bind.bind, Except.bind] at h
      cases hlink : c.links[epochIndex]? with
      | none => simp [hlink] at h
      | some link =>
        simp only [hlink] at h
        rcases hkey : link.recv.key hkdf index c.params with _ | ⟨recv', out'⟩
        · simp [hkey] at h
        · simp only [hkey, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, _⟩
          exact List.length_set

/-- `PhaseCreditSpec` for `PqRatchetStateEncodeToVecEnv st` on `fineCostModel` when
`pqRatchetStatePBEncodedLen st ≤ encodeCap`, covering both small (`≤ 135,167`) and large output
slices. -/
theorem pqRatchetStateEncodeToVec_fine_phaseCreditSpec_tight
    (st : PqRatchetState) {encodeCap : Nat}
    (hcap : pqRatchetStatePBEncodedLen st ≤ encodeCap) :
    PhaseCreditSpec fineCostModel (PqRatchetStateEncodeToVecEnv st)
      161532 (encodeCap + 8195) (encodeCap + 8195) encodeCap := by
  set len := pqRatchetStatePBEncodedLen st
  have hnil : PhaseCreditSpec fineCostModel (fun evs => len = 0 ∧ evs = []) 0 0 0 0 :=
    PhaseCreditSpec.of_eq_nil fun _ h => h.2
  have halloc : PhaseCreditSpec fineCostModel
      (fun evs => 0 < len ∧ evs = rustAllocEvents len 1)
      161532 (encodeCap + 8195) (encodeCap + 8195) encodeCap := by
    by_cases hpos : 0 < len
    · by_cases hsm : len ≤ HasFineReallocCredit.smallMaxReq fineCostModel
      · have hs := PhaseCreditSpec.rustAlloc_small fineCostModel (req := len) (al := 1)
          (by decide) hpos hsm
        have hcost := smallAllocCost_le_add_26365 len
        have hsm_num : len ≤ 135167 := by rwa [fineCostModel_smallMaxReq_eq] at hsm
        have hc_le : HasFineReallocCredit.smallAllocCost fineCostModel len ≤ 161532 :=
          Nat.le_trans hcost (Nat.le_trans (Nat.add_le_add_right hsm_num 26365) (by decide))
        exact (hs.of_imp fun _ h => h.2).mono hc_le (Nat.zero_le _) (Nat.zero_le _) hcap
      · have hgt : HasFineReallocCredit.smallMaxReq fineCostModel < len := by omega
        refine
          { req_align := fun _ hE ev hev => by
              rw [hE.2] at hev
              obtain ⟨hr, ha⟩ := req_align_rustAlloc_local (al := 1) (by decide) ev hev
              exact ⟨Nat.le_trans hr hcap, ha⟩
            credit_le := fun st0 {_} hE => by
              rw [hE.2]
              obtain ⟨hc, hl, hp⟩ := stepEvents_rustAlloc_large fineCostModel
                (req := len) (al := 1) st0 (by decide) hgt
              rw [fineCostModel_largeMetaCost_eq] at hc
              rw [fineCostModel_largeCost_eq] at hl hp
              have hlen_aff : len + 8195 ≤ encodeCap + 8195 := Nat.add_le_add_right hcap 8195
              exact ⟨Nat.le_trans hc (Nat.add_le_add_left (by decide : 122 ≤ 161532) _),
                Nat.le_trans hl (Nat.add_le_add_left hlen_aff _),
                Nat.le_trans hp (nat_max_le_max_local (Nat.le_refl _)
                  (Nat.add_le_add_left hlen_aff _))⟩ }
    · exact ((PhaseCreditSpec.empty fineCostModel).of_imp fun _ h => absurd h.1 hpos).mono
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  exact (hnil.or halloc).congr_mono (fun _ h => h)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)
    (Nat.max_le.mpr ⟨Nat.zero_le _, Nat.le_refl _⟩)

end LibsignalBinary.Proofs.PeakBudget.SpqrRecvTightHelpers
