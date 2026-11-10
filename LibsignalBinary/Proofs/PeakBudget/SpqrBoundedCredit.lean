/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas
public import LibsignalBinary.Proofs.PeakBudget.SpqrPolyBounds
public import LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget

/-!
# SPQR V1 Bounded-Event and State Codec `PhaseCreditSpec` Bounds

Establishes `PhaseCreditSpec` bounds for:
1. Generic `SpqrBoundedEvs maxAllocs maxReq` (handling `0`-byte and non-zero requests plus
   `FreeOnlyEvs` drops in binary order) and its small-class specialization (`Δlive = 0, Δpeak = 0`).
2. `<States>::into_pb` (`StatesIntoPbEnv`), `spqr::init_inner` (`InitInnerEnv`),
   `spqr::initial_state` (`InitialStateEnv`), and `PqRatchetState::encode_to_vec`
   (`PqRatchetStateEncodeToVecEnv`).
3. Low-intercept total-request envelope `SpqrBoundedTotalEvs` (`SpqrLowInterceptHyps`) for linear
   `O(bs.length)` `spqr::decode_state` bounds up to `2 MiB`.
4. Tight monotone small-class bucket envelope `SpqrTightEvs` and `StatesIntoPbTightEnv`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit

open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.LibsignalSpqrV1 (PolyDecoder PolyEncoder PqRatchetState V1State)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open CryptoVerification.SpqrV1.Prost.EncodeToVec (pqRatchetStatePBEncodedLen)
open CryptoVerification.SpqrV1.Top.StateSize (rawPqState rawV1State)
open VerifiedLibraries.Mallocng (mallocngAlignedEffSize)
open VerifiedLibraries.Mallocng.Proofs (nominalSlotCap sizeToClassUnits sizeToClass_spec)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine
  (FineScale MmapThresholdReq coarseGrpWtS coarseSlotWt declCost63 fineCostModel
   fineSmallAllocCost fineSmallReallocCost)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq fineCostModel_smallMaxReq_eq smallAllocCost_eq_188_of_le_12
   smallAllocCost_le_738_of_le_44 smallAllocCost_le_1997_of_le_108 smallAllocCost_le_77_mul_add)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SpqrV1.Poly.DecoderPb.IntoPbDefsBudget
  (DecoderIntoPbAllocEnv DecoderIntoPbEnv decoderIntoPbAllocEvents decoderIntoPbSlotEvents)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.DefsBudget
  (EncoderIntoPbAllocEnv EncoderIntoPbEnv encoderIntoPbAllocEvents encoderIntoPbSlotEvents
   encoderIntoPbVecs)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget
  (InitInnerEnv SpqrBoundedEvs StatesIntoPbEnv nonFreeCount nonFreeCount_append
   nonFreeCount_eq_zero_of_freeOnly)
open LibsignalBinary.Proofs.SpqrV1.Top.InitialState.DefsPlacedBudget (InitialStateEnv)
open LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.DefsBudget (PqRatchetStateEncodeToVecEnv)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKitLemmas (fineCostModel_modelHyps)
open LibsignalBinary.Proofs.PeakBudget.SpqrPolyBounds
  (pqRatchetStateEncodeToVec_len_le v1StateEncodeRaw_len_le)

/-! ## 1. Per-Event `eventStepReq` / `eventStepAlign` Bridges for `SpqrBoundedEvs` -/

theorem eventStepReq_le_reqBytes (ev : AllocEvent) :
    eventStepReq ev ≤ ev.reqBytes := by
  cases ev with
  | alloc req => exact Nat.le_refl req
  | aligned al req =>
    dsimp only [eventStepReq, AllocEvent.reqBytes, mallocngAlignedEffSize]
    split <;> omega
  | free _ _ => exact Nat.le_refl 0
  | realloc _ _ new => exact Nat.le_refl new

private theorem req_align_of_spqrBounded_mem {maxReq : Nat} {ev : AllocEvent}
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

/-! ## 2. Generic `SpqrBoundedEvs` `PhaseCreditSpec` -/

private theorem stepEvents_spqrBoundedEvs_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (maxReq : Nat) :
    ∀ (evs : List AllocEvent) (maxAllocs : Nat) (st0 : M.σ),
      SpqrBoundedEvs maxAllocs maxReq evs →
      HasFineReallocCredit.cumSmall (M.stepEvents evs st0) ≤
        HasFineReallocCredit.cumSmall st0 + maxAllocs * (2 * maxReq + 9539) ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st0) ≤
        HasFineReallocCredit.liveLarge st0 + maxAllocs * (maxReq + 8195) ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st0) ≤
        max (HasFineReallocCredit.peakLarge st0)
          (HasFineReallocCredit.liveLarge st0 + maxAllocs * (maxReq + 8195))
  | [], _, st0, _ => by
    simp only [AllocCostModel.stepEvents_nil]
    omega
  | .free al sz :: tl, maxAllocs, st0, ⟨hcnt, hall⟩ => by
    simp only [AllocCostModel.stepEvents_cons]
    have htl : SpqrBoundedEvs maxAllocs maxReq tl :=
      ⟨hcnt, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
    obtain ⟨hc₁, hl₁, hp₁⟩ := hM.freeNonInc al sz st0
    obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrBoundedEvs_le hM maxReq tl maxAllocs
      (M.step (.free al sz) st0) htl
    omega
  | .alloc req :: tl, maxAllocs, st0, ⟨hcnt, hall⟩ => by
    simp only [nonFreeCount] at hcnt
    cases maxAllocs with
    | zero => omega
    | succ k =>
      simp only [AllocCostModel.stepEvents_cons]
      have hc_step : (k + 1) * (2 * maxReq + 9539) = k * (2 * maxReq + 9539) + (2 * maxReq + 9539) :=
        Nat.succ_mul k _
      have hl_step : (k + 1) * (maxReq + 8195) = k * (maxReq + 8195) + (maxReq + 8195) :=
        Nat.succ_mul k _
      obtain ⟨hreq, hal⟩ := req_align_of_spqrBounded_mem (hall (.alloc req) List.mem_cons_self)
      have htl : SpqrBoundedEvs k maxReq tl :=
        ⟨by omega, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_nonFree_aff st0 hreq hal
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrBoundedEvs_le hM maxReq tl k
        (M.step (.alloc req) st0) htl
      omega
  | .aligned al req :: tl, maxAllocs, st0, ⟨hcnt, hall⟩ => by
    simp only [nonFreeCount] at hcnt
    cases maxAllocs with
    | zero => omega
    | succ k =>
      simp only [AllocCostModel.stepEvents_cons]
      have hc_step : (k + 1) * (2 * maxReq + 9539) = k * (2 * maxReq + 9539) + (2 * maxReq + 9539) :=
        Nat.succ_mul k _
      have hl_step : (k + 1) * (maxReq + 8195) = k * (maxReq + 8195) + (maxReq + 8195) :=
        Nat.succ_mul k _
      obtain ⟨hreq, hal⟩ :=
        req_align_of_spqrBounded_mem (hall (.aligned al req) List.mem_cons_self)
      have htl : SpqrBoundedEvs k maxReq tl :=
        ⟨by omega, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_nonFree_aff st0 hreq hal
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrBoundedEvs_le hM maxReq tl k
        (M.step (.aligned al req) st0) htl
      omega
  | .realloc al o n :: tl, maxAllocs, st0, ⟨hcnt, hall⟩ => by
    simp only [nonFreeCount] at hcnt
    cases maxAllocs with
    | zero => omega
    | succ k =>
      simp only [AllocCostModel.stepEvents_cons]
      have hc_step : (k + 1) * (2 * maxReq + 9539) = k * (2 * maxReq + 9539) + (2 * maxReq + 9539) :=
        Nat.succ_mul k _
      have hl_step : (k + 1) * (maxReq + 8195) = k * (maxReq + 8195) + (maxReq + 8195) :=
        Nat.succ_mul k _
      obtain ⟨hreq, hal⟩ :=
        req_align_of_spqrBounded_mem (hall (.realloc al o n) List.mem_cons_self)
      have htl : SpqrBoundedEvs k maxReq tl :=
        ⟨by omega, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_nonFree_aff st0 hreq hal
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrBoundedEvs_le hM maxReq tl k
        (M.step (.realloc al o n) st0) htl
      omega

/-- Generic `PhaseCreditSpec` for `SpqrBoundedEvs maxAllocs maxReq` under `ModelHyps M`. -/
theorem spqrBoundedEvs_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (maxAllocs maxReq : Nat) :
    PhaseCreditSpec M (SpqrBoundedEvs maxAllocs maxReq)
      (maxAllocs * (2 * maxReq + 9539))
      (maxAllocs * (maxReq + 8195))
      (maxAllocs * (maxReq + 8195))
      maxReq where
  req_align _ hE ev hev := req_align_of_spqrBounded_mem (hE.2 ev hev)
  credit_le st0 {evs} hE := stepEvents_spqrBoundedEvs_le hM maxReq evs maxAllocs st0 hE

/-! ## 3. `<States>::into_pb`, `spqr::init_inner`, and `spqr::initial_state` Specs -/

/-- Exact `PhaseCreditSpec` for `StatesIntoPbEnv x` (`Block 334`). -/
theorem statesIntoPb_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {F : ShaCompress} (x : StatesIntoPbGhost F) :
    let R := 2 * (V1State.encodeRaw x.st.into_pb).length + 1024
    PhaseCreditSpec M (StatesIntoPbEnv x)
      (64 * (2 * R + 9539)) (64 * (R + 8195)) (64 * (R + 8195)) R :=
  spqrBoundedEvs_phaseCreditSpec hM 64 (2 * (V1State.encodeRaw x.st.into_pb).length + 1024)

/-- Raw-byte-size weakened `PhaseCreditSpec` for `StatesIntoPbEnv x` (`R = 2 * rawV1State + 1824`). -/
theorem statesIntoPb_raw_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {F : ShaCompress} (x : StatesIntoPbGhost F) :
    let R := 2 * rawV1State x.st.into_pb + 1824
    PhaseCreditSpec M (StatesIntoPbEnv x)
      (64 * (2 * R + 9539)) (64 * (R + 8195)) (64 * (R + 8195)) R := by
  have hlen := v1StateEncodeRaw_len_le x.st.into_pb
  have hR : 2 * (V1State.encodeRaw x.st.into_pb).length + 1024 ≤
      2 * rawV1State x.st.into_pb + 1824 := by omega
  exact (spqrBoundedEvs_phaseCreditSpec hM 64 (2 * rawV1State x.st.into_pb + 1824)).of_imp
    fun _ hevs => SpqrBoundedEvs.mono (Nat.le_refl 64) hR hevs

/-- `PhaseCreditSpec` for `InitInnerEnv F x` (`Block 324`), uniform across `.v0` and `.v1`. -/
theorem initInner_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress) (x : InitInnerGhost) :
    let R := 2 * x.authKey.length + 2048
    PhaseCreditSpec M (InitInnerEnv F x)
      (96 * (2 * R + 9539)) (96 * (R + 8195)) (96 * (R + 8195)) R := by
  dsimp only
  unfold InitInnerEnv
  cases x.v with
  | v0 =>
    exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | v1 =>
    exact spqrBoundedEvs_phaseCreditSpec hM 96 (2 * x.authKey.length + 2048)

/-- `PhaseCreditSpec` for `InitialStateEnv F x` (`Block 327`), uniform across `.v0` and `.v1`. -/
theorem initialState_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress) (x : InitialStateGhost) :
    let R := 4 * x.p.authKey.length + 4096
    PhaseCreditSpec M (InitialStateEnv F x)
      (128 * (2 * R + 9539)) (128 * (R + 8195)) (128 * (R + 8195)) R := by
  dsimp only
  unfold InitialStateEnv
  cases x.p.version with
  | v0 =>
    exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | v1 =>
    exact spqrBoundedEvs_phaseCreditSpec hM 128 (4 * x.p.authKey.length + 4096)

/-! ## 4. `PqRatchetState::encode_to_vec` (`Block 426`) Specs -/

/-- Exact `PhaseCreditSpec` for `PqRatchetStateEncodeToVecEnv st` (`len = pqRatchetStatePBEncodedLen st`). -/
theorem pqRatchetStateEncodeToVec_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (st : PqRatchetState) :
    let len := pqRatchetStatePBEncodedLen st
    PhaseCreditSpec M (PqRatchetStateEncodeToVecEnv st)
      (2 * len + 9539) (len + 8195) (len + 8195) len := by
  dsimp only
  have hnil : PhaseCreditSpec M (fun evs => pqRatchetStatePBEncodedLen st = 0 ∧ evs = [])
      0 0 0 0 :=
    PhaseCreditSpec.of_eq_nil fun _ h => h.2
  have halloc : PhaseCreditSpec M
      (fun evs => 0 < pqRatchetStatePBEncodedLen st ∧
        evs = rustAllocEvents (pqRatchetStatePBEncodedLen st) 1)
      (2 * pqRatchetStatePBEncodedLen st + 9539)
      (pqRatchetStatePBEncodedLen st + 8195)
      (pqRatchetStatePBEncodedLen st + 8195)
      (pqRatchetStatePBEncodedLen st) :=
    (PhaseCreditSpec.rustAlloc_aff hM (req := pqRatchetStatePBEncodedLen st) (al := 1)
      (by decide)).of_imp fun _ h => h.2
  exact (hnil.or halloc).congr_mono (fun _ h => h)
    (by omega) (by omega) (by omega) (by omega)

/-- Raw-byte-size weakened `PhaseCreditSpec` for `PqRatchetStateEncodeToVecEnv st`
(`R = rawPqState st + 752`). -/
theorem pqRatchetStateEncodeToVec_raw_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (st : PqRatchetState) :
    let R := rawPqState st + 752
    PhaseCreditSpec M (PqRatchetStateEncodeToVecEnv st)
      (2 * R + 9539) (R + 8195) (R + 8195) R := by
  have hlen := pqRatchetStateEncodeToVec_len_le st
  exact (pqRatchetStateEncodeToVec_phaseCreditSpec hM st).mono
    (by omega) (by omega) (by omega) hlen

/-! ## 5. Low-Intercept Total-Request Bounded Envelope (`SpqrBoundedTotalEvs`) -/

/-- Additional low-intercept small-allocation hypothesis on `M` (proved on `fineCostModel` via
`ClientBounds.smallAllocCost_le_77_mul_add` and `fineCostModel_smallMaxReq_eq`), avoiding the
`9,539`-byte per-alloc slab-group intercept on linear-count small allocations. -/
structure SpqrLowInterceptHyps (M : AllocCostModel) [HasFineReallocCredit M] : Prop where
  hSmallMaxGe : 8195 ≤ HasFineReallocCredit.smallMaxReq M
  hSmallAlloc77 : ∀ r ≤ HasFineReallocCredit.smallMaxReq M,
    HasFineReallocCredit.smallAllocCost M r ≤ 77 * r + 188

/-- Discharge `SpqrLowInterceptHyps` on `fineCostModel`. -/
theorem fineCostModel_spqrLowInterceptHyps : SpqrLowInterceptHyps fineCostModel where
  hSmallMaxGe := by rw [fineCostModel_smallMaxReq_eq]; decide
  hSmallAlloc77 r _ := smallAllocCost_le_77_mul_add r

/-- Count of `.alloc` / `.aligned` events in `evs`. -/
def freshAllocCount : List AllocEvent → Nat
  | [] => 0
  | .alloc _ :: tl => freshAllocCount tl + 1
  | .aligned _ _ :: tl => freshAllocCount tl + 1
  | _ :: tl => freshAllocCount tl

/-- Count of `.realloc` events in `evs`. -/
def reallocCount : List AllocEvent → Nat
  | [] => 0
  | .realloc _ _ _ :: tl => reallocCount tl + 1
  | _ :: tl => reallocCount tl

/-- Sum of `eventStepReq` across all events in `evs`. -/
def totalStepReq : List AllocEvent → Nat
  | [] => 0
  | ev :: tl => eventStepReq ev + totalStepReq tl

/-- Total-request bounded `AllocEvent` envelope: bounds `.alloc`/`.aligned` count by `maxAllocs`,
`.realloc` count by `maxReallocs`, total `eventStepReq` sum by `totalReq`, and per-event request /
alignment by `(maxReq, 16)`. -/
def SpqrBoundedTotalEvs (maxAllocs maxReallocs totalReq maxReq : Nat)
    (evs : List AllocEvent) : Prop :=
  freshAllocCount evs ≤ maxAllocs ∧
  reallocCount evs ≤ maxReallocs ∧
  totalStepReq evs ≤ totalReq ∧
  ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16

private theorem stepEvents_spqrBoundedTotal_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M) (maxReq : Nat) :
    ∀ (evs : List AllocEvent) (maxAllocs maxReallocs totalReq : Nat) (st0 : M.σ),
      SpqrBoundedTotalEvs maxAllocs maxReallocs totalReq maxReq evs →
      HasFineReallocCredit.cumSmall (M.stepEvents evs st0) ≤
        HasFineReallocCredit.cumSmall st0 +
          (77 * totalReq + 188 * maxAllocs + 9539 * maxReallocs) ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st0) ≤
        HasFineReallocCredit.liveLarge st0 + 2 * totalReq ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st0) ≤
        max (HasFineReallocCredit.peakLarge st0)
          (HasFineReallocCredit.liveLarge st0 + 2 * totalReq)
  | [], _, _, _, st0, _ => by
    simp only [AllocCostModel.stepEvents_nil]
    omega
  | .free al sz :: tl, maxAllocs, maxReallocs, totalReq, st0, ⟨ha, hr, ht, hall⟩ => by
    simp only [AllocCostModel.stepEvents_cons]
    simp only [freshAllocCount, reallocCount, totalStepReq, eventStepReq, Nat.zero_add] at ha hr ht
    have htl : SpqrBoundedTotalEvs maxAllocs maxReallocs totalReq maxReq tl :=
      ⟨ha, hr, ht, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
    obtain ⟨hc₁, hl₁, hp₁⟩ := hM.freeNonInc al sz st0
    obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrBoundedTotal_le hM hLow maxReq tl
      maxAllocs maxReallocs totalReq (M.step (.free al sz) st0) htl
    omega
  | .alloc req :: tl, maxAllocs, maxReallocs, totalReq, st0, ⟨ha, hr, ht, hall⟩ => by
    simp only [freshAllocCount, reallocCount, totalStepReq, eventStepReq] at ha hr ht
    cases maxAllocs with
    | zero => omega
    | succ k =>
      simp only [AllocCostModel.stepEvents_cons]
      have hstep :
          let st1 := M.step (.alloc req) st0
          HasFineReallocCredit.cumSmall st1 ≤
            HasFineReallocCredit.cumSmall st0 + (77 * req + 188) ∧
          HasFineReallocCredit.liveLarge st1 ≤
            HasFineReallocCredit.liveLarge st0 + 2 * req ∧
          HasFineReallocCredit.peakLarge st1 ≤
            max (HasFineReallocCredit.peakLarge st0)
              (HasFineReallocCredit.liveLarge st0 + 2 * req) := by
        by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
        · obtain ⟨hc, hl, hp⟩ := hM.step_alloc_small_any st0 hle
          have hsa := hLow.hSmallAlloc77 req hle
          omega
        · have hgt : HasFineReallocCredit.smallMaxReq M < req := by omega
          obtain ⟨hc, hl, hp⟩ := HasFineReallocCredit.step_alloc_large st0 hgt
          have hm := hM.meta_le
          have hla := hM.largeCost_le hgt
          have hge := hLow.hSmallMaxGe
          omega
      have htl : SpqrBoundedTotalEvs k maxReallocs (totalReq - req) maxReq tl :=
        ⟨by omega, hr, by omega, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
      obtain ⟨hc₁, hl₁, hp₁⟩ := hstep
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrBoundedTotal_le hM hLow maxReq tl
        k maxReallocs (totalReq - req) (M.step (.alloc req) st0) htl
      have hreq_le : req ≤ totalReq := by omega
      have hmul77 : 77 * req + 77 * (totalReq - req) = 77 * totalReq := by
        rw [← Nat.mul_add, Nat.add_sub_of_le hreq_le]
      have hmul2 : 2 * req + 2 * (totalReq - req) = 2 * totalReq := by
        rw [← Nat.mul_add, Nat.add_sub_of_le hreq_le]
      have hmul188 : 188 * (k + 1) = 188 + 188 * k := by omega
      omega
  | .aligned al req :: tl, maxAllocs, maxReallocs, totalReq, st0, ⟨ha, hr, ht, hall⟩ => by
    simp only [freshAllocCount, reallocCount, totalStepReq, eventStepReq] at ha hr ht
    cases maxAllocs with
    | zero => omega
    | succ k =>
      simp only [AllocCostModel.stepEvents_cons]
      have hal : al ≤ 16 := (hall (.aligned al req) List.mem_cons_self).2
      have hstep :
          let st1 := M.step (.aligned al req) st0
          HasFineReallocCredit.cumSmall st1 ≤
            HasFineReallocCredit.cumSmall st0 + (77 * req + 188) ∧
          HasFineReallocCredit.liveLarge st1 ≤
            HasFineReallocCredit.liveLarge st0 + 2 * req ∧
          HasFineReallocCredit.peakLarge st1 ≤
            max (HasFineReallocCredit.peakLarge st0)
              (HasFineReallocCredit.liveLarge st0 + 2 * req) := by
        by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
        · obtain ⟨hc, hl, hp⟩ := hM.step_aligned_small_any st0 hal hle
          have hsa := hLow.hSmallAlloc77 req hle
          omega
        · have hgt : HasFineReallocCredit.smallMaxReq M < req := by omega
          obtain ⟨hc, hl, hp⟩ := HasFineReallocCredit.step_aligned_large st0 hal hgt
          have hm := hM.meta_le
          have hla := hM.largeCost_le hgt
          have hge := hLow.hSmallMaxGe
          omega
      have htl : SpqrBoundedTotalEvs k maxReallocs (totalReq - req) maxReq tl :=
        ⟨by omega, hr, by omega, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
      obtain ⟨hc₁, hl₁, hp₁⟩ := hstep
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrBoundedTotal_le hM hLow maxReq tl
        k maxReallocs (totalReq - req) (M.step (.aligned al req) st0) htl
      have hreq_le : req ≤ totalReq := by omega
      have hmul77 : 77 * req + 77 * (totalReq - req) = 77 * totalReq := by
        rw [← Nat.mul_add, Nat.add_sub_of_le hreq_le]
      have hmul2 : 2 * req + 2 * (totalReq - req) = 2 * totalReq := by
        rw [← Nat.mul_add, Nat.add_sub_of_le hreq_le]
      have hmul188 : 188 * (k + 1) = 188 + 188 * k := by omega
      omega
  | .realloc al o n :: tl, maxAllocs, maxReallocs, totalReq, st0, ⟨ha, hr, ht, hall⟩ => by
    simp only [freshAllocCount, reallocCount, totalStepReq, eventStepReq] at ha hr ht
    cases maxReallocs with
    | zero => omega
    | succ k =>
      simp only [AllocCostModel.stepEvents_cons]
      have hal : al ≤ 16 := (hall (.realloc al o n) List.mem_cons_self).2
      have hstep :
          let st1 := M.step (.realloc al o n) st0
          HasFineReallocCredit.cumSmall st1 ≤
            HasFineReallocCredit.cumSmall st0 + (77 * n + 9539) ∧
          HasFineReallocCredit.liveLarge st1 ≤
            HasFineReallocCredit.liveLarge st0 + 2 * n ∧
          HasFineReallocCredit.peakLarge st1 ≤
            max (HasFineReallocCredit.peakLarge st0)
              (HasFineReallocCredit.liveLarge st0 + 2 * n) := by
        by_cases hold_le : o ≤ HasFineReallocCredit.smallMaxReq M
        · by_cases hnew_le : n ≤ HasFineReallocCredit.smallMaxReq M
          · obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_small_any st0 hal hold_le hnew_le
            have hsr := hM.smallRealloc_le hnew_le
            omega
          · have hnew_gt : HasFineReallocCredit.smallMaxReq M < n := by omega
            obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_large_any st0 hal hold_le hnew_gt
            have hm := hM.meta_le
            have hla := hM.largeCost_le hnew_gt
            have hge := hLow.hSmallMaxGe
            omega
        · have hold_gt : HasFineReallocCredit.smallMaxReq M < o := by omega
          by_cases hnew_le : n ≤ HasFineReallocCredit.smallMaxReq M
          · obtain ⟨hc, hl, hp⟩ := hM.step_realloc_large_small_any st0 hal hold_gt hnew_le
            have hsr := hM.smallRealloc_le hnew_le
            omega
          · have hnew_gt : HasFineReallocCredit.smallMaxReq M < n := by omega
            obtain ⟨hc, hl, hp⟩ := HasFineReallocCredit.step_realloc_large_large st0 hal
              hold_gt hnew_gt
            have hm := hM.meta_le
            have hla := hM.largeCost_le hnew_gt
            have hge := hLow.hSmallMaxGe
            omega
      have htl : SpqrBoundedTotalEvs maxAllocs k (totalReq - n) maxReq tl :=
        ⟨ha, by omega, by omega, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
      obtain ⟨hc₁, hl₁, hp₁⟩ := hstep
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrBoundedTotal_le hM hLow maxReq tl
        maxAllocs k (totalReq - n) (M.step (.realloc al o n) st0) htl
      have hn_le : n ≤ totalReq := by omega
      have hmul77 : 77 * n + 77 * (totalReq - n) = 77 * totalReq := by
        rw [← Nat.mul_add, Nat.add_sub_of_le hn_le]
      have hmul2 : 2 * n + 2 * (totalReq - n) = 2 * totalReq := by
        rw [← Nat.mul_add, Nat.add_sub_of_le hn_le]
      have hmul9539 : 9539 * (k + 1) = 9539 + 9539 * k := by omega
      omega

/-- Linear `PhaseCreditSpec` for `SpqrBoundedTotalEvs maxAllocs maxReallocs totalReq maxReq`
under `ModelHyps M` and `SpqrLowInterceptHyps M`. -/
theorem spqrBoundedTotalEvs_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hLow : SpqrLowInterceptHyps M)
    (maxAllocs maxReallocs totalReq maxReq : Nat) :
    PhaseCreditSpec M (SpqrBoundedTotalEvs maxAllocs maxReallocs totalReq maxReq)
      (77 * totalReq + 188 * maxAllocs + 9539 * maxReallocs)
      (2 * totalReq)
      (2 * totalReq)
      maxReq where
  req_align _ hE := hE.2.2.2
  credit_le st0 {evs} hE :=
    stepEvents_spqrBoundedTotal_le hM hLow maxReq evs maxAllocs maxReallocs totalReq st0 hE

/-! ## 6. Small-Class `SpqrBoundedEvs` & `<States>::into_pb` (`Δlive = 0`, `Δpeak = 0`) -/

private theorem stepEvents_spqrBoundedEvs_small_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {maxReq : Nat} (hSmall : maxReq ≤ HasFineReallocCredit.smallMaxReq M) :
    ∀ (evs : List AllocEvent) (maxAllocs : Nat) (st0 : M.σ),
      SpqrBoundedEvs maxAllocs maxReq evs →
      HasFineReallocCredit.cumSmall (M.stepEvents evs st0) ≤
        HasFineReallocCredit.cumSmall st0 + maxAllocs * (2 * maxReq + 9539) ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st0) ≤
        HasFineReallocCredit.liveLarge st0 ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st0) ≤
        HasFineReallocCredit.peakLarge st0
  | [], _, st0, _ => by
    simp only [AllocCostModel.stepEvents_nil]
    omega
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
    | succ k =>
      simp only [AllocCostModel.stepEvents_cons]
      have hc_step : (k + 1) * (2 * maxReq + 9539) = k * (2 * maxReq + 9539) + (2 * maxReq + 9539) :=
        Nat.succ_mul k _
      obtain ⟨hreq, _⟩ := req_align_of_spqrBounded_mem (hall (.alloc req) List.mem_cons_self)
      simp only [eventStepReq] at hreq
      have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hSmall
      have htl : SpqrBoundedEvs k maxReq tl :=
        ⟨by omega, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_alloc_small_any st0 hle
      have hsa := hM.smallAlloc_le hle
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrBoundedEvs_small_le hM hSmall tl k
        (M.step (.alloc req) st0) htl
      omega
  | .aligned al req :: tl, maxAllocs, st0, ⟨hcnt, hall⟩ => by
    simp only [nonFreeCount] at hcnt
    cases maxAllocs with
    | zero => omega
    | succ k =>
      simp only [AllocCostModel.stepEvents_cons]
      have hc_step : (k + 1) * (2 * maxReq + 9539) = k * (2 * maxReq + 9539) + (2 * maxReq + 9539) :=
        Nat.succ_mul k _
      obtain ⟨hreq, hal⟩ :=
        req_align_of_spqrBounded_mem (hall (.aligned al req) List.mem_cons_self)
      simp only [eventStepReq, eventStepAlign] at hreq hal
      have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hSmall
      have htl : SpqrBoundedEvs k maxReq tl :=
        ⟨by omega, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
      obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_aligned_small_any st0 hal hle
      have hsa := hM.smallAlloc_le hle
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrBoundedEvs_small_le hM hSmall tl k
        (M.step (.aligned al req) st0) htl
      omega
  | .realloc al o n :: tl, maxAllocs, st0, ⟨hcnt, hall⟩ => by
    simp only [nonFreeCount] at hcnt
    cases maxAllocs with
    | zero => omega
    | succ k =>
      simp only [AllocCostModel.stepEvents_cons]
      have hc_step : (k + 1) * (2 * maxReq + 9539) = k * (2 * maxReq + 9539) + (2 * maxReq + 9539) :=
        Nat.succ_mul k _
      obtain ⟨hreq, hal⟩ :=
        req_align_of_spqrBounded_mem (hall (.realloc al o n) List.mem_cons_self)
      simp only [eventStepReq, eventStepAlign] at hreq hal
      have hnew_le : n ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hreq hSmall
      have hstep :
          let st1 := M.step (.realloc al o n) st0
          HasFineReallocCredit.cumSmall st1 ≤
            HasFineReallocCredit.cumSmall st0 + (2 * maxReq + 9539) ∧
          HasFineReallocCredit.liveLarge st1 ≤ HasFineReallocCredit.liveLarge st0 ∧
          HasFineReallocCredit.peakLarge st1 ≤ HasFineReallocCredit.peakLarge st0 := by
        by_cases hold_le : o ≤ HasFineReallocCredit.smallMaxReq M
        · obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_small_any st0 hal hold_le hnew_le
          have hsr := hM.smallRealloc_le hnew_le
          omega
        · have hold_gt : HasFineReallocCredit.smallMaxReq M < o := by omega
          obtain ⟨hc, hl, hp⟩ := hM.step_realloc_large_small_any st0 hal hold_gt hnew_le
          have hsr := hM.smallRealloc_le hnew_le
          omega
      have htl : SpqrBoundedEvs k maxReq tl :=
        ⟨by omega, fun e he => hall e (List.mem_cons_of_mem _ he)⟩
      obtain ⟨hc₁, hl₁, hp₁⟩ := hstep
      obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrBoundedEvs_small_le hM hSmall tl k
        (M.step (.realloc al o n) st0) htl
      omega

/-- Small-class `PhaseCreditSpec` for `SpqrBoundedEvs maxAllocs maxReq` (`maxReq ≤ smallMaxReq M`):
zero `sc = 63` `liveLarge` and `peakLarge` growth (`Δlive = 0`, `Δpeak = 0`). -/
theorem spqrBoundedEvs_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (maxAllocs : Nat) {maxReq : Nat}
    (hSmall : maxReq ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (SpqrBoundedEvs maxAllocs maxReq)
      (maxAllocs * (2 * maxReq + 9539)) 0 0 maxReq where
  req_align _ hE ev hev := req_align_of_spqrBounded_mem (hE.2 ev hev)
  credit_le st0 {evs} hE := by
    obtain ⟨hc, hl, hp⟩ := stepEvents_spqrBoundedEvs_small_le hM hSmall evs maxAllocs st0 hE
    omega

/-- Small-class `PhaseCreditSpec` on the existing `StatesIntoPbEnv x` (`Δlive = 0`, `Δpeak = 0`)
whenever `2 * (V1State.encodeRaw x.st.into_pb).length + 1024 ≤ smallMaxReq M`. -/
theorem statesIntoPb_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {F : ShaCompress} (x : StatesIntoPbGhost F)
    (hSmall : 2 * (V1State.encodeRaw x.st.into_pb).length + 1024 ≤
      HasFineReallocCredit.smallMaxReq M) :
    let R := 2 * (V1State.encodeRaw x.st.into_pb).length + 1024
    PhaseCreditSpec M (StatesIntoPbEnv x) (64 * (2 * R + 9539)) 0 0 R :=
  spqrBoundedEvs_small_phaseCreditSpec hM 64 hSmall

/-- Raw-byte-size small-class `PhaseCreditSpec` on `StatesIntoPbEnv x` (`Δlive = 0`, `Δpeak = 0`)
whenever `rawV1State x.st.into_pb ≤ v1Cap` and `2 * v1Cap + 1824 ≤ smallMaxReq M`. -/
theorem statesIntoPb_raw_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {F : ShaCompress} (x : StatesIntoPbGhost F) {v1Cap : Nat}
    (hCap : rawV1State x.st.into_pb ≤ v1Cap)
    (hSmall : 2 * v1Cap + 1824 ≤ HasFineReallocCredit.smallMaxReq M) :
    let R := 2 * v1Cap + 1824
    PhaseCreditSpec M (StatesIntoPbEnv x) (64 * (2 * R + 9539)) 0 0 R := by
  have hlen := v1StateEncodeRaw_len_le x.st.into_pb
  have hR : 2 * (V1State.encodeRaw x.st.into_pb).length + 1024 ≤ 2 * v1Cap + 1824 := by omega
  exact (spqrBoundedEvs_small_phaseCreditSpec hM 64 hSmall).of_imp
    fun _ hevs => SpqrBoundedEvs.mono (Nat.le_refl 64) hR hevs

/-- Small-class `PhaseCreditSpec` on `InitInnerEnv F x` (`Δlive = 0`, `Δpeak = 0`) when
`2 * x.authKey.length + 2048 ≤ smallMaxReq M`. -/
theorem initInner_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress) (x : InitInnerGhost)
    (hSmall : 2 * x.authKey.length + 2048 ≤ HasFineReallocCredit.smallMaxReq M) :
    let R := 2 * x.authKey.length + 2048
    PhaseCreditSpec M (InitInnerEnv F x) (96 * (2 * R + 9539)) 0 0 R := by
  dsimp only
  unfold InitInnerEnv
  cases x.v with
  | v0 =>
    exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | v1 =>
    exact spqrBoundedEvs_small_phaseCreditSpec hM 96 hSmall

/-- Small-class `PhaseCreditSpec` on `InitialStateEnv F x` (`Δlive = 0`, `Δpeak = 0`) when
`4 * x.p.authKey.length + 4096 ≤ smallMaxReq M`. -/
theorem initialState_small_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (F : ShaCompress) (x : InitialStateGhost)
    (hSmall : 4 * x.p.authKey.length + 4096 ≤ HasFineReallocCredit.smallMaxReq M) :
    let R := 4 * x.p.authKey.length + 4096
    PhaseCreditSpec M (InitialStateEnv F x) (128 * (2 * R + 9539)) 0 0 R := by
  dsimp only
  unfold InitialStateEnv
  cases x.p.version with
  | v0 =>
    exact (PhaseCreditSpec.nil M).mono
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  | v1 =>
    exact spqrBoundedEvs_small_phaseCreditSpec hM 128 hSmall

/-! ## 7. Tight Monotone Small-Class Bucket Envelope (`SpqrTightEvs`) -/

/-- Monotone piecewise upper envelope on `fineSmallAllocCost req` across `req ≤ 79,236`
(accounting for the `sc = 8..9` nested/root bump `9,789` B on `125..156` B, e.g. mid-epoch
64-point `128`-byte `PolyEncoder` / `PolyDecoder` slices). -/
def spqrAllocTightCost (req : Nat) : Nat :=
  if req ≤ 12 then 188
  else if req ≤ 44 then 738
  else if req ≤ 108 then 1997
  else if req ≤ 2560 then 9789
  else 90234

theorem spqrAllocTightCost_mono {r₁ r₂ : Nat} (h : r₁ ≤ r₂) :
    spqrAllocTightCost r₁ ≤ spqrAllocTightCost r₂ := by
  unfold spqrAllocTightCost
  split_ifs <;> omega

/-- Per-event tight `cumSmall` weight (`0` on `.free`, `spqrAllocTightCost` on `.alloc`/`.aligned`,
`9,789` on `.realloc` up to `384` B). -/
def spqrEventTightCost : AllocEvent → Nat
  | .free _ _ => 0
  | .alloc req => spqrAllocTightCost req
  | .aligned _ req => spqrAllocTightCost req
  | .realloc _ _ _ => 9789

/-- Additive tight `cumSmall` trace weight across `evs`. -/
def spqrTraceTightCost : List AllocEvent → Nat
  | [] => 0
  | ev :: tl => spqrEventTightCost ev + spqrTraceTightCost tl

theorem spqrTraceTightCost_nil : spqrTraceTightCost [] = 0 := rfl

theorem spqrTraceTightCost_append : ∀ evs₁ evs₂ : List AllocEvent,
    spqrTraceTightCost (evs₁ ++ evs₂) = spqrTraceTightCost evs₁ + spqrTraceTightCost evs₂
  | [], _ => by simp [spqrTraceTightCost]
  | ev :: tl, evs₂ => by
    simp only [List.cons_append, spqrTraceTightCost, spqrTraceTightCost_append tl evs₂]
    omega

theorem spqrTraceTightCost_eq_zero_of_freeOnly {evs : List AllocEvent} (h : FreeOnlyEvs evs) :
    spqrTraceTightCost evs = 0 := by
  induction evs with
  | nil => rfl
  | cons ev tl ih =>
    obtain ⟨al, sz, rfl⟩ := h ev List.mem_cons_self
    simp only [spqrTraceTightCost, spqrEventTightCost, Nat.zero_add]
    exact ih fun e he => h e (List.mem_cons_of_mem _ he)

private def tightMinReq (sc : Nat) : Nat :=
  if sc = 0 then 0 else nominalSlotCap (sc - 1) + 1

private def tightClassAllocWt (sc : Nat) : Nat :=
  coarseSlotWt sc + (122 * coarseGrpWtS sc + FineScale - 1) / FineScale

private def tightClassRealloc384Wt (sc : Nat) : Nat :=
  max (coarseSlotWt sc) (min 384 (nominalSlotCap sc) + 8195) +
    (122 * max (coarseGrpWtS sc) FineScale + FineScale - 1) / FineScale

private def checkFineTightBuckets : Bool :=
  (List.range 48).all fun sc =>
    let rMin := tightMinReq sc
    let aWt := tightClassAllocWt sc
    let rWt384 := tightClassRealloc384Wt sc
    decide (
      (rMin ≤ 2560 → aWt ≤ 9789) ∧
      (rMin ≤ 79236 → aWt ≤ 90234) ∧
      (rMin ≤ 384 → rWt384 ≤ 9789))

private theorem checkFineTightBuckets_true : checkFineTightBuckets = true := by
  decide +kernel

/-- Tight `fineCostModel` allocation bound `≤ 9,789` B across all `req ≤ 2,560` B. -/
theorem smallAllocCost_le_9789_of_le_2560 {req : Nat} (hreq : req ≤ 2560) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 9789 := by
  change fineSmallAllocCost req ≤ 9789
  have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  have hspec := sizeToClass_spec (req := req) (by unfold MmapThresholdReq at hle; exact hle)
  dsimp only at hspec
  have hrmin : tightMinReq (sizeToClassUnits ((req + 3) / 16)) ≤ 2560 := by
    unfold tightMinReq
    rcases hspec.2.2 with h0 | hprev
    · simp [h0]
    · split <;> omega
  unfold fineSmallAllocCost
  simp only [hle, ↓reduceIte]
  have hcell := List.all_eq_true.mp checkFineTightBuckets_true _ (List.mem_range.mpr hspec.1)
  exact (of_decide_eq_true hcell).1 hrmin

/-- Tight `fineCostModel` allocation bound `≤ 90,234` B across all `req ≤ 79,236` B
(`36 * 2,201` B `KeyHistory.prev` cap under `ValidChainParamsPB`). -/
theorem smallAllocCost_le_90234_of_le_79236 {req : Nat} (hreq : req ≤ 79236) :
    HasFineReallocCredit.smallAllocCost fineCostModel req ≤ 90234 := by
  change fineSmallAllocCost req ≤ 90234
  have hle : req ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  have hspec := sizeToClass_spec (req := req) (by unfold MmapThresholdReq at hle; exact hle)
  dsimp only at hspec
  have hrmin : tightMinReq (sizeToClassUnits ((req + 3) / 16)) ≤ 79236 := by
    unfold tightMinReq
    rcases hspec.2.2 with h0 | hprev
    · simp [h0]
    · split <;> omega
  unfold fineSmallAllocCost
  simp only [hle, ↓reduceIte]
  have hcell := List.all_eq_true.mp checkFineTightBuckets_true _ (List.mem_range.mpr hspec.1)
  exact (of_decide_eq_true hcell).2.1 hrmin

/-- Tight `fineCostModel` reallocation bound `≤ 9,789` B across all `newSz ≤ 384` B
(`Vec<Vec<u8>>` doubling `96 → 192 → 384` B). -/
theorem smallReallocCost_le_9789_of_le_384 {newSz : Nat} (hnew : newSz ≤ 384) :
    HasFineReallocCredit.smallReallocCost fineCostModel newSz ≤ 9789 := by
  change fineSmallReallocCost newSz ≤ 9789
  have hle : newSz ≤ MmapThresholdReq := by unfold MmapThresholdReq; omega
  have hspec := sizeToClass_spec (req := newSz) (by unfold MmapThresholdReq at hle; exact hle)
  dsimp only at hspec
  have hrmin : tightMinReq (sizeToClassUnits ((newSz + 3) / 16)) ≤ 384 := by
    unfold tightMinReq
    rcases hspec.2.2 with h0 | hprev
    · simp [h0]
    · split <;> omega
  have hcell := List.all_eq_true.mp checkFineTightBuckets_true _ (List.mem_range.mpr hspec.1)
  have hb := (of_decide_eq_true hcell).2.2 hrmin
  have hcap : newSz ≤ nominalSlotCap (sizeToClassUnits ((newSz + 3) / 16)) := hspec.2.1
  unfold fineSmallReallocCost tightClassRealloc384Wt declCost63 at *
  simp only [hle, ↓reduceIte]
  omega

/-- Abstract cost-model hypotheses discharging `SpqrTightEvs` bounds (proved on `fineCostModel`
via `fineCostModel_spqrTightHyps`). -/
structure SpqrTightHyps (M : AllocCostModel) [HasFineReallocCredit M] : Prop where
  hSmallMaxGe : 79236 ≤ HasFineReallocCredit.smallMaxReq M
  hAllocCost : ∀ r ≤ 79236, HasFineReallocCredit.smallAllocCost M r ≤ spqrAllocTightCost r
  hRealloc384 : ∀ n ≤ 384, HasFineReallocCredit.smallReallocCost M n ≤ 9789

/-- Concrete discharge of `SpqrTightHyps` on `fineCostModel`. -/
theorem fineCostModel_spqrTightHyps : SpqrTightHyps fineCostModel where
  hSmallMaxGe := by rw [fineCostModel_smallMaxReq_eq]; decide
  hAllocCost r hr := by
    unfold spqrAllocTightCost
    by_cases h12 : r ≤ 12
    · simp only [h12, ↓reduceIte]
      exact Nat.le_of_eq (smallAllocCost_eq_188_of_le_12 h12)
    · simp only [h12, ↓reduceIte]
      by_cases h44 : r ≤ 44
      · simp only [h44, ↓reduceIte]
        exact smallAllocCost_le_738_of_le_44 h44
      · simp only [h44, ↓reduceIte]
        by_cases h108 : r ≤ 108
        · simp only [h108, ↓reduceIte]
          exact smallAllocCost_le_1997_of_le_108 h108
        · simp only [h108, ↓reduceIte]
          by_cases h2560 : r ≤ 2560
          · simp only [h2560, ↓reduceIte]
            exact smallAllocCost_le_9789_of_le_2560 h2560
          · simp only [h2560, ↓reduceIte]
            exact smallAllocCost_le_90234_of_le_79236 hr
  hRealloc384 _ hn := smallReallocCost_le_9789_of_le_384 hn

/-- Tight small-class event envelope: bounds non-free op count by `maxOps`, tight `cumSmall` trace
weight by `cumCap`, `.realloc` target sizes by `384` B, and per-event `(eventStepReq, eventStepAlign)`
by `(maxReq, 16)`. -/
def SpqrTightEvs (maxOps cumCap maxReq : Nat) (evs : List AllocEvent) : Prop :=
  nonFreeCount evs ≤ maxOps ∧
  spqrTraceTightCost evs ≤ cumCap ∧
  (∀ al o n, AllocEvent.realloc al o n ∈ evs → n ≤ 384) ∧
  ∀ ev ∈ evs, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16

theorem SpqrTightEvs.nil (maxOps cumCap maxReq : Nat) :
    SpqrTightEvs maxOps cumCap maxReq [] := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, ?_, ?_⟩
  · intro _ _ _ h
    cases h
  · intro _ h
    cases h

theorem SpqrTightEvs.nonFreeCount_le {maxOps cumCap maxReq : Nat} {evs : List AllocEvent}
    (h : SpqrTightEvs maxOps cumCap maxReq evs) :
    nonFreeCount evs ≤ maxOps :=
  h.1

theorem SpqrTightEvs.mono {n₁ n₂ c₁ c₂ r₁ r₂ : Nat} {evs : List AllocEvent}
    (hn : n₁ ≤ n₂) (hc : c₁ ≤ c₂) (hr : r₁ ≤ r₂)
    (h : SpqrTightEvs n₁ c₁ r₁ evs) :
    SpqrTightEvs n₂ c₂ r₂ evs :=
  ⟨Nat.le_trans h.1 hn,
   Nat.le_trans h.2.1 hc,
   h.2.2.1,
   fun ev hev => ⟨Nat.le_trans (h.2.2.2 ev hev).1 hr, (h.2.2.2 ev hev).2⟩⟩

theorem SpqrTightEvs.of_freeOnly {evs : List AllocEvent} (hf : FreeOnlyEvs evs) :
    SpqrTightEvs 0 0 0 evs := by
  refine ⟨Nat.le_of_eq (nonFreeCount_eq_zero_of_freeOnly hf),
    Nat.le_of_eq (spqrTraceTightCost_eq_zero_of_freeOnly hf),
    fun al o n hmem => ?_, fun ev hev => ?_⟩
  · obtain ⟨_, _, h⟩ := hf _ hmem
    cases h
  · obtain ⟨al, sz, rfl⟩ := hf ev hev
    exact ⟨Nat.le_refl 0, Nat.le_refl 16⟩

theorem SpqrTightEvs.append {n₁ n₂ c₁ c₂ r₁ r₂ : Nat} {evs₁ evs₂ : List AllocEvent}
    (h₁ : SpqrTightEvs n₁ c₁ r₁ evs₁) (h₂ : SpqrTightEvs n₂ c₂ r₂ evs₂) :
    SpqrTightEvs (n₁ + n₂) (c₁ + c₂) (max r₁ r₂) (evs₁ ++ evs₂) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nonFreeCount_append]
    exact Nat.add_le_add h₁.1 h₂.1
  · rw [spqrTraceTightCost_append]
    exact Nat.add_le_add h₁.2.1 h₂.2.1
  · intro al o n hmem
    rcases List.mem_append.mp hmem with hm₁ | hm₂
    · exact h₁.2.2.1 al o n hm₁
    · exact h₂.2.2.1 al o n hm₂
  · intro ev hev
    rcases List.mem_append.mp hev with hm₁ | hm₂
    · exact ⟨Nat.le_trans (h₁.2.2.2 ev hm₁).1 (Nat.le_max_left r₁ r₂), (h₁.2.2.2 ev hm₁).2⟩
    · exact ⟨Nat.le_trans (h₂.2.2.2 ev hm₂).1 (Nat.le_max_right r₁ r₂), (h₂.2.2.2 ev hm₂).2⟩

theorem SpqrTightEvs.seq {n₁ n₂ c₁ c₂ r₁ r₂ : Nat} {evs : List AllocEvent}
    (h : SeqEnv (SpqrTightEvs n₁ c₁ r₁) (SpqrTightEvs n₂ c₂ r₂) evs) :
    SpqrTightEvs (n₁ + n₂) (c₁ + c₂) (max r₁ r₂) evs := by
  rcases h with h₁ | ⟨evs₁, evs₂, rfl, h₁, h₂⟩
  · exact h₁.mono (Nat.le_add_right n₁ n₂) (Nat.le_add_right c₁ c₂) (Nat.le_max_left r₁ r₂)
  · exact h₁.append h₂

theorem SpqrTightEvs.rustAlloc {req R al : Nat} (hR : req ≤ R) (hal : al ≤ 16) :
    SpqrTightEvs 1 (spqrAllocTightCost R) R (rustAllocEvents req al) := by
  have hcost := spqrAllocTightCost_mono hR
  unfold rustAllocEvents
  split
  · refine ⟨by simp [nonFreeCount],
      by simp only [spqrTraceTightCost, spqrEventTightCost, Nat.add_zero]; exact hcost,
      fun _ _ _ h => by simp at h,
      fun ev hev => ?_⟩
    rw [List.mem_singleton] at hev
    subst hev
    exact ⟨hR, Nat.le_refl 16⟩
  · refine ⟨by simp [nonFreeCount],
      by simp only [spqrTraceTightCost, spqrEventTightCost, Nat.add_zero]; exact hcost,
      fun _ _ _ h => by simp at h,
      fun ev hev => ?_⟩
    rw [List.mem_singleton] at hev
    subst hev
    exact ⟨hR, by simp only [eventStepAlign]; omega⟩

theorem SpqrTightEvs.rustDealloc (req al : Nat) :
    SpqrTightEvs 0 0 0 (rustDeallocEvents req al) := by
  refine SpqrTightEvs.of_freeOnly fun ev hev => ?_
  unfold rustDeallocEvents at hev
  rw [List.mem_singleton] at hev
  exact ⟨al, req, hev⟩

theorem SpqrTightEvs.rustRealloc384 {oldSz newSz al : Nat}
    (hal : al ≤ 16) (hal_new : al ≤ newSz) (hnew : newSz ≤ 384) :
    SpqrTightEvs 1 9789 newSz (rustReallocEvents oldSz newSz al) := by
  unfold rustReallocEvents
  simp only [hal, hal_new, and_self, ↓reduceIte]
  refine ⟨by simp [nonFreeCount],
    by simp [spqrTraceTightCost, spqrEventTightCost],
    fun _ _ n h => by simp at h; omega,
    fun ev hev => ?_⟩
  rw [List.mem_singleton] at hev
  subst hev
  exact ⟨Nat.le_refl newSz, hal⟩

theorem SpqrTightEvs.flatMap_const {α : Type} {f : α → List AllocEvent} {xs : List α}
    {k c r : Nat} (h : ∀ x ∈ xs, SpqrTightEvs k c r (f x)) :
    SpqrTightEvs (xs.length * k) (xs.length * c) r (xs.flatMap f) := by
  induction xs with
  | nil =>
    simpa using SpqrTightEvs.nil 0 0 r
  | cons x tl ih =>
    simp only [List.flatMap_cons, List.length_cons]
    have hx := h x List.mem_cons_self
    have htl := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    exact (hx.append htl).mono (by rw [Nat.succ_mul]; omega) (by rw [Nat.succ_mul]; omega) (by omega)

private theorem stepEvents_spqrTightEvs_le {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : SpqrTightHyps M) {maxReq : Nat} (hMax : maxReq ≤ 79236) :
    ∀ (evs : List AllocEvent) (maxOps cumCap : Nat) (st0 : M.σ),
      SpqrTightEvs maxOps cumCap maxReq evs →
      HasFineReallocCredit.cumSmall (M.stepEvents evs st0) ≤
        HasFineReallocCredit.cumSmall st0 + cumCap ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st0) ≤
        HasFineReallocCredit.liveLarge st0 ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st0) ≤
        HasFineReallocCredit.peakLarge st0
  | [], _, _, st0, _ => by
    simp only [AllocCostModel.stepEvents_nil]
    omega
  | .free al sz :: tl, maxOps, cumCap, st0, ⟨hcnt, hcost, hre, hall⟩ => by
    simp only [AllocCostModel.stepEvents_cons]
    simp only [nonFreeCount, spqrTraceTightCost, spqrEventTightCost, Nat.zero_add] at hcnt hcost
    have htl : SpqrTightEvs maxOps cumCap maxReq tl :=
      ⟨hcnt, hcost, fun a o n hm => hre a o n (List.mem_cons_of_mem _ hm),
       fun e he => hall e (List.mem_cons_of_mem _ he)⟩
    obtain ⟨hc₁, hl₁, hp₁⟩ := hM.freeNonInc al sz st0
    obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrTightEvs_le hM hT hMax tl maxOps cumCap
      (M.step (.free al sz) st0) htl
    omega
  | .alloc req :: tl, maxOps, cumCap, st0, ⟨hcnt, hcost, hre, hall⟩ => by
    simp only [AllocCostModel.stepEvents_cons]
    simp only [nonFreeCount, spqrTraceTightCost, spqrEventTightCost] at hcnt hcost
    have hreq : req ≤ maxReq := (hall (.alloc req) List.mem_cons_self).1
    have hr79 : req ≤ 79236 := Nat.le_trans hreq hMax
    have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hr79 hT.hSmallMaxGe
    obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_alloc_small_any st0 hle
    have hsa := hT.hAllocCost req hr79
    have htl : SpqrTightEvs (maxOps - 1) (cumCap - spqrAllocTightCost req) maxReq tl :=
      ⟨by omega, by omega, fun a o n hm => hre a o n (List.mem_cons_of_mem _ hm),
       fun e he => hall e (List.mem_cons_of_mem _ he)⟩
    obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrTightEvs_le hM hT hMax tl
      (maxOps - 1) (cumCap - spqrAllocTightCost req) (M.step (.alloc req) st0) htl
    omega
  | .aligned al req :: tl, maxOps, cumCap, st0, ⟨hcnt, hcost, hre, hall⟩ => by
    simp only [AllocCostModel.stepEvents_cons]
    simp only [nonFreeCount, spqrTraceTightCost, spqrEventTightCost] at hcnt hcost
    obtain ⟨hreq, hal⟩ := hall (.aligned al req) List.mem_cons_self
    simp only [eventStepReq, eventStepAlign] at hreq hal
    have hr79 : req ≤ 79236 := Nat.le_trans hreq hMax
    have hle : req ≤ HasFineReallocCredit.smallMaxReq M := Nat.le_trans hr79 hT.hSmallMaxGe
    obtain ⟨hc₁, hl₁, hp₁⟩ := hM.step_aligned_small_any st0 hal hle
    have hsa := hT.hAllocCost req hr79
    have htl : SpqrTightEvs (maxOps - 1) (cumCap - spqrAllocTightCost req) maxReq tl :=
      ⟨by omega, by omega, fun a o n hm => hre a o n (List.mem_cons_of_mem _ hm),
       fun e he => hall e (List.mem_cons_of_mem _ he)⟩
    obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrTightEvs_le hM hT hMax tl
      (maxOps - 1) (cumCap - spqrAllocTightCost req) (M.step (.aligned al req) st0) htl
    omega
  | .realloc al o n :: tl, maxOps, cumCap, st0, ⟨hcnt, hcost, hre, hall⟩ => by
    simp only [AllocCostModel.stepEvents_cons]
    simp only [nonFreeCount, spqrTraceTightCost, spqrEventTightCost] at hcnt hcost
    obtain ⟨_, hal⟩ := hall (.realloc al o n) List.mem_cons_self
    simp only [eventStepAlign] at hal
    have hn384 : n ≤ 384 := hre al o n List.mem_cons_self
    have hn_le : n ≤ HasFineReallocCredit.smallMaxReq M :=
      Nat.le_trans (Nat.le_trans hn384 (by decide : 384 ≤ 79236)) hT.hSmallMaxGe
    have hstep :
        let st1 := M.step (.realloc al o n) st0
        HasFineReallocCredit.cumSmall st1 ≤ HasFineReallocCredit.cumSmall st0 + 9789 ∧
        HasFineReallocCredit.liveLarge st1 ≤ HasFineReallocCredit.liveLarge st0 ∧
        HasFineReallocCredit.peakLarge st1 ≤ HasFineReallocCredit.peakLarge st0 := by
      have hsr := hT.hRealloc384 n hn384
      by_cases hold_le : o ≤ HasFineReallocCredit.smallMaxReq M
      · obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_small_any st0 hal hold_le hn_le
        omega
      · have hold_gt : HasFineReallocCredit.smallMaxReq M < o := by omega
        obtain ⟨hc, hl, hp⟩ := hM.step_realloc_large_small_any st0 hal hold_gt hn_le
        omega
    have htl : SpqrTightEvs (maxOps - 1) (cumCap - 9789) maxReq tl :=
      ⟨by omega, by omega, fun a o' n' hm => hre a o' n' (List.mem_cons_of_mem _ hm),
       fun e he => hall e (List.mem_cons_of_mem _ he)⟩
    obtain ⟨hc₁, hl₁, hp₁⟩ := hstep
    obtain ⟨hc₂, hl₂, hp₂⟩ := stepEvents_spqrTightEvs_le hM hT hMax tl
      (maxOps - 1) (cumCap - 9789) (M.step (.realloc al o n) st0) htl
    omega

/-- Generic `PhaseCreditSpec` for `SpqrTightEvs maxOps cumCap maxReq` (`maxReq ≤ 79,236`):
`Δcum = cumCap`, **`Δlive = 0`, `Δpeak = 0`**, `maxReq = maxReq`. -/
theorem spqrTightEvs_phaseCreditSpec {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : SpqrTightHyps M) (maxOps cumCap : Nat) {maxReq : Nat}
    (hMax : maxReq ≤ 79236) :
    PhaseCreditSpec M (SpqrTightEvs maxOps cumCap maxReq) cumCap 0 0 maxReq where
  req_align _ hE := hE.2.2.2
  credit_le st0 {evs} hE := by
    obtain ⟨hc, hl, hp⟩ := stepEvents_spqrTightEvs_le hM hT hMax evs maxOps cumCap st0 hE
    omega

/-- Concrete `fineCostModel` specialization of `spqrTightEvs_phaseCreditSpec`. -/
theorem spqrTightEvs_fine_phaseCreditSpec (maxOps cumCap : Nat) {maxReq : Nat}
    (hMax : maxReq ≤ 79236) :
    PhaseCreditSpec fineCostModel (SpqrTightEvs maxOps cumCap maxReq) cumCap 0 0 maxReq :=
  spqrTightEvs_phaseCreditSpec fineCostModel_modelHyps fineCostModel_spqrTightHyps
    maxOps cumCap hMax

/-- Tight `<States>::into_pb` (`Block 334`) allocation envelope under `StatesPtsBoundedAt 640` +
`StatesDecPtsNeededBound`: `≤ 42` small allocs (`≤ 128`), `cumSmall ≤ 376,193` B, `Δlive = 0`,
`Δpeak = 0`, `maxReq = 2,400` B (zero existential binders). -/
def StatesIntoPbTightEnv (evs : List AllocEvent) : Prop :=
  SpqrTightEvs 42 376193 2400 evs

def statesIntoPbTightDeltaCum : Nat := 376193
def statesIntoPbTightDeltaLive : Nat := 0
def statesIntoPbTightDeltaPeak : Nat := 0
def statesIntoPbTightMaxReq : Nat := 2400

theorem statesIntoPbTightEnv_nonFreeCount_le {evs : List AllocEvent}
    (h : StatesIntoPbTightEnv evs) :
    nonFreeCount evs ≤ 42 :=
  h.1

theorem statesIntoPb_phaseCreditSpec_tight {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (hT : SpqrTightHyps M) :
    PhaseCreditSpec M StatesIntoPbTightEnv
      statesIntoPbTightDeltaCum statesIntoPbTightDeltaLive
      statesIntoPbTightDeltaPeak statesIntoPbTightMaxReq :=
  spqrTightEvs_phaseCreditSpec hM hT 42 376193 (by decide)

theorem statesIntoPb_fine_phaseCreditSpec_tight :
    PhaseCreditSpec fineCostModel StatesIntoPbTightEnv
      statesIntoPbTightDeltaCum statesIntoPbTightDeltaLive
      statesIntoPbTightDeltaPeak statesIntoPbTightMaxReq :=
  statesIntoPb_phaseCreditSpec_tight fineCostModel_modelHyps fineCostModel_spqrTightHyps

/-- Tight leaf bridge for `<PolyEncoder>::into_pb` (`EncoderIntoPbAllocEnv enc`) when `enc` has
`≤ 16` slots each of length `≤ 640` (`≤ 1,280` B). -/
theorem encoderIntoPbAllocEnv_tight {enc : PolyEncoder} {evs : List AllocEvent}
    (hLen : (encoderIntoPbVecs enc).length ≤ 16)
    (hPts : ∀ cs ∈ encoderIntoPbVecs enc, cs.length ≤ 640)
    (hEnv : EncoderIntoPbAllocEnv enc evs) :
    SpqrTightEvs 18 176202 1280 evs := by
  rw [hEnv]
  unfold encoderIntoPbAllocEvents
  have h384 : SpqrTightEvs 1 9789 384 (rustAllocEvents 384 8) :=
    SpqrTightEvs.rustAlloc (Nat.le_refl 384) (by decide)
  have houter := h384.append h384
  have hslots : SpqrTightEvs ((encoderIntoPbVecs enc).length * 1)
      ((encoderIntoPbVecs enc).length * 9789) 1280
      ((encoderIntoPbVecs enc).flatMap encoderIntoPbSlotEvents) := by
    refine SpqrTightEvs.flatMap_const fun cs hcs => ?_
    unfold encoderIntoPbSlotEvents
    split
    · exact SpqrTightEvs.nil 1 9789 1280
    · have h2 : 2 * cs.length ≤ 1280 := by have := hPts cs hcs; omega
      exact SpqrTightEvs.rustAlloc h2 (by decide)
  exact (houter.append hslots).mono (by omega) (by omega) (by decide)

/-- Tight postcondition bridge for `<PolyEncoder>::into_pb` (`EncoderIntoPbEnv enc`). -/
theorem encoderIntoPbEnv_tight {enc : PolyEncoder} {evs : List AllocEvent}
    (hLen : (encoderIntoPbVecs enc).length ≤ 16)
    (hPts : ∀ cs ∈ encoderIntoPbVecs enc, cs.length ≤ 640)
    (hEnv : EncoderIntoPbEnv enc evs) :
    SpqrTightEvs 18 176202 1280 evs := by
  obtain ⟨evs_a, evs_f, rfl, ha, hf⟩ := hEnv
  exact ((encoderIntoPbAllocEnv_tight hLen hPts ha).append (SpqrTightEvs.of_freeOnly hf)).mono
    (by omega) (by omega) (by decide)

/-- Tight leaf bridge for `<PolyDecoder>::into_pb` (`DecoderIntoPbAllocEnv dec`) when `dec` has
`≤ 16` slots each of length `≤ 576` (`≤ 2,304` B). -/
theorem decoderIntoPbAllocEnv_tight {dec : PolyDecoder} {evs : List AllocEvent}
    (hLen : dec.pts.length ≤ 16)
    (hPts : ∀ s ∈ dec.pts, s.vec.length ≤ 576)
    (hEnv : DecoderIntoPbAllocEnv dec evs) :
    SpqrTightEvs 17 166413 2304 evs := by
  rw [hEnv]
  unfold decoderIntoPbAllocEvents
  have h384 : SpqrTightEvs 1 9789 384 (rustAllocEvents 384 8) :=
    SpqrTightEvs.rustAlloc (Nat.le_refl 384) (by decide)
  have hslots : SpqrTightEvs (dec.pts.length * 1) (dec.pts.length * 9789) 2304
      (dec.pts.flatMap fun s => decoderIntoPbSlotEvents s.vec) := by
    refine SpqrTightEvs.flatMap_const fun s hs => ?_
    unfold decoderIntoPbSlotEvents
    split
    · exact SpqrTightEvs.nil 1 9789 2304
    · have h4 : 4 * s.vec.length ≤ 2304 := by have := hPts s hs; omega
      exact SpqrTightEvs.rustAlloc h4 (by decide)
  exact (h384.append hslots).mono (by omega) (by omega) (by decide)

/-- Tight postcondition bridge for `<PolyDecoder>::into_pb` (`DecoderIntoPbEnv dec`). -/
theorem decoderIntoPbEnv_tight {dec : PolyDecoder} {evs : List AllocEvent}
    (hLen : dec.pts.length ≤ 16)
    (hPts : ∀ s ∈ dec.pts, s.vec.length ≤ 576)
    (hEnv : DecoderIntoPbEnv dec evs) :
    SpqrTightEvs 17 166413 2304 evs := by
  obtain ⟨evs_a, evs_f, rfl, ha, hf⟩ := hEnv
  exact ((decoderIntoPbAllocEnv_tight hLen hPts ha).append (SpqrTightEvs.of_freeOnly hf)).mono
    (by omega) (by omega) (by decide)

end LibsignalBinary.Proofs.PeakBudget.SpqrBoundedCredit
