/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LeafDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10Budget
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.W4InnerHelpers
public import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget

/-!
# Inner `PrevDec` (`SessionStructure::decode`) Peak Live-Heap Helpers

Parametric `(M : AllocCostModel) [HasFineReallocCredit M]` (`ModelHyps M`) sequential
`PhaseCreditSpec` bounds in exact binary call order for inlined `SessionStructure::decode` (`PrevDec`):
1. Affine and small-regime bounds for `rustReallocEvents` across all size-class transitions.
2. `finishGrowEvents`, `FinishGrow1Env`, and `GrowOne104Env` bounds.
3. `doReserveClearEvents`, `BytesMergeEnv`, and `BytesMergeProtoEnv` bounds cancelling temporary
   `Bytes` buffers from `Δlive` via `PhaseCreditSpec.tempAllocBodyFree_aff`.
4. Prost leaf bounds (`DropDecodeError`, `DecodeVarintSlice`, `Int32Merge`, `SkipField`) and
   field-list `IterSeqEnv` composition (`phaseCredit_prevDecFields`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W4PrevDecPeak

open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (BytesMergeProtoGhost)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH (FinishGrow1Call)
open CryptoVerification.LibsignalProtoCodec (WireType decodeVarint mergeBytes mergeUint32 skipField)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost Int32MergeGhost SkipFieldGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.MergeDefsBudget
  (BytesMergeProtoEnv)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10Budget
  (FinishGrow1Env finishGrow1Events)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv DeallocCreditSpec IterSeqEnv ModelHyps PhaseCreditSpec iterPeak)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (HasFineReallocCredit)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget
  (GrowOne104Env growOne104Events)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (finishGrowEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv DropDecodeErrorEnv Int32MergeEnv SkipFieldEnv
   decodeVarintSliceEvents int32MergeEvents skipFieldEventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bytesMergeEventsCore doReserveClearEvents)

/-! ## Universal `rustReallocEvents` Affine & Small-Regime Bounds -/

/-- Uniform affine `PhaseCreditSpec` for `rustReallocEvents old_sz new_sz al` (`al ≤ 16`)
across all 4 small/large size-class transitions and both `al ≤ new_sz` / `new_sz < al` branches. -/
theorem phaseCredit_rustRealloc_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (old_sz new_sz al : Nat) (hal16 : al ≤ 16) :
    PhaseCreditSpec M (· = rustReallocEvents old_sz new_sz al)
      (2 * new_sz + 9539) (new_sz + 8195) (new_sz + 8195) new_sz where
  req_align := by
    rintro _ rfl ev hev
    unfold rustReallocEvents at hev
    split at hev
    · simp only [List.mem_singleton] at hev
      subst hev
      exact ⟨Nat.le_refl new_sz, hal16⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
      rcases hev with rfl | rfl
      · exact ⟨Nat.le_refl new_sz, by simp only [eventStepAlign]; omega⟩
      · exact ⟨Nat.zero_le new_sz, by simp only [eventStepAlign]; omega⟩
  credit_le := by
    rintro st0 _ rfl
    unfold rustReallocEvents
    split
    · simp only [AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
      exact hM.step_nonFree_aff st0 (Nat.le_refl new_sz) hal16
    · simp only [AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
      have hal8 : eventStepAlign (.aligned (max al 8) new_sz) ≤ 16 := by
        simp only [eventStepAlign]; omega
      obtain ⟨hc1, hl1, hp1⟩ :=
        hM.step_nonFree_aff st0 (ev := .aligned (max al 8) new_sz) (maxReq := new_sz)
          (Nat.le_refl new_sz) hal8
      obtain ⟨hc2, hl2, hp2⟩ :=
        hM.freeNonInc al old_sz (M.step (.aligned (max al 8) new_sz) st0)
      omega

/-- Small-regime `PhaseCreditSpec` for `rustReallocEvents old_sz new_sz al` (`al ≤ 16`,
`old_sz ≤ smallMaxReq M`, `new_sz ≤ smallMaxReq M`), adding `0` to `liveLarge` and `peakLarge`. -/
theorem phaseCredit_rustRealloc_small_any {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (old_sz new_sz al : Nat) (hal16 : al ≤ 16)
    (hold_sm : old_sz ≤ HasFineReallocCredit.smallMaxReq M)
    (hnew_sm : new_sz ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = rustReallocEvents old_sz new_sz al)
      (2 * new_sz + 9539) 0 0 new_sz where
  req_align := by
    rintro _ rfl ev hev
    unfold rustReallocEvents at hev
    split at hev
    · simp only [List.mem_singleton] at hev
      subst hev
      exact ⟨Nat.le_refl new_sz, hal16⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
      rcases hev with rfl | rfl
      · exact ⟨Nat.le_refl new_sz, by simp only [eventStepAlign]; omega⟩
      · exact ⟨Nat.zero_le new_sz, by simp only [eventStepAlign]; omega⟩
  credit_le := by
    rintro st0 _ rfl
    unfold rustReallocEvents
    split
    · simp only [AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
      obtain ⟨hc, hl, hp⟩ := hM.step_realloc_small_small_any st0 hal16 hold_sm hnew_sm
      have hsr := hM.smallRealloc_le hnew_sm
      omega
    · simp only [AllocCostModel.stepEvents_cons, AllocCostModel.stepEvents_nil]
      have hal8 : max al 8 ≤ 16 := by omega
      obtain ⟨hc1, hl1, hp1⟩ := hM.step_aligned_small_any st0 hal8 hnew_sm
      obtain ⟨hc2, hl2, hp2⟩ :=
        hM.freeNonInc al old_sz (M.step (.aligned (max al 8) new_sz) st0)
      have hsa := hM.smallAlloc_le hnew_sm
      omega

/-! ## `finishGrowEvents`, `FinishGrow1Env`, & `GrowOne104Env` Bounds -/

/-- Regime-uniform `PhaseCreditSpec` for `finishGrowEvents cap new align stride` (`align ≤ 16`). -/
theorem phaseCredit_finishGrow_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (cap new align stride : Nat) (hal16 : align ≤ 16) :
    PhaseCreditSpec M (· = finishGrowEvents cap new align stride)
      (2 * (new * stride) + 9539)
      (new * stride + 8195)
      (new * stride + 8195)
      (new * stride) := by
  unfold finishGrowEvents
  by_cases hcap : cap = 0
  · simp only [hcap, ↓reduceIte]
    exact PhaseCreditSpec.rustAlloc_aff hM hal16
  · simp only [hcap, ↓reduceIte]
    exact phaseCredit_rustRealloc_aff hM (cap * stride) (new * stride) align hal16

/-- Small-regime `PhaseCreditSpec` for `finishGrowEvents cap new align stride` (`align ≤ 16`,
`cap * stride ≤ smallMaxReq M`, `new * stride ≤ smallMaxReq M`) with `Δlive = 0, Δpeak = 0`. -/
theorem phaseCredit_finishGrow_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (cap new align stride : Nat) (hal16 : align ≤ 16)
    (hold_sm : cap * stride ≤ HasFineReallocCredit.smallMaxReq M)
    (hnew_sm : new * stride ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (· = finishGrowEvents cap new align stride)
      (2 * (new * stride) + 9539) 0 0 (new * stride) := by
  unfold finishGrowEvents
  by_cases hcap : cap = 0
  · simp only [hcap, ↓reduceIte]
    exact (PhaseCreditSpec.rustAlloc_small_any hM hal16 hnew_sm).mono
      (hM.smallAlloc_le hnew_sm) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl _)
  · simp only [hcap, ↓reduceIte]
    exact phaseCredit_rustRealloc_small_any hM (cap * stride) (new * stride) align
      hal16 hold_sm hnew_sm

/-- `PhaseCreditSpec` for `FinishGrow1Env x` (`align = 1, stride = 1`). -/
theorem phaseCredit_finishGrow1 {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (x : FinishGrow1Call) :
    PhaseCreditSpec M (FinishGrow1Env x)
      (2 * x.new.toNat + 9539)
      (x.new.toNat + 8195)
      (x.new.toNat + 8195)
      x.new.toNat := by
  have h := phaseCredit_finishGrow_aff hM x.cap.toNat x.new.toNat 1 1 (by decide)
  have himp : ∀ evs, FinishGrow1Env x evs → evs = finishGrowEvents x.cap.toNat x.new.toNat 1 1 := by
    intro evs hevs
    simpa only [FinishGrow1Env, finishGrow1Events] using hevs
  exact (h.of_imp himp).mono (by omega) (by omega) (by omega) (by omega)

/-- Regime-uniform `PhaseCreditSpec` for `GrowOne104Env cap` (`cap.toNat < 5`, so
`newCap = max (2 * cap.toNat) 4 ≤ 8`, `newCap * 104 ≤ 832`). -/
theorem phaseCredit_growOne104_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (cap : BitVec 64) (hcap : cap.toNat < 5) :
    PhaseCreditSpec M (GrowOne104Env cap) 11203 9027 9027 832 := by
  let newCap := max (2 * cap.toNat) 4
  have hnew_bytes : newCap * 104 ≤ 832 := by omega
  have h := phaseCredit_finishGrow_aff hM cap.toNat newCap 8 104 (by decide)
  have himp : ∀ evs, GrowOne104Env cap evs → evs = finishGrowEvents cap.toNat newCap 8 104 := by
    intro evs hevs
    simpa only [GrowOne104Env, growOne104Events, newCap] using hevs
  exact (h.of_imp himp).mono (by omega) (by omega) (by omega) hnew_bytes

/-- Small-regime `PhaseCreditSpec` for `GrowOne104Env cap` (`cap.toNat < 5`,
`832 ≤ smallMaxReq M`): `Δcum = 11203, Δlive = 0, Δpeak = 0, maxReq = 832`. -/
theorem phaseCredit_growOne104_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (cap : BitVec 64) (hcap : cap.toNat < 5)
    (hSmall832 : 832 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (GrowOne104Env cap) 11203 0 0 832 := by
  let newCap := max (2 * cap.toNat) 4
  have hold_bytes : cap.toNat * 104 ≤ 832 := by omega
  have hnew_bytes : newCap * 104 ≤ 832 := by omega
  have h := phaseCredit_finishGrow_small hM cap.toNat newCap 8 104 (by decide)
    (Nat.le_trans hold_bytes hSmall832) (Nat.le_trans hnew_bytes hSmall832)
  have himp : ∀ evs, GrowOne104Env cap evs → evs = finishGrowEvents cap.toNat newCap 8 104 := by
    intro evs hevs
    simpa only [GrowOne104Env, growOne104Events, newCap] using hevs
  exact (h.of_imp himp).mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) hnew_bytes

/-! ## `doReserveClearEvents` & `BytesMergeEnv` / `BytesMergeProtoEnv` -/

/-- Regime-uniform `PhaseCreditSpec` for `doReserveClearEvents cap vLen` (`newCap =
reserveCap cap 0 vLen = max (max vLen (2 * cap)) 8`). -/
theorem phaseCredit_doReserveClear_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (cap vLen : Nat) :
    let newCap := reserveCap cap 0 vLen
    PhaseCreditSpec M (· = doReserveClearEvents cap vLen)
      (if vLen ≤ cap then 0 else 2 * newCap + 9539)
      (if vLen ≤ cap then 0 else newCap + 8195)
      (if vLen ≤ cap then 0 else newCap + 8195)
      (if vLen ≤ cap then 0 else newCap) := by
  dsimp only
  unfold doReserveClearEvents
  by_cases hle : vLen ≤ cap
  · simp only [hle, ↓reduceIte]
    exact PhaseCreditSpec.nil M
  · simp only [hle, ↓reduceIte]
    by_cases hc0 : cap = 0
    · simp only [hc0, ↓reduceIte]
      exact PhaseCreditSpec.rustAlloc_aff hM (by decide : 1 ≤ 16)
    · simp only [hc0, ↓reduceIte]
      exact phaseCredit_rustRealloc_aff hM cap (reserveCap cap 0 vLen) 1 (by decide)

/-- Small-regime `PhaseCreditSpec` for `doReserveClearEvents cap vLen` when both `cap` and
`reserveCap cap 0 vLen` are `≤ smallMaxReq M` (`Δlive = 0, Δpeak = 0`). -/
theorem phaseCredit_doReserveClear_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (cap vLen : Nat)
    (hold_sm : cap ≤ HasFineReallocCredit.smallMaxReq M)
    (hnew_sm : reserveCap cap 0 vLen ≤ HasFineReallocCredit.smallMaxReq M) :
    let newCap := reserveCap cap 0 vLen
    PhaseCreditSpec M (· = doReserveClearEvents cap vLen)
      (2 * newCap + 9539) 0 0 newCap := by
  dsimp only
  unfold doReserveClearEvents
  by_cases hle : vLen ≤ cap
  · simp only [hle, ↓reduceIte]
    exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0)
      (Nat.zero_le _)
  · simp only [hle, ↓reduceIte]
    by_cases hc0 : cap = 0
    · subst hc0
      simp only [↓reduceIte]
      exact (PhaseCreditSpec.rustAlloc_small_any hM (by decide : 1 ≤ 16) hnew_sm).mono
        (hM.smallAlloc_le hnew_sm) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl _)
    · simp only [hc0, ↓reduceIte]
      exact phaseCredit_rustRealloc_small_any hM cap (reserveCap cap 0 vLen) 1 (by decide)
        hold_sm hnew_sm

/-- Exact-order `PhaseCreditSpec` for `bytesMergeEventsCore wt valCap bs` given `v.length ≤ vCap`
whenever `mergeBytes wt bs = some (v, rest)` and `valCap.toNat ≤ capBound`:
* On `Err`: `rustAllocEvents 72 8`;
* On `Ok` (`0 < v.length`): `alloc(v.length, 1) ++ doReserveClearEvents ++ free(v.length, 1)`
  cancels `tmp` (`v.length`) from `Δlive` via `PhaseCreditSpec.tempAllocBodyFree_aff`. -/
theorem phaseCredit_bytesMergeCore_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (wt : WireType) (valCap : BitVec 64) (bs : List (BitVec 8))
    {capBound vCap : Nat}
    (hcap : valCap.toNat ≤ capBound)
    (hv_le : ∀ v rest, mergeBytes wt bs = some (v, rest) → v.length ≤ vCap) :
    let newCapBound := max (max vCap (2 * capBound)) 8
    PhaseCreditSpec M (· = bytesMergeEventsCore wt valCap bs)
      (max 9683 (2 * vCap + 2 * newCapBound + 19078))
      (max 8267 (newCapBound + 8195))
      (max 8267 ((vCap + 8195) + (newCapBound + 8195)))
      (max 72 (max vCap newCapBound)) := by
  intro newCapBound
  unfold bytesMergeEventsCore
  cases hm : mergeBytes wt bs with
  | none =>
    have h72 := PhaseCreditSpec.rustAlloc_aff hM (req := 72) (al := 8) (by decide)
    exact h72.mono (by omega) (by omega) (by omega) (by omega)
  | some vr =>
    rcases vr with ⟨v, rest⟩
    by_cases hv0 : v.length = 0
    · simp only [hv0, ↓reduceIte]
      exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
        (Nat.zero_le _)
    · simp only [hv0, ↓reduceIte]
      have hvCap : v.length ≤ vCap := hv_le v rest hm
      have hres_le : reserveCap valCap.toNat 0 v.length ≤ newCapBound := by
        dsimp only [reserveCap, newCapBound]
        omega
      have hdr := phaseCredit_doReserveClear_aff hM valCap.toNat v.length
      have hcancel := PhaseCreditSpec.tempAllocBodyFree_aff hM
        (req := v.length) (al := 1) (by decide) hdr
      have himp : ∀ evs,
          evs = rustAllocEvents v.length 1 ++
            doReserveClearEvents valCap.toNat v.length ++
            rustDeallocEvents v.length 1 →
          ConcatEnv
            (ConcatEnv (· = rustAllocEvents v.length 1)
              (· = doReserveClearEvents valCap.toNat v.length))
            (· = rustDeallocEvents v.length 1) evs := by
        rintro _ rfl
        exact ⟨_, _, rfl, ⟨_, _, rfl, rfl, rfl⟩, rfl⟩
      refine (hcancel.of_imp himp).mono ?_ ?_ ?_ ?_
      · by_cases hle : v.length ≤ valCap.toNat <;> simp only [hle, ↓reduceIte] <;> omega
      · by_cases hle : v.length ≤ valCap.toNat <;> simp only [hle, ↓reduceIte] <;> omega
      · by_cases hle : v.length ≤ valCap.toNat <;> simp only [hle, ↓reduceIte] <;> omega
      · by_cases hle : v.length ≤ valCap.toNat <;> simp only [hle, ↓reduceIte] <;> omega

/-- Fresh-destination (`valCap = 0#64`) specialization of `phaseCredit_bytesMergeCore_aff`
(used for single-occurrence `SessionStructure` `Bytes` fields `lik`, `rik`, `root`, `abk`, `pq`
where `valCap = 0#64` and `v.length ≤ vCap`, so `newCap ≤ max vCap 8 ≤ vCap + 8`). -/
theorem phaseCredit_bytesMergeCore_fresh {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (wt : WireType) (bs : List (BitVec 8)) {vCap : Nat}
    (hv_le : ∀ v rest, mergeBytes wt bs = some (v, rest) → v.length ≤ vCap) :
    PhaseCreditSpec M (· = bytesMergeEventsCore wt 0#64 bs)
      (4 * vCap + 19094)
      (vCap + 8267)
      (2 * vCap + 16398)
      (max 72 (vCap + 8)) := by
  have h := phaseCredit_bytesMergeCore_aff hM wt 0#64 bs (capBound := 0) (vCap := vCap)
    (by simp) hv_le
  dsimp only at h
  exact h.mono (by omega) (by omega) (by omega) (by omega)

/-- Small-regime specialization of `bytesMergeEventsCore` (e.g., `Chain` 32/33-byte key fields
and 16/32-byte `MessageKey` fields where `vCap ≤ 33`, `capBound ≤ 33`, and `72 ≤ smallMaxReq M`),
yielding `Δlive = 0` and `Δpeak = 0`. -/
theorem phaseCredit_bytesMergeCore_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (wt : WireType) (valCap : BitVec 64) (bs : List (BitVec 8))
    {capBound vCap : Nat}
    (hcap : valCap.toNat ≤ capBound)
    (hv_le : ∀ v rest, mergeBytes wt bs = some (v, rest) → v.length ≤ vCap)
    (hSmall72 : 72 ≤ HasFineReallocCredit.smallMaxReq M)
    (hSmallNew : max (max vCap (2 * capBound)) 8 ≤ HasFineReallocCredit.smallMaxReq M) :
    let newCapBound := max (max vCap (2 * capBound)) 8
    PhaseCreditSpec M (· = bytesMergeEventsCore wt valCap bs)
      (max 9683 (2 * vCap + 2 * newCapBound + 19078)) 0 0
      (max 72 (max vCap newCapBound)) := by
  intro newCapBound
  unfold bytesMergeEventsCore
  cases hm : mergeBytes wt bs with
  | none =>
    have h72 := (PhaseCreditSpec.rustAlloc_small_any hM (req := 72) (al := 8)
      (by decide) hSmall72).mono
      (hM.smallAlloc_le hSmall72) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 72)
    exact h72.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (by omega)
  | some vr =>
    rcases vr with ⟨v, rest⟩
    by_cases hv0 : v.length = 0
    · simp only [hv0, ↓reduceIte]
      exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0)
        (Nat.zero_le _)
    · simp only [hv0, ↓reduceIte]
      have hvCap : v.length ≤ vCap := hv_le v rest hm
      have hv_sm : v.length ≤ HasFineReallocCredit.smallMaxReq M :=
        Nat.le_trans hvCap (Nat.le_trans (Nat.le_max_left _ _)
          (Nat.le_trans (Nat.le_max_left _ _) hSmallNew))
      have hold_sm : valCap.toNat ≤ HasFineReallocCredit.smallMaxReq M := by
        have h2 : valCap.toNat ≤ 2 * capBound := by omega
        exact Nat.le_trans h2 (Nat.le_trans (Nat.le_max_right _ _)
          (Nat.le_trans (Nat.le_max_left _ _) hSmallNew))
      have hres_le : reserveCap valCap.toNat 0 v.length ≤ newCapBound := by
        dsimp only [reserveCap, newCapBound]; omega
      have hres_sm : reserveCap valCap.toNat 0 v.length ≤ HasFineReallocCredit.smallMaxReq M :=
        Nat.le_trans hres_le hSmallNew
      have ha := (PhaseCreditSpec.rustAlloc_small_any hM (req := v.length) (al := 1)
        (by decide) hv_sm).mono
        (hM.smallAlloc_le hv_sm) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl _)
      have hdr := phaseCredit_doReserveClear_small hM valCap.toNat v.length hold_sm hres_sm
      have hd := (DeallocCreditSpec.free_small M (req := v.length) (al := 1)
        (by decide) hv_sm).toPhaseCreditSpec
      have h123 := (ha.concat hdr).concat hd
      have himp : ∀ evs,
          evs = rustAllocEvents v.length 1 ++
            doReserveClearEvents valCap.toNat v.length ++
            rustDeallocEvents v.length 1 →
          ConcatEnv
            (ConcatEnv (· = rustAllocEvents v.length 1)
              (· = doReserveClearEvents valCap.toNat v.length))
            (· = rustDeallocEvents v.length 1) evs := by
        rintro _ rfl
        exact ⟨_, _, rfl, ⟨_, _, rfl, rfl, rfl⟩, rfl⟩
      exact (h123.of_imp himp).mono (by dsimp only at *; omega) (Nat.le_refl 0) (Nat.le_refl 0)
        (by dsimp only at *; omega)

/-- Wrapper lifting `phaseCredit_bytesMergeCore_aff` to `BytesMergeEnv x`. -/
theorem phaseCredit_bytesMerge_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (x : BytesMergeGhost) {capBound vCap : Nat}
    (hcap : x.valCap.toNat ≤ capBound)
    (hv_le : ∀ v rest, mergeBytes x.wt x.bs = some (v, rest) → v.length ≤ vCap) :
    let newCapBound := max (max vCap (2 * capBound)) 8
    PhaseCreditSpec M (BytesMergeEnv x)
      (max 9683 (2 * vCap + 2 * newCapBound + 19078))
      (max 8267 (newCapBound + 8195))
      (max 8267 ((vCap + 8195) + (newCapBound + 8195)))
      (max 72 (max vCap newCapBound)) :=
  phaseCredit_bytesMergeCore_aff hM x.wt x.valCap x.bs hcap hv_le

/-- Wrapper lifting `phaseCredit_bytesMerge_aff` to `BytesMergeProtoEnv x`. -/
theorem phaseCredit_bytesMergeProto_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (x : BytesMergeProtoGhost) {capBound vCap : Nat}
    (hcap : x.toCodec.valCap.toNat ≤ capBound)
    (hv_le : ∀ v rest, mergeBytes x.toCodec.wt x.toCodec.bs = some (v, rest) → v.length ≤ vCap) :
    let newCapBound := max (max vCap (2 * capBound)) 8
    PhaseCreditSpec M (BytesMergeProtoEnv x)
      (max 9683 (2 * vCap + 2 * newCapBound + 19078))
      (max 8267 (newCapBound + 8195))
      (max 8267 ((vCap + 8195) + (newCapBound + 8195)))
      (max 72 (max vCap newCapBound)) :=
  phaseCredit_bytesMerge_aff hM x.toCodec hcap hv_le

/-! ## Prost Leaf Bounds (`DropDecodeError`, `DecodeVarintSlice`, `Int32Merge`, `SkipField`) -/

/-- `DropDecodeErrorEnv` emits only `.free` events (`FreeOnlyEvs`), so its cost is `(0, 0, 0, 0)`. -/
theorem phaseCredit_dropDecodeError {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) :
    PhaseCreditSpec M DropDecodeErrorEnv 0 0 0 0 := by
  refine (PhaseCreditSpec.freeOnly_of_hyps hM).of_imp fun evs h => ?_
  rcases h with rfl | ⟨c, _, _, rfl⟩
  · intro ev hev
    simp only [rustDeallocEvents, List.mem_singleton] at hev
    exact ⟨8, 72, hev⟩
  · intro ev hev
    simp only [rustDeallocEvents, List.mem_append, List.mem_singleton] at hev
    rcases hev with rfl | rfl
    · exact ⟨8, c * 32, rfl⟩
    · exact ⟨8, 72, rfl⟩

/-- Small-regime `PhaseCreditSpec` for `DecodeVarintSliceEnv bs` (`72 ≤ smallMaxReq M`). -/
theorem phaseCredit_decodeVarintSlice_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (bs : List (BitVec 8))
    (hSmall72 : 72 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (DecodeVarintSliceEnv bs) 9683 0 0 72 := by
  unfold DecodeVarintSliceEnv decodeVarintSliceEvents
  cases decodeVarint bs with
  | some _ =>
    exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0)
      (Nat.zero_le _)
  | none =>
    have h72 := PhaseCreditSpec.rustAlloc_small_any hM (req := 72) (al := 8) (by decide) hSmall72
    have ha := hM.smallAlloc_le hSmall72
    exact h72.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 72)

/-- Small-regime `PhaseCreditSpec` for `Int32MergeEnv x` (`72 ≤ smallMaxReq M`). -/
theorem phaseCredit_int32Merge_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (x : Int32MergeGhost)
    (hSmall72 : 72 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (Int32MergeEnv x) 9683 0 0 72 := by
  unfold Int32MergeEnv int32MergeEvents
  cases mergeUint32 x.wt x.bs with
  | some _ =>
    exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0)
      (Nat.zero_le _)
  | none =>
    have h72 := PhaseCreditSpec.rustAlloc_small_any hM (req := 72) (al := 8) (by decide) hSmall72
    have ha := hM.smallAlloc_le hSmall72
    exact h72.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 72)

/-- Small-regime `PhaseCreditSpec` for `SkipFieldEnv x` (`72 ≤ smallMaxReq M`). -/
theorem phaseCredit_skipField_small {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (x : SkipFieldGhost)
    (hSmall72 : 72 ≤ HasFineReallocCredit.smallMaxReq M) :
    PhaseCreditSpec M (SkipFieldEnv x) 9683 0 0 72 := by
  unfold SkipFieldEnv skipFieldEventsCore
  cases skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs with
  | some _ =>
    exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.le_refl 0) (Nat.le_refl 0)
      (Nat.zero_le _)
  | none =>
    have h72 := PhaseCreditSpec.rustAlloc_small_any hM (req := 72) (al := 8) (by decide) hSmall72
    have ha := hM.smallAlloc_le hSmall72
    exact h72.mono (by omega) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl 72)

/-- Regime-uniform `PhaseCreditSpec` for `SkipFieldEnv x` (without `72 ≤ smallMaxReq M`). -/
theorem phaseCredit_skipField_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (x : SkipFieldGhost) :
    PhaseCreditSpec M (SkipFieldEnv x) 9683 8267 8267 72 := by
  unfold SkipFieldEnv skipFieldEventsCore
  cases skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs with
  | some _ =>
    exact (PhaseCreditSpec.nil M).mono (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      (Nat.zero_le _)
  | none =>
    exact PhaseCreditSpec.rustAlloc_aff hM (req := 72) (al := 8) (by decide)

/-! ## Field-List `IterSeqEnv` Composition Helper for `SessionStructure::decode` -/

private theorem foldr_max_le {α : Type} (f : α → Nat) (M_cap : Nat) (xs : List α)
    (h : ∀ x ∈ xs, f x ≤ M_cap) : (xs.map f).foldr max 0 ≤ M_cap := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact Nat.max_le.mpr ⟨h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem x hy))⟩

private theorem iterPeak_le_sum_add_const {α : Type} (l p : α → Nat) (pMax : Nat) (xs : List α)
    (hp : ∀ x ∈ xs, p x ≤ l x + pMax) :
    iterPeak l p xs ≤ (xs.map l).sum + pMax := by
  induction xs with
  | nil => simp [iterPeak]
  | cons x xs ih =>
    simp only [iterPeak, List.map_cons, List.sum_cons]
    have hx := hp x List.mem_cons_self
    have hxs := ih (fun y hy => hp y (List.mem_cons_of_mem x hy))
    omega

/-- Generic `IterSeqEnv` sum-and-peak aggregator for a protobuf field list `fs : List α`
(e.g., `fs = genFieldsQ (ssgqOf sess)` with `(fs.flatMap GenFieldQ.enc) = enc`):
sums `c`, sums `l`, bounds `iterPeak` by `(fs.map l).sum + pMax`, and bounds `maxReq` by `rMax`. -/
theorem phaseCredit_prevDecFields {α : Type} {M : AllocCostModel} [HasFineReallocCredit M]
    {Step : α → List AllocEvent → Prop}
    (c l p : α → Nat) {pMax rMax : Nat} (fs : List α)
    (hp : ∀ x ∈ fs, p x ≤ l x + pMax)
    (hstep : ∀ x ∈ fs, PhaseCreditSpec M (Step x) (c x) (l x) (p x) rMax) :
    PhaseCreditSpec M (IterSeqEnv Step fs)
      (fs.map c).sum
      (fs.map l).sum
      ((fs.map l).sum + pMax)
      rMax := by
  have hit := PhaseCreditSpec.iter c l p (fun _ => rMax) fs hstep
  have hpk := iterPeak_le_sum_add_const l p pMax fs hp
  have hr := foldr_max_le (fun _ => rMax) rMax fs (fun _ _ => Nat.le_refl rMax)
  exact hit.mono (Nat.le_refl _) (Nat.le_refl _) hpk hr

end LibsignalBinary.Proofs.PeakBudget.W4PrevDecPeak
