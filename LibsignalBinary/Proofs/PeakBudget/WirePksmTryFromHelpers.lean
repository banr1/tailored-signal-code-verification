/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PeakBudget.WireSignalHelpers
public import LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget

@[expose] public section

set_option autoImplicit false

/-!
# Fine-Credit Step Helpers for `PreKeySignalMessage::try_from`

Parametric `[HasFineReallocCredit M]` step, `eventStepReq`/`eventStepAlign`, and 4-field protobuf
decode loop / Kyber `Vec<u8>` overwrite bounds for:
- `doReserveClearEvents` (`Vec<u8>::clear` + `reserve`, including `0`-event overwrite when `len ≤ cap`),
- `bytesMergeEventsCore` (temporary `v.length` buffer alloc + reserve + temporary free, cancelling
  `largeCost M v.length` from `liveLarge` on `sc = 63`, plus `capsLargeCredit` L→L realloc cancel),
- `intoBoxedSliceEvents` / `intoBoxedCapEvents` (`Vec<u8>::into_boxed_slice` shrink/free on Kyber),
- `tryCloneFromRefEvents` (`Box<[u8]>` serialized wire copy),
- `mergeBytes` strict cursor progress (`v.length + 1 + rest.length ≤ bs.length`).
-/

namespace LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers

open CryptoVerification.LibsignalProtoCodec
  (WireType decodeVarint decodeVarintAux mergeBytes mergeUint32 skipField)
open CryptoVerification.LibsignalTripleRatchet
  (TryCloneSliceCall VecArg reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost
  (BytesMergeGhost Int32MergeGhost SkipFieldGhost)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents rustDeallocEvents
   rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds
  (eventStepAlign eventStepReq)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
  (ConcatEnv ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PeakBudget.WireSignalHelpers (bytesLargeLive)
open LibsignalBinary.Proofs.PeakBudget.WireTryFromHelpers
  (WireLowInterceptHyps bytesLargeLive_le_two_mul_of_le_max bytesMergeEventsCore_step_tight
   fineCostModel_wireLowInterceptHyps wireGrowsFrom wireRemGrows wireRemGrows_mono)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
  (HasFineReallocCredit stepEvents_rustAlloc_large stepEvents_rustAlloc_small
   stepEvents_rustDealloc_large stepEvents_rustDealloc_small
   stepEvents_rustRealloc_large_large stepEvents_rustRealloc_large_small
   stepEvents_rustRealloc_small_large stepEvents_rustRealloc_small_small)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (IntoBoxedSliceEnv TryCloneFromRefEnv intoBoxedSliceEvents
   tryCloneFromRefEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget
  (DecodeVarintSliceEnv DropDecodeErrorEnv Int32MergeEnv SkipFieldEnv
   decodeVarintSliceEvents int32MergeEvents skipFieldEventsCore)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (BytesMergeEnv bytesMergeEventsCore doReserveClearEvents)

/-! ## `reserveCap` Arithmetic Bounds -/

theorem reserveCap_zero_ge_len (cap len : Nat) :
    len ≤ reserveCap cap 0 len := by
  unfold reserveCap
  omega

theorem reserveCap_zero_ge_cap (cap len : Nat) :
    cap ≤ reserveCap cap 0 len := by
  unfold reserveCap
  omega

theorem reserveCap_zero_pos {cap len : Nat} (_hLen : 0 < len) :
    0 < reserveCap cap 0 len := by
  unfold reserveCap
  omega

theorem reserveCap_zero_le_max {cap len : Nat} (hLt : cap < len) :
    reserveCap cap 0 len ≤ max (2 * len) 8 := by
  unfold reserveCap
  omega

/-! ## `doReserveClearEvents` Fine-Credit Bounds -/

/-- Upper bound on `cumSmall` increase for `doReserveClearEvents cap len`. -/
def reserveClearSmallDelta (M : AllocCostModel) [HasFineReallocCredit M] (cap len : Nat) : Nat :=
  if len ≤ cap then 0
  else
    let newCap := reserveCap cap 0 len
    if cap = 0 then
      if newCap ≤ HasFineReallocCredit.smallMaxReq M then
        HasFineReallocCredit.smallAllocCost M newCap
      else
        HasFineReallocCredit.largeMetaCost M
    else if cap ≤ HasFineReallocCredit.smallMaxReq M then
      if newCap ≤ HasFineReallocCredit.smallMaxReq M then
        HasFineReallocCredit.smallReallocCost M newCap
      else
        HasFineReallocCredit.largeMetaCost M
    else
      HasFineReallocCredit.largeMetaCost M

/-- Upper bound on `liveLarge` and transient `peakLarge` increase for
`doReserveClearEvents cap len` (zero when `len ≤ cap` in-place overwrite or `newCap ≤ smallMaxReq M`). -/
def reserveClearLargeDelta (M : AllocCostModel) [HasFineReallocCredit M] (cap len : Nat) : Nat :=
  if len ≤ cap then 0
  else
    let newCap := reserveCap cap 0 len
    if newCap ≤ HasFineReallocCredit.smallMaxReq M then 0
    else HasFineReallocCredit.largeCost M newCap

theorem stepEvents_doReserveClearEvents_le (M : AllocCostModel) [HasFineReallocCredit M]
    (st : M.σ) (cap len : Nat) (hLen : 0 < len) :
    let sf := M.stepEvents (doReserveClearEvents cap len) st
    HasFineReallocCredit.cumSmall sf ≤
      HasFineReallocCredit.cumSmall st + reserveClearSmallDelta M cap len ∧
    HasFineReallocCredit.liveLarge sf ≤
      HasFineReallocCredit.liveLarge st + reserveClearLargeDelta M cap len ∧
    HasFineReallocCredit.peakLarge sf ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + reserveClearLargeDelta M cap len) := by
  dsimp only [doReserveClearEvents, reserveClearSmallDelta, reserveClearLargeDelta]
  split
  · simp only [AllocCostModel.stepEvents_nil, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _⟩
  · rename_i hNotLe
    have hNewPos : 0 < reserveCap cap 0 len := reserveCap_zero_pos hLen
    have hAl1 : (1 : Nat) ≤ 16 := by decide
    have hAlNew : 1 ≤ reserveCap cap 0 len := by omega
    by_cases hCap0 : cap = 0
    · subst hCap0
      simp only [↓reduceIte]
      by_cases hNewSm : reserveCap 0 0 len ≤ HasFineReallocCredit.smallMaxReq M
      · simp only [hNewSm, ↓reduceIte, Nat.add_zero]
        obtain ⟨hCum, hLive, hPeak⟩ :=
          stepEvents_rustAlloc_small M (req := reserveCap 0 0 len) (al := 1) st hAl1 hNewPos hNewSm
        exact ⟨hCum, hLive, Nat.le_trans hPeak (Nat.le_max_left _ _)⟩
      · have hNewLg : HasFineReallocCredit.smallMaxReq M < reserveCap 0 0 len := by omega
        simp only [hNewSm, ↓reduceIte]
        exact stepEvents_rustAlloc_large M (req := reserveCap 0 0 len) (al := 1) st hAl1 hNewLg
    · have hCapPos : 0 < cap := by omega
      simp only [hCap0, ↓reduceIte]
      by_cases hCapSm : cap ≤ HasFineReallocCredit.smallMaxReq M
      · simp only [hCapSm, ↓reduceIte]
        by_cases hNewSm : reserveCap cap 0 len ≤ HasFineReallocCredit.smallMaxReq M
        · simp only [hNewSm, ↓reduceIte, Nat.add_zero]
          obtain ⟨hCum, hLive, hPeak⟩ :=
            stepEvents_rustRealloc_small_small M (old := cap) (new := reserveCap cap 0 len)
              (al := 1) st hAl1 hAlNew hCapPos hCapSm hNewPos hNewSm
          exact ⟨hCum, hLive, Nat.le_trans hPeak (Nat.le_max_left _ _)⟩
        · have hNewLg : HasFineReallocCredit.smallMaxReq M < reserveCap cap 0 len := by omega
          simp only [hNewSm, ↓reduceIte]
          exact stepEvents_rustRealloc_small_large M (old := cap) (new := reserveCap cap 0 len)
            (al := 1) st hAl1 hAlNew hCapPos hCapSm hNewLg
      · have hCapLg : HasFineReallocCredit.smallMaxReq M < cap := by omega
        have hCapLeNew : cap ≤ reserveCap cap 0 len := reserveCap_zero_ge_cap cap len
        have hNewLg : HasFineReallocCredit.smallMaxReq M < reserveCap cap 0 len := by omega
        have hNotNewSm : ¬ reserveCap cap 0 len ≤ HasFineReallocCredit.smallMaxReq M := by omega
        simp only [hCapSm, hNotNewSm, ↓reduceIte]
        obtain ⟨hCum, hLive, hPeak⟩ :=
          stepEvents_rustRealloc_large_large M (old := cap) (new := reserveCap cap 0 len)
            (al := 1) st hAl1 hAlNew hCapLg hNewLg
        exact ⟨hCum, Nat.le_trans hLive (Nat.sub_le _ _), hPeak⟩

/-! ## `bytesMergeEventsCore` Fine-Credit Bounds -/

/-- Upper bound on `cumSmall` increase for an `Ok (v, _)` `bytes::merge` step of payload length `len`. -/
def bytesMergeOkSmallDelta (M : AllocCostModel) [HasFineReallocCredit M] (cap len : Nat) : Nat :=
  if len = 0 then 0
  else
    let tmpSmall :=
      if len ≤ HasFineReallocCredit.smallMaxReq M then
        HasFineReallocCredit.smallAllocCost M len
      else
        HasFineReallocCredit.largeMetaCost M
    tmpSmall + reserveClearSmallDelta M cap len

/-- Upper bound on net `liveLarge` increase for an `Ok (v, _)` `bytes::merge` step:
the temporary `len`-byte buffer is freed at the end of `bytes::merge`, cancelling its `largeCost`. -/
def bytesMergeOkLiveDelta (M : AllocCostModel) [HasFineReallocCredit M] (cap len : Nat) : Nat :=
  if len = 0 then 0 else reserveClearLargeDelta M cap len

/-- Upper bound on transient `peakLarge` spike above `liveLarge st` during `bytes::merge`:
while `doReserveClearEvents` runs, the temporary `len`-byte buffer is still live. -/
def bytesMergeOkPeakDelta (M : AllocCostModel) [HasFineReallocCredit M] (cap len : Nat) : Nat :=
  if len = 0 then 0
  else
    let tmpLarge :=
      if len ≤ HasFineReallocCredit.smallMaxReq M then 0
      else HasFineReallocCredit.largeCost M len
    tmpLarge + reserveClearLargeDelta M cap len

theorem stepEvents_bytesMergeOk_le (M : AllocCostModel) [HasFineReallocCredit M]
    (st : M.σ) (cap len : Nat) :
    let evs :=
      if len = 0 then []
      else rustAllocEvents len 1 ++ doReserveClearEvents cap len ++ rustDeallocEvents len 1
    let sf := M.stepEvents evs st
    HasFineReallocCredit.cumSmall sf ≤
      HasFineReallocCredit.cumSmall st + bytesMergeOkSmallDelta M cap len ∧
    HasFineReallocCredit.liveLarge sf ≤
      HasFineReallocCredit.liveLarge st + bytesMergeOkLiveDelta M cap len ∧
    HasFineReallocCredit.peakLarge sf ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + bytesMergeOkPeakDelta M cap len) := by
  dsimp only [bytesMergeOkSmallDelta, bytesMergeOkLiveDelta, bytesMergeOkPeakDelta]
  by_cases hZero : len = 0
  · subst hZero
    simp only [↓reduceIte, AllocCostModel.stepEvents_nil, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _⟩
  · have hPos : 0 < len := by omega
    have hAl1 : (1 : Nat) ≤ 16 := by decide
    simp only [hZero, ↓reduceIte, AllocCostModel.stepEvents_append]
    let st₁ := M.stepEvents (rustAllocEvents len 1) st
    let st₂ := M.stepEvents (doReserveClearEvents cap len) st₁
    obtain ⟨hCum₂, hLive₂, hPeak₂⟩ := stepEvents_doReserveClearEvents_le M st₁ cap len hPos
    by_cases hSm : len ≤ HasFineReallocCredit.smallMaxReq M
    · simp only [hSm, ↓reduceIte, Nat.zero_add]
      obtain ⟨hCum₁, hLive₁, hPeak₁⟩ :=
        stepEvents_rustAlloc_small M (req := len) (al := 1) st hAl1 hPos hSm
      obtain ⟨hCum₃, hLive₃, hPeak₃⟩ :=
        stepEvents_rustDealloc_small M (req := len) (al := 1) st₂ hAl1 hSm
      dsimp only [st₁, st₂] at *
      exact ⟨by omega, by omega, by omega⟩
    · have hLg : HasFineReallocCredit.smallMaxReq M < len := by omega
      simp only [hSm, ↓reduceIte]
      obtain ⟨hCum₁, hLive₁, hPeak₁⟩ :=
        stepEvents_rustAlloc_large M (req := len) (al := 1) st hAl1 hLg
      obtain ⟨hCum₃, hLive₃, hPeak₃⟩ :=
        stepEvents_rustDealloc_large M (req := len) (al := 1) st₂ hAl1 hLg
      dsimp only [st₁, st₂] at *
      exact ⟨by omega, by omega, by omega⟩

/-! ## `intoBoxedSliceEvents` & `tryCloneFromRefEvents` Fine-Credit Bounds -/

/-- Upper bound on `cumSmall` increase for `intoBoxedSliceEvents x` (e.g. Kyber `Vec` shrink). -/
def intoBoxedSmallDelta (M : AllocCostModel) [HasFineReallocCredit M] (len : Nat) : Nat :=
  if len = 0 then 0
  else if len ≤ HasFineReallocCredit.smallMaxReq M then
    HasFineReallocCredit.smallReallocCost M len
  else
    HasFineReallocCredit.largeMetaCost M

/-- Upper bound on `liveLarge` and `peakLarge` increase for `intoBoxedSliceEvents x`
(zero whenever `len ≤ smallMaxReq M`, e.g. `1569`-byte Kyber ciphertext on `fineCostModel`). -/
def intoBoxedLargeDelta (M : AllocCostModel) [HasFineReallocCredit M] (len : Nat) : Nat :=
  if len ≤ HasFineReallocCredit.smallMaxReq M then 0
  else HasFineReallocCredit.largeCost M len

theorem stepEvents_intoBoxedSliceEvents_le (M : AllocCostModel) [HasFineReallocCredit M]
    (st : M.σ) (x : VecArg) :
    let sf := M.stepEvents (intoBoxedSliceEvents x) st
    HasFineReallocCredit.cumSmall sf ≤
      HasFineReallocCredit.cumSmall st + intoBoxedSmallDelta M x.bytes.length ∧
    HasFineReallocCredit.liveLarge sf ≤
      HasFineReallocCredit.liveLarge st + intoBoxedLargeDelta M x.bytes.length ∧
    HasFineReallocCredit.peakLarge sf ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + intoBoxedLargeDelta M x.bytes.length) := by
  dsimp only [intoBoxedSliceEvents, intoBoxedSmallDelta, intoBoxedLargeDelta]
  have hAl1 : (1 : Nat) ≤ 16 := by decide
  split
  · simp only [AllocCostModel.stepEvents_nil]
    exact ⟨by omega, by omega, by omega⟩
  · rename_i hNotCapLe
    split
    · rename_i hEmpty
      have hLen0 : x.bytes.length = 0 := by simp [hEmpty]
      simp only [hLen0, Nat.zero_le, ↓reduceIte, Nat.add_zero]
      by_cases hCapSm : x.cap.toNat ≤ HasFineReallocCredit.smallMaxReq M
      · obtain ⟨hCum, hLive, hPeak⟩ :=
          stepEvents_rustDealloc_small M (req := x.cap.toNat) (al := 1) st hAl1 hCapSm
        exact ⟨hCum, hLive, Nat.le_trans hPeak (Nat.le_max_left _ _)⟩
      · have hCapLg : HasFineReallocCredit.smallMaxReq M < x.cap.toNat := by omega
        obtain ⟨hCum, hLive, hPeak⟩ :=
          stepEvents_rustDealloc_large M (req := x.cap.toNat) (al := 1) st hAl1 hCapLg
        exact ⟨hCum, by omega, Nat.le_trans hPeak (Nat.le_max_left _ _)⟩
    · rename_i hNonEmpty
      have hLenPos : 0 < x.bytes.length := List.length_pos_of_ne_nil hNonEmpty
      have hLenNe0 : x.bytes.length ≠ 0 := by omega
      have hAlLen : 1 ≤ x.bytes.length := by omega
      have hCapPos : 0 < x.cap.toNat := by omega
      simp only [hLenNe0, ↓reduceIte]
      by_cases hLenSm : x.bytes.length ≤ HasFineReallocCredit.smallMaxReq M
      · simp only [hLenSm, ↓reduceIte, Nat.add_zero]
        by_cases hCapSm : x.cap.toNat ≤ HasFineReallocCredit.smallMaxReq M
        · obtain ⟨hCum, hLive, hPeak⟩ :=
            stepEvents_rustRealloc_small_small M (old := x.cap.toNat) (new := x.bytes.length)
              (al := 1) st hAl1 hAlLen hCapPos hCapSm hLenPos hLenSm
          exact ⟨hCum, hLive, Nat.le_trans hPeak (Nat.le_max_left _ _)⟩
        · have hCapLg : HasFineReallocCredit.smallMaxReq M < x.cap.toNat := by omega
          obtain ⟨hCum, hLive, hPeak⟩ :=
            stepEvents_rustRealloc_large_small M (old := x.cap.toNat) (new := x.bytes.length)
              (al := 1) st hAl1 hAlLen hCapLg hLenPos hLenSm
          exact ⟨hCum, by omega, Nat.le_trans hPeak (Nat.le_max_left _ _)⟩
      · have hLenLg : HasFineReallocCredit.smallMaxReq M < x.bytes.length := by omega
        have hCapLg : HasFineReallocCredit.smallMaxReq M < x.cap.toNat := by omega
        simp only [hLenSm, ↓reduceIte]
        obtain ⟨hCum, hLive, hPeak⟩ :=
          stepEvents_rustRealloc_large_large M (old := x.cap.toNat) (new := x.bytes.length)
            (al := 1) st hAl1 hAlLen hCapLg hLenLg
        exact ⟨hCum, Nat.le_trans hLive (Nat.sub_le _ _), hPeak⟩

/-- Upper bound on `cumSmall` increase for `tryCloneFromRefEvents x` (`Box<[u8]>` wire copy). -/
def tryCloneSmallDelta (M : AllocCostModel) [HasFineReallocCredit M] (len : Nat) : Nat :=
  if len = 0 then 0
  else if len ≤ HasFineReallocCredit.smallMaxReq M then
    HasFineReallocCredit.smallAllocCost M len
  else
    HasFineReallocCredit.largeMetaCost M

/-- Upper bound on `liveLarge` / `peakLarge` increase for `tryCloneFromRefEvents x`. -/
def tryCloneLargeDelta (M : AllocCostModel) [HasFineReallocCredit M] (len : Nat) : Nat :=
  if len ≤ HasFineReallocCredit.smallMaxReq M then 0
  else HasFineReallocCredit.largeCost M len

theorem stepEvents_tryCloneFromRefEvents_le (M : AllocCostModel) [HasFineReallocCredit M]
    (st : M.σ) (x : TryCloneSliceCall) :
    let sf := M.stepEvents (tryCloneFromRefEvents x) st
    HasFineReallocCredit.cumSmall sf ≤
      HasFineReallocCredit.cumSmall st + tryCloneSmallDelta M x.bs.length ∧
    HasFineReallocCredit.liveLarge sf ≤
      HasFineReallocCredit.liveLarge st + tryCloneLargeDelta M x.bs.length ∧
    HasFineReallocCredit.peakLarge sf ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + tryCloneLargeDelta M x.bs.length) := by
  dsimp only [tryCloneFromRefEvents, tryCloneSmallDelta, tryCloneLargeDelta]
  have hAl1 : (1 : Nat) ≤ 16 := by decide
  split
  · rename_i hEmpty
    have hLen0 : x.bs.length = 0 := by simp [hEmpty]
    simp only [hLen0, Nat.zero_le, ↓reduceIte, AllocCostModel.stepEvents_nil, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _⟩
  · rename_i hNonEmpty
    have hLenPos : 0 < x.bs.length := List.length_pos_of_ne_nil hNonEmpty
    have hLenNe0 : x.bs.length ≠ 0 := by omega
    simp only [hLenNe0, ↓reduceIte]
    by_cases hSm : x.bs.length ≤ HasFineReallocCredit.smallMaxReq M
    · simp only [hSm, ↓reduceIte, Nat.add_zero]
      obtain ⟨hCum, hLive, hPeak⟩ :=
        stepEvents_rustAlloc_small M (req := x.bs.length) (al := 1) st hAl1 hLenPos hSm
      exact ⟨hCum, hLive, Nat.le_trans hPeak (Nat.le_max_left _ _)⟩
    · have hLg : HasFineReallocCredit.smallMaxReq M < x.bs.length := by omega
      simp only [hSm, ↓reduceIte]
      exact stepEvents_rustAlloc_large M (req := x.bs.length) (al := 1) st hAl1 hLg

/-! ## General `rustAllocEvents` Dispatch (`al ≤ 16`) & Wire-Length Progress -/

theorem stepEvents_rustAlloc_any_le (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (st : M.σ) (hal : al ≤ 16) (hpos : 0 < req) :
    let sf := M.stepEvents (rustAllocEvents req al) st
    HasFineReallocCredit.cumSmall sf ≤
      HasFineReallocCredit.cumSmall st + tryCloneSmallDelta M req ∧
    HasFineReallocCredit.liveLarge sf ≤
      HasFineReallocCredit.liveLarge st + tryCloneLargeDelta M req ∧
    HasFineReallocCredit.peakLarge sf ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + tryCloneLargeDelta M req) := by
  have hNe0 : req ≠ 0 := by omega
  dsimp only [tryCloneSmallDelta, tryCloneLargeDelta]
  simp only [hNe0, ↓reduceIte]
  by_cases hSm : req ≤ HasFineReallocCredit.smallMaxReq M
  · simp only [hSm, ↓reduceIte, Nat.add_zero]
    obtain ⟨hCum, hLive, hPeak⟩ :=
      stepEvents_rustAlloc_small M (req := req) (al := al) st hal hpos hSm
    exact ⟨hCum, hLive, Nat.le_trans hPeak (Nat.le_max_left _ _)⟩
  · have hLg : HasFineReallocCredit.smallMaxReq M < req := by omega
    simp only [hSm, ↓reduceIte]
    exact stepEvents_rustAlloc_large M (req := req) (al := al) st hal hLg

private theorem decodeVarintAux_length_lt :
    ∀ (i : Nat) (acc : BitVec 64) (bs rest : List (BitVec 8)) (v : BitVec 64),
      decodeVarintAux i acc bs = some (v, rest) → rest.length < bs.length
  | _, _, [], _, _, h => by simp [decodeVarintAux] at h
  | i, acc, b :: tail, rest, v, h => by
    simp only [decodeVarintAux] at h
    split at h
    · split at h
      · simp at h
      · injection h with hEq
        injection hEq with _ hRest
        subst hRest
        exact Nat.lt_succ_self _
    · split at h
      · simp at h
      · have ih := decodeVarintAux_length_lt (i + 1) _ tail rest v h
        exact Nat.lt_trans ih (Nat.lt_succ_self _)

theorem mergeBytes_length_sum {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, rest)) :
    v.length + 1 + rest.length ≤ bs.length := by
  unfold mergeBytes decodeVarint at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i _ len rest0 hVar
      split at h
      · simp at h
      · rename_i hNotLt
        injection h with hPair
        injection hPair with hv hrest
        subst hv hrest
        have hVarLt : rest0.length < bs.length :=
          decodeVarintAux_length_lt 0 0 bs rest0 len hVar
        have hTake : (rest0.take len.toNat).length = len.toNat :=
          List.length_take_of_le (by omega)
        have hDrop : (rest0.drop len.toNat).length = rest0.length - len.toNat :=
          List.length_drop
        omega

def bytesMergeCoreSmallDelta (M : AllocCostModel) [HasFineReallocCredit M]
    (wt : WireType) (valCap : BitVec 64) (bs : List (BitVec 8)) : Nat :=
  match mergeBytes wt bs with
  | none => tryCloneSmallDelta M 72
  | some (v, _) => bytesMergeOkSmallDelta M valCap.toNat v.length

def bytesMergeCoreLiveDelta (M : AllocCostModel) [HasFineReallocCredit M]
    (wt : WireType) (valCap : BitVec 64) (bs : List (BitVec 8)) : Nat :=
  match mergeBytes wt bs with
  | none => tryCloneLargeDelta M 72
  | some (v, _) => bytesMergeOkLiveDelta M valCap.toNat v.length

def bytesMergeCorePeakDelta (M : AllocCostModel) [HasFineReallocCredit M]
    (wt : WireType) (valCap : BitVec 64) (bs : List (BitVec 8)) : Nat :=
  match mergeBytes wt bs with
  | none => tryCloneLargeDelta M 72
  | some (v, _) => bytesMergeOkPeakDelta M valCap.toNat v.length

theorem stepEvents_bytesMergeEventsCore_le (M : AllocCostModel) [HasFineReallocCredit M]
    (st : M.σ) (wt : WireType) (valCap : BitVec 64) (bs : List (BitVec 8)) :
    let sf := M.stepEvents (bytesMergeEventsCore wt valCap bs) st
    HasFineReallocCredit.cumSmall sf ≤
      HasFineReallocCredit.cumSmall st + bytesMergeCoreSmallDelta M wt valCap bs ∧
    HasFineReallocCredit.liveLarge sf ≤
      HasFineReallocCredit.liveLarge st + bytesMergeCoreLiveDelta M wt valCap bs ∧
    HasFineReallocCredit.peakLarge sf ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + bytesMergeCorePeakDelta M wt valCap bs) := by
  dsimp only [bytesMergeEventsCore, bytesMergeCoreSmallDelta, bytesMergeCoreLiveDelta,
    bytesMergeCorePeakDelta]
  cases hMb : mergeBytes wt bs with
  | none =>
    simp only []
    exact stepEvents_rustAlloc_any_le M (req := 72) (al := 8) st (by decide) (by decide)
  | some pair =>
    rcases pair with ⟨v, rest⟩
    simp only []
    exact stepEvents_bytesMergeOk_le M st valCap.toNat v.length

/-! ## Per-Event `eventStepReq` & `eventStepAlign` Bounds (`PhaseCreditSpec.req_align`) -/

private theorem req_align_rustAlloc {req al : Nat} (hal : al ≤ 16)
    {ev : AllocEvent} (hev : ev ∈ rustAllocEvents req al) :
    eventStepReq ev ≤ req ∧ eventStepAlign ev ≤ 16 := by
  unfold rustAllocEvents at hev
  split at hev <;> rw [List.mem_singleton] at hev <;> subst hev <;>
    simp only [eventStepReq, eventStepAlign] <;> omega

private theorem req_align_rustDealloc {req al : Nat} (_hal : al ≤ 16)
    {ev : AllocEvent} (hev : ev ∈ rustDeallocEvents req al) :
    eventStepReq ev ≤ 0 ∧ eventStepAlign ev ≤ 16 := by
  unfold rustDeallocEvents at hev
  rw [List.mem_singleton] at hev
  subst hev
  simp only [eventStepReq, eventStepAlign]
  omega

private theorem req_align_rustRealloc {old new al : Nat} (hal : al ≤ 16) (hal_new : al ≤ new)
    {ev : AllocEvent} (hev : ev ∈ rustReallocEvents old new al) :
    eventStepReq ev ≤ new ∧ eventStepAlign ev ≤ 16 := by
  unfold rustReallocEvents at hev
  simp only [hal, hal_new, and_self, ↓reduceIte, List.mem_singleton] at hev
  subst hev
  exact ⟨Nat.le_refl new, hal⟩

theorem req_align_doReserveClearEvents {cap len : Nat} (hLen : 0 < len)
    {ev : AllocEvent} (hMem : ev ∈ doReserveClearEvents cap len) :
    eventStepReq ev ≤ max (2 * len) 8 ∧ eventStepAlign ev ≤ 16 := by
  unfold doReserveClearEvents at hMem
  split at hMem
  · nomatch hMem
  · rename_i hNotLe
    have hLt : cap < len := by omega
    have hCapBound : reserveCap cap 0 len ≤ max (2 * len) 8 := reserveCap_zero_le_max hLt
    have hPos : 1 ≤ reserveCap cap 0 len := by
      have := reserveCap_zero_pos (cap := cap) hLen
      omega
    by_cases hCap0 : cap = 0
    · subst hCap0
      simp only [↓reduceIte] at hMem
      obtain ⟨hReq, hAl⟩ := req_align_rustAlloc (by decide) hMem
      exact ⟨Nat.le_trans hReq hCapBound, hAl⟩
    · simp only [hCap0, ↓reduceIte] at hMem
      obtain ⟨hReq, hAl⟩ := req_align_rustRealloc (by decide) hPos hMem
      exact ⟨Nat.le_trans hReq hCapBound, hAl⟩

theorem req_align_bytesMergeEventsCore {wt : WireType} {valCap : BitVec 64}
    {bs : List (BitVec 8)} {ev : AllocEvent}
    (hMem : ev ∈ bytesMergeEventsCore wt valCap bs) :
    eventStepReq ev ≤ max 72 (max (2 * bs.length) 8) ∧ eventStepAlign ev ≤ 16 := by
  unfold bytesMergeEventsCore at hMem
  cases hMb : mergeBytes wt bs with
  | none =>
    simp only [hMb] at hMem
    obtain ⟨hReq, hAl⟩ := req_align_rustAlloc (by decide) hMem
    exact ⟨by omega, hAl⟩
  | some pair =>
    rcases pair with ⟨v, rest⟩
    simp only [hMb] at hMem
    have hVLe : v.length ≤ bs.length := by
      have := mergeBytes_length_sum hMb
      omega
    split at hMem
    · nomatch hMem
    · rename_i hNe0
      have hPos : 0 < v.length := by omega
      rcases List.mem_append.mp hMem with hMem12 | hMem3
      · rcases List.mem_append.mp hMem12 with hMem1 | hMem2
        · obtain ⟨hReq, hAl⟩ := req_align_rustAlloc (by decide) hMem1
          exact ⟨by omega, hAl⟩
        · obtain ⟨hReq, hAl⟩ := req_align_doReserveClearEvents hPos hMem2
          exact ⟨by omega, hAl⟩
      · obtain ⟨hReq, hAl⟩ := req_align_rustDealloc (by decide) hMem3
        exact ⟨by omega, hAl⟩

theorem req_align_intoBoxedSliceEvents {x : VecArg} {ev : AllocEvent}
    (hMem : ev ∈ intoBoxedSliceEvents x) :
    eventStepReq ev ≤ x.bytes.length ∧ eventStepAlign ev ≤ 16 := by
  unfold intoBoxedSliceEvents at hMem
  split at hMem
  · nomatch hMem
  · split at hMem
    · obtain ⟨hReq, hAl⟩ := req_align_rustDealloc (by decide) hMem
      exact ⟨by omega, hAl⟩
    · rename_i hNeNil
      have hPos : 1 ≤ x.bytes.length := List.length_pos_of_ne_nil hNeNil
      exact req_align_rustRealloc (by decide) hPos hMem

theorem req_align_tryCloneFromRefEvents {x : TryCloneSliceCall} {ev : AllocEvent}
    (hMem : ev ∈ tryCloneFromRefEvents x) :
    eventStepReq ev ≤ x.bs.length ∧ eventStepAlign ev ≤ 16 := by
  unfold tryCloneFromRefEvents at hMem
  split at hMem
  · nomatch hMem
  · exact req_align_rustAlloc (by decide) hMem

/-! ## `PhaseCreditSpec` Liftings for Prost Leaves & Canonical `PreKeyTryFromEnv` -/

theorem phaseCreditSpec_bytesMergeCore (M : AllocCostModel) [HasFineReallocCredit M]
    (wt : WireType) (valCap : BitVec 64) (bs : List (BitVec 8)) :
    PhaseCreditSpec M (· = bytesMergeEventsCore wt valCap bs)
      (bytesMergeCoreSmallDelta M wt valCap bs)
      (bytesMergeCoreLiveDelta M wt valCap bs)
      (bytesMergeCorePeakDelta M wt valCap bs)
      (max 72 (max (2 * bs.length) 8)) where
  req_align := by
    rintro _ rfl _ hMem
    exact req_align_bytesMergeEventsCore hMem
  credit_le := by
    rintro st0 _ rfl
    exact stepEvents_bytesMergeEventsCore_le M st0 wt valCap bs

theorem phaseCreditSpec_bytesMergeEnv (M : AllocCostModel) [HasFineReallocCredit M]
    (x : BytesMergeGhost) :
    PhaseCreditSpec M (BytesMergeEnv x)
      (bytesMergeCoreSmallDelta M x.wt x.valCap x.bs)
      (bytesMergeCoreLiveDelta M x.wt x.valCap x.bs)
      (bytesMergeCorePeakDelta M x.wt x.valCap x.bs)
      (max 72 (max (2 * x.bs.length) 8)) :=
  phaseCreditSpec_bytesMergeCore M x.wt x.valCap x.bs

theorem phaseCreditSpec_intoBoxedSlice (M : AllocCostModel) [HasFineReallocCredit M]
    (x : VecArg) :
    PhaseCreditSpec M (IntoBoxedSliceEnv x)
      (intoBoxedSmallDelta M x.bytes.length)
      (intoBoxedLargeDelta M x.bytes.length)
      (intoBoxedLargeDelta M x.bytes.length)
      x.bytes.length where
  req_align := by
    rintro _ rfl _ hMem
    exact req_align_intoBoxedSliceEvents hMem
  credit_le := by
    rintro st0 _ rfl
    exact stepEvents_intoBoxedSliceEvents_le M st0 x

theorem phaseCreditSpec_tryCloneFromRef (M : AllocCostModel) [HasFineReallocCredit M]
    (x : TryCloneSliceCall) :
    PhaseCreditSpec M (TryCloneFromRefEnv x)
      (tryCloneSmallDelta M x.bs.length)
      (tryCloneLargeDelta M x.bs.length)
      (tryCloneLargeDelta M x.bs.length)
      x.bs.length where
  req_align := by
    rintro _ rfl _ hMem
    exact req_align_tryCloneFromRefEvents hMem
  credit_le := by
    rintro st0 _ rfl
    exact stepEvents_tryCloneFromRefEvents_le M st0 x

theorem phaseCreditSpec_dropDecodeError (M : AllocCostModel) [HasFineReallocCredit M] :
    PhaseCreditSpec M DropDecodeErrorEnv 0 0 0 0 := by
  refine (PhaseCreditSpec.freeOnly_align16 M).of_imp ?_
  intro evs hEnv ev hMem
  rcases hEnv with rfl | ⟨c, _, _, rfl⟩
  · simp only [rustDeallocEvents, List.mem_singleton] at hMem
    subst hMem
    exact ⟨8, by decide, 72, rfl⟩
  · rcases List.mem_append.mp hMem with h1 | h2
    · simp only [rustDeallocEvents, List.mem_singleton] at h1
      subst h1
      exact ⟨8, by decide, c * 32, rfl⟩
    · simp only [rustDeallocEvents, List.mem_singleton] at h2
      subst h2
      exact ⟨8, by decide, 72, rfl⟩

theorem phaseCreditSpec_decodeVarintSlice (M : AllocCostModel) [HasFineReallocCredit M]
    (bs : List (BitVec 8)) :
    PhaseCreditSpec M (DecodeVarintSliceEnv bs)
      (tryCloneSmallDelta M 72) (tryCloneLargeDelta M 72) (tryCloneLargeDelta M 72) 72 where
  req_align := by
    rintro _ hEnv ev hMem
    unfold DecodeVarintSliceEnv decodeVarintSliceEvents at hEnv
    subst hEnv
    cases h : decodeVarint bs with
    | some _ => simp [h] at hMem
    | none =>
      simp only [h] at hMem
      exact req_align_rustAlloc (by decide) hMem
  credit_le := by
    rintro st0 _ hEnv
    unfold DecodeVarintSliceEnv decodeVarintSliceEvents at hEnv
    subst hEnv
    cases decodeVarint bs with
    | some _ =>
      simp only [AllocCostModel.stepEvents_nil]
      exact ⟨by omega, by omega, by omega⟩
    | none =>
      exact stepEvents_rustAlloc_any_le M (req := 72) (al := 8) st0 (by decide) (by decide)

theorem phaseCreditSpec_int32Merge (M : AllocCostModel) [HasFineReallocCredit M]
    (x : Int32MergeGhost) :
    PhaseCreditSpec M (Int32MergeEnv x)
      (tryCloneSmallDelta M 72) (tryCloneLargeDelta M 72) (tryCloneLargeDelta M 72) 72 where
  req_align := by
    rintro _ hEnv ev hMem
    unfold Int32MergeEnv int32MergeEvents at hEnv
    subst hEnv
    cases h : mergeUint32 x.wt x.bs with
    | some _ => simp [h] at hMem
    | none =>
      simp only [h] at hMem
      exact req_align_rustAlloc (by decide) hMem
  credit_le := by
    rintro st0 _ hEnv
    unfold Int32MergeEnv int32MergeEvents at hEnv
    subst hEnv
    cases mergeUint32 x.wt x.bs with
    | some _ =>
      simp only [AllocCostModel.stepEvents_nil]
      exact ⟨by omega, by omega, by omega⟩
    | none =>
      exact stepEvents_rustAlloc_any_le M (req := 72) (al := 8) st0 (by decide) (by decide)

theorem phaseCreditSpec_skipField (M : AllocCostModel) [HasFineReallocCredit M]
    (x : SkipFieldGhost) :
    PhaseCreditSpec M (SkipFieldEnv x)
      (tryCloneSmallDelta M 72) (tryCloneLargeDelta M 72) (tryCloneLargeDelta M 72) 72 where
  req_align := by
    rintro _ hEnv ev hMem
    unfold SkipFieldEnv skipFieldEventsCore at hEnv
    subst hEnv
    cases h : skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs with
    | some _ => simp [h] at hMem
    | none =>
      simp only [h] at hMem
      exact req_align_rustAlloc (by decide) hMem
  credit_le := by
    rintro st0 _ hEnv
    unfold SkipFieldEnv skipFieldEventsCore at hEnv
    subst hEnv
    cases skipField (2 * x.bs.length + 2) x.depth x.tag x.wt x.bs with
    | some _ =>
      simp only [AllocCostModel.stepEvents_nil]
      exact ⟨by omega, by omega, by omega⟩
    | none =>
      exact stepEvents_rustAlloc_any_le M (req := 72) (al := 8) st0 (by decide) (by decide)

/-! ## 4-Field Protobuf Loop `capsLargeCredit` Invariant & Kyber `Vec` Overwrite Cancellation -/

/-- Live `sc = 63` credit held by a `Vec<u8>` buffer of capacity `cap`. -/
def vecLargeCredit (M : AllocCostModel) [HasFineReallocCredit M] (cap : Nat) : Nat :=
  if cap ≤ HasFineReallocCredit.smallMaxReq M then 0
  else HasFineReallocCredit.largeCost M cap

@[simp]
theorem vecLargeCredit_zero (M : AllocCostModel) [HasFineReallocCredit M] :
    vecLargeCredit M 0 = 0 := by
  simp [vecLargeCredit]

theorem vecLargeCredit_le_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (cap : Nat) :
    vecLargeCredit M cap ≤ cap + 8195 := by
  unfold vecLargeCredit
  split
  · omega
  · rename_i hNotLe
    have hGt : HasFineReallocCredit.smallMaxReq M < cap := by omega
    exact hM.largeCost_le hGt

/-- `doReserveClearEvents` step bound cancelling any old `sc = 63` `vecLargeCredit M cap` on L→L
reallocation (`Vec<u8>` overwrite / growth). -/
theorem stepEvents_doReserveClearEvents_cancel (M : AllocCostModel) [HasFineReallocCredit M]
    (st : M.σ) {L_keep cap len : Nat}
    (hLive : HasFineReallocCredit.liveLarge st ≤ L_keep + vecLargeCredit M cap)
    (hLen : 0 < len) :
    let cap' := if len ≤ cap then cap else reserveCap cap 0 len
    let sf := M.stepEvents (doReserveClearEvents cap len) st
    HasFineReallocCredit.cumSmall sf ≤
      HasFineReallocCredit.cumSmall st + reserveClearSmallDelta M cap len ∧
    HasFineReallocCredit.liveLarge sf ≤ L_keep + vecLargeCredit M cap' ∧
    HasFineReallocCredit.peakLarge sf ≤
      max (HasFineReallocCredit.peakLarge st)
        (L_keep + vecLargeCredit M cap + reserveClearLargeDelta M cap len) := by
  dsimp only [doReserveClearEvents, reserveClearSmallDelta, reserveClearLargeDelta, vecLargeCredit]
  dsimp only [vecLargeCredit] at hLive
  split
  · simp only [AllocCostModel.stepEvents_nil, Nat.add_zero]
    exact ⟨Nat.le_refl _, hLive, Nat.le_max_left _ _⟩
  · rename_i hNotLe
    have hNewPos : 0 < reserveCap cap 0 len := reserveCap_zero_pos hLen
    have hAl1 : (1 : Nat) ≤ 16 := by decide
    have hAlNew : 1 ≤ reserveCap cap 0 len := by omega
    by_cases hCap0 : cap = 0
    · subst hCap0
      simp only [Nat.zero_le, ↓reduceIte, Nat.add_zero] at hLive ⊢
      by_cases hNewSm : reserveCap 0 0 len ≤ HasFineReallocCredit.smallMaxReq M
      · simp only [hNewSm, ↓reduceIte, Nat.add_zero]
        obtain ⟨hCum, hLv, hPk⟩ :=
          stepEvents_rustAlloc_small M (req := reserveCap 0 0 len) (al := 1) st hAl1 hNewPos hNewSm
        exact ⟨hCum, Nat.le_trans hLv hLive, Nat.le_trans hPk (Nat.le_max_left _ _)⟩
      · have hNewLg : HasFineReallocCredit.smallMaxReq M < reserveCap 0 0 len := by omega
        simp only [hNewSm, ↓reduceIte]
        obtain ⟨hCum, hLv, hPk⟩ :=
          stepEvents_rustAlloc_large M (req := reserveCap 0 0 len) (al := 1) st hAl1 hNewLg
        exact ⟨hCum, by omega, by omega⟩
    · have hCapPos : 0 < cap := by omega
      simp only [hCap0, ↓reduceIte]
      by_cases hCapSm : cap ≤ HasFineReallocCredit.smallMaxReq M
      · simp only [hCapSm, ↓reduceIte, Nat.add_zero] at hLive ⊢
        by_cases hNewSm : reserveCap cap 0 len ≤ HasFineReallocCredit.smallMaxReq M
        · simp only [hNewSm, ↓reduceIte, Nat.add_zero]
          obtain ⟨hCum, hLv, hPk⟩ :=
            stepEvents_rustRealloc_small_small M (old := cap) (new := reserveCap cap 0 len)
              (al := 1) st hAl1 hAlNew hCapPos hCapSm hNewPos hNewSm
          exact ⟨hCum, Nat.le_trans hLv hLive, Nat.le_trans hPk (Nat.le_max_left _ _)⟩
        · have hNewLg : HasFineReallocCredit.smallMaxReq M < reserveCap cap 0 len := by omega
          simp only [hNewSm, ↓reduceIte]
          obtain ⟨hCum, hLv, hPk⟩ :=
            stepEvents_rustRealloc_small_large M (old := cap) (new := reserveCap cap 0 len)
              (al := 1) st hAl1 hAlNew hCapPos hCapSm hNewLg
          exact ⟨hCum, by omega, by omega⟩
      · have hCapLg : HasFineReallocCredit.smallMaxReq M < cap := by omega
        have hCapLeNew : cap ≤ reserveCap cap 0 len := reserveCap_zero_ge_cap cap len
        have hNewLg : HasFineReallocCredit.smallMaxReq M < reserveCap cap 0 len := by omega
        have hNotNewSm : ¬ reserveCap cap 0 len ≤ HasFineReallocCredit.smallMaxReq M := by omega
        simp only [hCapSm, hNotNewSm, ↓reduceIte] at hLive ⊢
        obtain ⟨hCum, hLv, hPk⟩ :=
          stepEvents_rustRealloc_large_large M (old := cap) (new := reserveCap cap 0 len)
            (al := 1) st hAl1 hAlNew hCapLg hNewLg
        exact ⟨hCum, by omega, by omega⟩

/-- `bytes::merge` `Ok` step bound cancelling BOTH the temporary `len` buffer's `.free` AND any old
`sc = 63` `vecLargeCredit M cap` on `Vec<u8>` overwrite. -/
theorem stepEvents_bytesMergeOk_cancel (M : AllocCostModel) [HasFineReallocCredit M]
    (st : M.σ) {L_keep cap len : Nat}
    (hLive : HasFineReallocCredit.liveLarge st ≤ L_keep + vecLargeCredit M cap) :
    let cap' := if len ≤ cap then cap else reserveCap cap 0 len
    let evs :=
      if len = 0 then []
      else rustAllocEvents len 1 ++ doReserveClearEvents cap len ++ rustDeallocEvents len 1
    let sf := M.stepEvents evs st
    HasFineReallocCredit.cumSmall sf ≤
      HasFineReallocCredit.cumSmall st + bytesMergeOkSmallDelta M cap len ∧
    HasFineReallocCredit.liveLarge sf ≤ L_keep + vecLargeCredit M cap' ∧
    HasFineReallocCredit.peakLarge sf ≤
      max (HasFineReallocCredit.peakLarge st)
        (L_keep + vecLargeCredit M cap + bytesMergeOkPeakDelta M cap len) := by
  dsimp only [bytesMergeOkSmallDelta, bytesMergeOkPeakDelta]
  by_cases hZero : len = 0
  · subst hZero
    simp only [Nat.zero_le, ↓reduceIte, AllocCostModel.stepEvents_nil, Nat.add_zero]
    exact ⟨Nat.le_refl _, hLive, Nat.le_max_left _ _⟩
  · have hPos : 0 < len := by omega
    have hAl1 : (1 : Nat) ≤ 16 := by decide
    simp only [hZero, ↓reduceIte, AllocCostModel.stepEvents_append]
    let st₁ := M.stepEvents (rustAllocEvents len 1) st
    let st₂ := M.stepEvents (doReserveClearEvents cap len) st₁
    by_cases hSm : len ≤ HasFineReallocCredit.smallMaxReq M
    · simp only [hSm, ↓reduceIte, Nat.zero_add]
      obtain ⟨hCum₁, hLv₁, hPk₁⟩ :=
        stepEvents_rustAlloc_small M (req := len) (al := 1) st hAl1 hPos hSm
      obtain ⟨hCum₂, hLv₂, hPk₂⟩ :=
        stepEvents_doReserveClearEvents_cancel M st₁ (Nat.le_trans hLv₁ hLive) hPos
      obtain ⟨hCum₃, hLv₃, hPk₃⟩ :=
        stepEvents_rustDealloc_small M (req := len) (al := 1) st₂ hAl1 hSm
      dsimp only [st₁, st₂] at *
      exact ⟨by omega, Nat.le_trans hLv₃ hLv₂, by omega⟩
    · have hLg : HasFineReallocCredit.smallMaxReq M < len := by omega
      simp only [hSm, ↓reduceIte]
      obtain ⟨hCum₁, hLv₁, hPk₁⟩ :=
        stepEvents_rustAlloc_large M (req := len) (al := 1) st hAl1 hLg
      have hLv₁' :
          HasFineReallocCredit.liveLarge st₁ ≤
            (L_keep + HasFineReallocCredit.largeCost M len) + vecLargeCredit M cap := by
        dsimp only [st₁] at *
        omega
      obtain ⟨hCum₂, hLv₂, hPk₂⟩ :=
        stepEvents_doReserveClearEvents_cancel M st₁ hLv₁' hPos
      obtain ⟨hCum₃, hLv₃, hPk₃⟩ :=
        stepEvents_rustDealloc_large M (req := len) (al := 1) st₂ hAl1 hLg
      dsimp only [st₁, st₂] at *
      exact ⟨by omega, by omega, by omega⟩

/-- Four-slot `Vec<u8>` field selector for `ProtoPreKeySignalMessage` / `ProtoSignalMessage`. -/
inductive ProtoField4 where
  | f0 | f1 | f2 | f3

/-- Four-slot `Vec<u8>` capacity tracker for protobuf decode loops. -/
structure ProtoCaps4 where
  f0 : Nat
  f1 : Nat
  f2 : Nat
  f3 : Nat

def ProtoCaps4.zero : ProtoCaps4 := ⟨0, 0, 0, 0⟩

def ProtoCaps4.get (c : ProtoCaps4) : ProtoField4 → Nat
  | .f0 => c.f0 | .f1 => c.f1 | .f2 => c.f2 | .f3 => c.f3

def ProtoCaps4.set (c : ProtoCaps4) : ProtoField4 → Nat → ProtoCaps4
  | .f0, v => { c with f0 := v }
  | .f1, v => { c with f1 := v }
  | .f2, v => { c with f2 := v }
  | .f3, v => { c with f3 := v }

def ProtoCaps4.sum (c : ProtoCaps4) : Nat :=
  c.f0 + c.f1 + c.f2 + c.f3

def ProtoCaps4.largeCredit (M : AllocCostModel) [HasFineReallocCredit M] (c : ProtoCaps4) : Nat :=
  vecLargeCredit M c.f0 + vecLargeCredit M c.f1 + vecLargeCredit M c.f2 + vecLargeCredit M c.f3

def ProtoCaps4.otherLargeCredit (M : AllocCostModel) [HasFineReallocCredit M]
    (c : ProtoCaps4) : ProtoField4 → Nat
  | .f0 => vecLargeCredit M c.f1 + vecLargeCredit M c.f2 + vecLargeCredit M c.f3
  | .f1 => vecLargeCredit M c.f0 + vecLargeCredit M c.f2 + vecLargeCredit M c.f3
  | .f2 => vecLargeCredit M c.f0 + vecLargeCredit M c.f1 + vecLargeCredit M c.f3
  | .f3 => vecLargeCredit M c.f0 + vecLargeCredit M c.f1 + vecLargeCredit M c.f2

@[simp]
theorem ProtoCaps4.sum_zero : ProtoCaps4.zero.sum = 0 := rfl

@[simp]
theorem ProtoCaps4.largeCredit_zero (M : AllocCostModel) [HasFineReallocCredit M] :
    ProtoCaps4.zero.largeCredit M = 0 := by
  simp [ProtoCaps4.zero, ProtoCaps4.largeCredit]

theorem ProtoCaps4.largeCredit_eq_other_add (M : AllocCostModel) [HasFineReallocCredit M]
    (c : ProtoCaps4) (f : ProtoField4) :
    c.largeCredit M = c.otherLargeCredit M f + vecLargeCredit M (c.get f) := by
  cases f <;> simp only [ProtoCaps4.largeCredit, ProtoCaps4.otherLargeCredit, ProtoCaps4.get] <;>
    omega

theorem ProtoCaps4.largeCredit_set (M : AllocCostModel) [HasFineReallocCredit M]
    (c : ProtoCaps4) (f : ProtoField4) (v : Nat) :
    (c.set f v).largeCredit M = c.otherLargeCredit M f + vecLargeCredit M v := by
  cases f <;>
    simp only [ProtoCaps4.set, ProtoCaps4.largeCredit, ProtoCaps4.otherLargeCredit] <;> omega

theorem ProtoCaps4.sum_set_le (c : ProtoCaps4) (f : ProtoField4) (v : Nat) :
    (c.set f v).sum ≤ c.sum + v := by
  cases f <;> simp only [ProtoCaps4.set, ProtoCaps4.sum] <;> omega

theorem ProtoCaps4.sum_set_eq_of_eq (c : ProtoCaps4) (f : ProtoField4) :
    (c.set f (c.get f)).sum = c.sum := by
  cases f <;> rfl

theorem ProtoCaps4.largeCredit_le_sum_add {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (c : ProtoCaps4) :
    c.largeCredit M ≤ c.sum + 32780 := by
  have h0 := vecLargeCredit_le_aff hM c.f0
  have h1 := vecLargeCredit_le_aff hM c.f1
  have h2 := vecLargeCredit_le_aff hM c.f2
  have h3 := vecLargeCredit_le_aff hM c.f3
  unfold ProtoCaps4.largeCredit ProtoCaps4.sum
  omega

/-- Affine `ModelHyps M` step bounds for `bytesMergeOkSmallDelta`, `bytesMergeOkPeakDelta`, and
`reserveCap` given cursor progress `rem' + len + 1 ≤ rem`. -/
theorem bytesMergeOk_aff_bounds {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {cap len rem rem' : Nat}
    (hRem : rem' + len + 1 ≤ rem) :
    bytesMergeOkSmallDelta M cap len ≤ 9548 * (rem - rem') ∧
    bytesMergeOkPeakDelta M cap len ≤ 5 * (rem - rem') + 16390 ∧
    (cap < len → reserveCap cap 0 len ≤ 4 * (rem - rem')) := by
  have hRcMax : cap < len → reserveCap cap 0 len ≤ max (2 * len) 8 :=
    fun hLt => reserveCap_zero_le_max hLt
  by_cases hZero : len = 0
  · subst hZero
    simp only [bytesMergeOkSmallDelta, bytesMergeOkPeakDelta, ↓reduceIte]
    refine ⟨Nat.zero_le _, Nat.zero_le _, ?_⟩
    intro hLt
    omega
  · have hPos : 0 < len := by omega
    have hDeltaGe2 : 2 ≤ rem - rem' := by omega
    have hMaxLe : max (2 * len) 8 ≤ 4 * (rem - rem') := by omega
    refine ⟨?_, ?_, fun hLt => Nat.le_trans (hRcMax hLt) hMaxLe⟩
    · -- cumSmall bound: tmpSmall ≤ 2 * len + 9539, reserveClearSmallDelta ≤ 8 * Δ + 9539
      have hTmp :
          (if len ≤ HasFineReallocCredit.smallMaxReq M then
            HasFineReallocCredit.smallAllocCost M len
          else HasFineReallocCredit.largeMetaCost M) ≤ 2 * len + 9539 := by
        by_cases hLenSm : len ≤ HasFineReallocCredit.smallMaxReq M
        · simp only [hLenSm, ↓reduceIte]
          exact hM.smallAlloc_le hLenSm
        · simp only [hLenSm, ↓reduceIte]
          have hm := hM.meta_le
          omega
      have hRes : reserveClearSmallDelta M cap len ≤ 8 * (rem - rem') + 9539 := by
        dsimp only [reserveClearSmallDelta]
        by_cases hLe : len ≤ cap
        · simp only [hLe, ↓reduceIte]
          omega
        · simp only [hLe, ↓reduceIte]
          have hLt : cap < len := by omega
          have hRcLe : reserveCap cap 0 len ≤ 4 * (rem - rem') :=
            Nat.le_trans (hRcMax hLt) hMaxLe
          by_cases hCap0 : cap = 0
          · subst hCap0
            simp only [↓reduceIte]
            by_cases hNewSm : reserveCap 0 0 len ≤ HasFineReallocCredit.smallMaxReq M
            · simp only [hNewSm, ↓reduceIte]
              have hs := hM.smallAlloc_le hNewSm
              omega
            · simp only [hNewSm, ↓reduceIte]
              have hm := hM.meta_le
              omega
          · simp only [hCap0, ↓reduceIte]
            by_cases hCapSm : cap ≤ HasFineReallocCredit.smallMaxReq M
            · simp only [hCapSm, ↓reduceIte]
              by_cases hNewSm : reserveCap cap 0 len ≤ HasFineReallocCredit.smallMaxReq M
              · simp only [hNewSm, ↓reduceIte]
                have hs := hM.smallRealloc_le hNewSm
                omega
              · simp only [hNewSm, ↓reduceIte]
                have hm := hM.meta_le
                omega
            · simp only [hCapSm, ↓reduceIte]
              have hm := hM.meta_le
              omega
      simp only [bytesMergeOkSmallDelta, hZero, ↓reduceIte]
      omega
    · -- peakLarge bound: tmpLarge ≤ len + 8195, reserveClearLargeDelta ≤ 4 * Δ + 8195
      have hTmpL :
          (if len ≤ HasFineReallocCredit.smallMaxReq M then 0
          else HasFineReallocCredit.largeCost M len) ≤ len + 8195 := by
        by_cases hLenSm : len ≤ HasFineReallocCredit.smallMaxReq M
        · simp only [hLenSm, ↓reduceIte]
          omega
        · simp only [hLenSm, ↓reduceIte]
          have hLg : HasFineReallocCredit.smallMaxReq M < len := by omega
          exact hM.largeCost_le hLg
      have hResL : reserveClearLargeDelta M cap len ≤ 4 * (rem - rem') + 8195 := by
        dsimp only [reserveClearLargeDelta]
        by_cases hLe : len ≤ cap
        · simp only [hLe, ↓reduceIte]
          omega
        · simp only [hLe, ↓reduceIte]
          have hLt : cap < len := by omega
          have hRcLe : reserveCap cap 0 len ≤ 4 * (rem - rem') :=
            Nat.le_trans (hRcMax hLt) hMaxLe
          by_cases hNewSm : reserveCap cap 0 len ≤ HasFineReallocCredit.smallMaxReq M
          · simp only [hNewSm, ↓reduceIte]
            omega
          · simp only [hNewSm, ↓reduceIte]
            have hLg : HasFineReallocCredit.smallMaxReq M < reserveCap cap 0 len := by omega
            have hl := hM.largeCost_le hLg
            omega
      simp only [bytesMergeOkPeakDelta, hZero, ↓reduceIte]
      omega

/-- Complete 1-step `ProtoCaps4` invariant preservation and affine `ModelHyps M` bound for a
`bytesMergeEventsCore` step inside a protobuf decode loop (including Kyber `Vec<u8>` overwrites). -/
theorem stepEvents_bytesMergeCore_caps4_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (st : M.σ) (f : ProtoField4) (caps : ProtoCaps4)
    (wt : WireType) (bs v rest : List (BitVec 8))
    {L0 rem rem' used N : Nat}
    (hMerge : mergeBytes wt bs = some (v, rest))
    (hRem : rem' + v.length + 1 ≤ rem)
    (hCapFit : caps.get f < 2 ^ 64)
    (hLive : HasFineReallocCredit.liveLarge st ≤ L0 + caps.largeCredit M)
    (hSum : caps.sum ≤ 4 * used)
    (hUsed : used + (rem - rem') ≤ N) :
    let cap := caps.get f
    let cap' := if v.length ≤ cap then cap else reserveCap cap 0 v.length
    let caps' := caps.set f cap'
    let sf := M.stepEvents (bytesMergeEventsCore wt (BitVec.ofNat 64 cap) bs) st
    HasFineReallocCredit.cumSmall sf ≤
      HasFineReallocCredit.cumSmall st + 9548 * (rem - rem') ∧
    HasFineReallocCredit.liveLarge sf ≤ L0 + caps'.largeCredit M ∧
    HasFineReallocCredit.peakLarge sf ≤
      max (HasFineReallocCredit.peakLarge st) (L0 + 5 * N + 49170) ∧
    caps'.sum ≤ 4 * (used + (rem - rem')) := by
  have hBvCap : (BitVec.ofNat 64 (caps.get f)).toNat = caps.get f := Nat.mod_eq_of_lt hCapFit
  have hEvEq :
      bytesMergeEventsCore wt (BitVec.ofNat 64 (caps.get f)) bs =
        (if v.length = 0 then []
        else rustAllocEvents v.length 1 ++ doReserveClearEvents (caps.get f) v.length ++
          rustDeallocEvents v.length 1) := by
    simp only [bytesMergeEventsCore, hMerge, hBvCap]
  have hDecomp := ProtoCaps4.largeCredit_eq_other_add M caps f
  have hLiveSplit :
      HasFineReallocCredit.liveLarge st ≤
        (L0 + caps.otherLargeCredit M f) + vecLargeCredit M (caps.get f) := by
    omega
  obtain ⟨hCumStep, hLiveStep, hPeakStep⟩ :=
    stepEvents_bytesMergeOk_cancel M st (len := v.length) hLiveSplit
  rw [← hEvEq] at hCumStep hLiveStep hPeakStep
  obtain ⟨hAffSmall, hAffPeak, hRcBound⟩ :=
    bytesMergeOk_aff_bounds hM (cap := caps.get f) hRem
  have hCapsLargeLe : caps.largeCredit M ≤ caps.sum + 32780 :=
    ProtoCaps4.largeCredit_le_sum_add hM caps
  have hSetLarge :=
    ProtoCaps4.largeCredit_set M caps f
      (if v.length ≤ caps.get f then caps.get f else reserveCap (caps.get f) 0 v.length)
  have hSum' :
      (caps.set f
        (if v.length ≤ caps.get f then caps.get f else reserveCap (caps.get f) 0 v.length)).sum ≤
        4 * (used + (rem - rem')) := by
    by_cases hLe : v.length ≤ caps.get f
    · simp only [hLe, ↓reduceIte, ProtoCaps4.sum_set_eq_of_eq]
      omega
    · simp only [hLe, ↓reduceIte]
      have hLt : caps.get f < v.length := by omega
      have hRc := hRcBound hLt
      have hSetSum := ProtoCaps4.sum_set_le caps f (reserveCap (caps.get f) 0 v.length)
      omega
  refine ⟨by omega, ?_, by omega, hSum'⟩
  rw [hSetLarge]
  omega

/-- Affine `PhaseCreditSpec` for `intoBoxedSliceEvents ⟨0#64, cap, 0#64, bs⟩` under `ModelHyps M`. -/
theorem phaseCreditSpec_intoBoxedCap_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (bs : List (BitVec 8))
    (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs → ∃ cap : BitVec 64, evs = intoBoxedSliceEvents ⟨0#64, cap, 0#64, bs⟩) :
    PhaseCreditSpec M Env
      (if bs.length = 0 then 0 else 2 * bs.length + 9539)
      (if bs.length ≤ HasFineReallocCredit.smallMaxReq M then 0 else bs.length + 8195)
      (if bs.length ≤ HasFineReallocCredit.smallMaxReq M then 0 else bs.length + 8195)
      bs.length where
  req_align := by
    intro evs hE ev hMem
    obtain ⟨cap, rfl⟩ := hEnv evs hE
    exact req_align_intoBoxedSliceEvents (x := ⟨0#64, cap, 0#64, bs⟩) hMem
  credit_le := by
    intro st0 evs hE
    obtain ⟨cap, rfl⟩ := hEnv evs hE
    obtain ⟨hC, hL, hP⟩ := stepEvents_intoBoxedSliceEvents_le M st0 ⟨0#64, cap, 0#64, bs⟩
    dsimp only at hC hL hP
    have hSmBound :
        intoBoxedSmallDelta M bs.length ≤
          (if bs.length = 0 then 0 else 2 * bs.length + 9539) := by
      unfold intoBoxedSmallDelta
      by_cases hZ : bs.length = 0
      · simp only [hZ, ↓reduceIte]
        exact Nat.le_refl 0
      · simp only [hZ, ↓reduceIte]
        by_cases hSm : bs.length ≤ HasFineReallocCredit.smallMaxReq M
        · simp only [hSm, ↓reduceIte]
          exact hM.smallRealloc_le hSm
        · simp only [hSm, ↓reduceIte]
          have hm := hM.meta_le
          omega
    have hLgBound :
        intoBoxedLargeDelta M bs.length ≤
          (if bs.length ≤ HasFineReallocCredit.smallMaxReq M then 0 else bs.length + 8195) := by
      unfold intoBoxedLargeDelta
      by_cases hSm : bs.length ≤ HasFineReallocCredit.smallMaxReq M
      · simp only [hSm, ↓reduceIte]
        exact Nat.le_refl 0
      · simp only [hSm, ↓reduceIte]
        have hLg : HasFineReallocCredit.smallMaxReq M < bs.length := by omega
        exact hM.largeCost_le hLg
    exact ⟨by omega, by omega, by omega⟩

/-- Affine `PhaseCreditSpec` for `tryCloneFromRefEvents ⟨0#64, bs⟩` under `ModelHyps M`. -/
theorem phaseCreditSpec_tryCloneBytes_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (bs : List (BitVec 8)) :
    PhaseCreditSpec M (· = if bs = [] then [] else rustAllocEvents bs.length 1)
      (if bs.length = 0 then 0 else 2 * bs.length + 9539)
      (if bs.length ≤ HasFineReallocCredit.smallMaxReq M then 0 else bs.length + 8195)
      (if bs.length ≤ HasFineReallocCredit.smallMaxReq M then 0 else bs.length + 8195)
      bs.length := by
  have hBase := phaseCreditSpec_tryCloneFromRef M ⟨0#64, bs⟩
  dsimp only at hBase
  have hSmBound :
      tryCloneSmallDelta M bs.length ≤
        (if bs.length = 0 then 0 else 2 * bs.length + 9539) := by
    unfold tryCloneSmallDelta
    by_cases hZ : bs.length = 0
    · simp only [hZ, ↓reduceIte]
      exact Nat.le_refl 0
    · simp only [hZ, ↓reduceIte]
      by_cases hSm : bs.length ≤ HasFineReallocCredit.smallMaxReq M
      · simp only [hSm, ↓reduceIte]
        exact hM.smallAlloc_le hSm
      · simp only [hSm, ↓reduceIte]
        have hm := hM.meta_le
        omega
  have hLgBound :
      tryCloneLargeDelta M bs.length ≤
        (if bs.length ≤ HasFineReallocCredit.smallMaxReq M then 0 else bs.length + 8195) := by
    unfold tryCloneLargeDelta
    by_cases hSm : bs.length ≤ HasFineReallocCredit.smallMaxReq M
    · simp only [hSm, ↓reduceIte]
      exact Nat.le_refl 0
    · simp only [hSm, ↓reduceIte]
      have hLg : HasFineReallocCredit.smallMaxReq M < bs.length := by omega
      exact hM.largeCost_le hLg
  exact hBase.mono hSmBound hLgBound hLgBound (Nat.le_refl _)

/-! ## Tight `S`-Capped & `g`-Sum Helpers -/

theorem vecLargeCredit_eq_bytesLargeLive (M : AllocCostModel) [HasFineReallocCredit M] (cap : Nat) :
    vecLargeCredit M cap = bytesLargeLive M cap :=
  rfl

def ProtoCaps4.otherSum (c : ProtoCaps4) : ProtoField4 → Nat
  | .f0 => c.f1 + c.f2 + c.f3
  | .f1 => c.f0 + c.f2 + c.f3
  | .f2 => c.f0 + c.f1 + c.f3
  | .f3 => c.f0 + c.f1 + c.f2

def ProtoCaps4.minSum (S : Nat) (c : ProtoCaps4) : Nat :=
  min c.f0 S + min c.f1 S + min c.f2 S + min c.f3 S

def ProtoCaps4.remGrows (N : Nat) (c : ProtoCaps4) : Nat :=
  wireRemGrows N c.f0 + wireRemGrows N c.f1 + wireRemGrows N c.f2 + wireRemGrows N c.f3

def ProtoCaps4.otherRemGrows (N : Nat) (c : ProtoCaps4) : ProtoField4 → Nat
  | .f0 => wireRemGrows N c.f1 + wireRemGrows N c.f2 + wireRemGrows N c.f3
  | .f1 => wireRemGrows N c.f0 + wireRemGrows N c.f2 + wireRemGrows N c.f3
  | .f2 => wireRemGrows N c.f0 + wireRemGrows N c.f1 + wireRemGrows N c.f3
  | .f3 => wireRemGrows N c.f0 + wireRemGrows N c.f1 + wireRemGrows N c.f2

def ProtoCaps4.bounded (maxLen : Nat) (c : ProtoCaps4) : Prop :=
  c.f0 ≤ max 8 (2 * maxLen) ∧
  c.f1 ≤ max 8 (2 * maxLen) ∧
  c.f2 ≤ max 8 (2 * maxLen) ∧
  c.f3 ≤ max 8 (2 * maxLen)

def ProtoCaps4.boundedG (c g : ProtoCaps4) : Prop :=
  c.f0 ≤ max (2 * g.f0) 8 ∧
  c.f1 ≤ max (2 * g.f1) 8 ∧
  c.f2 ≤ max (2 * g.f2) 8 ∧
  c.f3 ≤ max (2 * g.f3) 8

theorem ProtoCaps4.remGrows_decomp (N : Nat) (c : ProtoCaps4) (f : ProtoField4) (v : Nat) :
    c.remGrows N = c.otherRemGrows N f + wireRemGrows N (c.get f) ∧
    (c.set f v).remGrows N = c.otherRemGrows N f + wireRemGrows N v := by
  cases f <;>
    dsimp only [ProtoCaps4.remGrows, ProtoCaps4.otherRemGrows, ProtoCaps4.get, ProtoCaps4.set] <;>
    exact ⟨by omega, by omega⟩

theorem ProtoCaps4.g_props {c g : ProtoCaps4} (hcg : c.boundedG g)
    (f : ProtoField4) {v_cap v_g : Nat} (hv : v_cap ≤ max (2 * v_g) 8) :
    g.sum = g.otherSum f + g.get f ∧
    (g.set f v_g).sum = g.otherSum f + v_g ∧
    c.get f ≤ max (2 * g.get f) 8 ∧
    (c.set f v_cap).boundedG (g.set f v_g) := by
  obtain ⟨h0, h1, h2, h3⟩ := hcg
  cases f <;>
    dsimp only [ProtoCaps4.get, ProtoCaps4.set, ProtoCaps4.sum, ProtoCaps4.otherSum,
      ProtoCaps4.boundedG] <;>
    exact ⟨by omega, by omega, by omega, ⟨by omega, by omega, by omega, by omega⟩⟩

theorem ProtoCaps4.minSum_props {S maxLen : Nat} {c : ProtoCaps4}
    (hc : c.bounded maxLen) (f : ProtoField4) {v : Nat}
    (hle : min (c.get f) S ≤ min v S) (hv : v ≤ max 8 (2 * maxLen)) :
    c.get f ≤ max 8 (2 * maxLen) ∧
    (c.set f v).bounded maxLen ∧
    c.minSum S ≤ 4 * min (max 8 (2 * maxLen)) S ∧
    (c.set f v).minSum S ≤ 4 * min (max 8 (2 * maxLen)) S ∧
    (c.set f v).minSum S + min (c.get f) S = c.minSum S + min v S := by
  obtain ⟨h0, h1, h2, h3⟩ := hc
  cases f <;>
    dsimp only [ProtoCaps4.get, ProtoCaps4.set, ProtoCaps4.bounded, ProtoCaps4.minSum] at hle ⊢ <;>
    exact ⟨by omega, ⟨by omega, by omega, by omega, by omega⟩, by omega, by omega, by omega⟩

theorem ProtoCaps4.otherLargeCredit_le_g {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS8 : 8 ≤ S)
    {c g : ProtoCaps4} (hcg : c.boundedG g) (f : ProtoField4) :
    c.otherLargeCredit M f ≤ 2 * g.otherSum f + 24585 := by
  obtain ⟨h0, h1, h2, h3⟩ := hcg
  have l0 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h0
  have l1 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h1
  have l2 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h2
  have l3 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h3
  cases f <;>
    simp only [ProtoCaps4.otherLargeCredit, ProtoCaps4.otherSum, vecLargeCredit_eq_bytesLargeLive] <;>
    omega

theorem ProtoCaps4.largeCredit_le_g {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S) (hS8 : 8 ≤ S)
    {c g : ProtoCaps4} (hcg : c.boundedG g) :
    c.largeCredit M ≤ 2 * g.sum + 32780 := by
  obtain ⟨h0, h1, h2, h3⟩ := hcg
  have l0 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h0
  have l1 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h1
  have l2 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h2
  have l3 := bytesLargeLive_le_two_mul_of_le_max hM hSm hS8 h3
  simp only [ProtoCaps4.largeCredit, ProtoCaps4.sum, vecLargeCredit_eq_bytesLargeLive]
  omega

/-- Tight `S`-capped `PhaseCreditSpec` for `intoBoxedSliceEvents ⟨0#64, cap, 0#64, bs⟩`. -/
theorem phaseCreditSpec_intoBoxedCap_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S)
    (bs : List (BitVec 8))
    (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs → ∃ cap : BitVec 64, evs = intoBoxedSliceEvents ⟨0#64, cap, 0#64, bs⟩) :
    PhaseCreditSpec M Env
      (2 * min bs.length S + 9539)
      (bs.length + 8195)
      (bs.length + 8195)
      bs.length where
  req_align evs hE ev hMem := by
    obtain ⟨cap, rfl⟩ := hEnv evs hE
    exact req_align_intoBoxedSliceEvents (x := ⟨0#64, cap, 0#64, bs⟩) hMem
  credit_le st0 {evs} hE := by
    obtain ⟨cap, rfl⟩ := hEnv evs hE
    obtain ⟨hC, hL, hP⟩ := stepEvents_intoBoxedSliceEvents_le M st0 ⟨0#64, cap, 0#64, bs⟩
    dsimp only at hC hL hP
    have hSmBound : intoBoxedSmallDelta M bs.length ≤ 2 * min bs.length S + 9539 := by
      unfold intoBoxedSmallDelta
      by_cases hZ : bs.length = 0
      · simp only [hZ, ↓reduceIte]; omega
      · simp only [hZ, ↓reduceIte]
        by_cases hLe : bs.length ≤ HasFineReallocCredit.smallMaxReq M
        · simp only [hLe, ↓reduceIte]
          have hr := hM.smallRealloc_le hLe
          omega
        · simp only [hLe, ↓reduceIte]
          have hm := hM.meta_le
          omega
    have hLgBound : intoBoxedLargeDelta M bs.length ≤ bs.length + 8195 := by
      unfold intoBoxedLargeDelta
      by_cases hLe : bs.length ≤ HasFineReallocCredit.smallMaxReq M
      · simp only [hLe, ↓reduceIte]; omega
      · simp only [hLe, ↓reduceIte]
        exact hM.largeCost_le (by omega)
    exact ⟨by omega, by omega, by omega⟩

/-- Small-slice specialization (`bs.length ≤ S`) of `intoBoxedSliceEvents`: zero `liveLarge` and
`peakLarge` delta. -/
theorem phaseCreditSpec_intoBoxedCap_small_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S)
    (bs : List (BitVec 8)) (hle : bs.length ≤ S)
    (Env : List AllocEvent → Prop)
    (hEnv : ∀ evs, Env evs → ∃ cap : BitVec 64, evs = intoBoxedSliceEvents ⟨0#64, cap, 0#64, bs⟩) :
    PhaseCreditSpec M Env (2 * bs.length + 9539) 0 0 bs.length := by
  have hBase := phaseCreditSpec_intoBoxedCap_aff hM bs Env hEnv
  have hSmLe : bs.length ≤ HasFineReallocCredit.smallMaxReq M := by omega
  simp only [hSmLe, ↓reduceIte] at hBase
  exact hBase.mono (by split <;> omega) (Nat.le_refl 0) (Nat.le_refl 0) (Nat.le_refl _)

/-- Tight `S`-capped `PhaseCreditSpec` for `tryCloneFromRefEvents ⟨0#64, bs⟩`. -/
theorem phaseCreditSpec_tryCloneBytes_S {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) {S : Nat} (hSm : HasFineReallocCredit.smallMaxReq M = S)
    (bs : List (BitVec 8)) :
    PhaseCreditSpec M (· = if bs = [] then [] else rustAllocEvents bs.length 1)
      (2 * min bs.length S + 9539)
      (bs.length + 8195)
      (bs.length + 8195)
      bs.length := by
  have hBase := phaseCreditSpec_tryCloneFromRef M ⟨0#64, bs⟩
  dsimp only at hBase
  have hSmBound : tryCloneSmallDelta M bs.length ≤ 2 * min bs.length S + 9539 := by
    unfold tryCloneSmallDelta
    by_cases hZ : bs.length = 0
    · simp only [hZ, ↓reduceIte]; omega
    · simp only [hZ, ↓reduceIte]
      by_cases hLe : bs.length ≤ HasFineReallocCredit.smallMaxReq M
      · simp only [hLe, ↓reduceIte]
        have ha := hM.smallAlloc_le hLe
        omega
      · simp only [hLe, ↓reduceIte]
        have hm := hM.meta_le
        omega
  have hLgBound : tryCloneLargeDelta M bs.length ≤ bs.length + 8195 := by
    unfold tryCloneLargeDelta
    by_cases hLe : bs.length ≤ HasFineReallocCredit.smallMaxReq M
    · simp only [hLe, ↓reduceIte]; omega
    · simp only [hLe, ↓reduceIte]
      exact hM.largeCost_le (by omega)
  exact hBase.mono hSmBound hLgBound hLgBound (Nat.le_refl _)

end LibsignalBinary.Proofs.PeakBudget.WirePksmTryFromHelpers
