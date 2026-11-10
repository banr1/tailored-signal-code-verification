/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.ClientBounds
public import LibsignalBinary.Proofs.PeakBudget.SeqCreditKit
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogueDeallocBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
public import LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget

/-!
# Parametric Fine-Credit Helpers for Wire `SignalMessage` & `PreKeySignalMessage`

Parametric `(M : AllocCostModel) [HasFineReallocCredit M]` step and cancellation lemmas:
1. Single `rustAllocEvents` / `rustDeallocEvents` / `rustReallocEvents` step bounds and
   `eventStepReq` / `eventStepAlign` lemmas.
2. `computeMacEvents` (`2 × (alloc 33 ++ dealloc 33)`) credit and cancellation bounds.
3. `<SignalMessage>::new` (`SignalMessageNewEnv` / `signalMessageNewEvents`) 11-segment live-large
   cancellation (`rk` 33 B, `ciphertext`, and `pqRatchet` temporaries freed in epilogue).
4. `<PreKeySignalMessage>::new` 9-segment credit and epilogue cancellation (`kyber` copy, two 33 B
   `PublicKey::serialize`, `msg.serialized` copy freed in epilogue, leaving `model.serialized`).
5. `<SignalMessage as TryFrom<&[u8]>>::try_from` bounded `DecodeError::push`, slice-shrinking
   `bytes::merge` loop step, and `into_boxed_slice` / `try_clone_from_ref` post-loop helpers.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.WireSignalHelpers

open CryptoGames.LibsignalSessionApi (KyberPayload)
open CryptoVerification.LibsignalProtoCodec (WireType encode mergeBytes)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (PreKeyMsgNewCall)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.Fine.ClientBounds (eventStepAlign eventStepReq)
open LibsignalBinary.Proofs.PeakBudget.SeqCreditKit (ModelHyps PhaseCreditSpec)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleesBudget (kyberDeallocEvs)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
  (HasFineReallocCredit
   stepEvents_rustAlloc_small stepEvents_rustAlloc_large
   stepEvents_rustDealloc_small stepEvents_rustDealloc_large
   stepEvents_rustRealloc_small_small stepEvents_rustRealloc_small_large
   stepEvents_rustRealloc_large_large stepEvents_rustRealloc_large_small)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (TryCloneSliceCall intoBoxedSliceEvents publicKeySerializeEvents tryCloneFromRefEvents)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget (computeMacEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.MergeDefsBudget
  (bytesMergeEventsCore doReserveClearEvents)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
  (SignalMessageNewEnv SignalMessageNewGhost signalMessageNewEvents)

/-! ## Symbolic Single-Allocation / Reallocation Cost Expressions -/

/-- Symbolic `cumSmall` charge of `rustAllocEvents req al` (`al ≤ 16`):
`0` when `req = 0`, `smallAllocCost req` when `0 < req ≤ smallMaxReq`, else `largeMetaCost`. -/
def bytesCumAlloc (M : AllocCostModel) [HasFineReallocCredit M] (req : Nat) : Nat :=
  if req = 0 then 0
  else if req ≤ HasFineReallocCredit.smallMaxReq M then
    HasFineReallocCredit.smallAllocCost M req
  else
    HasFineReallocCredit.largeMetaCost M

/-- Symbolic `cumSmall` charge of `rustReallocEvents old new al` (`al ≤ 16`):
`0` when `old = 0 ∨ new = 0`, `smallReallocCost new` when `0 < new ≤ smallMaxReq`,
else `largeMetaCost`. -/
def bytesCumRealloc (M : AllocCostModel) [HasFineReallocCredit M] (old new : Nat) : Nat :=
  if old = 0 ∨ new = 0 then 0
  else if new ≤ HasFineReallocCredit.smallMaxReq M then
    HasFineReallocCredit.smallReallocCost M new
  else
    HasFineReallocCredit.largeMetaCost M

/-- Symbolic `liveLarge` weight of a buffer of byte size `req` (`al ≤ 16`):
`0` when `req ≤ smallMaxReq`, else `largeCost req`. -/
def bytesLargeLive (M : AllocCostModel) [HasFineReallocCredit M] (req : Nat) : Nat :=
  if req ≤ HasFineReallocCredit.smallMaxReq M then 0
  else HasFineReallocCredit.largeCost M req

@[simp] theorem bytesCumAlloc_zero (M : AllocCostModel) [HasFineReallocCredit M] :
    bytesCumAlloc M 0 = 0 := rfl

@[simp] theorem bytesLargeLive_zero (M : AllocCostModel) [HasFineReallocCredit M] :
    bytesLargeLive M 0 = 0 := by
  simp [bytesLargeLive]

theorem bytesCumAlloc_le_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (req : Nat) :
    bytesCumAlloc M req ≤ 2 * req + 9539 := by
  unfold bytesCumAlloc
  split
  · omega
  · split
    · rename_i hsm
      exact hM.smallAlloc_le hsm
    · have hm := hM.meta_le
      omega

theorem bytesCumRealloc_le_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (old new : Nat) :
    bytesCumRealloc M old new ≤ 2 * new + 9539 := by
  unfold bytesCumRealloc
  split
  · omega
  · split
    · rename_i hsm
      exact hM.smallRealloc_le hsm
    · have hm := hM.meta_le
      omega

theorem bytesLargeLive_le_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (req : Nat) :
    bytesLargeLive M req ≤ req + 8195 := by
  unfold bytesLargeLive
  split
  · omega
  · rename_i hnot
    exact hM.largeCost_le (Nat.lt_of_not_ge hnot)

/-! ## `eventStepReq` & `eventStepAlign` Lemmas for `rust{Alloc,Dealloc,Realloc}Events` -/

theorem req_align_of_rustAllocEvents {req al maxReq : Nat}
    (hreq : req ≤ maxReq) (hal : al ≤ 16) :
    ∀ ev ∈ rustAllocEvents req al,
      eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  intro ev hev
  unfold rustAllocEvents at hev
  split at hev
  · simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨hreq, by simp [eventStepAlign]⟩
  · simp only [List.mem_singleton] at hev
    subst hev
    refine ⟨hreq, ?_⟩
    simp only [eventStepAlign]
    omega

theorem req_align_of_rustDeallocEvents {req al maxReq : Nat} (_hal : al ≤ 16) :
    ∀ ev ∈ rustDeallocEvents req al,
      eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  intro ev hev
  simp only [rustDeallocEvents, List.mem_singleton] at hev
  subst hev
  exact ⟨Nat.zero_le _, by simp [eventStepAlign]⟩

theorem req_align_of_rustReallocEvents {old new al maxReq : Nat}
    (hnew : new ≤ maxReq) (hal : al ≤ 16) :
    ∀ ev ∈ rustReallocEvents old new al,
      eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  intro ev hev
  unfold rustReallocEvents at hev
  split at hev
  · simp only [List.mem_singleton] at hev
    subst hev
    exact ⟨hnew, hal⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
    rcases hev with rfl | rfl
    · refine ⟨hnew, ?_⟩
      simp only [eventStepAlign]
      omega
    · exact ⟨Nat.zero_le _, by simp [eventStepAlign]⟩

/-! ## Single-Primitive `stepEvents` Credit Bounds -/

theorem stepEvents_rustAlloc_pos (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (hal : al ≤ 16) (hpos : 0 < req) (st : M.σ) :
    HasFineReallocCredit.cumSmall (M.stepEvents (rustAllocEvents req al) st) ≤
      HasFineReallocCredit.cumSmall st + bytesCumAlloc M req ∧
    HasFineReallocCredit.liveLarge (M.stepEvents (rustAllocEvents req al) st) ≤
      HasFineReallocCredit.liveLarge st + bytesLargeLive M req ∧
    HasFineReallocCredit.peakLarge (M.stepEvents (rustAllocEvents req al) st) ≤
      max (HasFineReallocCredit.peakLarge st)
          (HasFineReallocCredit.liveLarge st + bytesLargeLive M req) := by
  have hne : req ≠ 0 := Nat.ne_of_gt hpos
  dsimp only [bytesCumAlloc, bytesLargeLive]
  by_cases hsm : req ≤ HasFineReallocCredit.smallMaxReq M
  · have h := stepEvents_rustAlloc_small (M := M) st hal hpos hsm
    simp only [hne, hsm, ↓reduceIte, Nat.add_zero]
    exact ⟨h.1, h.2.1, Nat.le_trans h.2.2 (Nat.le_max_left _ _)⟩
  · have hlg : HasFineReallocCredit.smallMaxReq M < req := Nat.lt_of_not_ge hsm
    have h := stepEvents_rustAlloc_large (M := M) st hal hlg
    simp only [hne, hsm, ↓reduceIte]
    exact h

theorem stepEvents_rustAlloc_aff {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (req al : Nat) (hal : al ≤ 16) (st : M.σ) :
    HasFineReallocCredit.cumSmall (M.stepEvents (rustAllocEvents req al) st) ≤
      HasFineReallocCredit.cumSmall st + (2 * req + 9539) ∧
    HasFineReallocCredit.liveLarge (M.stepEvents (rustAllocEvents req al) st) ≤
      HasFineReallocCredit.liveLarge st + bytesLargeLive M req ∧
    HasFineReallocCredit.peakLarge (M.stepEvents (rustAllocEvents req al) st) ≤
      max (HasFineReallocCredit.peakLarge st)
          (HasFineReallocCredit.liveLarge st + bytesLargeLive M req) := by
  by_cases hpos : 0 < req
  · have hp := stepEvents_rustAlloc_pos M (req := req) (al := al) hal hpos st
    have hc := bytesCumAlloc_le_aff hM req
    exact ⟨by omega, hp.2.1, hp.2.2⟩
  · have hz : req = 0 := by omega
    subst hz
    rw [bytesLargeLive_zero]
    have h0 := (PhaseCreditSpec.rustAlloc_small_any hM hal (Nat.zero_le _)).credit_le
      st (evs := rustAllocEvents 0 al) rfl
    have hsm0 := hM.smallAlloc_le (Nat.zero_le _)
    exact ⟨by omega, by omega, by omega⟩

theorem stepEvents_rustDealloc_any (M : AllocCostModel) [HasFineReallocCredit M]
    (req al : Nat) (hal : al ≤ 16) (st : M.σ) :
    HasFineReallocCredit.cumSmall (M.stepEvents (rustDeallocEvents req al) st) ≤
      HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge (M.stepEvents (rustDeallocEvents req al) st) ≤
      HasFineReallocCredit.liveLarge st - bytesLargeLive M req ∧
    HasFineReallocCredit.peakLarge (M.stepEvents (rustDeallocEvents req al) st) ≤
      HasFineReallocCredit.peakLarge st := by
  dsimp only [bytesLargeLive]
  by_cases hsm : req ≤ HasFineReallocCredit.smallMaxReq M
  · have h := stepEvents_rustDealloc_small (M := M) st hal hsm
    simp only [hsm, ↓reduceIte, Nat.sub_zero]
    exact h
  · have hlg : HasFineReallocCredit.smallMaxReq M < req := Nat.lt_of_not_ge hsm
    have h := stepEvents_rustDealloc_large (M := M) st hal hlg
    simp only [hsm, ↓reduceIte]
    exact h

theorem stepEvents_rustRealloc_pos (M : AllocCostModel) [HasFineReallocCredit M]
    {old new al : Nat} (hal : al ≤ 16) (hal_new : al ≤ new)
    (hold_pos : 0 < old) (hnew_pos : 0 < new) (st : M.σ) :
    HasFineReallocCredit.cumSmall (M.stepEvents (rustReallocEvents old new al) st) ≤
      HasFineReallocCredit.cumSmall st + bytesCumRealloc M old new ∧
    HasFineReallocCredit.liveLarge (M.stepEvents (rustReallocEvents old new al) st) ≤
      (HasFineReallocCredit.liveLarge st + bytesLargeLive M new) - bytesLargeLive M old ∧
    HasFineReallocCredit.peakLarge (M.stepEvents (rustReallocEvents old new al) st) ≤
      max (HasFineReallocCredit.peakLarge st)
          (HasFineReallocCredit.liveLarge st + bytesLargeLive M new) := by
  have hnot0 : ¬ (old = 0 ∨ new = 0) := by omega
  dsimp only [bytesCumRealloc, bytesLargeLive]
  by_cases hold_sm : old ≤ HasFineReallocCredit.smallMaxReq M
  · by_cases hnew_sm : new ≤ HasFineReallocCredit.smallMaxReq M
    · have h := stepEvents_rustRealloc_small_small (M := M) st hal hal_new
        hold_pos hold_sm hnew_pos hnew_sm
      simp only [hnot0, hold_sm, hnew_sm, ↓reduceIte, Nat.add_zero, Nat.sub_zero]
      exact ⟨h.1, h.2.1, Nat.le_trans h.2.2 (Nat.le_max_left _ _)⟩
    · have hnew_lg : HasFineReallocCredit.smallMaxReq M < new := Nat.lt_of_not_ge hnew_sm
      have h := stepEvents_rustRealloc_small_large (M := M) st hal hal_new
        hold_pos hold_sm hnew_lg
      simp only [hnot0, hold_sm, hnew_sm, ↓reduceIte, Nat.sub_zero]
      exact h
  · have hold_lg : HasFineReallocCredit.smallMaxReq M < old := Nat.lt_of_not_ge hold_sm
    by_cases hnew_sm : new ≤ HasFineReallocCredit.smallMaxReq M
    · have h := stepEvents_rustRealloc_large_small (M := M) st hal hal_new
        hold_lg hnew_pos hnew_sm
      simp only [hnot0, hold_sm, hnew_sm, ↓reduceIte, Nat.add_zero]
      exact ⟨h.1, h.2.1, Nat.le_trans h.2.2 (Nat.le_max_left _ _)⟩
    · have hnew_lg : HasFineReallocCredit.smallMaxReq M < new := Nat.lt_of_not_ge hnew_sm
      have h := stepEvents_rustRealloc_large_large (M := M) st hal hal_new hold_lg hnew_lg
      simp only [hnot0, hold_sm, hnew_sm, ↓reduceIte]
      exact h

theorem stepEvents_optBytesAlloc (M : AllocCostModel) [HasFineReallocCredit M]
    (bs : List (BitVec 8)) (st : M.σ) :
    HasFineReallocCredit.cumSmall
        (M.stepEvents (if bs.isEmpty then [] else rustAllocEvents bs.length 1) st) ≤
      HasFineReallocCredit.cumSmall st + bytesCumAlloc M bs.length ∧
    HasFineReallocCredit.liveLarge
        (M.stepEvents (if bs.isEmpty then [] else rustAllocEvents bs.length 1) st) ≤
      HasFineReallocCredit.liveLarge st + bytesLargeLive M bs.length ∧
    HasFineReallocCredit.peakLarge
        (M.stepEvents (if bs.isEmpty then [] else rustAllocEvents bs.length 1) st) ≤
      max (HasFineReallocCredit.peakLarge st)
          (HasFineReallocCredit.liveLarge st + bytesLargeLive M bs.length) := by
  cases bs with
  | nil => simp [AllocCostModel.stepEvents]
  | cons _ tl =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    exact stepEvents_rustAlloc_pos M (al := 1) (by decide) (Nat.succ_pos tl.length) st

theorem stepEvents_optBytesDealloc (M : AllocCostModel) [HasFineReallocCredit M]
    (bs : List (BitVec 8)) (st : M.σ) :
    HasFineReallocCredit.cumSmall
        (M.stepEvents (if bs.isEmpty then [] else rustDeallocEvents bs.length 1) st) ≤
      HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge
        (M.stepEvents (if bs.isEmpty then [] else rustDeallocEvents bs.length 1) st) ≤
      HasFineReallocCredit.liveLarge st - bytesLargeLive M bs.length ∧
    HasFineReallocCredit.peakLarge
        (M.stepEvents (if bs.isEmpty then [] else rustDeallocEvents bs.length 1) st) ≤
      HasFineReallocCredit.peakLarge st := by
  cases bs with
  | nil => simp [AllocCostModel.stepEvents]
  | cons _ _ =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    exact stepEvents_rustDealloc_any M _ 1 (by decide) st

theorem req_align_optBytesAlloc {bs : List (BitVec 8)} {maxReq : Nat}
    (hlen : bs.length ≤ maxReq) :
    ∀ ev ∈ (if bs.isEmpty then ([] : List AllocEvent) else rustAllocEvents bs.length 1),
      eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  cases bs with
  | nil => intro _ h; cases h
  | cons _ _ => exact req_align_of_rustAllocEvents (al := 1) hlen (by decide)

theorem req_align_optBytesDealloc {bs : List (BitVec 8)} {maxReq : Nat} :
    ∀ ev ∈ (if bs.isEmpty then ([] : List AllocEvent) else rustDeallocEvents bs.length 1),
      eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  cases bs with
  | nil => intro _ h; cases h
  | cons _ _ => exact req_align_of_rustDeallocEvents (al := 1) (by decide)

/-! ## `computeMacEvents` Credit & Cancellation -/

theorem req_align_computeMac {maxReq : Nat} (h33 : 33 ≤ maxReq) :
    ∀ ev ∈ computeMacEvents, eventStepReq ev ≤ maxReq ∧ eventStepAlign ev ≤ 16 := by
  intro ev hev
  unfold computeMacEvents publicKeySerializeEvents at hev
  simp only [List.mem_append] at hev
  rcases hev with ((h1 | h2) | (h3 | h4))
  · exact req_align_of_rustAllocEvents h33 (by decide) ev h1
  · exact req_align_of_rustDeallocEvents (al := 1) (by decide) ev h2
  · exact req_align_of_rustAllocEvents h33 (by decide) ev h3
  · exact req_align_of_rustDeallocEvents (al := 1) (by decide) ev h4

theorem stepEvents_computeMac (M : AllocCostModel) [HasFineReallocCredit M] (st : M.σ) :
    HasFineReallocCredit.cumSmall (M.stepEvents computeMacEvents st) ≤
      HasFineReallocCredit.cumSmall st + 2 * bytesCumAlloc M 33 ∧
    HasFineReallocCredit.liveLarge (M.stepEvents computeMacEvents st) ≤
      HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge (M.stepEvents computeMacEvents st) ≤
      max (HasFineReallocCredit.peakLarge st)
          (HasFineReallocCredit.liveLarge st + bytesLargeLive M 33) := by
  unfold computeMacEvents publicKeySerializeEvents
  simp only [AllocCostModel.stepEvents_append]
  have h1 := stepEvents_rustAlloc_pos M (req := 33) (al := 1) (by decide) (by decide) st
  set s1 := M.stepEvents (rustAllocEvents 33 1) st
  have h2 := stepEvents_rustDealloc_any M 33 1 (by decide) s1
  set s2 := M.stepEvents (rustDeallocEvents 33 1) s1
  have h3 := stepEvents_rustAlloc_pos M (req := 33) (al := 1) (by decide) (by decide) s2
  set s3 := M.stepEvents (rustAllocEvents 33 1) s2
  have h4 := stepEvents_rustDealloc_any M 33 1 (by decide) s3
  exact ⟨by omega, by omega, by omega⟩

/-! ## `<SignalMessage>::new` (`SignalMessageNewEnv`) Fine-Credit Bounds -/

/-- Exact serialized byte length allocated by `<SignalMessage>::new`. -/
def signalMessageNewSerLen (parse : UuidParser) (x : SignalMessageNewGhost) : Nat :=
  (encode (x.protoMsg parse)).length + 9

/-- Symbolic `cumSmall` bound for `SignalMessageNewEnv parse x`. -/
def signalMessageNewCum (M : AllocCostModel) [HasFineReallocCredit M]
    (parse : UuidParser) (x : SignalMessageNewGhost) : Nat :=
  (if (x.addresses parse).isSome then bytesCumAlloc M 36 else 0) +
    3 * bytesCumAlloc M 33 +
    2 * bytesCumAlloc M x.ciphertext.length +
    2 * bytesCumAlloc M x.pqRatchet.length +
    bytesCumAlloc M (signalMessageNewSerLen parse x)

/-- Symbolic post-call `liveLarge` increment for `SignalMessageNewEnv parse x`
(temporary `rk` 33 B, `ciphertext`, and `pqRatchet` copies cancel in the epilogue). -/
def signalMessageNewLive (M : AllocCostModel) [HasFineReallocCredit M]
    (parse : UuidParser) (x : SignalMessageNewGhost) : Nat :=
  (if (x.addresses parse).isSome then bytesLargeLive M 36 else 0) +
    bytesLargeLive M x.ciphertext.length +
    bytesLargeLive M x.pqRatchet.length +
    bytesLargeLive M (signalMessageNewSerLen parse x)

/-- Symbolic transient `peakLarge` increment for `SignalMessageNewEnv parse x`. -/
def signalMessageNewPeak (M : AllocCostModel) [HasFineReallocCredit M]
    (parse : UuidParser) (x : SignalMessageNewGhost) : Nat :=
  (if (x.addresses parse).isSome then bytesLargeLive M 36 else 0) +
    2 * bytesLargeLive M 33 +
    2 * bytesLargeLive M x.ciphertext.length +
    2 * bytesLargeLive M x.pqRatchet.length +
    bytesLargeLive M (signalMessageNewSerLen parse x)

/-- Maximum single-event request size in `SignalMessageNewEnv parse x`. -/
def signalMessageNewMaxReq (parse : UuidParser) (x : SignalMessageNewGhost) : Nat :=
  max (max 36 x.ciphertext.length) (max x.pqRatchet.length (signalMessageNewSerLen parse x))

theorem req_align_signalMessageNew (parse : UuidParser) (x : SignalMessageNewGhost)
    {evs : List AllocEvent} (hEnv : SignalMessageNewEnv parse x evs) :
    ∀ ev ∈ evs,
      eventStepReq ev ≤ signalMessageNewMaxReq parse x ∧ eventStepAlign ev ≤ 16 := by
  rw [hEnv]
  intro ev hev
  unfold signalMessageNewEvents publicKeySerializeEvents at hev
  simp only [List.mem_append] at hev
  have h36 : 36 ≤ signalMessageNewMaxReq parse x := by unfold signalMessageNewMaxReq; omega
  have h33 : 33 ≤ signalMessageNewMaxReq parse x := by unfold signalMessageNewMaxReq; omega
  have hct : x.ciphertext.length ≤ signalMessageNewMaxReq parse x := by
    unfold signalMessageNewMaxReq; omega
  have hpq : x.pqRatchet.length ≤ signalMessageNewMaxReq parse x := by
    unfold signalMessageNewMaxReq; omega
  have hser : (encode (x.protoMsg parse)).length + 9 ≤ signalMessageNewMaxReq parse x := by
    unfold signalMessageNewMaxReq signalMessageNewSerLen; omega
  rcases hev with ((((((((((h1 | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9) | h10) | h11)
  · split at h1
    · exact req_align_of_rustAllocEvents h36 (by decide) ev h1
    · cases h1
  · exact req_align_of_rustAllocEvents h33 (by decide) ev h2
  · exact req_align_optBytesAlloc hct ev h3
  · exact req_align_optBytesAlloc hpq ev h4
  · exact req_align_of_rustAllocEvents hser (by decide) ev h5
  · exact req_align_computeMac h33 ev h6
  · exact req_align_optBytesAlloc hct ev h7
  · exact req_align_optBytesAlloc hpq ev h8
  · exact req_align_of_rustDeallocEvents (al := 1) (by decide) ev h9
  · exact req_align_optBytesDealloc ev h10
  · exact req_align_optBytesDealloc ev h11

theorem credit_signalMessageNew (M : AllocCostModel) [HasFineReallocCredit M]
    (parse : UuidParser) (x : SignalMessageNewGhost) (st0 : M.σ)
    {evs : List AllocEvent} (hEnv : SignalMessageNewEnv parse x evs) :
    HasFineReallocCredit.cumSmall (M.stepEvents evs st0) ≤
      HasFineReallocCredit.cumSmall st0 + signalMessageNewCum M parse x ∧
    HasFineReallocCredit.liveLarge (M.stepEvents evs st0) ≤
      HasFineReallocCredit.liveLarge st0 + signalMessageNewLive M parse x ∧
    HasFineReallocCredit.peakLarge (M.stepEvents evs st0) ≤
      max (HasFineReallocCredit.peakLarge st0)
          (HasFineReallocCredit.liveLarge st0 + signalMessageNewPeak M parse x) := by
  rw [hEnv]
  unfold signalMessageNewEvents publicKeySerializeEvents
  simp only [AllocCostModel.stepEvents_append]
  set e1 := if (x.addresses parse).isSome then rustAllocEvents 36 1 else []
  set serLen := (encode (x.protoMsg parse)).length + 9 with hser_eq
  set s1 := M.stepEvents e1 st0
  have h1 :
      HasFineReallocCredit.cumSmall s1 ≤
        HasFineReallocCredit.cumSmall st0 +
          (if (x.addresses parse).isSome then bytesCumAlloc M 36 else 0) ∧
      HasFineReallocCredit.liveLarge s1 ≤
        HasFineReallocCredit.liveLarge st0 +
          (if (x.addresses parse).isSome then bytesLargeLive M 36 else 0) ∧
      HasFineReallocCredit.peakLarge s1 ≤
        max (HasFineReallocCredit.peakLarge st0)
            (HasFineReallocCredit.liveLarge st0 +
              (if (x.addresses parse).isSome then bytesLargeLive M 36 else 0)) := by
    dsimp only [s1, e1]
    cases (x.addresses parse).isSome
    · simp [AllocCostModel.stepEvents]
    · simp only [↓reduceIte]
      exact stepEvents_rustAlloc_pos M (req := 36) (al := 1) (by decide) (by decide) st0
  have h2 := stepEvents_rustAlloc_pos M (req := 33) (al := 1) (by decide) (by decide) s1
  set s2 := M.stepEvents (rustAllocEvents 33 1) s1
  have h3 := stepEvents_optBytesAlloc M x.ciphertext s2
  set s3 := M.stepEvents (if x.ciphertext.isEmpty then [] else rustAllocEvents x.ciphertext.length 1) s2
  have h4 := stepEvents_optBytesAlloc M x.pqRatchet s3
  set s4 := M.stepEvents (if x.pqRatchet.isEmpty then [] else rustAllocEvents x.pqRatchet.length 1) s3
  have h5 := stepEvents_rustAlloc_pos M (req := serLen) (al := 1) (by decide) (by omega) s4
  set s5 := M.stepEvents (rustAllocEvents serLen 1) s4
  have h6 := stepEvents_computeMac M s5
  set s6 := M.stepEvents computeMacEvents s5
  have h7 := stepEvents_optBytesAlloc M x.ciphertext s6
  set s7 := M.stepEvents (if x.ciphertext.isEmpty then [] else rustAllocEvents x.ciphertext.length 1) s6
  have h8 := stepEvents_optBytesAlloc M x.pqRatchet s7
  set s8 := M.stepEvents (if x.pqRatchet.isEmpty then [] else rustAllocEvents x.pqRatchet.length 1) s7
  have h9 := stepEvents_rustDealloc_any M 33 1 (by decide) s8
  set s9 := M.stepEvents (rustDeallocEvents 33 1) s8
  have h10 := stepEvents_optBytesDealloc M x.ciphertext s9
  set s10 := M.stepEvents (if x.ciphertext.isEmpty then [] else rustDeallocEvents x.ciphertext.length 1) s9
  have h11 := stepEvents_optBytesDealloc M x.pqRatchet s10
  unfold signalMessageNewCum signalMessageNewLive signalMessageNewPeak signalMessageNewSerLen
  rw [← hser_eq]
  exact ⟨by omega, by omega, by omega⟩

/-! ## `<PreKeySignalMessage>::new` Fine-Credit Bounds -/

/-- Prologue Kyber ciphertext copy events in `PreKeySignalMessage::new` (mirrors `kyberDeallocEvs`). -/
def kyberCopyEvs (kp : Option KyberPayload) : List AllocEvent :=
  match kp with
  | none => []
  | some k =>
    if k.ciphertext = [] then []
    else rustAllocEvents k.ciphertext.length 1

/-- Byte length of optional Kyber ciphertext in `PreKeyMsgNewCall`. -/
def kyberPayloadLen : Option KyberPayload → Nat
  | none => 0
  | some k => k.ciphertext.length

/-- Exact 9-segment allocator event list of `PreKeySignalMessage::new`
(`FieldsEpilogueDeallocBudget.lean:66–71,495–497`). -/
def preKeyMsgNewEvents (x : PreKeyMsgNewCall) : List AllocEvent :=
  kyberCopyEvs x.kp ++
    (rustAllocEvents 33 1 ++ rustAllocEvents 33 1) ++
    rustAllocEvents x.msg.serialized.length 1 ++
    rustAllocEvents x.model.serialized.length 1 ++
    kyberDeallocEvs x.kp ++
    (rustDeallocEvents 33 1 ++ rustDeallocEvents 33 1) ++
    rustDeallocEvents x.msg.serialized.length 1

/-- Maximum single-event request size in `preKeyMsgNewEvents x`. -/
def preKeyMsgNewMaxReq (x : PreKeyMsgNewCall) : Nat :=
  max (max (kyberPayloadLen x.kp) 33)
      (max x.msg.serialized.length x.model.serialized.length)

theorem stepEvents_kyberCopyEvs (M : AllocCostModel) [HasFineReallocCredit M]
    (kp : Option KyberPayload) (st : M.σ) :
    HasFineReallocCredit.cumSmall (M.stepEvents (kyberCopyEvs kp) st) ≤
      HasFineReallocCredit.cumSmall st + bytesCumAlloc M (kyberPayloadLen kp) ∧
    HasFineReallocCredit.liveLarge (M.stepEvents (kyberCopyEvs kp) st) ≤
      HasFineReallocCredit.liveLarge st + bytesLargeLive M (kyberPayloadLen kp) ∧
    HasFineReallocCredit.peakLarge (M.stepEvents (kyberCopyEvs kp) st) ≤
      max (HasFineReallocCredit.peakLarge st)
          (HasFineReallocCredit.liveLarge st + bytesLargeLive M (kyberPayloadLen kp)) := by
  cases kp with
  | none => simp [kyberCopyEvs, kyberPayloadLen, AllocCostModel.stepEvents]
  | some k =>
    dsimp only [kyberCopyEvs, kyberPayloadLen]
    cases hct : k.ciphertext with
    | nil => simp [AllocCostModel.stepEvents]
    | cons _ tl =>
      simp only [reduceCtorEq, ↓reduceIte, List.length_cons]
      exact stepEvents_rustAlloc_pos M (al := 1) (by decide) (Nat.succ_pos tl.length) st

theorem stepEvents_kyberDeallocEvs (M : AllocCostModel) [HasFineReallocCredit M]
    (kp : Option KyberPayload) (st : M.σ) :
    HasFineReallocCredit.cumSmall (M.stepEvents (kyberDeallocEvs kp) st) ≤
      HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge (M.stepEvents (kyberDeallocEvs kp) st) ≤
      HasFineReallocCredit.liveLarge st - bytesLargeLive M (kyberPayloadLen kp) ∧
    HasFineReallocCredit.peakLarge (M.stepEvents (kyberDeallocEvs kp) st) ≤
      HasFineReallocCredit.peakLarge st := by
  cases kp with
  | none => simp [kyberDeallocEvs, kyberPayloadLen, AllocCostModel.stepEvents]
  | some k =>
    dsimp only [kyberDeallocEvs, kyberPayloadLen]
    cases hct : k.ciphertext with
    | nil => simp [AllocCostModel.stepEvents]
    | cons _ _ =>
      simp only [reduceCtorEq, ↓reduceIte, List.length_cons]
      exact stepEvents_rustDealloc_any M _ 1 (by decide) st

theorem req_align_preKeyMsgNew (x : PreKeyMsgNewCall) :
    ∀ ev ∈ preKeyMsgNewEvents x,
      eventStepReq ev ≤ preKeyMsgNewMaxReq x ∧ eventStepAlign ev ≤ 16 := by
  intro ev hev
  unfold preKeyMsgNewEvents at hev
  simp only [List.mem_append] at hev
  have hky : kyberPayloadLen x.kp ≤ preKeyMsgNewMaxReq x := by unfold preKeyMsgNewMaxReq; omega
  have h33 : 33 ≤ preKeyMsgNewMaxReq x := by unfold preKeyMsgNewMaxReq; omega
  have hmsg : x.msg.serialized.length ≤ preKeyMsgNewMaxReq x := by unfold preKeyMsgNewMaxReq; omega
  have hmod : x.model.serialized.length ≤ preKeyMsgNewMaxReq x := by unfold preKeyMsgNewMaxReq; omega
  rcases hev with ((((((h1 | (h2 | h3)) | h4) | h5) | h6) | (h7 | h8)) | h9)
  · cases hkp : x.kp with
    | none => simp [hkp, kyberCopyEvs] at h1
    | some k =>
      simp only [hkp, kyberCopyEvs] at h1
      simp only [hkp, kyberPayloadLen] at hky
      split at h1
      · cases h1
      · exact req_align_of_rustAllocEvents hky (by decide) ev h1
  · exact req_align_of_rustAllocEvents h33 (by decide) ev h2
  · exact req_align_of_rustAllocEvents h33 (by decide) ev h3
  · exact req_align_of_rustAllocEvents hmsg (by decide) ev h4
  · exact req_align_of_rustAllocEvents hmod (by decide) ev h5
  · cases hkp : x.kp with
    | none => simp [hkp, kyberDeallocEvs] at h6
    | some k =>
      simp only [hkp, kyberDeallocEvs] at h6
      split at h6
      · cases h6
      · exact req_align_of_rustDeallocEvents (al := 1) (by decide) ev h6
  · exact req_align_of_rustDeallocEvents (al := 1) (by decide) ev h7
  · exact req_align_of_rustDeallocEvents (al := 1) (by decide) ev h8
  · exact req_align_of_rustDeallocEvents (al := 1) (by decide) ev h9

theorem credit_preKeyMsgNew {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (x : PreKeyMsgNewCall) (st0 : M.σ) :
    HasFineReallocCredit.cumSmall (M.stepEvents (preKeyMsgNewEvents x) st0) ≤
      HasFineReallocCredit.cumSmall st0 +
        (2 * kyberPayloadLen x.kp + 2 * x.msg.serialized.length +
          2 * x.model.serialized.length + 47827) ∧
    HasFineReallocCredit.liveLarge (M.stepEvents (preKeyMsgNewEvents x) st0) ≤
      HasFineReallocCredit.liveLarge st0 + (x.model.serialized.length + 8195) ∧
    HasFineReallocCredit.peakLarge (M.stepEvents (preKeyMsgNewEvents x) st0) ≤
      max (HasFineReallocCredit.peakLarge st0)
          (HasFineReallocCredit.liveLarge st0 +
            (kyberPayloadLen x.kp + x.msg.serialized.length +
              x.model.serialized.length + 41041)) := by
  unfold preKeyMsgNewEvents
  simp only [AllocCostModel.stepEvents_append]
  have h1 := stepEvents_kyberCopyEvs M x.kp st0
  set s1 := M.stepEvents (kyberCopyEvs x.kp) st0
  have h2 := stepEvents_rustAlloc_aff hM 33 1 (by decide) s1
  set s2 := M.stepEvents (rustAllocEvents 33 1) s1
  have h3 := stepEvents_rustAlloc_aff hM 33 1 (by decide) s2
  set s3 := M.stepEvents (rustAllocEvents 33 1) s2
  have h4 := stepEvents_rustAlloc_aff hM x.msg.serialized.length 1 (by decide) s3
  set s4 := M.stepEvents (rustAllocEvents x.msg.serialized.length 1) s3
  have h5 := stepEvents_rustAlloc_aff hM x.model.serialized.length 1 (by decide) s4
  set s5 := M.stepEvents (rustAllocEvents x.model.serialized.length 1) s4
  have h6 := stepEvents_kyberDeallocEvs M x.kp s5
  set s6 := M.stepEvents (kyberDeallocEvs x.kp) s5
  have h7 := stepEvents_rustDealloc_any M 33 1 (by decide) s6
  set s7 := M.stepEvents (rustDeallocEvents 33 1) s6
  have h8 := stepEvents_rustDealloc_any M 33 1 (by decide) s7
  set s8 := M.stepEvents (rustDeallocEvents 33 1) s7
  have h9 := stepEvents_rustDealloc_any M x.msg.serialized.length 1 (by decide) s8
  have hc_ky := bytesCumAlloc_le_aff hM (kyberPayloadLen x.kp)
  have hl_ky := bytesLargeLive_le_aff hM (kyberPayloadLen x.kp)
  have hl_33 := bytesLargeLive_le_aff hM 33
  have hl_msg := bytesLargeLive_le_aff hM x.msg.serialized.length
  have hl_mod := bytesLargeLive_le_aff hM x.model.serialized.length
  exact ⟨by omega, by omega, by omega⟩

theorem phaseCredit_signalMessageNew {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (parse : UuidParser) (x : SignalMessageNewGhost) :
    PhaseCreditSpec M (SignalMessageNewEnv parse x)
      (4 * x.ciphertext.length + 4 * x.pqRatchet.length +
        2 * signalMessageNewSerLen parse x + 86121)
      (x.ciphertext.length + x.pqRatchet.length + signalMessageNewSerLen parse x + 32816)
      (2 * x.ciphertext.length + 2 * x.pqRatchet.length + signalMessageNewSerLen parse x + 65662)
      (signalMessageNewMaxReq parse x) where
  req_align _ hE := req_align_signalMessageNew parse x hE
  credit_le st0 {_} hE := by
    obtain ⟨hc, hl, hp⟩ := credit_signalMessageNew M parse x st0 hE
    have hc36 := bytesCumAlloc_le_aff hM 36
    have hc33 := bytesCumAlloc_le_aff hM 33
    have hc_ct := bytesCumAlloc_le_aff hM x.ciphertext.length
    have hc_pq := bytesCumAlloc_le_aff hM x.pqRatchet.length
    have hc_ser := bytesCumAlloc_le_aff hM (signalMessageNewSerLen parse x)
    have hl36 := bytesLargeLive_le_aff hM 36
    have hl33 := bytesLargeLive_le_aff hM 33
    have hl_ct := bytesLargeLive_le_aff hM x.ciphertext.length
    have hl_pq := bytesLargeLive_le_aff hM x.pqRatchet.length
    have hl_ser := bytesLargeLive_le_aff hM (signalMessageNewSerLen parse x)
    unfold signalMessageNewCum at hc
    unfold signalMessageNewLive at hl
    unfold signalMessageNewPeak at hp
    cases h : (x.addresses parse).isSome <;>
      simp only [h, Bool.false_eq_true, ↓reduceIte] at hc hl hp <;>
      exact ⟨by omega, by omega, by omega⟩

theorem phaseCredit_preKeyMsgNew {M : AllocCostModel} [HasFineReallocCredit M]
    (hM : ModelHyps M) (x : PreKeyMsgNewCall) :
    PhaseCreditSpec M (· = preKeyMsgNewEvents x)
      (2 * kyberPayloadLen x.kp + 2 * x.msg.serialized.length +
        2 * x.model.serialized.length + 47827)
      (x.model.serialized.length + 8195)
      (kyberPayloadLen x.kp + x.msg.serialized.length +
        x.model.serialized.length + 41041)
      (preKeyMsgNewMaxReq x) where
  req_align := by
    rintro _ rfl
    exact req_align_preKeyMsgNew x
  credit_le := by
    rintro st0 _ rfl
    exact credit_preKeyMsgNew hM x st0

end LibsignalBinary.Proofs.PeakBudget.WireSignalHelpers
