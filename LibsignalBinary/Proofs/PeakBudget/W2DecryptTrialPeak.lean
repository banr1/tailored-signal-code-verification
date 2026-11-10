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
public import LibsignalBinary.Proofs.PeakBudget.W2DecryptCmkDhPeak

/-!
# Segment 7/9 and `≤ 5`-Session Trial-Decrypt Loop Cancellation Helpers

Symbolic `[HasFineReallocCredit M]` peak and credit combinators for W2 `message_decrypt`:
Segment 7 (`compute_mac` + `serialize_addresses` + `23` B error string), Segment 9 small-allocation
lists and optional large deallocation cancellation, failed-trial `SessionClone` cancellation, and
multi-session (`≤ n`) trial-decrypt loop composition.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak

open LibsignalBinary.Heap (
  AllocCostModel AllocEvent rustAllocEvents rustDeallocEvents
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
  stepEvents_rustAlloc_small
  stepEvents_rustDealloc_large stepEvents_rustDealloc_small
)
open LibsignalBinary.Proofs.PeakBudget.W2DecryptLeavesPeak (
  singleAllocLarge stepEvents_rustAlloc_dealloc_cancel
)

/-! ## 1. W2 Segment 7 (`compute_mac` and `verify_mac`) Credit Bounds -/

/-- Events of `SignalMessage::compute_mac` (`2 × 33` B public-key serializations and deallocations).
-/
def computeMacEvs : List AllocEvent :=
  (rustAllocEvents 33 1 ++ rustDeallocEvents 33 1) ++
    (rustAllocEvents 33 1 ++ rustDeallocEvents 33 1)

theorem stepEvents_computeMac_small (M : AllocCostModel) [HasFineReallocCredit M]
    (st : M.σ) (h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M) :
    let st' := M.stepEvents computeMacEvs st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + 2 * HasFineReallocCredit.smallAllocCost M 33 ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  dsimp only [computeMacEvs]
  rw [M.stepEvents_append, M.stepEvents_append, M.stepEvents_append]
  rcases stepEvents_rustAlloc_small M (req := 33) (al := 1) st (by decide) (by decide) h33 with
    ⟨hc1, hl1, hp1⟩
  rcases stepEvents_rustDealloc_small M (req := 33) (al := 1)
      (M.stepEvents (rustAllocEvents 33 1) st) (by decide) h33 with ⟨hc2, hl2, hp2⟩
  let stMid := M.stepEvents (rustDeallocEvents 33 1) (M.stepEvents (rustAllocEvents 33 1) st)
  rcases stepEvents_rustAlloc_small M (req := 33) (al := 1) stMid (by decide) (by decide) h33 with
    ⟨hc3, hl3, hp3⟩
  rcases stepEvents_rustDealloc_small M (req := 33) (al := 1)
      (M.stepEvents (rustAllocEvents 33 1) stMid) (by decide) h33 with ⟨hc4, hl4, hp4⟩
  dsimp only [stMid] at hc3 hl3 hp3 hc4 hl4 hp4
  exact ⟨by omega, by omega, by omega⟩

/-- Events of `verifyMacWithAddressesEvents`. -/
def vmacEvs (withAddr : Bool) : List AllocEvent :=
  if withAddr then
    computeMacEvs ++ (rustAllocEvents 36 1 ++ rustDeallocEvents 36 1)
  else
    computeMacEvs

/-- Events of Segment 7 (`vmacEvs withAddr` + optional `23` B error allocation). -/
def s7CoreEvs (withAddr errAlloc : Bool) : List AllocEvent :=
  vmacEvs withAddr ++ (if errAlloc then rustAllocEvents 23 1 else [])

theorem stepEvents_vmac_small (M : AllocCostModel) [HasFineReallocCredit M]
    (withAddr : Bool) (st : M.σ)
    (h36 : 36 ≤ HasFineReallocCredit.smallMaxReq M) :
    let st' := M.stepEvents (vmacEvs withAddr) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st +
        (2 * HasFineReallocCredit.smallAllocCost M 33 + HasFineReallocCredit.smallAllocCost M 36) ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  have h33 : 33 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  dsimp only [vmacEvs]
  cases withAddr
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases stepEvents_computeMac_small M st h33 with ⟨hc, hl, hp⟩
    exact ⟨by omega, hl, hp⟩
  · simp only [↓reduceIte]
    rw [M.stepEvents_append, M.stepEvents_append]
    rcases stepEvents_computeMac_small M st h33 with ⟨hc1, hl1, hp1⟩
    rcases stepEvents_rustAlloc_small M (req := 36) (al := 1)
        (M.stepEvents computeMacEvs st) (by decide) (by decide) h36 with ⟨hc2, hl2, hp2⟩
    rcases stepEvents_rustDealloc_small M (req := 36) (al := 1)
        (M.stepEvents (rustAllocEvents 36 1) (M.stepEvents computeMacEvs st))
        (by decide) h36 with ⟨hc3, hl3, hp3⟩
    exact ⟨by omega, by omega, by omega⟩

theorem stepEvents_s7Core_small (M : AllocCostModel) [HasFineReallocCredit M]
    (withAddr errAlloc : Bool) (st : M.σ)
    (h36 : 36 ≤ HasFineReallocCredit.smallMaxReq M) :
    let st' := M.stepEvents (s7CoreEvs withAddr errAlloc) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st +
        (2 * HasFineReallocCredit.smallAllocCost M 33 +
          HasFineReallocCredit.smallAllocCost M 36 +
          HasFineReallocCredit.smallAllocCost M 23) ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  have h23 : 23 ≤ HasFineReallocCredit.smallMaxReq M := by omega
  dsimp only [s7CoreEvs]
  rw [M.stepEvents_append]
  rcases stepEvents_vmac_small M withAddr st h36 with ⟨hc1, hl1, hp1⟩
  cases errAlloc
  · simp only [Bool.false_eq_true, ↓reduceIte, AllocCostModel.stepEvents_nil]
    exact ⟨by omega, hl1, hp1⟩
  · simp only [↓reduceIte]
    rcases stepEvents_rustAlloc_small M (req := 23) (al := 1)
        (M.stepEvents (vmacEvs withAddr) st) (by decide) (by decide) h23 with ⟨hc2, hl2, hp2⟩
    exact ⟨by omega, by omega, by omega⟩

/-! ## 2. Small-Allocation Lists and `sc = 63` Free Cancellation -/

def smallAllocListEvs : List Nat → List AllocEvent
  | [] => []
  | r :: rs => rustAllocEvents r 1 ++ smallAllocListEvs rs

def smallAllocListCum (M : AllocCostModel) [HasFineReallocCredit M] : List Nat → Nat
  | [] => 0
  | r :: rs => HasFineReallocCredit.smallAllocCost M r + smallAllocListCum M rs

/-- Credit bound for a sequence of small `align = 1` allocations (`0 < r ≤ smallMaxReq M`). -/
theorem stepEvents_smallAllocList (M : AllocCostModel) [HasFineReallocCredit M] :
    ∀ (reqs : List Nat) (st : M.σ),
      (∀ r ∈ reqs, 0 < r ∧ r ≤ HasFineReallocCredit.smallMaxReq M) →
      let st' := M.stepEvents (smallAllocListEvs reqs) st
      HasFineReallocCredit.cumSmall st' ≤
        HasFineReallocCredit.cumSmall st + smallAllocListCum M reqs ∧
      HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
      HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st
  | [], st, _ => by
    simp only [smallAllocListEvs, smallAllocListCum, AllocCostModel.stepEvents_nil, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  | r :: rs, st, hall => by
    dsimp only [smallAllocListEvs, smallAllocListCum]
    rw [M.stepEvents_append]
    obtain ⟨hpos, hle⟩ := hall r List.mem_cons_self
    rcases stepEvents_rustAlloc_small M (req := r) (al := 1) st (by decide) hpos hle with
      ⟨hc1, hl1, hp1⟩
    rcases stepEvents_smallAllocList M rs (M.stepEvents (rustAllocEvents r 1) st)
        (fun x hx => hall x (List.mem_cons_of_mem r hx)) with ⟨hc2, hl2, hp2⟩
    exact ⟨by omega, by omega, by omega⟩

/-- Optional `rustDeallocEvents req al` cancels `singleAllocLarge M req` from `liveLarge`. -/
theorem stepEvents_optDealloc_cancel_large (M : AllocCostModel) [HasFineReallocCredit M]
    {req al L₀ : Nat} (st : M.σ) (hal : al ≤ 16)
    (hlive : HasFineReallocCredit.liveLarge st ≤
      L₀ + (if req = 0 then 0 else singleAllocLarge M req)) :
    let evs := if req = 0 then [] else rustDeallocEvents req al
    let st' := M.stepEvents evs st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤ L₀ ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  dsimp only
  by_cases h0 : req = 0
  · subst h0
    simp only [↓reduceIte, AllocCostModel.stepEvents_nil, Nat.add_zero] at hlive ⊢
    exact ⟨Nat.le_refl _, hlive, Nat.le_refl _⟩
  · simp only [h0, ↓reduceIte] at hlive ⊢
    by_cases hle : req ≤ HasFineReallocCredit.smallMaxReq M
    · simp only [singleAllocLarge, hle, ↓reduceIte, Nat.add_zero] at hlive
      rcases stepEvents_rustDealloc_small M (req := req) (al := al) st hal hle with ⟨hc, hl, hp⟩
      exact ⟨hc, by omega, hp⟩
    · have hgt : HasFineReallocCredit.smallMaxReq M < req := Nat.lt_of_not_ge hle
      simp only [singleAllocLarge, hle, ↓reduceIte] at hlive
      rcases stepEvents_rustDealloc_large M (req := req) (al := al) st hal hgt with ⟨hc, hl, hp⟩
      exact ⟨hc, by omega, hp⟩

def optDeallocListEvs : List (Nat × Nat) → List AllocEvent
  | [] => []
  | (req, al) :: rest =>
    (if req = 0 then [] else rustDeallocEvents req al) ++ optDeallocListEvs rest

def optDeallocListLarge (M : AllocCostModel) [HasFineReallocCredit M] : List (Nat × Nat) → Nat
  | [] => 0
  | (req, _) :: rest =>
    (if req = 0 then 0 else singleAllocLarge M req) + optDeallocListLarge M rest

/-- Multi-buffer `sc = 63` deallocation credit cancellation across `optDeallocListEvs pairs`. -/
theorem stepEvents_optDeallocList_cancel (M : AllocCostModel) [HasFineReallocCredit M] :
    ∀ (pairs : List (Nat × Nat)) {L₀ : Nat} (st : M.σ),
      (∀ p ∈ pairs, p.2 ≤ 16) →
      HasFineReallocCredit.liveLarge st ≤ L₀ + optDeallocListLarge M pairs →
      let st' := M.stepEvents (optDeallocListEvs pairs) st
      HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
      HasFineReallocCredit.liveLarge st' ≤ L₀ ∧
      HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st
  | [], _, st, _, hlive => by
    simp only [optDeallocListEvs, optDeallocListLarge, AllocCostModel.stepEvents_nil,
      Nat.add_zero] at hlive ⊢
    exact ⟨Nat.le_refl _, hlive, Nat.le_refl _⟩
  | (req, al) :: rest, L₀, st, hal_all, hlive => by
    dsimp only [optDeallocListEvs, optDeallocListLarge] at hlive ⊢
    rw [M.stepEvents_append]
    have hal : al ≤ 16 := hal_all (req, al) List.mem_cons_self
    have hlive_reassoc : HasFineReallocCredit.liveLarge st ≤
        (L₀ + optDeallocListLarge M rest) +
          (if req = 0 then 0 else singleAllocLarge M req) := by omega
    rcases stepEvents_optDealloc_cancel_large M (req := req) (al := al)
        (L₀ := L₀ + optDeallocListLarge M rest) st hal hlive_reassoc with ⟨hc1, hl1, hp1⟩
    rcases stepEvents_optDeallocList_cancel M rest (L₀ := L₀)
        _ (fun p hp => hal_all p (List.mem_cons_of_mem _ hp)) hl1 with ⟨hc2, hl2, hp2⟩
    exact ⟨by omega, hl2, by omega⟩

/-! ## 3. Single Failed-Trial Cancellation -/

/-- Composes `SessionClone`, failed `try_decrypt` (`Δlive = 0`), and `drop_clone` (`- ΔlClone`), restoring `Δlive = 0`.
-/
theorem stepEvents_failedTrial_cancel (M : AllocCostModel) [HasFineReallocCredit M]
    {evsClone evsTd evsDrop : List AllocEvent}
    {ΔcClone ΔlClone ΔpClone ΔcTd ΔpTd ΔcDrop ΔpDrop : Nat}
    (st0 : M.σ)
    (hClone :
      let st1 := M.stepEvents evsClone st0
      HasFineReallocCredit.cumSmall st1 ≤ HasFineReallocCredit.cumSmall st0 + ΔcClone ∧
      HasFineReallocCredit.liveLarge st1 ≤ HasFineReallocCredit.liveLarge st0 + ΔlClone ∧
      HasFineReallocCredit.peakLarge st1 ≤
        max (HasFineReallocCredit.peakLarge st0)
          (HasFineReallocCredit.liveLarge st0 + ΔpClone))
    (hTd : ∀ st1 : M.σ,
      let st2 := M.stepEvents evsTd st1
      HasFineReallocCredit.cumSmall st2 ≤ HasFineReallocCredit.cumSmall st1 + ΔcTd ∧
      HasFineReallocCredit.liveLarge st2 ≤ HasFineReallocCredit.liveLarge st1 ∧
      HasFineReallocCredit.peakLarge st2 ≤
        max (HasFineReallocCredit.peakLarge st1)
          (HasFineReallocCredit.liveLarge st1 + ΔpTd))
    (hDrop : ∀ st2 : M.σ,
      HasFineReallocCredit.liveLarge st2 ≤ HasFineReallocCredit.liveLarge st0 + ΔlClone →
      let st3 := M.stepEvents evsDrop st2
      HasFineReallocCredit.cumSmall st3 ≤ HasFineReallocCredit.cumSmall st2 + ΔcDrop ∧
      HasFineReallocCredit.liveLarge st3 ≤ HasFineReallocCredit.liveLarge st0 ∧
      HasFineReallocCredit.peakLarge st3 ≤
        max (HasFineReallocCredit.peakLarge st2)
          (HasFineReallocCredit.liveLarge st0 + ΔpDrop)) :
    let st3 := M.stepEvents (evsClone ++ evsTd ++ evsDrop) st0
    HasFineReallocCredit.cumSmall st3 ≤
      HasFineReallocCredit.cumSmall st0 + (ΔcClone + ΔcTd + ΔcDrop) ∧
    HasFineReallocCredit.liveLarge st3 ≤ HasFineReallocCredit.liveLarge st0 ∧
    HasFineReallocCredit.peakLarge st3 ≤
      max (HasFineReallocCredit.peakLarge st0)
        (HasFineReallocCredit.liveLarge st0 + max ΔpClone (max (ΔlClone + ΔpTd) ΔpDrop)) := by
  dsimp only
  rw [M.stepEvents_append, M.stepEvents_append]
  rcases hClone with ⟨hc1, hl1, hp1⟩
  rcases hTd (M.stepEvents evsClone st0) with ⟨hc2, hl2, hp2⟩
  have hl2' : HasFineReallocCredit.liveLarge (M.stepEvents evsTd (M.stepEvents evsClone st0)) ≤
      HasFineReallocCredit.liveLarge st0 + ΔlClone := by omega
  rcases hDrop (M.stepEvents evsTd (M.stepEvents evsClone st0)) hl2' with ⟨hc3, hl3, hp3⟩
  exact ⟨by omega, hl3, by omega⟩

/-! ## 4. Multi-Session (`≤ 5`) Trial-Decrypt Loop Composition -/

/-- Sequential composition of `evsList` failed session trials (`Δlive = 0` each), keeping `peakLarge` at `1×`.
-/
theorem stepEvents_failedTrials_seq (M : AllocCostModel) [HasFineReallocCredit M]
    {ΔcFail ΔpFail : Nat} :
    ∀ (evsList : List (List AllocEvent)) (st0 : M.σ),
      (∀ evs ∈ evsList, ∀ st : M.σ,
        HasFineReallocCredit.cumSmall (M.stepEvents evs st) ≤
          HasFineReallocCredit.cumSmall st + ΔcFail ∧
        HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤
          HasFineReallocCredit.liveLarge st ∧
        HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤
          max (HasFineReallocCredit.peakLarge st)
            (HasFineReallocCredit.liveLarge st + ΔpFail)) →
      let st' := M.stepEvents evsList.flatten st0
      HasFineReallocCredit.cumSmall st' ≤
        HasFineReallocCredit.cumSmall st0 + evsList.length * ΔcFail ∧
      HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st0 ∧
      HasFineReallocCredit.peakLarge st' ≤
        max (HasFineReallocCredit.peakLarge st0)
          (HasFineReallocCredit.liveLarge st0 + ΔpFail)
  | [], st0, _ => by
    simp only [List.flatten_nil, AllocCostModel.stepEvents_nil, List.length_nil,
      Nat.zero_mul, Nat.add_zero]
    exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _⟩
  | evs :: rest, st0, hall => by
    simp only [List.flatten_cons, List.length_cons]
    rw [M.stepEvents_append]
    rcases hall evs List.mem_cons_self st0 with ⟨hc1, hl1, hp1⟩
    rcases stepEvents_failedTrials_seq M rest (M.stepEvents evs st0)
        (fun e he => hall e (List.mem_cons_of_mem evs he)) with ⟨hc2, hl2, hp2⟩
    have hmul : (rest.length + 1) * ΔcFail = ΔcFail + rest.length * ΔcFail := by
      rw [Nat.succ_mul, Nat.add_comm]
    exact ⟨by omega, by omega, by omega⟩

/-- Composes `evsList` failed session trials (`evsList.length + 1 ≤ n`) with a final trial `evsLast`.
-/
theorem stepEvents_trialLoop_with_final (M : AllocCostModel) [HasFineReallocCredit M]
    {n ΔcFail ΔpFail ΔcLast ΔlLast ΔpLast : Nat}
    (evsList : List (List AllocEvent)) (evsLast : List AllocEvent) (st0 : M.σ)
    (hlen : evsList.length + 1 ≤ n)
    (hFail : ∀ evs ∈ evsList, ∀ st : M.σ,
      HasFineReallocCredit.cumSmall (M.stepEvents evs st) ≤
        HasFineReallocCredit.cumSmall st + ΔcFail ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evs st) ≤
        HasFineReallocCredit.liveLarge st ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evs st) ≤
        max (HasFineReallocCredit.peakLarge st)
          (HasFineReallocCredit.liveLarge st + ΔpFail))
    (hLast : ∀ st : M.σ,
      HasFineReallocCredit.cumSmall (M.stepEvents evsLast st) ≤
        HasFineReallocCredit.cumSmall st + ΔcLast ∧
      HasFineReallocCredit.liveLarge (M.stepEvents evsLast st) ≤
        HasFineReallocCredit.liveLarge st + ΔlLast ∧
      HasFineReallocCredit.peakLarge (M.stepEvents evsLast st) ≤
        max (HasFineReallocCredit.peakLarge st)
          (HasFineReallocCredit.liveLarge st + ΔpLast)) :
    let st' := M.stepEvents (evsList.flatten ++ evsLast) st0
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st0 + ((n - 1) * ΔcFail + ΔcLast) ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st0 + ΔlLast ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st0)
        (HasFineReallocCredit.liveLarge st0 + max ΔpFail ΔpLast) := by
  dsimp only
  rw [M.stepEvents_append]
  rcases stepEvents_failedTrials_seq M evsList st0 hFail with ⟨hc1, hl1, hp1⟩
  rcases hLast (M.stepEvents evsList.flatten st0) with ⟨hc2, hl2, hp2⟩
  have hk_le : evsList.length ≤ n - 1 := by omega
  have hcmul : evsList.length * ΔcFail ≤ (n - 1) * ΔcFail :=
    Nat.mul_le_mul_right _ hk_le
  exact ⟨by omega, by omega, by omega⟩

end LibsignalBinary.Proofs.PeakBudget.W2DecryptTrialPeak
