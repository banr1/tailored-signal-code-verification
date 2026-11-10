/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget

/-!
# Parametric Fine-Model Reallocation and Deallocation Credit Interface

Defines the symbolic `HasFineReallocCredit (M : AllocCostModel)` typeclass over `AllocCostModel`:
* Symbolic thresholds and cost projections (`smallMaxReq`, `smallAllocCost`, `smallReallocCost`,
  `largeCost`, `largeMetaCost`, `baseFine`).
* Saturating `Nat`-subtraction `liveLarge` credit inequalities on `realloc` and `free` transitions.
* `fitsStep_of_fine_bounds` reducing `FitsStep` (`2 * stepB`) to bounds on `cumSmall`, `liveLarge`,
  and `peakLarge`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit

open Arm64 ProofLib
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits FitsStep FitsEvent FitsEvents
  rustAllocEvents rustDeallocEvents rustReallocEvents
)

/-- Symbolic fine-model credit interface over `M : AllocCostModel`, separating cumulative
small-class charges (`cumSmall`), currently live large-allocation bytes (`liveLarge`, credited back
on `.free` and `.realloc`), and historical peak large-allocation bytes (`peakLarge`). -/
class HasFineReallocCredit (M : AllocCostModel) where
  /-- Largest request byte size treated by `M` as a small-class allocation (`req ≤ smallMaxReq`). -/
  smallMaxReq : Nat
  /-- Upper bound on the `cumSmall` charge of a small `.alloc` or `al ≤ 16` `.aligned` event. -/
  smallAllocCost : Nat → Nat
  /-- Upper bound on the `cumSmall` charge of a small-target `al ≤ 16` `.realloc` event. -/
  smallReallocCost : Nat → Nat
  /-- Direct-`mmap` byte weight tracked in `liveLarge` / `peakLarge` for `req > smallMaxReq`. -/
  largeCost : Nat → Nat
  /-- Metadata charge added to `cumSmall` on a large-allocating event (`> smallMaxReq`). -/
  largeMetaCost : Nat
  /-- Constant base overhead term in `M.footprint st`. -/
  baseFine : Nat
  /-- Cumulative small-class and metadata footprint component at state `st`. -/
  cumSmall : M.σ → Nat
  /-- Currently live large-allocation byte component at state `st`. -/
  liveLarge : M.σ → Nat
  /-- Historical peak of `liveLarge` up to state `st`. -/
  peakLarge : M.σ → Nat
  /-- Total mapped-footprint bound in terms of `baseFine`, `cumSmall`, `liveLarge`, and `peakLarge`. -/
  footprint_le : ∀ st : M.σ,
    M.footprint st ≤ baseFine + cumSmall st + max (liveLarge st) (peakLarge st)
  /-- Initial `cumSmall` at `M.init`. -/
  cumSmall_init : cumSmall M.init = 0
  /-- Initial `liveLarge` at `M.init`. -/
  liveLarge_init : liveLarge M.init = 0
  /-- Initial `peakLarge` at `M.init`. -/
  peakLarge_init : peakLarge M.init = 0
  /-- Small `.alloc req` (`0 < req ≤ smallMaxReq`). -/
  step_alloc_small : ∀ {req : Nat} (st : M.σ),
    0 < req → req ≤ smallMaxReq →
    let st' := M.step (.alloc req) st
    cumSmall st' ≤ cumSmall st + smallAllocCost req ∧
    liveLarge st' ≤ liveLarge st ∧
    peakLarge st' ≤ peakLarge st
  /-- Large `.alloc req` (`smallMaxReq < req`). -/
  step_alloc_large : ∀ {req : Nat} (st : M.σ),
    smallMaxReq < req →
    let st' := M.step (.alloc req) st
    cumSmall st' ≤ cumSmall st + largeMetaCost ∧
    liveLarge st' ≤ liveLarge st + largeCost req ∧
    peakLarge st' ≤ max (peakLarge st) (liveLarge st + largeCost req)
  /-- Small `.aligned al req` (`al ≤ 16`, `0 < req ≤ smallMaxReq`). -/
  step_aligned_small : ∀ {al req : Nat} (st : M.σ),
    al ≤ 16 → 0 < req → req ≤ smallMaxReq →
    let st' := M.step (.aligned al req) st
    cumSmall st' ≤ cumSmall st + smallAllocCost req ∧
    liveLarge st' ≤ liveLarge st ∧
    peakLarge st' ≤ peakLarge st
  /-- Large `.aligned al req` (`al ≤ 16`, `smallMaxReq < req`). -/
  step_aligned_large : ∀ {al req : Nat} (st : M.σ),
    al ≤ 16 → smallMaxReq < req →
    let st' := M.step (.aligned al req) st
    cumSmall st' ≤ cumSmall st + largeMetaCost ∧
    liveLarge st' ≤ liveLarge st + largeCost req ∧
    peakLarge st' ≤ max (peakLarge st) (liveLarge st + largeCost req)
  /-- Quadrant S→S `.realloc al old new` (`al ≤ 16`, `0 < old ≤ smallMaxReq`, `0 < new ≤ smallMaxReq`). -/
  step_realloc_small_small : ∀ {al old new : Nat} (st : M.σ),
    al ≤ 16 → 0 < old → old ≤ smallMaxReq → 0 < new → new ≤ smallMaxReq →
    let st' := M.step (.realloc al old new) st
    cumSmall st' ≤ cumSmall st + smallReallocCost new ∧
    liveLarge st' ≤ liveLarge st ∧
    peakLarge st' ≤ peakLarge st
  /-- Quadrant S→L `.realloc al old new` (`al ≤ 16`, `0 < old ≤ smallMaxReq < new`). -/
  step_realloc_small_large : ∀ {al old new : Nat} (st : M.σ),
    al ≤ 16 → 0 < old → old ≤ smallMaxReq → smallMaxReq < new →
    let st' := M.step (.realloc al old new) st
    cumSmall st' ≤ cumSmall st + largeMetaCost ∧
    liveLarge st' ≤ liveLarge st + largeCost new ∧
    peakLarge st' ≤ max (peakLarge st) (liveLarge st + largeCost new)
  /-- Quadrant L→L `.realloc al old new` (`al ≤ 16`, `smallMaxReq < old`, `smallMaxReq < new`),
  with transient overlap `liveLarge st + largeCost new` and post-step credit `- largeCost old`. -/
  step_realloc_large_large : ∀ {al old new : Nat} (st : M.σ),
    al ≤ 16 → smallMaxReq < old → smallMaxReq < new →
    let st' := M.step (.realloc al old new) st
    cumSmall st' ≤ cumSmall st + largeMetaCost ∧
    liveLarge st' ≤ (liveLarge st + largeCost new) - largeCost old ∧
    peakLarge st' ≤ max (peakLarge st) (liveLarge st + largeCost new)
  /-- Quadrant L→S `.realloc al old new` (`al ≤ 16`, `smallMaxReq < old`, `0 < new ≤ smallMaxReq`). -/
  step_realloc_large_small : ∀ {al old new : Nat} (st : M.σ),
    al ≤ 16 → smallMaxReq < old → 0 < new → new ≤ smallMaxReq →
    let st' := M.step (.realloc al old new) st
    cumSmall st' ≤ cumSmall st + smallReallocCost new ∧
    liveLarge st' ≤ liveLarge st - largeCost old ∧
    peakLarge st' ≤ peakLarge st
  /-- Small `.free al req` (`al ≤ 16`, `req ≤ smallMaxReq`). -/
  step_free_small : ∀ {al req : Nat} (st : M.σ),
    al ≤ 16 → req ≤ smallMaxReq →
    let st' := M.step (.free al req) st
    cumSmall st' ≤ cumSmall st ∧
    liveLarge st' ≤ liveLarge st ∧
    peakLarge st' ≤ peakLarge st
  /-- Large `.free al req` (`al ≤ 16`, `smallMaxReq < req`), crediting `largeCost req` back from `liveLarge`. -/
  step_free_large : ∀ {al req : Nat} (st : M.σ),
    al ≤ 16 → smallMaxReq < req →
    let st' := M.step (.free al req) st
    cumSmall st' ≤ cumSmall st ∧
    liveLarge st' ≤ liveLarge st - largeCost req ∧
    peakLarge st' ≤ peakLarge st

/-! ## `rustAllocEvents` / `rustDeallocEvents` / `rustReallocEvents` Dispatch Lemmas (`al ≤ 16`) -/

/-- Small `rustAllocEvents req al` (`al ≤ 16`, `0 < req ≤ smallMaxReq M`), covering both
`[.alloc req]` (`al ≤ req`) and `[.aligned (max al 8) req]` (`req < al`). -/
theorem stepEvents_rustAlloc_small (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (st : M.σ)
    (hal : al ≤ 16) (hpos : 0 < req) (hle : req ≤ HasFineReallocCredit.smallMaxReq M) :
    let st' := M.stepEvents (rustAllocEvents req al) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + HasFineReallocCredit.smallAllocCost M req ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  unfold rustAllocEvents
  split
  · exact HasFineReallocCredit.step_alloc_small st hpos hle
  · exact HasFineReallocCredit.step_aligned_small st (by omega) hpos hle

/-- Large `rustAllocEvents req al` (`al ≤ 16`, `smallMaxReq M < req`), covering both
`[.alloc req]` and `[.aligned (max al 8) req]`. -/
theorem stepEvents_rustAlloc_large (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (st : M.σ)
    (hal : al ≤ 16) (hgt : HasFineReallocCredit.smallMaxReq M < req) :
    let st' := M.stepEvents (rustAllocEvents req al) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + HasFineReallocCredit.largeMetaCost M ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st + HasFineReallocCredit.largeCost M req ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + HasFineReallocCredit.largeCost M req) := by
  unfold rustAllocEvents
  split
  · exact HasFineReallocCredit.step_alloc_large st hgt
  · exact HasFineReallocCredit.step_aligned_large st (by omega) hgt

/-- Small `rustDeallocEvents req al` (`al ≤ 16`, `req ≤ smallMaxReq M`). -/
theorem stepEvents_rustDealloc_small (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (st : M.σ)
    (hal : al ≤ 16) (hle : req ≤ HasFineReallocCredit.smallMaxReq M) :
    let st' := M.stepEvents (rustDeallocEvents req al) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st :=
  HasFineReallocCredit.step_free_small st hal hle

/-- Large `rustDeallocEvents req al` (`al ≤ 16`, `smallMaxReq M < req`). -/
theorem stepEvents_rustDealloc_large (M : AllocCostModel) [HasFineReallocCredit M]
    {req al : Nat} (st : M.σ)
    (hal : al ≤ 16) (hgt : HasFineReallocCredit.smallMaxReq M < req) :
    let st' := M.stepEvents (rustDeallocEvents req al) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st - HasFineReallocCredit.largeCost M req ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st :=
  HasFineReallocCredit.step_free_large st hal hgt

/-- Quadrant S→S `rustReallocEvents old new al` (`al ≤ 16`, `al ≤ new`). -/
theorem stepEvents_rustRealloc_small_small (M : AllocCostModel) [HasFineReallocCredit M]
    {old new al : Nat} (st : M.σ)
    (hal : al ≤ 16) (hal_new : al ≤ new)
    (hold_pos : 0 < old) (hold_le : old ≤ HasFineReallocCredit.smallMaxReq M)
    (hnew_pos : 0 < new) (hnew_le : new ≤ HasFineReallocCredit.smallMaxReq M) :
    let st' := M.stepEvents (rustReallocEvents old new al) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + HasFineReallocCredit.smallReallocCost M new ∧
    HasFineReallocCredit.liveLarge st' ≤ HasFineReallocCredit.liveLarge st ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  unfold rustReallocEvents
  simp only [hal, hal_new, and_self, ↓reduceIte]
  exact HasFineReallocCredit.step_realloc_small_small st hal hold_pos hold_le hnew_pos hnew_le

/-- Quadrant S→L `rustReallocEvents old new al` (`al ≤ 16`, `al ≤ new`). -/
theorem stepEvents_rustRealloc_small_large (M : AllocCostModel) [HasFineReallocCredit M]
    {old new al : Nat} (st : M.σ)
    (hal : al ≤ 16) (hal_new : al ≤ new)
    (hold_pos : 0 < old) (hold_le : old ≤ HasFineReallocCredit.smallMaxReq M)
    (hnew_gt : HasFineReallocCredit.smallMaxReq M < new) :
    let st' := M.stepEvents (rustReallocEvents old new al) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + HasFineReallocCredit.largeMetaCost M ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st + HasFineReallocCredit.largeCost M new ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + HasFineReallocCredit.largeCost M new) := by
  unfold rustReallocEvents
  simp only [hal, hal_new, and_self, ↓reduceIte]
  exact HasFineReallocCredit.step_realloc_small_large st hal hold_pos hold_le hnew_gt

/-- Quadrant L→L `rustReallocEvents old new al` (`al ≤ 16`, `al ≤ new`). -/
theorem stepEvents_rustRealloc_large_large (M : AllocCostModel) [HasFineReallocCredit M]
    {old new al : Nat} (st : M.σ)
    (hal : al ≤ 16) (hal_new : al ≤ new)
    (hold_gt : HasFineReallocCredit.smallMaxReq M < old)
    (hnew_gt : HasFineReallocCredit.smallMaxReq M < new) :
    let st' := M.stepEvents (rustReallocEvents old new al) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + HasFineReallocCredit.largeMetaCost M ∧
    HasFineReallocCredit.liveLarge st' ≤
      (HasFineReallocCredit.liveLarge st + HasFineReallocCredit.largeCost M new) -
        HasFineReallocCredit.largeCost M old ∧
    HasFineReallocCredit.peakLarge st' ≤
      max (HasFineReallocCredit.peakLarge st)
        (HasFineReallocCredit.liveLarge st + HasFineReallocCredit.largeCost M new) := by
  unfold rustReallocEvents
  simp only [hal, hal_new, and_self, ↓reduceIte]
  exact HasFineReallocCredit.step_realloc_large_large st hal hold_gt hnew_gt

/-- Quadrant L→S `rustReallocEvents old new al` (`al ≤ 16`, `al ≤ new`). -/
theorem stepEvents_rustRealloc_large_small (M : AllocCostModel) [HasFineReallocCredit M]
    {old new al : Nat} (st : M.σ)
    (hal : al ≤ 16) (hal_new : al ≤ new)
    (hold_gt : HasFineReallocCredit.smallMaxReq M < old)
    (hnew_pos : 0 < new) (hnew_le : new ≤ HasFineReallocCredit.smallMaxReq M) :
    let st' := M.stepEvents (rustReallocEvents old new al) st
    HasFineReallocCredit.cumSmall st' ≤
      HasFineReallocCredit.cumSmall st + HasFineReallocCredit.smallReallocCost M new ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st - HasFineReallocCredit.largeCost M old ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  unfold rustReallocEvents
  simp only [hal, hal_new, and_self, ↓reduceIte]
  exact HasFineReallocCredit.step_realloc_large_small st hal hold_gt hnew_pos hnew_le

/-! ## Fine-to-`FitsStep` `2 * stepB` Bridge -/

/-- Fine-to-`FitsStep` bridge (`2 * stepB` physical-RAM inequality):
reduces `FitsStep lim stepB (M.maxDynIvs st) (M.footprint st)` to explicit bounds on
`cumSmall st`, `liveLarge st`, and `peakLarge st` under
`lim.staticBytes + (baseFine + cumB + peakB) + 2 * stepB ≤ lim.physCap` and the 48-bit VA gap bound. -/
theorem fitsStep_of_fine_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    {lim : BudgetLimits} {st : M.σ} {stepB dynB cumB peakB : Nat}
    (henf : lim.enforced = true)
    (hdyn : M.maxDynIvs st ≤ dynB)
    (hcum : HasFineReallocCredit.cumSmall st ≤ cumB)
    (hlive : HasFineReallocCredit.liveLarge st ≤ peakB)
    (hpeak : HasFineReallocCredit.peakLarge st ≤ peakB)
    (hram : lim.staticBytes +
      (HasFineReallocCredit.baseFine (M := M) + cumB + peakB) + 2 * stepB ≤ lim.physCap)
    (hva : MMAP_MIN_ADDR + lim.staticBytes +
      (HasFineReallocCredit.baseFine (M := M) + cumB + peakB) + stepB +
      (lim.staticCount + dynB + 16) * (stepB + PAGE_SIZE) + stepB ≤ 2 ^ 48) :
    FitsStep lim stepB (M.maxDynIvs st) (M.footprint st) := by
  have hfp0 := HasFineReallocCredit.footprint_le (M := M) st
  have hfp : M.footprint st ≤ HasFineReallocCredit.baseFine (M := M) + cumB + peakB := by omega
  exact FitsStep.mono ⟨henf, hram, hva⟩ (Nat.le_refl _) hdyn hfp

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit
