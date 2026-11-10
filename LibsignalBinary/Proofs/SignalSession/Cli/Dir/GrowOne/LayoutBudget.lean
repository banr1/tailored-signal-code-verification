/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.Layout

/-!
# Budget-Threaded Cell and Byte Wrappers for `RawVec<(String, Vec<u8>)>::grow_one`

Defines `finishGrowZeroCellsSpec`, `finishGrowNeCellsSpec`, `growOneDirBytesInnerSpec`, and their
conditional-OOM counterparts over `rawVecGrowEvents`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.LayoutBudget

open Arm64 ProofLib
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget FitsEnv FitsEvents
   NullAllowed OomPreserved rustAllocEvents rustReallocEvents)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rawVecGrowEvents)
open CryptoVerification.RustHeap (LayoutOk allocFailedEvent)
open CryptoVerification.LibsignalTripleRatchet (finishGrowStackX)
open CryptoVerification.SignalSession.Cli.GrowOne.Helpers
  (cliGrowOneStack CliGrowBytesGhost FGCellsGhost)

/-- Event envelope of `finishGrowZeroCellsSpec` (`cap = 0`). -/
def FinishGrowZeroEnv (new stride align : BitVec 64) (evs : List AllocEvent) : Prop :=
  evs = rustAllocEvents (new.toNat * stride.toNat) align.toNat

/-- Event envelope of `finishGrowNeCellsSpec` (`cap ≠ 0`). -/
def FinishGrowNeEnv (cap new stride align : BitVec 64) (evs : List AllocEvent) : Prop :=
  evs = rustReallocEvents (cap.toNat * stride.toNat) (new.toNat * stride.toNat) align.toNat

/-- Event envelope of `growOneDirBytesInnerSpec` (`elemSz = 48, minCap = 4, align = 8`). -/
def GrowOneDirBytesEnv (cap : BitVec 64) (evs : List AllocEvent) : Prop :=
  evs = rawVecGrowEvents 48 4 8 cap

/-- Budget-threaded `finishGrowZeroCellsSpec`: under `LayoutOk` and `FitsEnv`, `__rust_alloc`
cannot return null, so the `Err(AllocError)` (`tag = 1#64`) branch is dead. -/
def finishGrowZeroCellsSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (FGCellsGhost × M.σ) where
  pre := fun ((out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧ LayoutOk (new.toNat * stride.toNat) align.toNat ∧
      FitsEnv M lim st (FinishGrowZeroEnv new stride align)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool lim st s ∗ stackAt fsp finishGrowStackX
  post := fun ((out, _cap, _ptr, new, align, stride, _bs, _o0, _o1, _o2, fsp), st) s0 sf =>
    ∃∗ evs : List AllocEvent, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ sf.trace = s0.trace ∧
        FinishGrowZeroEnv new stride align evs⌝ ∗
      A.live p' (new.toNat * stride.toNat) align.toNat ∗
      memRegion p' (new.toNat * stride.toNat) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt fsp finishGrowStackX ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

/-- Conditional-OOM variant of `finishGrowZeroCellsSpec` without `FitsEnv` in `pre`. -/
def finishGrowZeroCellsCondSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FGCellsGhost × M.σ) where
  pre := fun ((out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs = [] ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧ LayoutOk (new.toNat * stride.toNat) align.toNat⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.pool lim st s ∗ stackAt fsp finishGrowStackX
  post := fun ((out, _cap, _ptr, new, align, stride, _bs, _o0, _o1, _o2, fsp), st) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜NullAllowed (new.toNat * stride.toNat) align.toNat ∧
          sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
        A.pool lim st sf
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (new.toNat * stride.toNat) align.toNat ∗
          memRegion p' (new.toNat * stride.toNat) ∗
          A.pool lim (M.stepEvents (rustAllocEvents (new.toNat * stride.toNat) align.toNat) st) sf) ∗
      stackAt fsp finishGrowStackX ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')
  onOom := fun ((_out, _cap, _ptr, new, align, stride, _bs, _o0, _o1, _o2, _fsp), st) s0 sf =>
    ⌜¬ FitsEvents M lim st (rustAllocEvents (new.toNat * stride.toNat) align.toNat) ∧
      OomPreserved s0 sf⌝

/-- Budget-threaded `finishGrowNeCellsSpec`: under `LayoutOk` and `FitsEnv`, `__rust_realloc`
cannot return null, so the `Err(AllocError)` (`tag = 1#64`) branch is dead. -/
def finishGrowNeCellsSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (FGCellsGhost × M.σ) where
  pre := fun ((out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat * stride.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧ LayoutOk (new.toNat * stride.toNat) align.toNat ∧
      FitsEnv M lim st (FinishGrowNeEnv cap new stride align)⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr (cap.toNat * stride.toNat) align.toNat ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride.toNat - bs.length) ∗
    A.pool lim st s ∗ stackAt fsp finishGrowStackX
  post := fun ((out, cap, _ptr, new, align, stride, bs, _o0, _o1, _o2, fsp), st) s0 sf =>
    ∃∗ evs : List AllocEvent, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      ⌜p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ sf.trace = s0.trace ∧
        FinishGrowNeEnv cap new stride align evs⌝ ∗
      A.live p' (new.toNat * stride.toNat) align.toNat ∗ (p' ↦ₛ bs) ∗
      memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * stride.toNat - bs.length) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt fsp finishGrowStackX ∗
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')

/-- Conditional-OOM variant of `finishGrowNeCellsSpec` without `FitsEnv` in `pre`. -/
def finishGrowNeCellsCondSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (FGCellsGhost × M.σ) where
  pre := fun ((out, cap, ptr, new, align, stride, bs, o0, o1, o2, fsp), st) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = align ∧ s.readReg64 .x5 = stride ∧
      s.sp = fsp ∧ cap ≠ 0#64 ∧ bs.length ≤ cap.toNat * stride.toNat ∧ cap.toNat ≤ new.toNat ∧
      0 < new.toNat ∧ 0 < stride.toNat ∧ LayoutOk (new.toNat * stride.toNat) align.toNat⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗
    A.live ptr (cap.toNat * stride.toNat) align.toNat ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride.toNat - bs.length) ∗
    A.pool lim st s ∗ stackAt fsp finishGrowStackX
  post := fun ((out, cap, ptr, new, align, stride, bs, _o0, _o1, _o2, fsp), st) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64,
      (if tag = 1#64 then
        ⌜NullAllowed (new.toNat * stride.toNat) align.toNat ∧
          sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
          A.live ptr (cap.toNat * stride.toNat) align.toNat ∗ (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * stride.toNat - bs.length) ∗
          A.pool lim st sf
       else
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (new.toNat * stride.toNat) align.toNat ∗ (p' ↦ₛ bs) ∗
          memRegion (p' + BitVec.ofNat 64 bs.length) (new.toNat * stride.toNat - bs.length) ∗
          A.pool lim
            (M.stepEvents (rustReallocEvents (cap.toNat * stride.toNat)
              (new.toNat * stride.toNat) align.toNat) st) sf) ∗
      stackAt fsp finishGrowStackX ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')
  onOom := fun ((_out, cap, _ptr, new, align, stride, _bs, _o0, _o1, _o2, _fsp), st) s0 sf =>
    ⌜¬ FitsEvents M lim st (rustReallocEvents (cap.toNat * stride.toNat)
        (new.toNat * stride.toNat) align.toNat) ∧
      OomPreserved s0 sf⌝

/-- Budget-threaded `growOneDirBytesInnerSpec` (`onPanic = ⌜False⌝` under `FitsEnv`). -/
def growOneDirBytesInnerSpec {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (CliGrowBytesGhost × M.σ) where
  pre := fun ((v, cap, ptr, bs), st) s =>
    ⌜s.readReg64 .x0 = v ∧ bs.length ≤ cap.toNat * 48 ∧ ptr ≠ 0#64 ∧
      max (2 * cap.toNat) 4 * 48 + 8 ≤ 2 ^ 63 ∧
      FitsEnv M lim st (GrowOneDirBytesEnv cap)⌝ ∗
    (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
    (if cap = 0#64 then emp
     else A.live ptr (cap.toNat * 48) 8 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat * 48 - bs.length)) ∗
    A.pool lim st s ∗ stackAt s.sp cliGrowOneStack
  post := fun ((v, cap, _, bs), st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ GrowOneDirBytesEnv cap evs⌝ ∗
      (∃∗ p' : BitVec 64,
        ⌜p' ≠ 0#64 ∧ p'.toNat % 8 = 0⌝ ∗
        (v ↦₆₄ BitVec.ofNat 64 (max (2 * cap.toNat) 4)) ∗ ((v + 8#64) ↦₆₄ p') ∗
        A.live p' (max (2 * cap.toNat) 4 * 48) 8 ∗ (p' ↦ₛ bs) ∗
        memRegion (p' + BitVec.ofNat 64 bs.length) (max (2 * cap.toNat) 4 * 48 - bs.length)) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp cliGrowOneStack

end LibsignalBinary.Proofs.SignalSession.Cli.Dir.GrowOne.LayoutBudget
