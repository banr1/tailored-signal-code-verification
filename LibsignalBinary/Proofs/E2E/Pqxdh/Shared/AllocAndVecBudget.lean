/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVec
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget

/-!
# Budget-Threaded `RawVecInner::try_allocate_in` Specifications

Defines the deterministic allocator event list `tryAllocateInEvents`, envelope `TryAllocateInEnv`,
and total-correctness (`FitsEnv`) and conditional-OOM `RustCliAllocBudget M` contracts for
`<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]` (Block `588`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecBudget

open Arm64 ProofLib
open CryptoVerification.RustHeap (LayoutOk allocFailedEvent)
open CryptoVerification.LibsignalTripleRatchet (finishGrowStack)
open CryptoVerification.E2E.Pqxdh.Shared (TryAllocateInCall)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents NullAllowed OomPreserved
  RustCliAllocBudget rustAllocEvents
)

/-! ## Allocator Event List and Envelope -/

/-- Deterministic `AllocEvent` list emitted by `<alloc::raw_vec::RawVecInner>::try_allocate_in`. -/
def tryAllocateInEvents (x : TryAllocateInCall) : List AllocEvent :=
  rustAllocEvents (x.new.toNat * x.stride.toNat) x.align.toNat

def TryAllocateInEnv (x : TryAllocateInCall) (evs : List AllocEvent) : Prop :=
  evs = tryAllocateInEvents x

theorem tryAllocateInEnv_events (x : TryAllocateInCall) :
    TryAllocateInEnv x (tryAllocateInEvents x) :=
  rfl

theorem fitsEnv_tryAllocateIn_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    (x : TryAllocateInCall) :
    FitsEnv M lim st (TryAllocateInEnv x) ↔ FitsEvents M lim st (tryAllocateInEvents x) :=
  FitsEnv.eq_iff

theorem fitsEvents_tryAllocateIn_of_fitsEnv (M : AllocCostModel) (lim : BudgetLimits) (st : M.σ)
    (x : TryAllocateInCall) (h : FitsEnv M lim st (TryAllocateInEnv x)) :
    FitsEvents M lim st (tryAllocateInEvents x) :=
  h (tryAllocateInEvents x) rfl

/-! ## Budget-Threaded Specifications -/

/-- Total-correctness (`FitsEnv`) contract for `<alloc::raw_vec::RawVecInner>::try_allocate_in [local#2]`
(Block `588`): under `LayoutOk` and `FitsEnv M lim st (TryAllocateInEnv x)`, `__rust_alloc` returns
a non-null pointer (`tag = 0#64`), so `onPanic = ⌜False⌝` and `onOom = ⌜False⌝`. -/
def tryAllocateInSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (TryAllocateInCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.new ∧
      s.readReg64 .x2 = x.align ∧ s.readReg64 .x3 = x.stride ∧
      0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat ∧
      FitsEnv M lim st (TryAllocateInEnv x)⌝ ∗
    memRegion x.out 24 ∗ A.pool lim st s ∗ stackAt s.sp finishGrowStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent, ∃∗ p' : BitVec 64,
      (x.out ↦₆₄ 0#64) ∗ ((x.out + 8#64) ↦₆₄ x.new) ∗ ((x.out + 16#64) ↦₆₄ p') ∗
      ⌜p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0 ∧ sf.trace = s0.trace ∧
        TryAllocateInEnv x evs⌝ ∗
      A.live p' (x.new.toNat * x.stride.toNat) x.align.toNat ∗
      memRegion p' (x.new.toNat * x.stride.toNat) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp finishGrowStack

/-- Conditional-OOM variant of `tryAllocateInSpec` without `FitsEnv` in `pre`. -/
def tryAllocateInCondSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (TryAllocateInCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.new ∧
      s.readReg64 .x2 = x.align ∧ s.readReg64 .x3 = x.stride ∧
      0 < x.new.toNat ∧ 0 < x.stride.toNat ∧
      LayoutOk (x.new.toNat * x.stride.toNat) x.align.toNat⌝ ∗
    memRegion x.out 24 ∗ A.pool lim st s ∗ stackAt s.sp finishGrowStack
  post := fun (x, st) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64,
      (x.out ↦₆₄ tag) ∗
      (if tag = 1#64 then
        ((x.out + 8#64) ↦₆₄ x.align) ∗
        ((x.out + 16#64) ↦₆₄ BitVec.ofNat 64 (x.new.toNat * x.stride.toNat)) ∗
        ⌜NullAllowed (x.new.toNat * x.stride.toNat) x.align.toNat ∧
          p' = 0#64 ∧ sf.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
        A.pool lim st sf
       else
        ((x.out + 8#64) ↦₆₄ x.new) ∗
        ((x.out + 16#64) ↦₆₄ p') ∗
        ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ p'.toNat % x.align.toNat = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live p' (x.new.toNat * x.stride.toNat) x.align.toNat ∗
          memRegion p' (x.new.toNat * x.stride.toNat) ∗
          A.pool lim (M.stepEvents (tryAllocateInEvents x) st) sf) ∗
      stackAt s0.sp finishGrowStack
  onOom := fun (x, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (tryAllocateInEvents x) ∧ OomPreserved s0 sf⌝

end LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVecBudget
