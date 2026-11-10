/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceLemmas
public import LibsignalBinary.Heap.IfaceSimp
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WP.StepsProcess
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Placement-Independent Budgeted Heap Contracts

Unplaced (`…Base`) budget-threaded Rust allocator specifications, arbitrary-stack wrappers, and
`wp_call`-compatible extern contracts.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Heap

open Arm64 Arm64.CType ProofLib ProofLib.StdStartup
open CryptoVerification.RustHeap (RustAlloc LayoutOk allocHookStack)

/-- Conditional-OOM budget-threaded contract for `__rust_alloc` (`zeroed = false`) and
    `__rust_alloc_zeroed` (`zeroed = true`). Ghost: `(size, align, st)`.
    `.OutOfMemory` is permitted **only** when `¬ FitsEvents M lim st (rustAllocEvents size align)`. -/
def rustCliAllocBudgetSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (zeroed : Bool) : Spec (Nat × Nat × M.σ) where
  pre := fun (size, align, st) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧
      RustLayoutOk size align⌝ ∗
      A.pool lim st s ∗ stackAt s.sp allocHookStack
  post := fun (size, align, st) s0 sf =>
    let st' := if sf.readReg64 .x0 = 0 then st else M.stepEvents (rustAllocEvents size align) st
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st' sf ∗ stackAt s0.sp allocHookStack ∗
      (if sf.readReg64 .x0 = 0 then ⌜NullAllowed size align⌝
       else ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) size align ∗
         (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
          else memRegion (sf.readReg64 .x0) size))
  onOom := fun (size, align, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (rustAllocEvents size align) ∧ OomPreserved s0 sf⌝

/-- Budget-threaded contract for `__rust_dealloc(ptr = x0, size = x1, align = x2)`.
    Ghost: `(ptr, size, align, st)`. Never hits `.OutOfMemory` (`onOom := ⌜False⌝`) and guarantees
    `M.liveBytes (M.stepEvents (rustDeallocEvents size align) st) ≤ M.liveBytes st`. -/
def rustCliDeallocBudgetSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := fun (p, size, align, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧ (s.readReg64 .x2).toNat = align⌝ ∗
      A.pool lim st s ∗ A.live p size align ∗ memRegion p size ∗ stackAt s.sp allocHookStack
  post := fun (_, size, align, st) s0 sf =>
    let st' := M.stepEvents (rustDeallocEvents size align) st
    ⌜AllocCallPreserved s0 sf ∧ M.liveBytes st' ≤ M.liveBytes st⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp allocHookStack

/-- Conditional-OOM budget-threaded contract for `__rust_realloc(ptr, old, align, new)`.
    Ghost: `(ptr, old, align, new, bs, st)`.
    `.OutOfMemory` is permitted **only** when `¬ FitsEvents M lim st (rustReallocEvents old new align)`. -/
def rustCliReallocBudgetSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ) where
  pre := fun (p, old, align, new, bs, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ RustLayoutOk new align ∧ bs.length ≤ old ∧
      bs.length ≤ new⌝ ∗
      A.pool lim st s ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp allocHookStack
  post := fun (p, old, align, new, bs, st) s0 sf =>
    let st' := if sf.readReg64 .x0 = 0 then st else M.stepEvents (rustReallocEvents old new align) st
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st' sf ∗ stackAt s0.sp allocHookStack ∗
      (if sf.readReg64 .x0 = 0 then
        ⌜NullAllowed new align⌝ ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)
       else
        ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) new align ∗
          (sf.readReg64 .x0 ↦ₛ bs) ∗
          memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))
  onOom := fun (_, old, align, new, _, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (rustReallocEvents old new align) ∧ OomPreserved s0 sf⌝

/-- Total-correctness (`onOom := ⌜False⌝`, non-null return) contract for `__rust_alloc` under
    `FitsEvents M lim st (rustAllocEvents size align)`. Both `.OutOfMemory` and `NullAllowed` are
    ruled out by `FitsEvents`. -/
def rustCliAllocNoOomSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (zeroed : Bool) : Spec (Nat × Nat × M.σ) where
  pre := fun (size, align, st) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧
      RustLayoutOk size align ∧ FitsEvents M lim st (rustAllocEvents size align)⌝ ∗
      A.pool lim st s ∗ stackAt s.sp allocHookStack
  post := fun (size, align, st) s0 sf =>
    let st' := M.stepEvents (rustAllocEvents size align) st
    ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % align = 0⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp allocHookStack ∗
      A.live (sf.readReg64 .x0) size align ∗
      (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
       else memRegion (sf.readReg64 .x0) size)
  onOom := fun _ _ _ => ⌜False⌝

abbrev rustCliDeallocNoOomSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × M.σ) :=
  rustCliDeallocBudgetSpecBase M A lim

/-- Total-correctness (`onOom := ⌜False⌝`, non-null return) contract for `__rust_realloc` under
    `FitsEvents M lim st (rustReallocEvents old new align)`. Both `.OutOfMemory` and `NullAllowed`
    are ruled out by `FitsEvents`. -/
def rustCliReallocNoOomSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ) where
  pre := fun (p, old, align, new, bs, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ RustLayoutOk new align ∧ bs.length ≤ old ∧
      bs.length ≤ new ∧ FitsEvents M lim st (rustReallocEvents old new align)⌝ ∗
      A.pool lim st s ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp allocHookStack
  post := fun (_, old, align, new, bs, st) s0 sf =>
    let st' := M.stepEvents (rustReallocEvents old new align) st
    ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % align = 0⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp allocHookStack ∗
      A.live (sf.readReg64 .x0) new align ∗
      (sf.readReg64 .x0 ↦ₛ bs) ∗
      memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length)
  onOom := fun _ _ _ => ⌜False⌝

/-! ## Hook and Subroutine Bundles -/

/-- Hook-mode bundle for conditional-OOM budget-threaded allocator contracts across all `lim`. -/
structure RustCliAllocBudgetHooksBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (hooks : String → Option (State → State)) : Prop where
  alloc : ∀ lim : BudgetLimits, HookSat hooks "__rustc::__rust_alloc"
    (rustCliAllocBudgetSpecBase M A lim false)
  dealloc : ∀ lim : BudgetLimits, HookSat hooks "__rustc::__rust_dealloc"
    (rustCliDeallocBudgetSpecBase M A lim)
  realloc : ∀ lim : BudgetLimits, HookSat hooks "__rustc::__rust_realloc"
    (rustCliReallocBudgetSpecBase M A lim)

/-- Native placed subroutine bundle (`subroutine_ok P`) for conditional-OOM budget-threaded
    allocator contracts across all `lim : BudgetLimits`. -/
structure RustCliAllocBudgetEntriesBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (P : Program) (addrs : RustAllocAddrs) : Prop where
  alloc : ∀ lim : BudgetLimits,
    subroutine_ok P addrs.alloc (rustCliAllocBudgetSpecBase M A lim false)
  dealloc : ∀ lim : BudgetLimits,
    subroutine_ok P addrs.dealloc (rustCliDeallocBudgetSpecBase M A lim)
  realloc : ∀ lim : BudgetLimits,
    subroutine_ok P addrs.realloc (rustCliReallocBudgetSpecBase M A lim)

/-- Native placed subroutine bundle (`subroutine_ok P`) specialized to `onOom := ⌜False⌝` at `lim`. -/
structure RustCliAllocNoOomEntriesBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (P : Program) (addrs : RustAllocAddrs) : Prop where
  alloc : subroutine_ok P addrs.alloc (rustCliAllocNoOomSpecBase M A lim false)
  dealloc : subroutine_ok P addrs.dealloc (rustCliDeallocNoOomSpecBase M A lim)
  realloc : subroutine_ok P addrs.realloc (rustCliReallocNoOomSpecBase M A lim)

theorem subroutine_ok_allocNoOom_of_budgetBase {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {entry : BitVec 64} {zeroed : Bool}
    (h : subroutine_ok P entry (rustCliAllocBudgetSpecBase M A lim zeroed)) :
    subroutine_ok P entry (rustCliAllocNoOomSpecBase M A lim zeroed) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨size, align, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [rustCliAllocNoOomSpecBase] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hlay, hFit⟩, hrest⟩
  have hpreB : s0.mem ⊨ (rustCliAllocBudgetSpecBase M A lim zeroed).pre (size, align, st) s0 ∗ R := by
    dsimp only [rustCliAllocBudgetSpecBase]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hlay⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (size, align, st) R s0 hpc hrun hpreB hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustCliAllocBudgetSpecBase] at hpost
    by_cases hnull : sf.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte] at hpost
      have hna : NullAllowed size align := by
        have hEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗
              stackAt s0.sp allocHookStack ∗ ⌜NullAllowed size align⌝) ∗ R =
            ⌜NullAllowed size align⌝ ∗
              (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗
                stackAt s0.sp allocHookStack ∗ R) := by ac_rfl
        rw [hEq, satisfies_pure_sepConj] at hpost
        exact hpost.1
      exact False.elim (not_nullAllowed_of_fitsAllocEvents hlay hFit hna)
    · simp only [hnull, ↓reduceIte] at hpost
      dsimp only [rustCliAllocNoOomSpecBase]
      have hEq1 :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
            stackAt s0.sp allocHookStack ∗
            (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) size align ∗
              (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
               else memRegion (sf.readReg64 .x0) size))) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
              (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
                stackAt s0.sp allocHookStack ∗ A.live (sf.readReg64 .x0) size align ∗
                (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
                 else memRegion (sf.readReg64 .x0) size) ∗ R)) := by ac_rfl
      rw [hEq1, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hacp, hpost⟩
      rw [satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hal, hspRest⟩
      have hne0 : sf.readReg64 .x0 ≠ 0#64 := hnull
      have hEq2 :
          (⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
              (sf.readReg64 .x0).toNat % align = 0⌝ ∗
            A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
            stackAt s0.sp allocHookStack ∗ A.live (sf.readReg64 .x0) size align ∗
            (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
             else memRegion (sf.readReg64 .x0) size)) ∗ R =
          ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
              (sf.readReg64 .x0).toNat % align = 0⌝ ∗
            (A.pool lim (M.stepEvents (rustAllocEvents size align) st) sf ∗
              stackAt s0.sp allocHookStack ∗ A.live (sf.readReg64 .x0) size align ∗
              (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
               else memRegion (sf.readReg64 .x0) size) ∗ R) := by ac_rfl
      rw [hEq2, satisfies_pure_sepConj]
      exact ⟨⟨hacp, hne0, hal⟩, hspRest⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · dsimp only [rustCliAllocBudgetSpecBase] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim (hoom.1.1 hFit)

theorem subroutine_ok_reallocNoOom_of_budgetBase {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {P : Program} {entry : BitVec 64}
    (h : subroutine_ok P entry (rustCliReallocBudgetSpecBase M A lim)) :
    subroutine_ok P entry (rustCliReallocNoOomSpecBase M A lim) := by
  apply subroutine_ok.of_codeLoaded
  rintro ⟨p, old, align, new, bs, st⟩ R s0 hpc hrun hpre hsp _
  dsimp only [rustCliReallocNoOomSpecBase] at hpre
  have hpreEq :
      (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧
          (s0.readReg64 .x2).toNat = align ∧ (s0.readReg64 .x3).toNat = new ∧
          RustLayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new ∧
          FitsEvents M lim st (rustReallocEvents old new align)⌝ ∗
        A.pool lim st s0 ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
        memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
        stackAt s0.sp allocHookStack) ∗ R =
      ⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧
          (s0.readReg64 .x2).toNat = align ∧ (s0.readReg64 .x3).toNat = new ∧
          RustLayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new ∧
          FitsEvents M lim st (rustReallocEvents old new align)⌝ ∗
        (A.pool lim st s0 ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
          stackAt s0.sp allocHookStack ∗ R) := by ac_rfl
  rw [hpreEq, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlay, hbo, hbn, hFit⟩, hrest⟩
  have hpreB : s0.mem ⊨
      (rustCliReallocBudgetSpecBase M A lim).pre (p, old, align, new, bs, st) s0 ∗ R := by
    dsimp only [rustCliReallocBudgetSpecBase]
    have hEq :
        (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧
            (s0.readReg64 .x2).toNat = align ∧ (s0.readReg64 .x3).toNat = new ∧
            RustLayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new⌝ ∗
          A.pool lim st s0 ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
          stackAt s0.sp allocHookStack) ∗ R =
        ⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧
            (s0.readReg64 .x2).toNat = align ∧ (s0.readReg64 .x3).toNat = new ∧
            RustLayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new⌝ ∗
          (A.pool lim st s0 ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
            stackAt s0.sp allocHookStack ∗ R) := by ac_rfl
    rw [hEq, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hlay, hbo, hbn⟩, hrest⟩
  refine subroutine_ok.mono_outcome h (p, old, align, new, bs, st) R s0 hpc hrun hpreB hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustCliReallocBudgetSpecBase] at hpost
    by_cases hnull : sf.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte] at hpost
      have hna : NullAllowed new align := by
        have hEq :
            (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗
              stackAt s0.sp allocHookStack ∗
              (⌜NullAllowed new align⌝ ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
                memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length))) ∗ R =
            ⌜NullAllowed new align⌝ ∗
              (⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st sf ∗
                stackAt s0.sp allocHookStack ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
                memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ R) := by ac_rfl
        rw [hEq, satisfies_pure_sepConj] at hpost
        exact hpost.1
      exact False.elim (not_nullAllowed_of_fitsReallocEvents hlay hFit hna)
    · simp only [hnull, ↓reduceIte] at hpost
      dsimp only [rustCliReallocNoOomSpecBase]
      have hEq1 :
          (⌜AllocCallPreserved s0 sf⌝ ∗
            A.pool lim (M.stepEvents (rustReallocEvents old new align) st) sf ∗
            stackAt s0.sp allocHookStack ∗
            (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) new align ∗
              (sf.readReg64 .x0 ↦ₛ bs) ∗
              memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))) ∗ R =
          ⌜AllocCallPreserved s0 sf⌝ ∗
            (⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
              (A.pool lim (M.stepEvents (rustReallocEvents old new align) st) sf ∗
                stackAt s0.sp allocHookStack ∗ A.live (sf.readReg64 .x0) new align ∗
                (sf.readReg64 .x0 ↦ₛ bs) ∗
                memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length) ∗ R)) := by
        ac_rfl
      rw [hEq1, satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hacp, hpost⟩
      rw [satisfies_pure_sepConj] at hpost
      rcases hpost with ⟨hal, hspRest⟩
      have hne0 : sf.readReg64 .x0 ≠ 0#64 := hnull
      have hGoalEq :
          (⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
              (sf.readReg64 .x0).toNat % align = 0⌝ ∗
            A.pool lim (M.stepEvents (rustReallocEvents old new align) st) sf ∗
            stackAt s0.sp allocHookStack ∗ A.live (sf.readReg64 .x0) new align ∗
            (sf.readReg64 .x0 ↦ₛ bs) ∗
            memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length)) ∗ R =
          ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
              (sf.readReg64 .x0).toNat % align = 0⌝ ∗
            (A.pool lim (M.stepEvents (rustReallocEvents old new align) st) sf ∗
              stackAt s0.sp allocHookStack ∗ A.live (sf.readReg64 .x0) new align ∗
              (sf.readReg64 .x0 ↦ₛ bs) ∗
              memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length) ∗ R) := by
        simp only [sepConj_assoc]
      rw [hGoalEq, satisfies_pure_sepConj]
      exact ⟨⟨hacp, hne0, hal⟩, hspRest⟩
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · dsimp only [rustCliReallocBudgetSpecBase] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim (hoom.1.1 hFit)

/-- Specialize `RustCliAllocBudgetEntriesBase` at any `lim : BudgetLimits` to total-correctness
    `RustCliAllocNoOomEntriesBase` (`onOom := ⌜False⌝`, non-null return). -/
theorem RustCliAllocBudgetEntriesBase.toNoOom {M : AllocCostModel} {A : RustCliAllocBudget M}
    {P : Program} {addrs : RustAllocAddrs}
    (h : RustCliAllocBudgetEntriesBase M A P addrs) (lim : BudgetLimits) :
    RustCliAllocNoOomEntriesBase M A lim P addrs where
  alloc := subroutine_ok_allocNoOom_of_budgetBase (h.alloc lim)
  dealloc := h.dealloc lim
  realloc := subroutine_ok_reallocNoOom_of_budgetBase (h.realloc lim)

/-- Every `RustCliAllocBudgetEntriesBase M A P addrs` projects to `RustCliAllocEntries A.toRustCliAlloc P addrs` by evaluating `lim := zeroBudgetLimits` and existentializing `st : M.σ`. -/
theorem rustCliAllocEntries_of_budgetBase {M : AllocCostModel} {A : RustCliAllocBudget M}
    {P : Program} {addrs : RustAllocAddrs}
    (h : RustCliAllocBudgetEntriesBase M A P addrs) :
    RustCliAllocEntries A.toRustCliAlloc P addrs where
  alloc := by
    apply subroutine_ok.of_codeLoaded
    rintro ⟨size, align⟩ R s0 hpc hrun hpre hsp _
    dsimp only [rustCliAllocSpec, RustCliAllocBudget.toRustCliAlloc] at hpre
    have hEx : s0.mem ⊨
        ∃∗ st : M.σ,
          (rustCliAllocBudgetSpecBase M A zeroBudgetLimits false).pre (size, align, st) s0 ∗ R := by
      dsimp only [rustCliAllocBudgetSpecBase]
      have hEq :
          (⌜(s0.readReg64 .x0).toNat = size ∧ (s0.readReg64 .x1).toNat = align ∧
              RustLayoutOk size align⌝ ∗
            (∃∗ st : M.σ, A.pool zeroBudgetLimits st s0) ∗
            stackAt s0.sp allocHookStack) ∗ R =
          ∃∗ st : M.σ,
            (⌜(s0.readReg64 .x0).toNat = size ∧ (s0.readReg64 .x1).toNat = align ∧
                RustLayoutOk size align⌝ ∗
              A.pool zeroBudgetLimits st s0 ∗ stackAt s0.sp allocHookStack) ∗ R := by
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      rwa [← hEq]
    obtain ⟨st, hpreSt⟩ := (satisfies_sepExists _ _).1 hEx
    refine subroutine_ok.mono_outcome (h.alloc zeroBudgetLimits) (size, align, st) R s0
      hpc hrun hpreSt hsp ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [rustCliAllocBudgetSpecBase] at hpost
      dsimp only [rustCliAllocSpec, RustCliAllocBudget.toRustCliAlloc]
      let st' := if sf.readReg64 .x0 = 0 then st else M.stepEvents (rustAllocEvents size align) st
      have hexI : A.pool zeroBudgetLimits st' sf ⊢ ∃∗ y : M.σ, A.pool zeroBudgetLimits y sf :=
        @Entails.sepExists_intro M.σ (fun y => A.pool zeroBudgetLimits y sf) st'
      refine Satisfies.mono ?_ hpost
      exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hexI))
    · exact Or.inr (Or.inl ⟨hp, hpan⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
    · refine Or.inr (Or.inr (Or.inr ⟨ho, ?_⟩))
      dsimp only [rustCliAllocBudgetSpecBase] at hoom
      dsimp only [rustCliAllocSpec]
      rw [satisfies_pure_sepConj] at hoom ⊢
      exact ⟨hoom.1.2, hoom.2⟩
  dealloc := by
    apply subroutine_ok.of_codeLoaded
    rintro ⟨p, size, align⟩ R s0 hpc hrun hpre hsp _
    dsimp only [rustCliDeallocSpec, RustCliAllocBudget.toRustCliAlloc] at hpre
    have hEx : s0.mem ⊨
        ∃∗ st : M.σ,
          (rustCliDeallocBudgetSpecBase M A zeroBudgetLimits).pre (p, size, align, st) s0 ∗ R := by
      dsimp only [rustCliDeallocBudgetSpecBase]
      have hEq :
          (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = size ∧
              (s0.readReg64 .x2).toNat = align⌝ ∗
            (∃∗ st : M.σ, A.pool zeroBudgetLimits st s0) ∗
            A.live p size align ∗ memRegion p size ∗ stackAt s0.sp allocHookStack) ∗ R =
          ∃∗ st : M.σ,
            (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = size ∧
                (s0.readReg64 .x2).toNat = align⌝ ∗
              A.pool zeroBudgetLimits st s0 ∗ A.live p size align ∗ memRegion p size ∗
              stackAt s0.sp allocHookStack) ∗ R := by
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      rwa [← hEq]
    obtain ⟨st, hpreSt⟩ := (satisfies_sepExists _ _).1 hEx
    refine subroutine_ok.mono_outcome (h.dealloc zeroBudgetLimits) (p, size, align, st) R s0
      hpc hrun hpreSt hsp ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [rustCliDeallocBudgetSpecBase] at hpost
      dsimp only [rustCliDeallocSpec, RustCliAllocBudget.toRustCliAlloc]
      let st' := M.stepEvents (rustDeallocEvents size align) st
      have hexI : A.pool zeroBudgetLimits st' sf ⊢ ∃∗ y : M.σ, A.pool zeroBudgetLimits y sf :=
        @Entails.sepExists_intro M.σ (fun y => A.pool zeroBudgetLimits y sf) st'
      refine Satisfies.mono ?_ hpost
      exact sepConj_mono_left (Entails.pure_left fun hp =>
        Entails.pure_right hp.1 (sepConj_mono_left hexI))
    · exact Or.inr (Or.inl ⟨hp, hpan⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))
  realloc := by
    apply subroutine_ok.of_codeLoaded
    rintro ⟨p, old, align, new, bs⟩ R s0 hpc hrun hpre hsp _
    dsimp only [rustCliReallocSpec, RustCliAllocBudget.toRustCliAlloc] at hpre
    have hEx : s0.mem ⊨
        ∃∗ st : M.σ,
          (rustCliReallocBudgetSpecBase M A zeroBudgetLimits).pre (p, old, align, new, bs, st) s0 ∗ R := by
      dsimp only [rustCliReallocBudgetSpecBase]
      have hEq :
          (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧
              (s0.readReg64 .x2).toNat = align ∧ (s0.readReg64 .x3).toNat = new ∧
              RustLayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new⌝ ∗
            (∃∗ st : M.σ, A.pool zeroBudgetLimits st s0) ∗
            A.live p old align ∗ (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
            stackAt s0.sp allocHookStack) ∗ R =
          ∃∗ st : M.σ,
            (⌜s0.readReg64 .x0 = p ∧ (s0.readReg64 .x1).toNat = old ∧
                (s0.readReg64 .x2).toNat = align ∧ (s0.readReg64 .x3).toNat = new ∧
                RustLayoutOk new align ∧ bs.length ≤ old ∧ bs.length ≤ new⌝ ∗
              A.pool zeroBudgetLimits st s0 ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
              memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗
              stackAt s0.sp allocHookStack) ∗ R := by
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      rwa [← hEq]
    obtain ⟨st, hpreSt⟩ := (satisfies_sepExists _ _).1 hEx
    refine subroutine_ok.mono_outcome (h.realloc zeroBudgetLimits)
      (p, old, align, new, bs, st) R s0 hpc hrun hpreSt hsp ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [rustCliReallocBudgetSpecBase] at hpost
      dsimp only [rustCliReallocSpec, RustCliAllocBudget.toRustCliAlloc]
      let st' :=
        if sf.readReg64 .x0 = 0 then st else M.stepEvents (rustReallocEvents old new align) st
      have hexI : A.pool zeroBudgetLimits st' sf ⊢ ∃∗ y : M.σ, A.pool zeroBudgetLimits y sf :=
        @Entails.sepExists_intro M.σ (fun y => A.pool zeroBudgetLimits y sf) st'
      refine Satisfies.mono ?_ hpost
      exact sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hexI))
    · exact Or.inr (Or.inl ⟨hp, hpan⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
    · refine Or.inr (Or.inr (Or.inr ⟨ho, ?_⟩))
      dsimp only [rustCliReallocBudgetSpecBase] at hoom
      dsimp only [rustCliReallocSpec]
      rw [satisfies_pure_sepConj] at hoom ⊢
      exact ⟨hoom.1.2, hoom.2⟩

end LibsignalBinary.Heap

namespace LibsignalBinary.Heap.IfaceBudgetLemmas

open Arm64 ProofLib SepProp
open CryptoVerification.RustHeap (RustAlloc LayoutOk allocHookStack)
open LibsignalBinary.Heap (
  PoolPreserved AllocCallPreserved OomPreserved RustLayoutOk NullAllowed
  VmPreserved AllocEvent AllocCostModel BudgetLimits zeroBudgetLimits
  FitsStep FitsEvent FitsEvents FitsTrace FitsTraceOf
  rustAllocEvents rustDeallocEvents rustReallocEvents
  RustCliAllocBudget
  rustCliAllocBudgetSpecBase rustCliDeallocBudgetSpecBase rustCliReallocBudgetSpecBase
  rustCliAllocNoOomSpecBase rustCliDeallocNoOomSpecBase rustCliReallocNoOomSpecBase
  RustCliAllocBudgetHooksBase RustAllocAddrs RustCliAllocBudgetEntriesBase RustCliAllocNoOomEntriesBase
  subroutine_ok_allocNoOom_of_budgetBase subroutine_ok_reallocNoOom_of_budgetBase
)
open LibsignalBinary.Heap.IfaceLemmas (
  subroutine_ok_frame_oom'
)

private theorem stackAt_split_from_allocHookStack (sp : BitVec 64) {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗ stackAt sp allocHookStack := by
  have hsplit : stk = allocHookStack + (stk - allocHookStack) := by
    dsimp only [allocHookStack] at hle ⊢; omega
  have h0 := ProofLib.stackAt_split_bottom sp allocHookStack (stk - allocHookStack)
    (by dsimp only [allocHookStack] at hle ⊢; omega)
  rwa [← hsplit] at h0

def rustCliAllocBudgetSpecWithStackBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (zeroed : Bool) (stk : Nat) : Spec (Nat × Nat × M.σ) where
  pre := fun (size, align, st) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧
      RustLayoutOk size align⌝ ∗
      A.pool lim st s ∗ stackAt s.sp stk
  post := fun (size, align, st) s0 sf =>
    let st' := if sf.readReg64 .x0 = 0 then st else M.stepEvents (rustAllocEvents size align) st
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st' sf ∗ stackAt s0.sp stk ∗
      (if sf.readReg64 .x0 = 0 then ⌜NullAllowed size align⌝
       else ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) size align ∗
         (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
          else memRegion (sf.readReg64 .x0) size))
  onOom := fun (size, align, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (rustAllocEvents size align) ∧ OomPreserved s0 sf⌝

def rustCliDeallocBudgetSpecWithStackBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := fun (p, size, align, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧ (s.readReg64 .x2).toNat = align⌝ ∗
      A.pool lim st s ∗ A.live p size align ∗ memRegion p size ∗ stackAt s.sp stk
  post := fun (_, size, align, st) s0 sf =>
    let st' := M.stepEvents (rustDeallocEvents size align) st
    ⌜AllocCallPreserved s0 sf ∧ M.liveBytes st' ≤ M.liveBytes st⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp stk

def rustCliReallocBudgetSpecWithStackBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ) where
  pre := fun (p, old, align, new, bs, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ RustLayoutOk new align ∧ bs.length ≤ old ∧
      bs.length ≤ new⌝ ∗
      A.pool lim st s ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp stk
  post := fun (p, old, align, new, bs, st) s0 sf =>
    let st' := if sf.readReg64 .x0 = 0 then st else M.stepEvents (rustReallocEvents old new align) st
    ⌜AllocCallPreserved s0 sf⌝ ∗ A.pool lim st' sf ∗ stackAt s0.sp stk ∗
      (if sf.readReg64 .x0 = 0 then
        ⌜NullAllowed new align⌝ ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)
       else
        ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) new align ∗
          (sf.readReg64 .x0 ↦ₛ bs) ∗
          memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))
  onOom := fun (_, old, align, new, _, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (rustReallocEvents old new align) ∧ OomPreserved s0 sf⌝

def rustCliAllocNoOomSpecWithStackBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (zeroed : Bool) (stk : Nat) : Spec (Nat × Nat × M.σ) where
  pre := fun (size, align, st) s =>
    ⌜(s.readReg64 .x0).toNat = size ∧ (s.readReg64 .x1).toNat = align ∧
      RustLayoutOk size align ∧ FitsEvents M lim st (rustAllocEvents size align)⌝ ∗
      A.pool lim st s ∗ stackAt s.sp stk
  post := fun (size, align, st) s0 sf =>
    let st' := M.stepEvents (rustAllocEvents size align) st
    ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % align = 0⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp stk ∗
      A.live (sf.readReg64 .x0) size align ∗
      (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
       else memRegion (sf.readReg64 .x0) size)
  onOom := fun _ _ _ => ⌜False⌝

abbrev rustCliDeallocNoOomSpecWithStackBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) : Spec (BitVec 64 × Nat × Nat × M.σ) :=
  rustCliDeallocBudgetSpecWithStackBase M A lim stk

def rustCliReallocNoOomSpecWithStackBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stk : Nat) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ) where
  pre := fun (p, old, align, new, bs, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ RustLayoutOk new align ∧ bs.length ≤ old ∧
      bs.length ≤ new ∧ FitsEvents M lim st (rustReallocEvents old new align)⌝ ∗
      A.pool lim st s ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp stk
  post := fun (_, old, align, new, bs, st) s0 sf =>
    let st' := M.stepEvents (rustReallocEvents old new align) st
    ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % align = 0⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp stk ∗
      A.live (sf.readReg64 .x0) new align ∗
      (sf.readReg64 .x0 ↦ₛ bs) ∗
      memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length)
  onOom := fun _ _ _ => ⌜False⌝

theorem subroutine_ok_rustCliAllocBudget_withStackBase {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (rustCliAllocBudgetSpecBase M A lim zeroed)) :
    subroutine_ok prog entry (rustCliAllocBudgetSpecWithStackBase M A lim zeroed stk) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨size, align, st⟩ s0
    dsimp only [rustCliAllocBudgetSpecBase, rustCliAllocBudgetSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨size, align, st⟩ s0 sf
    dsimp only [rustCliAllocBudgetSpecBase, rustCliAllocBudgetSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_inImage_rustCliAllocBudget_withStackBase {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {img : Obj.Image} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((rustCliAllocBudgetSpecBase M A lim zeroed).inImage img)) :
    subroutine_ok prog entry ((rustCliAllocBudgetSpecWithStackBase M A lim zeroed stk).inImage img) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨size, align, st⟩ s0
    dsimp only [Spec.inImage, rustCliAllocBudgetSpecBase, rustCliAllocBudgetSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨size, align, st⟩ s0 sf
    dsimp only [Spec.inImage, rustCliAllocBudgetSpecBase, rustCliAllocBudgetSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_rustCliDeallocBudget_withStackBase {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok prog entry (rustCliDeallocBudgetSpecWithStackBase M A lim stk) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨p, size, align, st⟩ s0
    dsimp only [rustCliDeallocBudgetSpecBase, rustCliDeallocBudgetSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, size, align, st⟩ s0 sf
    dsimp only [rustCliDeallocBudgetSpecBase, rustCliDeallocBudgetSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_inImage_rustCliDeallocBudget_withStackBase {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {img : Obj.Image} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((rustCliDeallocBudgetSpecBase M A lim).inImage img)) :
    subroutine_ok prog entry ((rustCliDeallocBudgetSpecWithStackBase M A lim stk).inImage img) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨p, size, align, st⟩ s0
    dsimp only [Spec.inImage, rustCliDeallocBudgetSpecBase, rustCliDeallocBudgetSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, size, align, st⟩ s0 sf
    dsimp only [Spec.inImage, rustCliDeallocBudgetSpecBase, rustCliDeallocBudgetSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_rustCliReallocBudget_withStackBase {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (rustCliReallocBudgetSpecBase M A lim)) :
    subroutine_ok prog entry (rustCliReallocBudgetSpecWithStackBase M A lim stk) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨p, old, align, new, bs, st⟩ s0
    dsimp only [rustCliReallocBudgetSpecBase, rustCliReallocBudgetSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, old, align, new, bs, st⟩ s0 sf
    dsimp only [rustCliReallocBudgetSpecBase, rustCliReallocBudgetSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_inImage_rustCliReallocBudget_withStackBase {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {img : Obj.Image} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((rustCliReallocBudgetSpecBase M A lim).inImage img)) :
    subroutine_ok prog entry ((rustCliReallocBudgetSpecWithStackBase M A lim stk).inImage img) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨p, old, align, new, bs, st⟩ s0
    dsimp only [Spec.inImage, rustCliReallocBudgetSpecBase, rustCliReallocBudgetSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, old, align, new, bs, st⟩ s0 sf
    dsimp only [Spec.inImage, rustCliReallocBudgetSpecBase, rustCliReallocBudgetSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_rustCliAllocNoOom_withStackBase {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (rustCliAllocNoOomSpecBase M A lim zeroed)) :
    subroutine_ok prog entry (rustCliAllocNoOomSpecWithStackBase M A lim zeroed stk) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨size, align, st⟩ s0
    dsimp only [rustCliAllocNoOomSpecBase, rustCliAllocNoOomSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨size, align, st⟩ s0 sf
    dsimp only [rustCliAllocNoOomSpecBase, rustCliAllocNoOomSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_inImage_rustCliAllocNoOom_withStackBase {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {img : Obj.Image} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((rustCliAllocNoOomSpecBase M A lim zeroed).inImage img)) :
    subroutine_ok prog entry ((rustCliAllocNoOomSpecWithStackBase M A lim zeroed stk).inImage img) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨size, align, st⟩ s0
    dsimp only [Spec.inImage, rustCliAllocNoOomSpecBase, rustCliAllocNoOomSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨size, align, st⟩ s0 sf
    dsimp only [Spec.inImage, rustCliAllocNoOomSpecBase, rustCliAllocNoOomSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_rustCliReallocNoOom_withStackBase {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (rustCliReallocNoOomSpecBase M A lim)) :
    subroutine_ok prog entry (rustCliReallocNoOomSpecWithStackBase M A lim stk) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨p, old, align, new, bs, st⟩ s0
    dsimp only [rustCliReallocNoOomSpecBase, rustCliReallocNoOomSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, old, align, new, bs, st⟩ s0 sf
    dsimp only [rustCliReallocNoOomSpecBase, rustCliReallocNoOomSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_inImage_rustCliReallocNoOom_withStackBase {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {img : Obj.Image} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64)
    (h : subroutine_ok prog entry ((rustCliReallocNoOomSpecBase M A lim).inImage img)) :
    subroutine_ok prog entry ((rustCliReallocNoOomSpecWithStackBase M A lim stk).inImage img) := by
  refine subroutine_ok_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) h ?_ ?_
  · rintro ⟨p, old, align, new, bs, st⟩ s0
    dsimp only [Spec.inImage, rustCliReallocNoOomSpecBase, rustCliReallocNoOomSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, old, align, new, bs, st⟩ s0 sf
    dsimp only [Spec.inImage, rustCliReallocNoOomSpecBase, rustCliReallocNoOomSpecWithStackBase]
    rw [stackAt_split_from_allocHookStack s0.sp hle hbound]
    exact Entails.of_eq (by sep_ac_rfl)

/-! ## `wp_call`-Compatible Extern Contracts -/

/-- `wp_call`-compatible extern wrapper for `rustCliAllocBudgetSpecWithStackBase` (`AllocCallPreserved`
    projected to `sf.trace = s0.trace` on normal return, matching `Hooks2.rustAllocSpecWithStack`). -/
def _root_.LibsignalBinary.Heap.rustCliAllocBudgetExternSpecWithStackBase
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (zeroed : Bool) (stk : Nat := 16384) : Spec (Nat × Nat × M.σ) where
  pre := (rustCliAllocBudgetSpecWithStackBase M A lim zeroed stk).pre
  post := fun (size, align, st) s0 sf =>
    let st' := if sf.readReg64 .x0 = 0 then st else M.stepEvents (rustAllocEvents size align) st
    ⌜sf.trace = s0.trace⌝ ∗ A.pool lim st' sf ∗ stackAt s0.sp stk ∗
      (if sf.readReg64 .x0 = 0 then ⌜NullAllowed size align⌝
       else ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗ A.live (sf.readReg64 .x0) size align ∗
         (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
          else memRegion (sf.readReg64 .x0) size))
  onOom := fun (size, align, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (rustAllocEvents size align) ∧ OomPreserved s0 sf⌝

/-- `wp_call`-compatible extern wrapper for `rustCliDeallocBudgetSpecWithStackBase` (`AllocCallPreserved`
    projected to `sf.trace = s0.trace`, matching `Hooks2.rustDeallocExternSpecWithStack`). -/
def _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStackBase
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := 16384) : Spec (BitVec 64 × Nat × Nat × M.σ) where
  pre := fun (p, size, align, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = size ∧
      (s.readReg64 .x2).toNat = align ∧ RustLayoutOk size align⌝ ∗
      A.pool lim st s ∗ A.live p size align ∗ memRegion p size ∗ stackAt s.sp stk
  post := fun (_, size, align, st) s0 sf =>
    let st' := M.stepEvents (rustDeallocEvents size align) st
    ⌜sf.trace = s0.trace⌝ ∗ A.pool lim st' sf ∗ stackAt s0.sp stk
  onOom := fun _ _ _ => ⌜False⌝

/-- `wp_call`-compatible extern wrapper for `rustCliReallocBudgetSpecWithStackBase` (adds
    `RustLayoutOk old align` in `pre` and projects `AllocCallPreserved` to `sf.trace = s0.trace`,
    matching `Hooks2.rustReallocExternSpecWithStack`). -/
def _root_.LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStackBase
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := 16384) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ) where
  pre := fun (p, old, align, new, bs, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ RustLayoutOk old align ∧ RustLayoutOk new align ∧
      bs.length ≤ old ∧ bs.length ≤ new⌝ ∗
      A.pool lim st s ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp stk
  post := fun (p, old, align, new, bs, st) s0 sf =>
    let st' := if sf.readReg64 .x0 = 0 then st else M.stepEvents (rustReallocEvents old new align) st
    A.pool lim st' sf ∗ stackAt s0.sp stk ∗
      (if sf.readReg64 .x0 = 0 then
        ⌜sf.trace = s0.trace ∧ NullAllowed new align⌝ ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
          memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)
       else
        ⌜(sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace⌝ ∗
          A.live (sf.readReg64 .x0) new align ∗ (sf.readReg64 .x0 ↦ₛ bs) ∗
          memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length))
  onOom := fun (_, old, align, new, _, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (rustReallocEvents old new align) ∧ OomPreserved s0 sf⌝

/-- `wp_call`-compatible total-correctness (`NoOom`) extern wrapper for `__rust_alloc`. -/
def _root_.LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStackBase
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (zeroed : Bool) (stk : Nat := 16384) : Spec (Nat × Nat × M.σ) where
  pre := (rustCliAllocNoOomSpecWithStackBase M A lim zeroed stk).pre
  post := fun (size, align, st) s0 sf =>
    let st' := M.stepEvents (rustAllocEvents size align) st
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % align = 0⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp stk ∗
      A.live (sf.readReg64 .x0) size align ∗
      (if zeroed then (sf.readReg64 .x0 ↦ₛ List.replicate size 0#8)
       else memRegion (sf.readReg64 .x0) size)
  onOom := fun _ _ _ => ⌜False⌝

abbrev _root_.LibsignalBinary.Heap.rustCliDeallocNoOomExternSpecWithStackBase
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := 16384) : Spec (BitVec 64 × Nat × Nat × M.σ) :=
  _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStackBase M A lim stk

/-- `wp_call`-compatible total-correctness (`NoOom`) extern wrapper for `__rust_realloc`. -/
def _root_.LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStackBase
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (stk : Nat := 16384) :
    Spec (BitVec 64 × Nat × Nat × Nat × List (BitVec 8) × M.σ) where
  pre := fun (p, old, align, new, bs, st) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = old ∧ (s.readReg64 .x2).toNat = align ∧
      (s.readReg64 .x3).toNat = new ∧ RustLayoutOk old align ∧ RustLayoutOk new align ∧
      bs.length ≤ old ∧ bs.length ≤ new ∧ FitsEvents M lim st (rustReallocEvents old new align)⌝ ∗
      A.pool lim st s ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length) ∗ stackAt s.sp stk
  post := fun (_, old, align, new, bs, st) s0 sf =>
    let st' := M.stepEvents (rustReallocEvents old new align) st
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % align = 0⌝ ∗
      A.pool lim st' sf ∗ stackAt s0.sp stk ∗
      A.live (sf.readReg64 .x0) new align ∗
      (sf.readReg64 .x0 ↦ₛ bs) ∗
      memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length)
  onOom := fun _ _ _ => ⌜False⌝

abbrev rustCliAllocBudgetExternSpecWithStackBase :=
  @_root_.LibsignalBinary.Heap.rustCliAllocBudgetExternSpecWithStackBase
abbrev rustCliDeallocBudgetExternSpecWithStackBase :=
  @_root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStackBase
abbrev rustCliReallocBudgetExternSpecWithStackBase :=
  @_root_.LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStackBase
abbrev rustCliAllocNoOomExternSpecWithStackBase :=
  @_root_.LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStackBase
abbrev rustCliDeallocNoOomExternSpecWithStackBase :=
  @_root_.LibsignalBinary.Heap.rustCliDeallocNoOomExternSpecWithStackBase
abbrev rustCliReallocNoOomExternSpecWithStackBase :=
  @_root_.LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStackBase

private theorem pure_sepConj_imp {P Q : Prop} {R : SepProp} (h : P → Q) :
    ⌜P⌝ ∗ R ⊢ ⌜Q⌝ ∗ R :=
  Entails.pure_left fun hp => Entails.pure_right (h hp) (Entails.refl R)

theorem subroutine_ok_rustCliAllocBudget_externWithStackBase {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide)
    (h : subroutine_ok prog entry (rustCliAllocBudgetSpecBase M A lim zeroed)) :
    subroutine_ok prog entry (rustCliAllocBudgetExternSpecWithStackBase M A lim zeroed stk) := by
  refine subroutine_ok_frame_oom' (fun _ _ => emp)
    (subroutine_ok_rustCliAllocBudget_withStackBase hle hbound h) ?_ ?_
  · rintro ⟨size, align, st⟩ s0
    rw [sepConj_emp]
    exact Entails.refl _
  · rintro ⟨size, align, st⟩ s0 sf
    dsimp only [rustCliAllocBudgetSpecWithStackBase, rustCliAllocBudgetExternSpecWithStackBase,
      _root_.LibsignalBinary.Heap.rustCliAllocBudgetExternSpecWithStackBase]
    rw [sepConj_emp]
    exact pure_sepConj_imp (fun hacp => hacp.2.1)

theorem subroutine_ok_rustCliDeallocBudget_externWithStackBase {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide)
    (h : subroutine_ok prog entry (rustCliDeallocBudgetSpecBase M A lim)) :
    subroutine_ok prog entry (rustCliDeallocBudgetExternSpecWithStackBase M A lim stk) := by
  refine subroutine_ok_frame_oom' (fun _ _ => emp)
    (subroutine_ok_rustCliDeallocBudget_withStackBase hle hbound h) ?_ ?_
  · rintro ⟨p, size, align, st⟩ s0
    dsimp only [rustCliDeallocBudgetSpecWithStackBase, rustCliDeallocBudgetExternSpecWithStackBase,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStackBase]
    rw [sepConj_emp]
    exact pure_sepConj_imp (fun ⟨h0, h1, h2, _hl⟩ => ⟨h0, h1, h2⟩)
  · rintro ⟨p, size, align, st⟩ s0 sf
    dsimp only [rustCliDeallocBudgetSpecWithStackBase, rustCliDeallocBudgetExternSpecWithStackBase,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStackBase]
    rw [sepConj_emp]
    exact pure_sepConj_imp (fun ⟨hacp, _⟩ => hacp.2.1)

theorem subroutine_ok_rustCliReallocBudget_externWithStackBase {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide)
    (h : subroutine_ok prog entry (rustCliReallocBudgetSpecBase M A lim)) :
    subroutine_ok prog entry (rustCliReallocBudgetExternSpecWithStackBase M A lim stk) := by
  refine subroutine_ok_frame_oom' (fun _ _ => emp)
    (subroutine_ok_rustCliReallocBudget_withStackBase hle hbound h) ?_ ?_
  · rintro ⟨p, old, align, new, bs, st⟩ s0
    dsimp only [rustCliReallocBudgetSpecWithStackBase, rustCliReallocBudgetExternSpecWithStackBase,
      _root_.LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStackBase]
    rw [sepConj_emp]
    exact pure_sepConj_imp
      (fun ⟨h0, h1, h2, h3, _hold, hnew, hblo, hbln⟩ =>
        ⟨h0, h1, h2, h3, hnew, hblo, hbln⟩)
  · rintro ⟨p, old, align, new, bs, st⟩ s0 sf
    dsimp only [rustCliReallocBudgetSpecWithStackBase, rustCliReallocBudgetExternSpecWithStackBase,
      _root_.LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStackBase]
    rw [sepConj_emp]
    by_cases h0 : sf.readReg64 .x0 = 0
    · simp only [h0, ↓reduceIte]
      refine Entails.pure_left fun hacp => ?_
      refine Entails.trans
        (Q := ⌜NullAllowed new align⌝ ∗
          (A.pool lim st sf ∗ stackAt s0.sp stk ∗ A.live p old align ∗ (p ↦ₛ bs) ∗
            memRegion (p + BitVec.ofNat 64 bs.length) (old - bs.length)))
        (Entails.of_eq (by sep_ac_rfl)) ?_
      refine Entails.trans
        (pure_sepConj_imp (fun hnull => (⟨hacp.2.1, hnull⟩ : sf.trace = s0.trace ∧ NullAllowed new align))) ?_
      exact Entails.of_eq (by sep_ac_rfl)
    · simp only [h0, ↓reduceIte]
      refine Entails.pure_left fun hacp => ?_
      refine Entails.trans
        (Q := ⌜(sf.readReg64 .x0).toNat % align = 0⌝ ∗
          (A.pool lim (M.stepEvents (rustReallocEvents old new align) st) sf ∗
            stackAt s0.sp stk ∗ A.live (sf.readReg64 .x0) new align ∗
            (sf.readReg64 .x0 ↦ₛ bs) ∗
            memRegion (sf.readReg64 .x0 + BitVec.ofNat 64 bs.length) (new - bs.length)))
        (Entails.of_eq (by sep_ac_rfl)) ?_
      refine Entails.trans
        (pure_sepConj_imp (fun hal =>
          (⟨hal, hacp.2.1⟩ : (sf.readReg64 .x0).toNat % align = 0 ∧ sf.trace = s0.trace))) ?_
      exact Entails.of_eq (by sep_ac_rfl)

theorem subroutine_ok_rustCliAllocNoOom_externWithStackBase {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide)
    (h : subroutine_ok prog entry (rustCliAllocNoOomSpecBase M A lim zeroed)) :
    subroutine_ok prog entry (rustCliAllocNoOomExternSpecWithStackBase M A lim zeroed stk) := by
  refine subroutine_ok_frame_oom' (fun _ _ => emp)
    (subroutine_ok_rustCliAllocNoOom_withStackBase hle hbound h) ?_ ?_
  · rintro ⟨size, align, st⟩ s0
    rw [sepConj_emp]
    exact Entails.refl _
  · rintro ⟨size, align, st⟩ s0 sf
    dsimp only [rustCliAllocNoOomSpecWithStackBase, rustCliAllocNoOomExternSpecWithStackBase,
      _root_.LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStackBase]
    rw [sepConj_emp]
    exact pure_sepConj_imp (fun ⟨hacp, hne, hal⟩ => ⟨hacp.2.1, hne, hal⟩)

theorem subroutine_ok_rustCliReallocNoOom_externWithStackBase {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {stk : Nat}
    (hle : allocHookStack ≤ stk := by decide) (hbound : stk ≤ 2 ^ 64 := by decide)
    (h : subroutine_ok prog entry (rustCliReallocNoOomSpecBase M A lim)) :
    subroutine_ok prog entry (rustCliReallocNoOomExternSpecWithStackBase M A lim stk) := by
  refine subroutine_ok_frame_oom' (fun _ _ => emp)
    (subroutine_ok_rustCliReallocNoOom_withStackBase hle hbound h) ?_ ?_
  · rintro ⟨p, old, align, new, bs, st⟩ s0
    dsimp only [rustCliReallocNoOomSpecWithStackBase, rustCliReallocNoOomExternSpecWithStackBase,
      _root_.LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStackBase]
    rw [sepConj_emp]
    exact pure_sepConj_imp
      (fun ⟨h0, h1, h2, h3, _hold, hnew, hblo, hbln, hfit⟩ =>
        ⟨h0, h1, h2, h3, hnew, hblo, hbln, hfit⟩)
  · rintro ⟨p, old, align, new, bs, st⟩ s0 sf
    dsimp only [rustCliReallocNoOomSpecWithStackBase, rustCliReallocNoOomExternSpecWithStackBase,
      _root_.LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStackBase]
    rw [sepConj_emp]
    exact pure_sepConj_imp (fun ⟨hacp, hne, hal⟩ => ⟨hacp.2.1, hne, hal⟩)

end LibsignalBinary.Heap.IfaceBudgetLemmas

namespace LibsignalBinary.Heap
export LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStackBase
  rustCliDeallocBudgetSpecWithStackBase
  rustCliReallocBudgetSpecWithStackBase
  rustCliAllocNoOomSpecWithStackBase
  rustCliDeallocNoOomSpecWithStackBase
  rustCliReallocNoOomSpecWithStackBase
)
end LibsignalBinary.Heap

namespace LibsignalBinary.Heap.SpecBudget

open Arm64 ProofLib
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget
  rustCliAllocBudgetSpecBase rustCliDeallocBudgetSpecBase rustCliReallocBudgetSpecBase
  RustCliAllocBudgetHooksBase
)

/-- Hook-mode bundle for conditional-OOM budget-threaded allocator contracts at a fixed `lim`,
    mirroring `AllocHooks A hooks` (`ProofLib/Abi/Rust/Heap/Alloc.lean`). -/
structure AllocHooksBudgetBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hooks : String → Option (State → State)) : Prop where
  alloc : HookSat hooks "__rustc::__rust_alloc" (rustCliAllocBudgetSpecBase M A lim false)
  dealloc : HookSat hooks "__rustc::__rust_dealloc" (rustCliDeallocBudgetSpecBase M A lim)
  realloc : HookSat hooks "__rustc::__rust_realloc" (rustCliReallocBudgetSpecBase M A lim)

theorem RustCliAllocBudgetHooksBase.atLim {M : AllocCostModel} {A : RustCliAllocBudget M}
    {hooks : String → Option (State → State)}
    (h : RustCliAllocBudgetHooksBase M A hooks) (lim : BudgetLimits) :
    AllocHooksBudgetBase M A lim hooks :=
  ⟨h.alloc lim, h.dealloc lim, h.realloc lim⟩

/-- Budget-threaded counterpart of `rustAllocZeroedSpec` (`rustCliAllocBudgetSpecBase M A lim true`). -/
abbrev rustAllocZeroedBudgetSpecBase (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (Nat × Nat × M.σ) :=
  rustCliAllocBudgetSpecBase M A lim true

end LibsignalBinary.Heap.SpecBudget

namespace LibsignalBinary.Heap
export LibsignalBinary.Heap.SpecBudget (
  AllocHooksBudgetBase
  rustAllocZeroedBudgetSpecBase
)
end LibsignalBinary.Heap
