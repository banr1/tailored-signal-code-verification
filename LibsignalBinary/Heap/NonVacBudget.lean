/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import ProofLib
public import LibsignalBinary.Heap.IfaceBudgetBase

/-!
# Budget-Threaded Allocator Non-Vacuity and Caller-Threading Examples

Non-vacuity client proofs (`onOom := ⌜False⌝` under `FitsEvents`/`FitsTraceOf` and conditional-OOM
witness extraction without `FitsEvents`) and multi-call `FitsTrace`/`SeqEnv` reductions over
`LibsignalBinary.Heap.IfaceBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Heap

open Arm64 ProofLib SepProp
open CryptoVerification.RustHeap (allocHookStack)

private theorem entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

/-! ## Total-Correctness (`NoOom`) Client (`__rust_alloc(72, 8)`) -/

/-- Total-correctness (`onOom := ⌜False⌝`) client contract for calling `__rust_alloc(72, 8)` under
    `FitsEvents M lim st [.alloc 72]`. -/
def smokeAlloc72NoOomSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec M.σ where
  pre := fun st s =>
    ⌜s.readReg64 .x0 = 72#64 ∧ s.readReg64 .x1 = 8#64 ∧
      FitsEvents M lim st [.alloc 72]⌝ ∗
      A.pool lim st s ∗ stackAt s.sp allocHookStack
  post := fun st s0 sf =>
    ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % 8 = 0 ∧
      (sf.readReg64 .x0).toNat + 72 < 2 ^ 64⌝ ∗
      A.pool lim (M.step (.alloc 72) st) sf ∗
      stackAt s0.sp allocHookStack ∗
      A.live (sf.readReg64 .x0) 72 8 ∗
      memRegion (sf.readReg64 .x0) 72
  onOom := fun _ _ _ => ⌜False⌝

/-- Under `FitsEvents M lim st [.alloc 72]`, calling `addrs.alloc(72, 8)` satisfies
`smokeAlloc72NoOomSpec` (`onPanic = ⌜False⌝`, `onExit = ⌜False⌝`, `onOom = ⌜False⌝`). -/
theorem rustCliAllocNoOom_smoke_alloc72_at {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {P : Program} {addrs : RustAllocAddrs}
    (hEntries : RustCliAllocNoOomEntriesBase M A lim P addrs)
    (hFit : FitsEvents M lim st [.alloc 72])
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = addrs.alloc)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = 72#64)
    (hx1 : s0.readReg64 .x1 = 8#64)
    (hmem : s0.mem ⊨ A.pool lim st s0 ∗ stackAt s0.sp allocHookStack ∗ R) :
    reaches_outcome P (smokeAlloc72NoOomSpec M A lim) st R s0 s0 := by
  have hEvEq : rustAllocEvents 72 8 = [.alloc 72] := by decide
  have hLayout : RustLayoutOk 72 8 := ⟨⟨by decide, ⟨3, rfl⟩, by decide⟩, by decide⟩
  have hpure :
      (s0.readReg64 .x0).toNat = 72 ∧ (s0.readReg64 .x1).toNat = 8 ∧
      RustLayoutOk 72 8 ∧ FitsEvents M lim st (rustAllocEvents 72 8) :=
    ⟨by rw [hx0]; decide, by rw [hx1]; decide, hLayout, by rwa [hEvEq]⟩
  have hpre : s0.mem ⊨ (rustCliAllocNoOomSpecBase M A lim false).pre (72, 8, st) s0 ∗ R := by
    refine Satisfies.mono ?_ hmem
    dsimp only [rustCliAllocNoOomSpecBase]
    refine Entails.trans
      (Q := ⌜(s0.readReg64 .x0).toNat = 72 ∧ (s0.readReg64 .x1).toNat = 8 ∧
        RustLayoutOk 72 8 ∧ FitsEvents M lim st (rustAllocEvents 72 8)⌝ ∗
        (A.pool lim st s0 ∗ stackAt s0.sp allocHookStack ∗ R))
      (Entails.pure_right hpure (Entails.refl _)) ?_
    exact entails_of_eq (by simp only [sepConj_assoc])
  refine subroutine_ok.mono_outcome hEntries.alloc (72, 8, st) R s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpanic⟩ | ⟨c, hex, hexit⟩ | ⟨ho, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustCliAllocNoOomSpecBase] at hpost
    rw [hEvEq] at hpost
    dsimp only [AllocCostModel.stepEvents, List.foldl] at hpost
    simp only [Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hpost
    obtain ⟨⟨hacp, hne0, hal8⟩, hpost1⟩ := (satisfies_pure_sepConj _ _ _).1 hpost
    have hpost2 := Satisfies.mono
      (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (A.block_valid (sf.readReg64 .x0) 72 8)))) hpost1
    simp only [sepConj_assoc] at hpost2
    rw [sepConj_left_comm (stackAt _ _), sepConj_left_comm (A.pool _ _ _)] at hpost2
    obtain ⟨⟨_, _, hfit64, _⟩, hmemf⟩ := (satisfies_pure_sepConj _ _ _).1 hpost2
    dsimp only [smokeAlloc72NoOomSpec]
    simp only [sepConj_assoc]
    exact (satisfies_pure_sepConj _ _ _).2 ⟨⟨hacp, hne0, hal8, hfit64⟩, hmemf⟩
  · exact Or.inr (Or.inl ⟨hp, hpanic⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hex, hexit⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

theorem rustCliAllocNoOom_smoke_alloc72_subroutine_ok {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hEntries : RustCliAllocNoOomEntriesBase M A lim P addrs) :
    subroutine_ok P addrs.alloc (smokeAlloc72NoOomSpec M A lim) := by
  apply subroutine_ok.of_codeLoaded
  intro st R s0 hpc hrun hpre hsp _
  dsimp only [smokeAlloc72NoOomSpec] at hpre
  simp only [sepConj_assoc] at hpre
  obtain ⟨⟨hx0, hx1, hFit⟩, hmem⟩ := (satisfies_pure_sepConj _ _ _).1 hpre
  exact rustCliAllocNoOom_smoke_alloc72_at hEntries hFit R s0 hpc hrun hsp hx0 hx1 hmem

/-- Derive `FitsEvents M lim M.init [.alloc 72]` from `FitsTraceOf M lim [.alloc 72]` and prove `reaches_outcome` for `smokeAlloc72NoOomSpec`. -/
theorem rustCliAllocBudget_smoke_alloc72 {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {P : Program} {addrs : RustAllocAddrs}
    (hEntries : RustCliAllocBudgetEntriesBase M A P addrs)
    (hFit : FitsTraceOf M lim [.alloc 72])
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = addrs.alloc)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = 72#64)
    (hx1 : s0.readReg64 .x1 = 8#64)
    (hmem : s0.mem ⊨ A.pool lim M.init s0 ∗ stackAt s0.sp allocHookStack ∗ R) :
    reaches_outcome P (smokeAlloc72NoOomSpec M A lim) M.init R s0 s0 := by
  have hFitEvs : FitsEvents M lim M.init [.alloc 72] :=
    fitsEvents_of_subtrace_fitsTrace (pre := []) (suf := []) rfl hFit
  exact rustCliAllocNoOom_smoke_alloc72_at (hEntries.toNoOom lim) hFitEvs
    R s0 hpc hrun hsp hx0 hx1 hmem

/-! ## Conditional-OOM Client (`¬ FitsEvents` Witness on `.OutOfMemory`) -/

/-- Conditional-OOM client contract for `__rust_alloc(72, 8)` without assuming `FitsEvents`:
    `.OutOfMemory` carries `¬ FitsEvents M lim st [.alloc 72] ∧ OomPreserved s0 sf`. -/
def smokeAlloc72ConditionalSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec M.σ where
  pre := fun st s =>
    ⌜s.readReg64 .x0 = 72#64 ∧ s.readReg64 .x1 = 8#64⌝ ∗
      A.pool lim st s ∗ stackAt s.sp allocHookStack
  post := fun st s0 sf =>
    ⌜AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % 8 = 0 ∧
      (sf.readReg64 .x0).toNat + 72 < 2 ^ 64⌝ ∗
      A.pool lim (M.step (.alloc 72) st) sf ∗
      stackAt s0.sp allocHookStack ∗
      A.live (sf.readReg64 .x0) 72 8 ∗
      memRegion (sf.readReg64 .x0) 72
  onOom := fun st s0 sf =>
    ⌜¬ FitsEvents M lim st [.alloc 72] ∧ OomPreserved s0 sf⌝

/-- Without assuming `FitsEvents`, `RustCliAllocBudgetEntries` guarantees `reaches_outcome` for
    `smokeAlloc72ConditionalSpec` (so `.OutOfMemory` is accompanied by
    `¬ FitsEvents M lim st [.alloc 72]`). -/
theorem rustCliAllocBudget_smoke_alloc72_conditional {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {P : Program} {addrs : RustAllocAddrs}
    (hEntries : RustCliAllocBudgetEntriesBase M A P addrs)
    (R : SepProp) (s0 : State)
    (hpc : s0.pc = addrs.alloc)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = 72#64)
    (hx1 : s0.readReg64 .x1 = 8#64)
    (hmem : s0.mem ⊨ A.pool lim st s0 ∗ stackAt s0.sp allocHookStack ∗ R) :
    reaches_outcome P (smokeAlloc72ConditionalSpec M A lim) st R s0 s0 := by
  have hEvEq : rustAllocEvents 72 8 = [.alloc 72] := by decide
  have hLayout : RustLayoutOk 72 8 := ⟨⟨by decide, ⟨3, rfl⟩, by decide⟩, by decide⟩
  have hpure : (s0.readReg64 .x0).toNat = 72 ∧ (s0.readReg64 .x1).toNat = 8 ∧ RustLayoutOk 72 8 :=
    ⟨by rw [hx0]; decide, by rw [hx1]; decide, hLayout⟩
  have hpre : s0.mem ⊨ (rustCliAllocBudgetSpecBase M A lim false).pre (72, 8, st) s0 ∗ R := by
    refine Satisfies.mono ?_ hmem
    dsimp only [rustCliAllocBudgetSpecBase]
    refine Entails.trans
      (Q := ⌜(s0.readReg64 .x0).toNat = 72 ∧ (s0.readReg64 .x1).toNat = 8 ∧ RustLayoutOk 72 8⌝ ∗
        (A.pool lim st s0 ∗ stackAt s0.sp allocHookStack ∗ R))
      (Entails.pure_right hpure (Entails.refl _)) ?_
    exact entails_of_eq (by simp only [sepConj_assoc])
  refine subroutine_ok.mono_outcome (hEntries.alloc lim) (72, 8, st) R s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpanic⟩ | ⟨c, hex, hexit⟩ | ⟨hoomStatus, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustCliAllocBudgetSpecBase] at hpost
    rw [hEvEq] at hpost
    dsimp only [AllocCostModel.stepEvents, List.foldl] at hpost
    by_cases hnull : sf.readReg64 .x0 = 0
    · simp only [hnull, ↓reduceIte, sepConj_assoc] at hpost
      obtain ⟨_, hpost1⟩ := (satisfies_pure_sepConj _ _ _).1 hpost
      rw [sepConj_left_comm (stackAt _ _), sepConj_left_comm (A.pool _ _ _)] at hpost1
      have hfalse : NullAllowed 72 8 := ((satisfies_pure_sepConj _ _ _).1 hpost1).1
      unfold NullAllowed at hfalse
      omega
    · simp only [hnull, Bool.false_eq_true, ↓reduceIte, sepConj_assoc] at hpost
      obtain ⟨hacp, hpost1⟩ := (satisfies_pure_sepConj _ _ _).1 hpost
      rw [sepConj_left_comm (stackAt _ _), sepConj_left_comm (A.pool _ _ _)] at hpost1
      obtain ⟨_, hpost2⟩ := (satisfies_pure_sepConj _ _ _).1 hpost1
      have hpost3 := Satisfies.mono
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (A.block_valid (sf.readReg64 .x0) 72 8)))) hpost2
      simp only [sepConj_assoc] at hpost3
      rw [sepConj_left_comm (stackAt _ _), sepConj_left_comm (A.pool _ _ _)] at hpost3
      obtain ⟨⟨hne0, hal8, hfit64, _⟩, hmemf⟩ := (satisfies_pure_sepConj _ _ _).1 hpost3
      dsimp only [smokeAlloc72ConditionalSpec]
      simp only [sepConj_assoc]
      exact (satisfies_pure_sepConj _ _ _).2 ⟨⟨hacp, hne0, hal8, hfit64⟩, hmemf⟩
  · exact Or.inr (Or.inl ⟨hp, hpanic⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hex, hexit⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨hoomStatus, ?_⟩))
    dsimp only [rustCliAllocBudgetSpecBase] at hoom
    rw [hEvEq] at hoom
    exact hoom

/-! ## Multi-Call `FitsTrace` and `SeqEnv` Reductions -/

/-- Canonical 3-call caller trace: `alloc(32, 8)` → `realloc(32 → 64, 8)` → `dealloc(64, 8)`. -/
def workedCallerTrace : List AllocEvent :=
  rustAllocEvents 32 8 ++ rustReallocEvents 32 64 8 ++ rustDeallocEvents 64 8

/-- A single `FitsTrace M lim maxStep workedCallerTrace` hypothesis discharges per-call `FitsEvents` across `alloc(32, 8)`, `realloc(32 → 64, 8)`, and `dealloc(64, 8)`. -/
theorem rustCliAllocNoOom_worked_trace_obligations (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (maxStep : Nat)
    (hFit : FitsTrace M lim maxStep workedCallerTrace)
    (sAfterAlloc sBeforeRealloc : State) (hvm : VmPreserved sAfterAlloc sBeforeRealloc) :
    let st0 := M.init
    let st1 := M.stepEvents (rustAllocEvents 32 8) st0
    let st2 := M.stepEvents (rustReallocEvents 32 64 8) st1
    let st3 := M.stepEvents (rustDeallocEvents 64 8) st2
    FitsEvents M lim st0 (rustAllocEvents 32 8) ∧
    (A.atState lim st1 sAfterAlloc).pool = A.pool lim st1 sBeforeRealloc ∧
    FitsEvents M lim st1 (rustReallocEvents 32 64 8) ∧
    FreeOnlyEvs (rustDeallocEvents 64 8) ∧
    st3 = M.evalLog workedCallerTrace := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fitsEvents_of_subtrace_fitsTrace
      (pre := []) (suf := rustReallocEvents 32 64 8 ++ rustDeallocEvents 64 8)
      (by simp [workedCallerTrace, List.append_assoc]) hFit
  · rw [A.atState_pool, A.pool_transport lim _ sAfterAlloc sBeforeRealloc hvm]
  · exact fitsEvents_of_subtrace_fitsTrace
      (pre := rustAllocEvents 32 8) (suf := rustDeallocEvents 64 8)
      (by simp [workedCallerTrace, List.append_assoc]) hFit
  · exact FreeOnlyEvs.singleton 8 64
  · unfold workedCallerTrace AllocCostModel.evalLog
    rw [M.stepEvents_append, M.stepEvents_append]

/-- Split `FitsEnv M lim st (SeqEnv E₁ E₂)` across two sequential callees emitting `evs₁` and `evs₂`. -/
theorem rustCliAllocNoOom_worked_seqEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {E₁ E₂ : List AllocEvent → Prop} {evs₁ evs₂ : List AllocEvent}
    (hEnv : FitsEnv M lim st (SeqEnv E₁ E₂))
    (h1 : E₁ evs₁) (h2 : E₂ evs₂) :
    FitsEnv M lim st E₁ ∧
    FitsEnv M lim (M.stepEvents evs₁ st) E₂ ∧
    SeqEnv E₁ E₂ (evs₁ ++ evs₂) ∧
    M.stepEvents evs₂ (M.stepEvents evs₁ st) = M.stepEvents (evs₁ ++ evs₂) st :=
  ⟨hEnv.seq_left, hEnv.seq_right h1, SeqEnv.append h1 h2, (M.stepEvents_append evs₁ evs₂ st).symm⟩

end LibsignalBinary.Heap
