/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.DefsV1StateBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesEncodedLen
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget

/-!
# Budget-Threaded Allocator Stack Wrappers for `spqr::send`

Stack-framed `spqrSendCalleeStack` specifications and `subroutine_ok` lifting lemmas for the
allocator no-op shim and `__rust_alloc` in `spqr::send` under `RustCliAllocBudget`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesEncodedLenBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.SpqrV1.Top.Send (spqrSendCalleeStack)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEvents NullAllowed OomPreserved
  RustCliAllocBudget VmPreserved not_nullAllowed_of_fitsAllocEvents rustAllocEvents
  rustCliAllocBudgetSpec rustCliAllocNoOomSpec subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStack rustCliAllocNoOomSpecWithStack
  subroutine_ok_rustCliAllocBudget_withStack subroutine_ok_rustCliAllocNoOom_withStack
)
open LibsignalBinary.Heap.IfaceLemmas (subroutine_ok_frame_oom')
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)

/-- Budget-threaded stack-equipped no-op shim contract at `s.sp` with `spqrSendCalleeStack`,
    preserving `AllocCallPreserved` and `VmPreserved` so `A.pool` transports across the call. -/
def spqrSendShimStackSpec : Spec Unit where
  pre := fun _ s => stackAt s.sp spqrSendCalleeStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ VmPreserved s0 sf⌝ ∗
      stackAt s0.sp spqrSendCalleeStack

/-- Budget-threaded stack-equipped `__rust_alloc(sz, 1)` conditional-OOM contract at `s.sp` with
    `spqrSendCalleeStack`. -/
def spqrSendRustAllocStackSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (Nat × M.σ) where
  pre := fun (sz, st) s =>
    ⌜(s.readReg64 .x0).toNat = sz ∧ s.readReg64 .x1 = 1#64 ∧ 0 < sz ∧ sz < 2 ^ 63 ∧
      LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack
  post := fun (sz, st) s0 sf =>
    ⌜AllocCallPreserved s0 sf⌝ ∗
      A.pool lim (if sf.readReg64 .x0 = 0#64 then st else M.stepEvents (rustAllocEvents sz 1) st) sf ∗
      stackAt s0.sp spqrSendCalleeStack ∗
      if sf.readReg64 .x0 = 0#64 then
        ⌜NullAllowed sz 1⌝
      else
        A.live (sf.readReg64 .x0) sz 1 ∗ memRegion (sf.readReg64 .x0) sz
  onOom := fun (sz, st) s0 sf =>
    ⌜¬ FitsEvents M lim st (rustAllocEvents sz 1) ∧ OomPreserved s0 sf⌝

/-- Budget-threaded stack-equipped `__rust_alloc(sz, 1)` total-correctness (`NoOom`) contract at
    `s.sp` with `spqrSendCalleeStack` when `FitsEvents M lim st (rustAllocEvents sz 1)` holds. -/
def spqrSendRustAllocNoOomStackSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (Nat × M.σ) where
  pre := fun (sz, st) s =>
    ⌜(s.readReg64 .x0).toNat = sz ∧ s.readReg64 .x1 = 1#64 ∧ 0 < sz ∧ sz < 2 ^ 63 ∧
      FitsEvents M lim st (rustAllocEvents sz 1) ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      A.pool lim st s ∗ stackAt s.sp spqrSendCalleeStack
  post := fun (sz, st) s0 sf =>
    ⌜sf.trace = s0.trace ∧ AllocCallPreserved s0 sf ∧ sf.readReg64 .x0 ≠ 0#64⌝ ∗
      A.live (sf.readReg64 .x0) sz 1 ∗ memRegion (sf.readReg64 .x0) sz ∗
      A.pool lim (M.stepEvents (rustAllocEvents sz 1) st) sf ∗
      stackAt s0.sp spqrSendCalleeStack

/-- Lift `rustAllocShimVmSpec` to `spqrSendShimStackSpec` by framing `stackAt s.sp
    spqrSendCalleeStack`. -/
theorem subroutine_ok_spqrSendShimStackSpec {prog : Program} {entry : BitVec 64}
    (hshim : subroutine_ok prog entry rustAllocShimVmSpec) :
    subroutine_ok prog entry spqrSendShimStackSpec := by
  refine subroutine_ok_frame_oom' (fun _ s0 => stackAt s0.sp spqrSendCalleeStack) hshim ?_ ?_
  · intro _ s0
    dsimp only [rustAllocShimVmSpec, spqrSendShimStackSpec]
    rw [emp_sepConj]
    exact Entails.refl _
  · intro _ s0 sf
    dsimp only [rustAllocShimVmSpec, spqrSendShimStackSpec]
    refine Entails.pure_left fun ⟨hacp, hvm⟩ => ?_
    exact Entails.pure_right ⟨hacp.2.1, hacp, hvm⟩ (Entails.refl _)

/-- Lift `rustCliAllocBudgetSpec M A lim false` to `spqrSendRustAllocStackSpec M A lim`. -/
theorem subroutine_ok_spqrSendRustAllocStackSpec [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (halloc : subroutine_ok prog entry (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok prog entry (spqrSendRustAllocStackSpec M A lim) := by
  have hstk := subroutine_ok_rustCliAllocBudget_withStack
    (stk := spqrSendCalleeStack) (by decide) (by decide) halloc
  refine subroutine_ok.of_codeLoaded fun ⟨sz, st⟩ R s hpc hrun hpre hal _ => ?_
  dsimp only [spqrSendRustAllocStackSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hpos, hlt, hlr⟩, hrest⟩
  have hpre' : s.mem ⊨ (rustCliAllocBudgetSpecWithStack M A lim false spqrSendCalleeStack).pre (sz, 1, st) s ∗ R := by
    dsimp only [rustCliAllocBudgetSpecWithStack]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    have hx1' : (s.readReg64 .x1).toNat = 1 := by rw [hx1]; rfl
    exact ⟨⟨hx0, hx1', ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩, hlr⟩, hrest⟩
  refine hstk.mono_outcome (sz, 1, st) R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustCliAllocBudgetSpecWithStack, spqrSendRustAllocStackSpec] at hpost ⊢
    by_cases hnull : sf.readReg64 .x0 = 0
    · have hnull64 : sf.readReg64 .x0 = 0#64 := hnull
      simp only [hnull, ↓reduceIte] at hpost
      simp only [hnull64, ↓reduceIte]
      exact hpost
    · have hnull64 : sf.readReg64 .x0 ≠ 0#64 := hnull
      simp only [hnull, Bool.false_eq_true, ↓reduceIte] at hpost
      simp only [hnull64, ↓reduceIte]
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
      exact Entails.pure_left fun _ => Entails.refl _
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

/-- Lift `rustCliAllocBudgetSpec M A lim false` to total-correctness
    `spqrSendRustAllocNoOomStackSpec M A lim` when `FitsEvents M lim st (rustAllocEvents sz 1)`
    holds. -/
theorem subroutine_ok_spqrSendRustAllocNoOomStackSpec [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} {entry : BitVec 64}
    (halloc : subroutine_ok prog entry (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok prog entry (spqrSendRustAllocNoOomStackSpec M A lim) := by
  have hnooom := subroutine_ok_rustCliAllocNoOom_withStack
    (stk := spqrSendCalleeStack) (by decide) (by decide)
    (subroutine_ok_allocNoOom_of_budget halloc)
  refine subroutine_ok.of_codeLoaded fun ⟨sz, st⟩ R s hpc hrun hpre hal _ => ?_
  dsimp only [spqrSendRustAllocNoOomStackSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hpos, hlt, hfit, hlr⟩, hrest⟩
  have hpre' : s.mem ⊨ (rustCliAllocNoOomSpecWithStack M A lim false spqrSendCalleeStack).pre (sz, 1, st) s ∗ R := by
    dsimp only [rustCliAllocNoOomSpecWithStack]
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    have hx1' : (s.readReg64 .x1).toNat = 1 := by rw [hx1]; rfl
    exact ⟨⟨hx0, hx1', ⟨⟨hpos, ⟨0, rfl⟩, by omega⟩, by decide⟩, hfit, hlr⟩, hrest⟩
  refine hnooom.mono_outcome (sz, 1, st) R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustCliAllocNoOomSpecWithStack, spqrSendRustAllocNoOomStackSpec] at hpost ⊢
    simp only [Bool.false_eq_true, ↓reduceIte] at hpost
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    refine Entails.pure_left fun ⟨hacp, hne0, _⟩ => ?_
    refine Entails.pure_right ⟨hacp.2.1, hacp, hne0⟩ ?_
    exact Entails.of_eq (by sep_ac_rfl)
  · exact Or.inr (Or.inl ⟨hp, hpan⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hex⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom⟩))

end LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesEncodedLenBudget
