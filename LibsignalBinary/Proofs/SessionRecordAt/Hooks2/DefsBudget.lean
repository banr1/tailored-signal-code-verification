/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Defs
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.SessionRecordAt.TripleRatchet.HooksX

/-!
# Budget-Threaded `withLsCodeLoaded` Combinators and Allocator Bundles

OOM-preserving `subroutine_ok` consequence and stack-slack framing lemmas under `withLsCodeLoaded`
and `withLsCl`, together with `RustCliAllocBudget`-threaded `[LibsignalPlacement]` allocator
bundles (`AllocContractsXPlaced` and `AllocNoOomContractsXPlaced`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget

open Arm64 ProofLib SepProp
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl withLsCodeLoaded withLsCl
  extract_withLsCodeLoaded lsρ lsRustAllocSym lsRustDeallocSym lsRustReallocSym
)
open CryptoVerification.LibsignalTripleRatchet (
  ls_hook_ok_of_caller ls_subroutine_ok_cl_of_withLsCodeLoaded
  ls_subroutine_ok_cl_of_plain_prog ls_subroutine_ok_cl_of_callee
)
open Proofs.libsignal.Hooks2 (subroutine_ok_withExternStackFromAlloc')
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
  rustCliAllocNoOomSpec rustCliDeallocNoOomSpec rustCliReallocNoOomSpec
  subroutine_ok_allocNoOom_of_budget subroutine_ok_reallocNoOom_of_budget
)
open LibsignalBinary.Heap.IfaceLemmas (
  withHookStackOom withExternStackFromAllocOom' satisfies_drop_mid_entails
  subroutine_ok_withExternStackFromAllocOom'
)

/-! ## 1. OOM-Preserving `withLsCodeLoaded` & `withLsCl` Consequence and Stack-Slack Framing -/

/-- Lift `subroutine_ok_map_oom'` across `withLsCodeLoaded pl`. -/
theorem subroutine_ok_withLsCodeLoaded_map_oom' {α β : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        (∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.onOom x s0 sf ∗ R') → (sf.mem ⊨ spec'.onOom y s0 sf ∗ R)))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code →
        ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec') := by
  refine subroutine_ok_map_oom' h (fun y R s0 hpre => ?_) h_no_panic h_no_exit
  have ⟨hcl, hpre'⟩ := extract_withLsCodeLoaded hpre
  obtain ⟨x, R', hm, hpost, hoom⟩ := hmap y R s0 hpre'
  refine ⟨x, R', ?_, hpost, hoom⟩
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
  exact ⟨hcl, hm⟩

/-- Panic- and OOM-preserving lift across `withLsCodeLoaded pl`. -/
theorem subroutine_ok_withLsCodeLoaded_map_panic_oom' {α β : Type} {prog : Program}
    {entry : BitVec 64} {pl : Obj.MultiPlacement} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        (∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.onPanic x s0 sf ∗ R') →
          (sf.mem ⊨ spec'.onPanic y s0 sf ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.onOom x s0 sf ∗ R') → (sf.mem ⊨ spec'.onOom y s0 sf ∗ R)))
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code →
        ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he) :
    subroutine_ok prog entry (withLsCodeLoaded pl spec') := by
  refine subroutine_ok_outcome_intro fun y R s0 hpc hrun hpre hsp => ?_
  have ⟨hcl, hpre'⟩ := extract_withLsCodeLoaded hpre
  obtain ⟨x, R', hm, hpost, hpan, hoom⟩ := hmap y R s0 hpre'
  have hm_cl : s0.mem ⊨ (withLsCodeLoaded pl spec).pre x s0 ∗ R' := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hm⟩
  refine h.mono_outcome x R' s0 hpc hrun hm_cl hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp_st, hq⟩ | ⟨code, hex, hq⟩ | ⟨ho_st, hq⟩
  · exact Or.inl ⟨hret, hcc, hpost sf hq⟩
  · exact Or.inr (Or.inl ⟨hp_st, hpan sf hq⟩)
  · exact False.elim (h_no_exit x code R' s0 sf hex hq)
  · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hoom sf hq⟩))

/-- Lift `subroutine_ok_map_oom'` across `withLsCl pl`. -/
theorem subroutine_ok_withLsCl_map_oom' {α β : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (withLsCl pl spec))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        (∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.onOom x s0 sf ∗ R') → (sf.mem ⊨ spec'.onOom y s0 sf ∗ R)))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code →
        ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he) :
    subroutine_ok prog entry (withLsCl pl spec') := by
  apply ls_subroutine_ok_cl_of_withLsCodeLoaded
  have h0 : subroutine_ok prog entry (withLsCodeLoaded pl spec) :=
    subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)
  exact subroutine_ok_withLsCodeLoaded_map_oom' h0 hmap h_no_panic h_no_exit

/-- Panic- and OOM-preserving lift across `withLsCl pl`. -/
theorem subroutine_ok_withLsCl_map_panic_oom' {α β : Type} {prog : Program} {entry : BitVec 64}
    {pl : Obj.MultiPlacement} {spec : Spec α} {spec' : Spec β}
    (h : subroutine_ok prog entry (withLsCl pl spec))
    (hmap : ∀ (y : β) (R : SepProp) (s0 : State), (s0.mem ⊨ spec'.pre y s0 ∗ R) →
      ∃ (x : α) (R' : SepProp), (s0.mem ⊨ spec.pre x s0 ∗ R') ∧
        (∀ sf : State, (sf.mem ⊨ spec.post x s0 sf ∗ R') → (sf.mem ⊨ spec'.post y s0 sf ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.onPanic x s0 sf ∗ R') →
          (sf.mem ⊨ spec'.onPanic y s0 sf ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ spec.onOom x s0 sf ∗ R') → (sf.mem ⊨ spec'.onOom y s0 sf ∗ R)))
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code →
        ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he) :
    subroutine_ok prog entry (withLsCl pl spec') := by
  apply ls_subroutine_ok_cl_of_withLsCodeLoaded
  have h0 : subroutine_ok prog entry (withLsCodeLoaded pl spec) :=
    subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
      dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      exact hq.2)
  exact subroutine_ok_withLsCodeLoaded_map_panic_oom' h0 hmap h_no_exit

/-- OOM-preserving stack-slack framing for `Spec.withHookStackOom` under `withLsCodeLoaded pl`. -/
theorem subroutine_ok_withLsCodeLoaded_withHookStackOom_mono {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Obj.MultiPlacement} {spec : Spec α} {s1 s2 : Nat}
    (hle : s1 ≤ s2) (hbound : s2 ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (withLsCodeLoaded pl (spec.withHookStackOom s1)))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code →
        ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he) :
    subroutine_ok prog entry (withLsCodeLoaded pl (spec.withHookStackOom s2)) := by
  refine subroutine_ok_withLsCodeLoaded_map_oom' h (fun x R s0 hpre => ?_) h_no_panic h_no_exit
  have hsplit : s2 = s1 + (s2 - s1) := by omega
  have hstack_pre : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h0 := ProofLib.stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [← hsplit] at h0
  refine ⟨x, memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R, ?_, ?_, ?_⟩
  · change s0.mem ⊨ (spec.pre x s0 ∗ stackAt s0.sp s2) ∗ R at hpre
    rw [hstack_pre] at hpre
    change s0.mem ⊨ (spec.pre x s0 ∗ stackAt s0.sp s1) ∗
      (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R)
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  · intro sf hpost
    change sf.mem ⊨ (spec.post x s0 sf ∗ stackAt s0.sp s1) ∗
      (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R) at hpost
    change sf.mem ⊨ (spec.post x s0 sf ∗ stackAt s0.sp s2) ∗ R
    rw [hstack_pre]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · intro sf hoom
    exact satisfies_drop_mid_entails (Entails.refl _) hoom

/-- OOM-preserving stack-slack framing for `Spec.withHookStackOom` under `withLsCl pl`. -/
theorem subroutine_ok_withLsCl_withHookStackOom_mono {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : Obj.MultiPlacement} {spec : Spec α} {s1 s2 : Nat}
    (hle : s1 ≤ s2) (hbound : s2 ≤ 2 ^ 64)
    (h : subroutine_ok prog entry (withLsCl pl (spec.withHookStackOom s1)))
    (h_no_panic : ∀ x R' s0 sf, sf.status = .Panicked → ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_exit : ∀ x code R' s0 sf, sf.status = .Exited code →
        ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ _ he; exact not_satisfies_false_sepConj he) :
    subroutine_ok prog entry (withLsCl pl (spec.withHookStackOom s2)) := by
  refine subroutine_ok_withLsCl_map_oom' h (fun x R s0 hpre => ?_) h_no_panic h_no_exit
  have hsplit : s2 = s1 + (s2 - s1) := by omega
  have hstack_pre : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h0 := ProofLib.stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [← hsplit] at h0
  refine ⟨x, memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R, ?_, ?_, ?_⟩
  · change s0.mem ⊨ (spec.pre x s0 ∗ stackAt s0.sp s2) ∗ R at hpre
    rw [hstack_pre] at hpre
    change s0.mem ⊨ (spec.pre x s0 ∗ stackAt s0.sp s1) ∗
      (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R)
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpre
  · intro sf hpost
    change sf.mem ⊨ (spec.post x s0 sf ∗ stackAt s0.sp s1) ∗
      (memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R) at hpost
    change sf.mem ⊨ (spec.post x s0 sf ∗ stackAt s0.sp s2) ∗ R
    rw [hstack_pre]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · intro sf hoom
    exact satisfies_drop_mid_entails (Entails.refl _) hoom

/-! ## 2. Budget-Threaded `[LibsignalPlacement]` Allocator Contract Bundles -/

/-- Conditional-OOM budget-threaded `[LibsignalPlacement]` counterpart of
`Hooks2.AllocContractsXPlaced` (`withExternStackFromAllocOom'`). -/
structure AllocContractsXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  alloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocBudgetSpec M A lim false).withExternStackFromAllocOom')
  dealloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocBudgetSpec M A lim).withExternStackFromAllocOom')
  realloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustReallocSym)
      (withLsCl lsmpl (rustCliReallocBudgetSpec M A lim).withExternStackFromAllocOom')

theorem AllocContractsXPlaced.of_block0 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {blk0Prog : Program} [IsLsBlockProg blk0Prog 0 H]
    (halloc : subroutine_ok blk0Prog (lsρ lsRustAllocSym)
      (withLsCodeLoaded lsmpl (rustCliAllocBudgetSpec M A lim false).withExternStackFromAllocOom'))
    (hdealloc : subroutine_ok blk0Prog (lsρ lsRustDeallocSym)
      (withLsCodeLoaded lsmpl (rustCliDeallocBudgetSpec M A lim).withExternStackFromAllocOom'))
    (hrealloc : subroutine_ok blk0Prog (lsρ lsRustReallocSym)
      (withLsCodeLoaded lsmpl (rustCliReallocBudgetSpec M A lim).withExternStackFromAllocOom')) :
    AllocContractsXPlaced A lim H where
  alloc := ls_subroutine_ok_cl_of_callee (j := 0) halloc
  dealloc := ls_subroutine_ok_cl_of_callee (j := 0) hdealloc
  realloc := ls_subroutine_ok_cl_of_callee (j := 0) hrealloc

theorem AllocContractsXPlaced.of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    AllocContractsXPlaced A lim H where
  alloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAllocOom' (ls_hook_ok_of_caller halloc))
  dealloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAllocOom' (ls_hook_ok_of_caller hdealloc))
  realloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAllocOom' (ls_hook_ok_of_caller hrealloc))

/-- Total-correctness (`NoOom` under `FitsEvents`) `[LibsignalPlacement]` counterpart of
`Hooks2.AllocContractsXPlaced` (`withExternStackFromAlloc'`). -/
structure AllocNoOomContractsXPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop where
  alloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustAllocSym)
      (withLsCl lsmpl (rustCliAllocNoOomSpec M A lim false).withExternStackFromAlloc')
  dealloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocNoOomSpec M A lim).withExternStackFromAlloc')
  realloc : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    subroutine_ok callerProg (lsρ lsRustReallocSym)
      (withLsCl lsmpl (rustCliReallocNoOomSpec M A lim).withExternStackFromAlloc')

theorem AllocNoOomContractsXPlaced.of_block0 [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {blk0Prog : Program} [IsLsBlockProg blk0Prog 0 H]
    (halloc : subroutine_ok blk0Prog (lsρ lsRustAllocSym)
      (withLsCodeLoaded lsmpl (rustCliAllocNoOomSpec M A lim false).withExternStackFromAlloc'))
    (hdealloc : subroutine_ok blk0Prog (lsρ lsRustDeallocSym)
      (withLsCodeLoaded lsmpl (rustCliDeallocNoOomSpec M A lim).withExternStackFromAlloc'))
    (hrealloc : subroutine_ok blk0Prog (lsρ lsRustReallocSym)
      (withLsCodeLoaded lsmpl (rustCliReallocNoOomSpec M A lim).withExternStackFromAlloc')) :
    AllocNoOomContractsXPlaced A lim H where
  alloc := ls_subroutine_ok_cl_of_callee (j := 0) halloc
  dealloc := ls_subroutine_ok_cl_of_callee (j := 0) hdealloc
  realloc := ls_subroutine_ok_cl_of_callee (j := 0) hrealloc

theorem AllocNoOomContractsXPlaced.of_hooks [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    AllocNoOomContractsXPlaced A lim H where
  alloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAlloc'
      (subroutine_ok_allocNoOom_of_budget (ls_hook_ok_of_caller halloc)))
  dealloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAlloc' (ls_hook_ok_of_caller hdealloc))
  realloc := ls_subroutine_ok_cl_of_plain_prog
    (subroutine_ok_withExternStackFromAlloc'
      (subroutine_ok_reallocNoOom_of_budget (ls_hook_ok_of_caller hrealloc)))

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget
