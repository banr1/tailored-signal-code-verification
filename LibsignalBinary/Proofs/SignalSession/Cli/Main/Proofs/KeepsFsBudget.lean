/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Filesystem, VM, and Stack Framing for Hook Contracts

Lifts `HookOk` contracts to `withVmPreserved` and OOM-aware stack-framed allocator specs under
`RustCliAllocBudget M` (and their `NoOom` counterparts under `FitsEvents`) for
`allocHookStack ≤ stk ≤ 2 ^ 64`.
-/

@[expose] public section

set_option linter.dupNamespace false
set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget

open Arm64 ProofLib SepProp
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.RustHeap (allocHookStack)
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel BudgetLimits FitsEvents NullAllowed OomPreserved
  RustCliAllocBudget RustLayoutOk VmPreserved
  rustAllocEvents rustDeallocEvents rustReallocEvents
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
  rustCliAllocNoOomSpec rustCliReallocNoOomSpec
)
open LibsignalBinary.Heap.IfaceLemmas (satisfies_drop_mid_entails)
open LibsignalBinary.Heap.IfaceBudgetLemmas (
  rustCliAllocBudgetSpecWithStack rustCliAllocBudgetExternSpecWithStack
  rustCliDeallocBudgetSpecWithStack rustCliDeallocBudgetExternSpecWithStack
  rustCliReallocBudgetSpecWithStack rustCliReallocBudgetExternSpecWithStack
  rustCliAllocNoOomSpecWithStack rustCliAllocNoOomExternSpecWithStack
  rustCliReallocNoOomSpecWithStack rustCliReallocNoOomExternSpecWithStack
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)

export CryptoVerification.SignalSession.Cli.MainHops (retHook_fs hookOk_withStack)

/-- Lift `HookOk h spec` to `HookOk h (withVmPreserved spec)` when `h` preserves VM state. -/
theorem hookOk_withVmPreserved {α : Type} {h : State → State} {spec : Spec α}
    (hh : HookOk h spec) (hvm : ∀ s, VmPreserved s (h s)) :
    HookOk h (withVmPreserved spec) := by
  intro x R s0 hrun hpre hsp
  obtain ⟨hkf, hsym, hout⟩ := hh x R s0 hrun hpre hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm s0, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

private theorem stackAt_split_from_allocHookStack (sp : BitVec 64) {stk : Nat}
    (hle : allocHookStack ≤ stk) (hbound : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - allocHookStack) ∗ stackAt sp allocHookStack := by
  have hsplit : stk = allocHookStack + (stk - allocHookStack) := by
    dsimp only [allocHookStack] at hle ⊢; omega
  have h0 := ProofLib.stackAt_split_bottom sp allocHookStack (stk - allocHookStack)
    (by dsimp only [allocHookStack] at hle ⊢; omega)
  rwa [← hsplit] at h0

private theorem pure_sepConj_imp {P Q : Prop} {R : SepProp} (h : P → Q) :
    ⌜P⌝ ∗ R ⊢ ⌜Q⌝ ∗ R :=
  Entails.pure_left fun hp => Entails.pure_right (h hp) (Entails.refl R)

private theorem hookOk_frame_oom' {α : Type} {h : State → State} {spec spec' : Spec α}
    (F : α → State → SepProp) (hh : HookOk h spec)
    (hpre : ∀ x s0, spec'.pre x s0 ⊢ spec.pre x s0 ∗ F x s0)
    (hpost : ∀ x s0 sf, spec.post x s0 sf ∗ F x s0 ⊢ spec'.post x s0 sf)
    (hoom : ∀ x R s0 sf,
      (sf.mem ⊨ spec.onOom x s0 sf ∗ (F x s0 ∗ R)) → (sf.mem ⊨ spec'.onOom x s0 sf ∗ R))
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk h spec' := by
  intro x R s0 hrun hp hsp
  have hp' : s0.mem ⊨ spec.pre x s0 ∗ (F x s0 ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre x s0)) hp
  obtain ⟨hkf, hsym, hout⟩ := hh x (F x s0 ∗ R) s0 hrun hp' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨_, hp_sat⟩ | ⟨code, _, he_sat⟩ | ⟨ho_st, ho_sat⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpost x s0 (h s0))) hq
  · rw [hpan x s0 (h s0), satisfies_pure_sepConj] at hp_sat
    exact False.elim hp_sat.1
  · rw [hex x code s0 (h s0), satisfies_pure_sepConj] at he_sat
    exact False.elim he_sat.1
  · exact Or.inr (Or.inr (Or.inr ⟨ho_st, hoom x R s0 (h s0) ho_sat⟩))

theorem hookOk_rustAllocWithStack [LibsignalPlacement] {M : AllocCostModel} {h : State → State}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    (hh : HookOk h (rustCliAllocBudgetSpec M A lim zeroed))
    (hle : allocHookStack ≤ stk := by decide) (hmax : stk ≤ 2 ^ 64 := by decide) :
    HookOk h (rustCliAllocBudgetSpecWithStack M A lim zeroed stk) := by
  refine hookOk_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) hh ?_ ?_ ?_
  · rintro ⟨size, align, st⟩ s0
    dsimp only [rustCliAllocBudgetSpec, rustCliAllocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hmax]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨size, align, st⟩ s0 sf
    dsimp only [rustCliAllocBudgetSpec, rustCliAllocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hmax]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨size, align, st⟩ R s0 sf hoom
    dsimp only [rustCliAllocBudgetSpec, rustCliAllocBudgetSpecWithStack] at hoom ⊢
    exact satisfies_drop_mid_entails (Entails.refl _) hoom

theorem hookOk_rustAllocExternWithStack [LibsignalPlacement] {M : AllocCostModel} {h : State → State}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    (hh : HookOk h (rustCliAllocBudgetSpec M A lim zeroed))
    (hle : allocHookStack ≤ stk := by decide) (hmax : stk ≤ 2 ^ 64 := by decide) :
    HookOk h (rustCliAllocBudgetExternSpecWithStack M A lim zeroed stk) := by
  refine hookOk_frame_oom' (fun _ _ => emp)
    (hookOk_rustAllocWithStack hh hle hmax) ?_ ?_ ?_
  · rintro ⟨size, align, st⟩ s0
    rw [sepConj_emp]
    exact Entails.refl _
  · rintro ⟨size, align, st⟩ s0 sf
    dsimp only [rustCliAllocBudgetSpecWithStack, rustCliAllocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliAllocBudgetExternSpecWithStack]
    rw [sepConj_emp]
    exact pure_sepConj_imp (fun hacp => hacp.2.1)
  · rintro ⟨size, align, st⟩ R s0 sf hoom
    dsimp only [rustCliAllocBudgetSpecWithStack, rustCliAllocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliAllocBudgetExternSpecWithStack] at hoom ⊢
    rw [emp_sepConj] at hoom
    exact hoom

theorem hookOk_rustDeallocWithStack [LibsignalPlacement] {M : AllocCostModel} {h : State → State}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    (hh : HookOk h (rustCliDeallocBudgetSpec M A lim))
    (hle : allocHookStack ≤ stk := by decide) (hmax : stk ≤ 2 ^ 64 := by decide) :
    HookOk h (rustCliDeallocBudgetSpecWithStack M A lim stk) := by
  refine hookOk_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) hh ?_ ?_ ?_
  · rintro ⟨p, size, align, st⟩ s0
    dsimp only [rustCliDeallocBudgetSpec, rustCliDeallocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hmax]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, size, align, st⟩ s0 sf
    dsimp only [rustCliDeallocBudgetSpec, rustCliDeallocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hmax]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, size, align, st⟩ R s0 sf hoom
    dsimp only [rustCliDeallocBudgetSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem hookOk_rustDeallocExternWithStack [LibsignalPlacement] {M : AllocCostModel} {h : State → State}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    (hh : HookOk h (rustCliDeallocBudgetSpec M A lim))
    (hle : allocHookStack ≤ stk := by decide) (hmax : stk ≤ 2 ^ 64 := by decide) :
    HookOk h (rustCliDeallocBudgetExternSpecWithStack M A lim stk) := by
  refine hookOk_frame_oom' (fun _ _ => emp)
    (hookOk_rustDeallocWithStack hh hle hmax) ?_ ?_ ?_
  · rintro ⟨p, size, align, st⟩ s0
    dsimp only [rustCliDeallocBudgetSpecWithStack, rustCliDeallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_emp]
    exact pure_sepConj_imp (by tauto)
  · rintro ⟨p, size, align, st⟩ s0 sf
    dsimp only [rustCliDeallocBudgetSpecWithStack, rustCliDeallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliDeallocBudgetExternSpecWithStack]
    rw [sepConj_emp]
    exact pure_sepConj_imp (fun ⟨hacp, _⟩ => hacp.2.1)
  · rintro ⟨p, size, align, st⟩ R s0 sf hoom
    dsimp only [rustCliDeallocBudgetSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem hookOk_rustReallocWithStack [LibsignalPlacement] {M : AllocCostModel} {h : State → State}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    (hh : HookOk h (rustCliReallocBudgetSpec M A lim))
    (hle : allocHookStack ≤ stk := by decide) (hmax : stk ≤ 2 ^ 64 := by decide) :
    HookOk h (rustCliReallocBudgetSpecWithStack M A lim stk) := by
  refine hookOk_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) hh ?_ ?_ ?_
  · rintro ⟨p, old, align, new, bs, st⟩ s0
    dsimp only [rustCliReallocBudgetSpec, rustCliReallocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hmax]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, old, align, new, bs, st⟩ s0 sf
    dsimp only [rustCliReallocBudgetSpec, rustCliReallocBudgetSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hmax]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, old, align, new, bs, st⟩ R s0 sf hoom
    dsimp only [rustCliReallocBudgetSpec, rustCliReallocBudgetSpecWithStack] at hoom ⊢
    exact satisfies_drop_mid_entails (Entails.refl _) hoom

theorem hookOk_rustReallocExternWithStack [LibsignalPlacement] {M : AllocCostModel} {h : State → State}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    (hh : HookOk h (rustCliReallocBudgetSpec M A lim))
    (hle : allocHookStack ≤ stk := by decide) (hmax : stk ≤ 2 ^ 64 := by decide) :
    HookOk h (rustCliReallocBudgetExternSpecWithStack M A lim stk) := by
  refine hookOk_frame_oom' (fun _ _ => emp)
    (hookOk_rustReallocWithStack hh hle hmax) ?_ ?_ ?_
  · rintro ⟨p, old, align, new, bs, st⟩ s0
    dsimp only [rustCliReallocBudgetSpecWithStack, rustCliReallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack]
    rw [sepConj_emp]
    exact pure_sepConj_imp (by tauto)
  · rintro ⟨p, old, align, new, bs, st⟩ s0 sf
    dsimp only [rustCliReallocBudgetSpecWithStack, rustCliReallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack]
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
        (pure_sepConj_imp (fun hnull =>
          (⟨hacp.2.1, hnull⟩ : sf.trace = s0.trace ∧ NullAllowed new align))) ?_
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
  · rintro ⟨p, old, align, new, bs, st⟩ R s0 sf hoom
    dsimp only [rustCliReallocBudgetSpecWithStack, rustCliReallocBudgetExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliReallocBudgetExternSpecWithStack] at hoom ⊢
    rw [emp_sepConj] at hoom
    exact hoom

theorem hookOk_rustAllocNoOomWithStack [LibsignalPlacement] {M : AllocCostModel} {h : State → State}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    (hh : HookOk h (rustCliAllocNoOomSpec M A lim zeroed))
    (hle : allocHookStack ≤ stk := by decide) (hmax : stk ≤ 2 ^ 64 := by decide) :
    HookOk h (rustCliAllocNoOomSpecWithStack M A lim zeroed stk) := by
  refine hookOk_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) hh ?_ ?_ ?_
  · rintro ⟨size, align, st⟩ s0
    dsimp only [rustCliAllocNoOomSpec, rustCliAllocNoOomSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hmax]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨size, align, st⟩ s0 sf
    dsimp only [rustCliAllocNoOomSpec, rustCliAllocNoOomSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hmax]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨size, align, st⟩ R s0 sf hoom
    dsimp only [rustCliAllocNoOomSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem hookOk_rustAllocNoOomExternWithStack [LibsignalPlacement] {M : AllocCostModel} {h : State → State}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {zeroed : Bool} {stk : Nat}
    (hh : HookOk h (rustCliAllocNoOomSpec M A lim zeroed))
    (hle : allocHookStack ≤ stk := by decide) (hmax : stk ≤ 2 ^ 64 := by decide) :
    HookOk h (rustCliAllocNoOomExternSpecWithStack M A lim zeroed stk) := by
  refine hookOk_frame_oom' (fun _ _ => emp)
    (hookOk_rustAllocNoOomWithStack hh hle hmax) ?_ ?_ ?_
  · rintro ⟨size, align, st⟩ s0
    rw [sepConj_emp]
    exact Entails.refl _
  · rintro ⟨size, align, st⟩ s0 sf
    dsimp only [rustCliAllocNoOomSpecWithStack, rustCliAllocNoOomExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliAllocNoOomExternSpecWithStack]
    rw [sepConj_emp]
    exact pure_sepConj_imp (fun ⟨hacp, hne, hal⟩ => ⟨hacp.2.1, hne, hal⟩)
  · rintro ⟨size, align, st⟩ R s0 sf hoom
    dsimp only [rustCliAllocNoOomSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem hookOk_rustReallocNoOomWithStack [LibsignalPlacement] {M : AllocCostModel} {h : State → State}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    (hh : HookOk h (rustCliReallocNoOomSpec M A lim))
    (hle : allocHookStack ≤ stk := by decide) (hmax : stk ≤ 2 ^ 64 := by decide) :
    HookOk h (rustCliReallocNoOomSpecWithStack M A lim stk) := by
  refine hookOk_frame_oom'
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - allocHookStack)) hh ?_ ?_ ?_
  · rintro ⟨p, old, align, new, bs, st⟩ s0
    dsimp only [rustCliReallocNoOomSpec, rustCliReallocNoOomSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hmax]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, old, align, new, bs, st⟩ s0 sf
    dsimp only [rustCliReallocNoOomSpec, rustCliReallocNoOomSpecWithStack]
    rw [stackAt_split_from_allocHookStack s0.sp hle hmax]
    exact Entails.of_eq (by sep_ac_rfl)
  · rintro ⟨p, old, align, new, bs, st⟩ R s0 sf hoom
    dsimp only [rustCliReallocNoOomSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

theorem hookOk_rustReallocNoOomExternWithStack [LibsignalPlacement] {M : AllocCostModel} {h : State → State}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stk : Nat}
    (hh : HookOk h (rustCliReallocNoOomSpec M A lim))
    (hle : allocHookStack ≤ stk := by decide) (hmax : stk ≤ 2 ^ 64 := by decide) :
    HookOk h (rustCliReallocNoOomExternSpecWithStack M A lim stk) := by
  refine hookOk_frame_oom' (fun _ _ => emp)
    (hookOk_rustReallocNoOomWithStack hh hle hmax) ?_ ?_ ?_
  · rintro ⟨p, old, align, new, bs, st⟩ s0
    dsimp only [rustCliReallocNoOomSpecWithStack, rustCliReallocNoOomExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStack]
    rw [sepConj_emp]
    exact pure_sepConj_imp (by tauto)
  · rintro ⟨p, old, align, new, bs, st⟩ s0 sf
    dsimp only [rustCliReallocNoOomSpecWithStack, rustCliReallocNoOomExternSpecWithStack,
      _root_.LibsignalBinary.Heap.rustCliReallocNoOomExternSpecWithStack]
    rw [sepConj_emp]
    exact pure_sepConj_imp (fun ⟨hacp, hne, hal⟩ => ⟨hacp.2.1, hne, hal⟩)
  · rintro ⟨p, old, align, new, bs, st⟩ R s0 sf hoom
    dsimp only [rustCliReallocNoOomSpecWithStack] at hoom
    rw [satisfies_pure_sepConj] at hoom
    exact False.elim hoom.1

end LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
