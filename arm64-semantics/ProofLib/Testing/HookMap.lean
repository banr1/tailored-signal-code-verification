/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Hoare.HookMap

/-!
# `HookMap` Regression Tests

Positive and negative satisfiability tests for `hookMap`, `HookSat.same_hook`, `Spec.allowOom`,
and `subroutine_ok_of_ghost`.
-/

@[expose] public section

namespace Examples.Testing.HookMapTest

open Arm64 ProofLib

/-! ## Synthetic contracts -/

/-- Read-only `widget_peek(w)`: reads the `bs` bytes at `w`, uses the hook stack. -/
def widgetPeekSpec : Spec (BitVec 64 × List (BitVec 8)) where
  pre := fun (w, bs) s0 => (w ↦ₛ bs) ∗ stackAt s0.sp 4096
  post := fun (w, bs) s0 _ => (w ↦ₛ bs) ∗ stackAt s0.sp 4096

/-- Stack-only `widget_peek` contract (a second call site with nothing to read). -/
def widgetPeekStackSpec : Spec Unit where
  pre := fun _ s0 => stackAt s0.sp 64
  post := fun _ s0 _ => stackAt s0.sp 64

/-- A bundle with a duplicate, compatible pair of contracts on `widget_peek`. -/
structure WidgetHooks (hooks : String → Option (State → State)) : Prop where
  memcpy    : HookSat hooks "memcpy" (libcMemcpySpec 4096)
  memset    : HookSat hooks "memset" (libcMemsetSpec 4096)
  free      : HookSat hooks "widget_free" (libcFreeSpec 4096)
  peek      : HookSat hooks "widget_peek" widgetPeekSpec
  peekStack : HookSat hooks "widget_peek" widgetPeekStackSpec

/-- The hook table witnessing `WidgetHooks`. -/
def widgetHookMap : String → Option (State → State) :=
  hookMap [("memcpy", hookMemcpy), ("memset", hookMemset), ("widget_free", freePoolHook),
    ("widget_peek", hookNoop)] (fun _ => none)

theorem widgetPeek_ok : HookOk hookNoop widgetPeekSpec :=
  hookNoop_ok_of_entails fun _ _ => Entails.refl _

theorem widgetPeekStack_ok : HookOk hookNoop widgetPeekStackSpec :=
  hookNoop_ok_of_entails fun _ _ => Entails.refl _

/-- Positive test: the bundle is satisfiable, each field reduced to `HookOk` by `simp`. -/
theorem WidgetHooks_sat : ∃ H, WidgetHooks H :=
  ⟨widgetHookMap,
    { memcpy := by simp [widgetHookMap, hookMemcpy_ok]
      memset := by simp [widgetHookMap, hookMemset_ok]
      free := by simp [widgetHookMap, hookFree_ok]
      peek := by simp [widgetHookMap, widgetPeek_ok]
      peekStack := by simp [widgetHookMap, widgetPeekStack_ok] }⟩

/-- Duplicate fields project to one joint witness (`HookSat_and_iff`). -/
example : ∃ f, HookOk f widgetPeekSpec ∧ HookOk f widgetPeekStackSpec :=
  let ⟨_, h⟩ := WidgetHooks_sat
  HookSat.same_hook h.peek h.peekStack

/-- A symbol missing from the table satisfies no contract. -/
example : ¬ HookSat widgetHookMap "widget_new" widgetPeekStackSpec := by
  simp [widgetHookMap]

-- `simp` reduces a field whose symbol is missing from the table to `False`.
/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : HookSat widgetHookMap "widget_new" widgetPeekStackSpec := by
  simp [widgetHookMap]

/-! ## Negative test: contradictory contracts on one symbol -/

/-- `widget_free` returning `0` in `X0`. -/
def widgetFreeZeroSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ _ sf => ⌜sf.readReg64 .x0 = 0#64⌝

/-- `widget_free` returning `1` in `X0`. -/
def widgetFreeOneSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ _ sf => ⌜sf.readReg64 .x0 = 1#64⌝

/-- A buggy bundle: both contracts are assumed on the same non-OOM symbol `widget_free`. -/
structure BadWidgetHooks (hooks : String → Option (State → State)) : Prop where
  memcpy   : HookSat hooks "memcpy" (libcMemcpySpec 4096)
  freeZero : HookSat hooks "widget_free" widgetFreeZeroSpec
  freeOne  : HookSat hooks "widget_free" widgetFreeOneSpec
  noOom    : ∀ f, hooks "widget_free" = some f → (f default).status ≠ .OutOfMemory

/-- No single non-OOM hook meets both `widget_free` contracts: run it on the default state. -/
theorem widgetFree_no_joint_hook :
    ¬ ∃ f, (f default).status ≠ .OutOfMemory ∧
      HookOk f widgetFreeZeroSpec ∧ HookOk f widgetFreeOneSpec := by
  rintro ⟨f, hnoom, h0, h1⟩
  have hpre : ∀ (spec : Spec Unit), spec.pre = (fun _ _ => emp) →
      ((default : State).mem ⊨ spec.pre () default ∗ emp) := by
    intro spec hs
    rw [hs, emp_sepConj]
    exact satisfies_emp _
  obtain ⟨_, _, o0⟩ := h0 () emp default rfl (hpre _ rfl) (by decide)
  obtain ⟨_, _, o1⟩ := h1 () emp default rfl (hpre _ rfl) (by decide)
  rcases o0 with ⟨_, _, q0⟩ | ⟨_, q0⟩ | ⟨_, _, q0⟩ | ⟨hoom, _⟩
  · rcases o1 with ⟨_, _, q1⟩ | ⟨_, q1⟩ | ⟨_, _, q1⟩ | ⟨hoom, _⟩
    · simp only [widgetFreeZeroSpec, widgetFreeOneSpec, satisfies_pure_sepConj] at q0 q1
      rw [q0.1] at q1
      exact absurd q1.1 (by decide)
    · exact not_satisfies_false_sepConj q1
    · exact not_satisfies_false_sepConj q1
    · exact hnoom hoom
  · exact not_satisfies_false_sepConj q0
  · exact not_satisfies_false_sepConj q0
  · exact hnoom hoom

/-- Negative test: the buggy bundle is unsatisfiable, so every theorem assuming it is vacuous. -/
theorem BadWidgetHooks_unsat : ¬ ∃ H, BadWidgetHooks H := by
  rintro ⟨H, h⟩
  obtain ⟨f, hf, h0, h1⟩ := HookSat_and_iff.mp ⟨h.freeZero, h.freeOne⟩
  exact widgetFree_no_joint_hook ⟨f, h.noOom f hf, h0, h1⟩

/-! ## Positive and negative tests for `Spec.allowOom` / `subroutine_ok_of_ghost` -/

example {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry widgetFreeZeroSpec.allowOom) :
    subroutine_ok prog entry widgetFreeZeroSpec.allowOom := by
  refine subroutine_ok_of_ghost h ?_
  intro u R s0 hpre
  exact ⟨u, emp, by simpa [emp_sepConj] using hpre, fun _ _ hpost => by simpa [emp_sepConj] using hpost⟩

/--
error: could not synthesize default value for parameter 'h_oom' using tactics
---
error: Application type mismatch: The argument
  ho✝
has type
  sf✝.mem ⊨ ⌜True⌝ ∗ F✝ ∗ R✝
but is expected to have type
  ?m.72 ⊨ ?m.69 ∗ ?m.70 ∗ ?m.66 ∗ ?m.67
in the application
  Satisfies.drop_mid ho✝

Note: The following definitions were not unfolded because their definition is not exposed:
  Satisfies ↦ 4
  sepConj ↦ 10
-/
#guard_msgs in
example {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry widgetFreeZeroSpec.allowOom) :
    subroutine_ok prog entry widgetFreeZeroSpec := by
  refine subroutine_ok_of_ghost h ?_
  intro u R s0 hpre
  exact ⟨u, emp, by simpa [Spec.allowOom, emp_sepConj] using hpre,
    fun _ _ hpost => by simpa [Spec.allowOom, emp_sepConj] using hpost⟩

end Examples.Testing.HookMapTest
