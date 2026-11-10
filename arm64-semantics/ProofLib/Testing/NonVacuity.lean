/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import ProofLib

/-!
# Derived Non-Vacuity Regression Tests (`Examples.Testing.ProofLib.NonVacuity`)

- **Layer / Role**: Untrusted test suite (`Lib::Testing`, `Role::Test`, outside TCB).
- **Covers**:
  1. Passing `#nonvacuous` and `#nonvacuous?` derivation, emitting both `<foo>.nonvacuous` and
     the kernel-checked `<foo>.nonvacuous_adequate`.
  2. Negative `#guard_msgs` adequacy checks: a hand-written witness that drops a premise or proves
     a strictly weaker premise fails kernel checking in `<witness>_adequate`, and an incomplete
     proof inside `#nonvacuous` fails elaboration.
  3. Dependent `Prop` binders, both in an intermediate hypothesis (`∃ h : H, P h`) and in the
     conclusion (`∃ xs h, C[xs, h]`), plus negated conclusions (`x ≠ 0`) not spuriously unfolded.
  4. Partial instantiation (`(reps := …)`), second witness commands with more concrete parameters
     (`.nonvacuous_2`), binder-reordered `witness` arguments, implicit type inference, and
     `section` `variable` scoping.
  5. Controlled unfolding (`unfold := […]`) on both `subroutine_ok` / `Program.subroutineOk` with
     `Spec.pre` and bundled `Contract.pre` predicates.
  6. `witness` discharging callee hook hypotheses directly from closed callee theorems (both
     binder-named and unnamed arrow hypotheses), plus `#guard_msgs` diagnostics on unknown binders.
  7. Environment coverage lint (`@[contract]`, `@[vacuity_exempt "reason"]`, and
     `#check_nonvacuity_coverage`): fails via `#guard_msgs` when a `@[contract]` theorem lacks a
     witness, rejects empty exemption strings, and passes once every `@[contract]` theorem has
     either `.nonvacuous` or `@[vacuity_exempt "reason"]`.
-/

namespace Examples.Testing.ProofLib.NonVacuity

open Arm64 _root_.ProofLib ProofLib.SepLogic

/-! ## 1. Basic Passing Example & `#nonvacuous?` Output -/

theorem basic_add_contract (x y : Nat) (hx : x > 0) (hy : y > 10) (hxy : x < y) :
    x + y > 11 ∧ y ≠ 0 := by
  let _ := hxy
  omega

/--
info: -- Examples.Testing.ProofLib.NonVacuity.basic_add_contract.nonvacuous :
∃ x y, x > 0 ∧ y > 10 ∧ x < y
-/
#guard_msgs in
#nonvacuous? basic_add_contract

#nonvacuous basic_add_contract := by
  witness y := 20, x := 5
  all_goals decide

-- Check exact types of both generated sibling declarations.
example : ∃ x y, x > 0 ∧ y > 10 ∧ x < y := basic_add_contract.nonvacuous
example : ∃ x y, x + y > 11 ∧ y ≠ 0 := basic_add_contract.nonvacuous_adequate

/-! ## 2. Dropped or Weakened Premise Fails Kernel Adequacy (`#guard_msgs`) -/

-- Witness that drops the third conjunct `x < y` completely.
theorem bad_dropped_witness : ∃ (x y : Nat), x > 0 ∧ y > 10 :=
  ⟨50, 20, by decide, by decide⟩

/-- error: Unknown identifier `w_1✝` -/
#guard_msgs (substring := true) in
#nonvacuous_adequate basic_add_contract bad_dropped_witness

-- Witness with the right arity of conjuncts, but weakening `x < y` to `x ≤ y` (satisfied at `20, 20`,
-- where `basic_add_contract`'s real premise `20 < 20` is false).
theorem bad_weakened_witness : ∃ (x y : Nat), x > 0 ∧ y > 10 ∧ x ≤ y :=
  ⟨20, 20, by decide, by decide, by decide⟩

/-- error: Application type mismatch -/
#guard_msgs (substring := true) in
#nonvacuous_adequate basic_add_contract bad_weakened_witness

-- Omitting a premise subgoal inside `#nonvacuous` fails elaboration.
/-- error: unsolved goals -/
#guard_msgs (substring := true) in
#nonvacuous basic_add_contract := by
  witness x := 25, y := 20
  · decide
  · decide

/-! ## 3. Dependent `Prop` Binders & Negated Conclusions -/

/-- Later hypothesis `hhead` depends on proof binder `hne : xs ≠ []`. -/
theorem dependent_prop_hyp (xs : List Nat) (hne : xs ≠ []) (hhead : xs.head hne > 3) :
    xs.length > 0 := by
  let _ := hhead
  exact List.length_pos_iff.mpr hne

#nonvacuous dependent_prop_hyp := by
  witness xs := [7], hne := by decide
  decide

example : ∃ (xs : List Nat) (hne : xs ≠ []), xs.head hne > 3 :=
  dependent_prop_hyp.nonvacuous
example : ∃ (xs : List Nat), xs.length > 0 :=
  dependent_prop_hyp.nonvacuous_adequate

/-- Conclusion itself depends on proof binder `hne : xs ≠ []`. -/
theorem dependent_prop_concl (xs : List Nat) (hne : xs ≠ []) (hlen : xs.length = 2) :
    xs.head hne = xs[0]'(List.length_pos_iff.mpr hne) := by
  let _ := hlen
  cases xs with
  | nil => contradiction
  | cons a _ => rfl

#nonvacuous dependent_prop_concl := by
  witness xs := [42, 99], hne := by decide
  rfl

example : ∃ (xs : List Nat) (hne : xs ≠ []), xs.head hne = xs[0]'(List.length_pos_iff.mpr hne) :=
  dependent_prop_concl.nonvacuous_adequate

/-- Negated conclusion (`x ≠ 0`, i.e., `x = 0 → False`) must NOT have `x = 0` peeled as a premise. -/
theorem negated_conclusion (x : Nat) (hx : x = 5) : x ≠ 0 := by
  omega

#nonvacuous negated_conclusion := by
  witness x := 5
  rfl

example : ∃ x : Nat, x = 5 := negated_conclusion.nonvacuous

/-! ## 4. Partial Instantiation, Multiple Witnesses, Implicit Inference & `section` Variables -/

structure WidgetReps where
  magic : BitVec 64
  limit : Nat

def abstractReps : WidgetReps := { magic := 0xab#64, limit := 10 }
def concreteReps : WidgetReps := { magic := 0xab#64, limit := 64 }

theorem widget_step_contract
    (reps : WidgetReps) (cap : Nat) (s0 : State)
    (_hmagic : reps.magic = 0xab#64)
    (hlimit : reps.limit ≥ 10)
    (hcap : cap ≥ reps.limit)
    (hsp : s0.sp = 0x30000#64) :
    s0.sp ≠ 0#64 ∧ cap ≥ 10 := by
  exact ⟨by rw [hsp]; decide, by omega⟩

-- Partial instantiation fixing `reps := abstractReps`, filling `s0` and `cap` out of binder order:
#nonvacuous widget_step_contract (reps := abstractReps) := by
  witness s0 := { sp := 0x30000#64 }, cap := 16
  all_goals decide

-- Second witness on the same theorem with concrete reps and fixed `cap` (`.nonvacuous_2`):
#nonvacuous widget_step_contract (reps := concreteReps) (cap := 128) := by
  witness s0 := { sp := 0x30000#64 }
  all_goals decide

example : ∃ (cap : Nat) (s0 : State), s0.sp ≠ 0#64 ∧ cap ≥ 10 := widget_step_contract.nonvacuous_adequate
example : ∃ (s0 : State), s0.sp ≠ 0#64 ∧ 128 ≥ 10 := widget_step_contract.nonvacuous_2_adequate

-- Implicit type parameter `{α : Type}` unified automatically from a later `witness` argument:
theorem poly_slice_contract {α : Type} (xs : List α) (s0 : State)
    (hlen : xs.length > 0) (hsp : s0.sp = 0x20000#64) :
    xs ≠ [] ∧ s0.sp = 0x20000#64 :=
  ⟨List.ne_nil_of_length_pos hlen, hsp⟩

#nonvacuous poly_slice_contract := by
  witness xs := [1, 2, 3], s0 := { sp := 0x20000#64 }
  all_goals decide

-- `section` + `variable` partial instantiation:
section WithSectionVar
variable (cfgBase : Nat)

theorem section_contract (x : Nat) (hx : x = cfgBase + 1) : x > cfgBase := by
  omega

#nonvacuous section_contract (cfgBase := cfgBase) := by
  witness x := cfgBase + 1
  rfl

end WithSectionVar

/-! ## 5. Controlled Unfolding (`unfold := […]`) on `subroutine_ok` / `Spec.pre` & `Contract.pre` -/

/-- Bundled precondition predicate (`Contract.pre`). -/
def WidgetContractPre (reps : WidgetReps) (s0 : State) : Prop :=
  reps.magic = 0xab#64 ∧
  s0.status = .Running ∧
  s0.spAligned = true

theorem widget_bundled_contract (reps : WidgetReps) (s0 : State) :
    WidgetContractPre reps s0 →
    s0.status = .Running :=
  fun h => h.2.1

#nonvacuous widget_bundled_contract (reps := abstractReps) (unfold := [WidgetContractPre]) := by
  witness s0 := { sp := 0x30000#64, status := .Running }
  · rfl
  · rfl
  · decide

/-- Real 2-instruction ARM64 subroutine (`ADD X0, X0, #1; RET`) verified against a `Spec`. -/
def widgetAddCode : FnCode :=
  .atAddr "widget_add" 0x10000#64
    [ 0x91000400#32  -- add x0, x0, #1
    , 0xd65f03c0#32  -- ret
    ]

def widgetAddProg : Program :=
  Program.ofWords 0x10000#64 widgetAddCode.hex [("widget_add", 0x10000#64)]

def widgetAddSpec : Spec (BitVec 64) where
  pre x s0 := ⌜s0.readReg64 .x0 = x⌝
  post x _ sf := ⌜sf.readReg64 .x0 = x + 1#64⌝

theorem widget_add_ok : widgetAddProg.subroutineOk "widget_add" widgetAddSpec := by
  have h_code : widgetAddCode.holds widgetAddProg := by decide
  wp_init x s0
  wp_steps
  wp_done

#nonvacuous widget_add_ok (unfold := [subroutine_ok, Spec.pre]) := by
  witness x := 41#64, R := ⌜True⌝,
    s0 := { regs := RegFile.empty.write 0#5 41#64
            sp := 0x30000#64
            pc := widgetAddProg.fnAddr "widget_add" }
  · rfl
  · rfl
  · dsimp only [widgetAddSpec]; rw [satisfies_pure_sepConj, satisfies_pure]; exact ⟨rfl, trivial⟩
  · decide

-- Adequacy derives `reaches_outcome` at the concrete witness state directly from `widget_add_ok`:
example : ∃ x R s0, reaches_outcome widgetAddProg widgetAddSpec x R s0 s0 :=
  widget_add_ok.nonvacuous_adequate

/-! ## 6. Callee Hook Hypotheses Discharged by Closed Callee Theorems & Diagnostics -/

/-- Caller contract with a named callee `subroutine_ok` hook hypothesis. -/
theorem caller_named_hook
    (prog : Program) (s0 : State)
    (hcallee : subroutine_ok prog (prog.fnAddr "widget_add") widgetAddSpec)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true) :
    reaches_outcome prog widgetAddSpec (s0.readReg64 .x0) (⌜True⌝)
      (s0.setPC (prog.fnAddr "widget_add")) (s0.setPC (prog.fnAddr "widget_add")) := by
  apply hcallee.to_outcome
  · rfl
  · simpa [State.setPC] using hrun
  · dsimp only [widgetAddSpec]; rw [satisfies_pure_sepConj, satisfies_pure]; exact ⟨rfl, trivial⟩
  · simpa [State.setPC, State.spAligned] using hsp

-- Discharge `hcallee` by binder name using the closed callee theorem `widget_add_ok`:
#nonvacuous caller_named_hook := by
  witness prog := widgetAddProg, s0 := { sp := 0x30000#64 }, hcallee := widget_add_ok
  · rfl
  · decide

/-- Caller contract with an unnamed arrow callee `subroutine_ok` hypothesis. -/
theorem caller_arrow_hook (prog : Program) (s0 : State) :
    subroutine_ok prog (prog.fnAddr "widget_add") widgetAddSpec →
    s0.status = .Running →
    s0.spAligned = true →
    reaches_outcome prog widgetAddSpec (s0.readReg64 .x0) (⌜True⌝)
      (s0.setPC (prog.fnAddr "widget_add")) (s0.setPC (prog.fnAddr "widget_add")) :=
  fun hcallee hrun hsp => caller_named_hook prog s0 hcallee hrun hsp

-- Discharge unnamed arrow hook hypothesis directly by passing closed callee theorem `widget_add_ok`:
#nonvacuous caller_arrow_hook := by
  witness prog := widgetAddProg, s0 := { sp := 0x30000#64 }, widget_add_ok
  · rfl
  · decide

-- `witness` rejects misspelled binder names with an actionable list of available binders.
/--
error: witness: unknown or already-instantiated binder `typo` (available binders: [x, y, hx, hy, hxy])
-/
#guard_msgs in
example : hyps_of% basic_add_contract := by
  witness typo := 5

/-! ## 7. Coverage Lint (`@[contract]`, `@[vacuity_exempt]`, `#check_nonvacuity_coverage`) -/

@[contract]
theorem audited_contract (n : Nat) (hn : n ≥ 4) : n > 2 := by
  omega

-- Coverage lint fails when an `@[contract]` theorem has neither `.nonvacuous` nor an exemption.
/--
error: non-vacuity coverage check failed: 1 `@[contract]` declaration(s) missing a `.nonvacuous` witness or `@[vacuity_exempt "reason"]`:
  • `Examples.Testing.ProofLib.NonVacuity.audited_contract` (in current module)
-/
#guard_msgs in
#check_nonvacuity_coverage

-- Empty exemption reason strings are rejected at attribute application time.
/--
error: `@[vacuity_exempt]` requires a non-empty reason string
-/
#guard_msgs in
@[vacuity_exempt ""]
theorem bad_empty_exemption : True := trivial

-- Supplying `#nonvacuous audited_contract` satisfies the coverage check:
#nonvacuous audited_contract := by
  witness n := 4
  decide

-- Hand-written `foo.nonvacuous : True` (even paired with a spoofed `foo.nonvacuous_adequate : True`)
-- is rejected by `#check_nonvacuity_coverage` because it was not registered by `#nonvacuous` with a
-- kernel adequacy proof referencing `spoofed_contract`:
@[contract]
theorem spoofed_contract (n : Nat) (hn : n ≥ 10) : n > 5 := by
  omega

theorem spoofed_contract.nonvacuous : True := trivial
theorem spoofed_contract.nonvacuous_adequate : True := trivial

/--
error: non-vacuity coverage check failed: 1 `@[contract]` declaration(s) missing a `.nonvacuous` witness or `@[vacuity_exempt "reason"]`:
  • `Examples.Testing.ProofLib.NonVacuity.spoofed_contract` (in current module; found unverified `.nonvacuous` sibling not generated by `#nonvacuous`)
-/
#guard_msgs in
#check_nonvacuity_coverage

-- Supplying a genuine `#nonvacuous` witness (which emits `.nonvacuous_2` and `.nonvacuous_2_adequate`
-- linked to `@spoofed_contract`) satisfies the coverage check:
#nonvacuous spoofed_contract := by
  witness n := 10
  decide

-- Explicit documented exemption also satisfies the coverage check:
@[contract, vacuity_exempt "pure algebraic identity with no environment assumptions"]
theorem exempt_identity_contract (x : Nat) : x + 0 = x :=
  Nat.add_zero x

-- Whole-environment coverage check now passes with zero uncovered `@[contract]` declarations:
#check_nonvacuity_coverage

end Examples.Testing.ProofLib.NonVacuity
