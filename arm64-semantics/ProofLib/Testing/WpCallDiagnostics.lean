/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP

/-!
# `wp_call` Failure Diagnostics Tests

Tests error messages produced by `wp_call` and `wpp_call` (`withCallFailureDiagnostics`) when
callee `onOom` is not admitted by the caller's `oom` condition and when pure or spatial callee
preconditions fail to discharge.
-/

@[expose] public section

namespace Examples.Testing.ProofLib.WpCallDiagnostics

open Arm64 _root_.ProofLib

/-- A named callee contract that admits out-of-memory termination. -/
def widgetAllocSpec : Spec Unit :=
  Spec.allowOom { pre := fun _ _ => emp, post := fun _ _ sf => ⌜sf.readReg64 .x0 = 42#64⌝ }

/-! ## `onOom` mismatch -/

-- Plain contract, `SepWP` goal with the default `oom`.
/--
error: wp_call: callee `onOom` is not admitted by the goal's `oom`, so the call rule's OOM side condition could not be discharged
  callee onOom:
  fun x x_1 x_2 => ⌜True⌝
  goal oom:
  fun x => ⌜False⌝
hint: state the enclosing `SepWP` / `SepWPp` goal with an `oom` that admits the callee's (e.g. `fun _ => ⌜True⌝`, and `Spec.allowOom` on the caller's contract), or call a contract whose `onOom` is `⌜False⌝`
-/
#guard_msgs in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog entry
      (Spec.allowOom { pre := fun (_ : Unit) _ => emp, post := fun _ _ sf => ⌜sf.readReg64 .x0 = 42#64⌝ })) :
    SepWP prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 42#64) := by
  wp_call h_callee ()

-- `Spec.split` contract.
/--
error: wp_call: callee `onOom` is not admitted by the goal's `oom`, so the call rule's OOM side condition could not be discharged
  callee onOom:
  fun x x_1 x_2 => ⌜True⌝
  goal oom:
  fun x => ⌜False⌝
hint: state the enclosing `SepWP` / `SepWPp` goal with an `oom` that admits the callee's (e.g. `fun _ => ⌜True⌝`, and `Spec.allowOom` on the caller's contract), or call a contract whose `onOom` is `⌜False⌝`
-/
#guard_msgs in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog entry
      (Spec.allowOom (Spec.split (fun (_ : Unit) _ => True) (fun _ => emp)
        (fun _ _ sf => sf.readReg64 .x0 = 42#64) (fun _ => emp)))) :
    SepWP prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 42#64) := by
  wp_call h_callee ()

-- `SepWPp` goal through `wp_call` (delegates to `wpp_call`).
/--
error: wp_call: callee `onOom` is not admitted by the goal's `oom`, so the call rule's OOM side condition could not be discharged
  callee onOom:
  fun x x_1 x_2 => ⌜True⌝
  goal oom:
  fun x => ⌜False⌝
hint: state the enclosing `SepWP` / `SepWPp` goal with an `oom` that admits the callee's (e.g. `fun _ => ⌜True⌝`, and `Spec.allowOom` on the caller's contract), or call a contract whose `onOom` is `⌜False⌝`
-/
#guard_msgs in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog entry
      (Spec.allowOom { pre := fun (_ : Unit) _ => emp, post := fun _ _ sf => ⌜sf.readReg64 .x0 = 42#64⌝ })) :
    SepWPp prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 42#64) (fun _ _ => False) := by
  wp_call h_callee ()

-- `SepWPp` goal through `wpp_call`.
/--
error: wpp_call: callee `onOom` is not admitted by the goal's `oom`, so the call rule's OOM side condition could not be discharged
  callee onOom:
  fun x x_1 x_2 => ⌜True⌝
  goal oom:
  fun x => ⌜False⌝
hint: state the enclosing `SepWP` / `SepWPp` goal with an `oom` that admits the callee's (e.g. `fun _ => ⌜True⌝`, and `Spec.allowOom` on the caller's contract), or call a contract whose `onOom` is `⌜False⌝`
-/
#guard_msgs in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog entry
      (Spec.allowOom { pre := fun (_ : Unit) _ => emp, post := fun _ _ sf => ⌜sf.readReg64 .x0 = 42#64⌝ })) :
    SepWPp prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 42#64) (fun _ _ => False) := by
  wpp_call h_callee ()

-- Named contract constant: the spec is unfolded to read its `onOom` field.
/--
error: wp_call: callee `onOom` is not admitted by the goal's `oom`, so the call rule's OOM side condition could not be discharged
  callee onOom:
  fun x x_1 x_2 => ⌜True⌝
  goal oom:
  fun x => ⌜False⌝
hint: state the enclosing `SepWP` / `SepWPp` goal with an `oom` that admits the callee's (e.g. `fun _ => ⌜True⌝`, and `Spec.allowOom` on the caller's contract), or call a contract whose `onOom` is `⌜False⌝`
-/
#guard_msgs in
example (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog entry widgetAllocSpec) :
    SepWP prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 42#64) := by
  wp_call h_callee ()

-- Positive control: the goal admits OOM, so the same call succeeds.
example (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog entry
      (Spec.allowOom { pre := fun (_ : Unit) _ => emp, post := fun _ _ sf => ⌜sf.readReg64 .x0 = 42#64⌝ })) :
    SepWP prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 42#64) (fun _ => ⌜True⌝) := by
  wp_call h_callee ()
  wp_done

/-! ## Callee precondition failures -/

-- Positive: the numeric conjunct `Can 22` is discharged from `Can xs.length` and `xs.length = 22`.
example (Can : Nat → Prop) (prog : Program) (entry ret_pc : BitVec 64) (s : State) (xs : List Nat)
    (h_pc : s.pc = entry)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (hcan : Can xs.length) (hm : xs.length = 22)
    (h_callee : subroutine_ok prog entry
      { pre := fun (_ : Unit) _ => ⌜Can 22⌝, post := fun _ _ sf => ⌜sf.readReg64 .x0 = 42#64⌝ }) :
    SepWPp prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 42#64) (fun _ _ => False) := by
  wp_call h_callee ()
  wp_done

-- Unprovable pure conjunct in a `SepWPp` goal: named with its index.
/--
error: wp_call: failed to prove callee precondition conjunct: (conjunct 1/2)
  Can 22
normalized:
  Can 22
with unified ghost(s): ghost := emp
hint: prove `have h_pre : Can 22 := by ...` before `wp_call`
-/
#guard_msgs in
example (Can : Nat → Prop) (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (hcan : Can 23)
    (h_callee : subroutine_ok prog entry
      { pre := fun (_ : Unit) _ => ⌜Can 22⌝, post := fun _ _ sf => ⌜sf.readReg64 .x0 = 42#64⌝ }) :
    SepWPp prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 42#64) (fun _ _ => False) := by
  wp_call h_callee ()

-- Unprovable register-level conjunct of a `Spec.split` contract.
/--
error: wp_call: failed to prove callee precondition conjunct: (conjunct 1/2)
  Can 22
normalized:
  Can 22
hint: prove `have h_pre : Can 22 := by ...` before `wp_call`
-/
#guard_msgs in
example (Can : Nat → Prop) (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (hcan : Can 23)
    (h_callee : subroutine_ok prog entry
      (Spec.split (fun (_ : Unit) _ => Can 22) (fun _ => emp)
        (fun _ _ sf => sf.readReg64 .x0 = 42#64) (fun _ => emp))) :
    SepWP prog ret_pc s emp (fun sf _ => sf.readReg64 .x0 = 42#64) := by
  wp_call h_callee ()

-- Unmatched spatial atom: the frame candidates are listed.
/--
error: wp_call: frame_split: no match for Cell
  22 (note: `Cell` is a local variable — possible typo or auto-bound implicit) in precondition; candidates: Cell
  23, Other
hint: target contains unassigned metavariable atom(s) ?«ghost», which `frame_split` never matches against concrete atoms; instantiate them first (e.g. `refine`/`show` with an explicit frame, or `sep_focus` on a `P = Q ∗ ?F` equation, which assigns `?F` to the leftover atoms: Cell
  23, Other)
ghost(s) being unified: [ghost]
-/
#guard_msgs in
example (Cell : Nat → SepProp) (Other : SepProp) (prog : Program) (entry ret_pc : BitVec 64) (s : State)
    (h_pc : s.pc = entry)
    (h_run : s.status = .Running)
    (h_sp : s.spAligned = true)
    (h_lr : s.readReg64 .lr = ret_pc)
    (h_callee : subroutine_ok prog entry
      { pre := fun (_ : Unit) _ => Cell 22, post := fun _ _ _ => Cell 22 }) :
    SepWP prog ret_pc s (Cell 23 ∗ Other) (fun _ _ => True) := by
  wp_call h_callee ()

end Examples.Testing.ProofLib.WpCallDiagnostics
