/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.ObjectLoad
public import ProofLib.GenDecodes

/-!
# Tail-Call, Callee-Saved Preservation, and `sep_eq` Tests

Regression tests for `sep_eq`, `[callee_saved_split]` and `split_callee_saved`, automatic
program-wrapper unfolding in `wp_init`, and tail-call stopping and `wp_tailcall` in `wp_steps`.
-/

@[expose] public section

open Arm64
open _root_.ProofLib

namespace Examples.Testing.ProofLib.TailcallCalleeSavedSepEq

theorem sep_eq_9_way_reassoc (A1 A2 A3 A4 A5 A6 A7 A8 A9 : SepProp) :
    (A1 ∗ A2 ∗ A3 ∗ A4 ∗ A5 ∗ A6 ∗ A7 ∗ A8 ∗ A9) =
    (A9 ∗ A3 ∗ A7 ∗ A1 ∗ A5 ∗ A2 ∗ A8 ∗ A4 ∗ A6) := by
  sep_eq

theorem sep_eq_emp_and_rw (A B C : SepProp) (m : Memory) (h : m ⊨ (emp ∗ A) ∗ (B ∗ emp) ∗ C) :
    m ⊨ C ∗ B ∗ A := by
  rw [show ((emp ∗ A) ∗ (B ∗ emp) ∗ C) = (C ∗ B ∗ A) by sep_eq] at h
  exact h

/--
error: sep_eq: atom multisets differ:
  only in LHS: `p ↦₆₄ v`
  only in RHS: `q ↦₆₄ v`
  LHS: `p ↦₆₄ v`
  RHS: `q ↦₆₄ v`
-/
#guard_msgs in
example (p q : BitVec 64) (v : BitVec 64) : (p ↦₆₄ v) = (q ↦₆₄ v) := by
  sep_eq

/--
error: sep_eq: atom multisets differ:
  only in LHS: `p ↦₆₄ v`
  only in RHS: `q ↦₆₄ v`
  LHS: `a ↦₆₄ x`, `p ↦₆₄ v`, `b ↦₆₄ y`
  RHS: `b ↦₆₄ y`, `q ↦₆₄ v`, `a ↦₆₄ x`
-/
#guard_msgs in
example (a b p q x y v : BitVec 64) :
    ((a ↦₆₄ x) ∗ (p ↦₆₄ v) ∗ (b ↦₆₄ y)) = ((b ↦₆₄ y) ∗ (q ↦₆₄ v) ∗ (a ↦₆₄ x)) := by
  sep_eq

theorem callee_saved_chain_and_projections (s0 s1 s2 s3 : State)
    (h01 : CalleeSavedPreserved s0 s1)
    (h12 : CalleeSavedPreserved s1 s2)
    (h23 : CalleeSavedPreserved s2 s3) :
    s3.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) ∧
    s3.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
    s3.readReg64 Reg.fp = s0.readReg64 Reg.fp ∧
    s3.readReg32 (.gpr 21#5) = s0.readReg32 (.gpr 21#5) ∧
    CalleeSavedPreserved s0 s0 := by
  have h03 : CalleeSavedPreserved s0 s3 := (h01.trans h12).trans h23
  exact ⟨h03.readReg64_x19, h03.readReg64_x28, h03.readReg64_fp, h03.readReg32_x21,
         CalleeSavedPreserved.rfl s0⟩

theorem split_callee_saved_tactic_test (s0 s1 sf : State) (v : BitVec 64)
    (hcs1 : CalleeSavedPreserved s0 s1)
    (hcs2 : CalleeSavedPreserved (s1.writeReg64 .x0 v) sf) :
    sf.readReg64 (.gpr 19#5) = s0.readReg64 (.gpr 19#5) ∧
    sf.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
    sf.readReg64 Reg.fp = s0.readReg64 Reg.fp := by
  split_callee_saved
  refine ⟨?_, ?_, ?_⟩ <;> simp_all

open ProofLib.ProgramReflection
open ProofLib.GenDecodes

def widgetRawProg_tree : WordTree :=
  .node 2
    (.node 1
      (.leaf 0x01#8 0x01#8 0x80#8 0xd2#8)  -- 0x00: mov x1, #8
      (.leaf 0x3f#8 0x00#8 0x00#8 0x14#8)) -- 0x04: b 0x100
    (.node 1
      (.leaf 0x40#8 0x05#8 0x80#8 0xd2#8)  -- 0x08: mov x0, #42
      (.leaf 0x7d#8 0x00#8 0x00#8 0x14#8)) -- 0x0c: b 0x200

def widgetRawProg : Program :=
  { base := 0#64
    code := widgetRawProg_tree.toBytes
    symbols := [
      ("widget_tailcall_hook", 0x00),
      ("widget_tailcall_ext",  0x08)
    ]
    stubs := [
      ("widget_free", 0x100)
    ] }

@[simp, arm64_norm]
theorem widgetRawProg_fnOff_hook : widgetRawProg.fnOff "widget_tailcall_hook" = 0x00 := rfl

@[simp, arm64_norm]
theorem widgetRawProg_fnOff_ext : widgetRawProg.fnOff "widget_tailcall_ext" = 0x08 := rfl

theorem widgetRawProg_fetch_at (off : Nat) (inst : Instr)
    (h : widgetRawProg_tree.fetchDecodeAt off = some inst) (hoff : off < 2 ^ 64) :
    widgetRawProg.fetch (BitVec.ofNat 64 off) = some inst := by
  simpa [widgetRawProg] using
    fetch_of_wordTree (prog := widgetRawProg) (t := widgetRawProg_tree) 4 rfl rfl h hoff
      (hookAtOff?_eq_none_of_isNone (fun _ => rfl) (fun _ => rfl) off)

theorem widgetRawProg_fetch_rebase_text (b : BitVec 64) (X : String → Option (State → State))
    (off : Nat) (inst : Instr) (h : widgetRawProg_tree.fetchDecodeAt off = some inst)
    (htext : off < 256) (hoff : off < 2 ^ 64) :
    (widgetRawProg.rebase b X).fetch (b + BitVec.ofNat 64 off) = some inst :=
  (Program.fetch_rebase_of_noStubBefore (P := widgetRawProg) rfl (fun _ => rfl) (fun _ => rfl) rfl
    b X htext hoff).trans (widgetRawProg_fetch_at off inst h hoff)

gen_fetches widgetRawProg widget 256 true [0 → 12]

@[simp, arm64_norm] theorem widget_extern_100 {b : BitVec 64} {H : String → Option (State → State)} :
    (widgetRawProg.rebase b H).externAt? (b + 0x100#64) = H "widget_free" := by
  rw [Program.externAt?_rebase_add (P := widgetRawProg) (b := b) (X := H) (O := fun _ => none) 0x100]
  simp (config := { decide := true }) [Program.hookAtOff?, Program.rebase, widgetRawProg, List.findSome?, Option.or]
  cases H "widget_free" <;> rfl

declare_rebased_program widgetRebased (0x400000#64 : BitVec 64) widgetRawProg

def widgetParamProg (b : BitVec 64)
    (H : String → Option (State → State)) : Program :=
  widgetRawProg.rebase b H

def widgetFreeSpec : Spec (BitVec 64) :=
  { pre  := fun ptr s => ⌜s.readReg64 .x0 = ptr ∧ s.readReg64 .x1 = 8#64⌝ ∗ memRegion ptr 8
    post := fun _ _ _ => emp }

def widgetTailcallHookSpec : Spec (BitVec 64) :=
  { pre  := fun ptr s => ⌜s.readReg64 .x0 = ptr⌝ ∗ memRegion ptr 8
    post := fun _ _ _ => emp }

def widgetExtSpec : Spec Unit :=
  { pre  := fun _ s => ⌜s.readReg64 .x0 = 42#64⌝
    post := fun _ _ sf => ⌜sf.readReg64 .x0 = 99#64⌝ }

def widgetTailcallExtCallerSpec : Spec Unit :=
  { pre  := fun _ _ => emp
    post := fun _ _ sf => ⌜sf.readReg64 .x0 = 99#64⌝ }

theorem widget_tailcall_hook_via_hooksat_ok (b : BitVec 64)
    (H : String → Option (State → State))
    (hfree_sat : HookSat H "widget_free" widgetFreeSpec) :
    (widgetParamProg b H).subroutineOk "widget_tailcall_hook" widgetTailcallHookSpec := by
  wp_init ptr s0
  wp_steps
  wp_tailcall hfree_sat
  wp_done

theorem widget_tailcall_hook_pre_branch_ok (b : BitVec 64)
    (H : String → Option (State → State))
    (hfree_sat : HookSat H "widget_free" widgetFreeSpec) :
    (widgetParamProg b H).subroutineOk "widget_tailcall_hook" widgetTailcallHookSpec := by
  wp_init ptr s0
  wp_steps 1
  wp_tailcall hfree_sat
  wp_done

theorem widget_tailcall_ext_ok (b : BitVec 64)
    (H : String → Option (State → State))
    (hext : subroutine_ok (widgetRawProg.rebase b H) (b + 0x200#64) widgetExtSpec) :
    (widgetParamProg b H).subroutineOk "widget_tailcall_ext" widgetTailcallExtCallerSpec := by
  wp_init _u s0
  wp_steps
  wp_tailcall hext
  wp_done

theorem widget_fixed_rebased_auto_unfold_ok
    (hext : subroutine_ok (widgetRawProg.rebase 0x400000#64) (0x400000#64 + 0x200#64) widgetExtSpec) :
    widgetRebased.subroutineOk "widget_tailcall_ext" widgetTailcallExtCallerSpec := by
  wp_init _u s0
  wp_steps
  wp_tailcall hext
  wp_done

theorem widget_tailcall_ext_mono_outcome_ok (b : BitVec 64)
    (H : String → Option (State → State))
    (hext : subroutine_ok (widgetRawProg.rebase b H) (b + 0x200#64) widgetExtSpec) :
    (widgetParamProg b H).subroutineOk "widget_tailcall_ext"
      { widgetTailcallExtCallerSpec with post := fun _ _ sf => ⌜sf.readReg64 .x0 ≠ 0#64⌝ } := by
  apply subroutine_ok_outcome_intro
  intro u R s0 hpc hrun hpre hsp
  refine (widget_tailcall_ext_ok b H hext).mono_outcome u R s0 hpc hrun hpre hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨c, hex, hq⟩ | ⟨hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [widgetTailcallExtCallerSpec, ToBaseSpec.toSpec] at hq ⊢
    rw [satisfies_pure_sepConj] at hq ⊢
    exact ⟨by rw [hq.1]; decide, hq.2⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hex, hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hoom, hq⟩))

/--
error: Application type mismatch: The argument
  hpre
has type
  s0.mem ⊨ widgetTailcallExtCallerSpec.pre Unit u s0 ∗ R
but is expected to have type
  s0.mem ⊨ widgetExtSpec.pre Unit u s0 ∗ R
in the application
  subroutine_ok.mono_outcome hext u R s0 hpc hrun hpre

Note: The following definitions were not unfolded because their definition is not exposed:
  Satisfies ↦ 4
  SepProp.pure ↦ 3
  emp ↦ 1
  sepConj ↦ 4
-/
#guard_msgs in
example (prog : Program) (a : BitVec 64)
    (hext : subroutine_ok prog a widgetExtSpec)
    (u : Unit) (R : SepProp) (s0 : State)
    (hpc : s0.pc = a) (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ widgetTailcallExtCallerSpec.pre u s0 ∗ R)
    (hsp : s0.spAligned = true) :
    reaches_outcome prog widgetTailcallExtCallerSpec u R s0 s0 :=
  hext.mono_outcome u R s0 hpc hrun hpre hsp (fun _ h => h)

/--
error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce

prog : Program
a : BitVec 64
⊢ subroutine_ok prog a widgetExtSpec
-/
#guard_msgs in
example (prog : Program) (a : BitVec 64) :
    subroutine_ok prog a widgetExtSpec := by
  intro u

end Examples.Testing.ProofLib.TailcallCalleeSavedSepEq

end
