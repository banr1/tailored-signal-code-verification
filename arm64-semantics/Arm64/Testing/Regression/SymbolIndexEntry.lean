/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import Arm64.Testing.Regression.CExamplesFixture

/-!
# Symbol Index, `stackFrameFor`, and `wp_entry` Regressions

Regression tests for generated `fnSize` and `fnFrameBytes` simp lemmas, `stackFrameAt` and
`stackFrameFor` reduction, and `wp_entry` / `wp_init_fn` entry normalization and callee-address
bridging.
-/

@[expose] public section

namespace Testing.SymbolIndexEntry

open Arm64 ProofLib Testing.CExamplesFixture

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

attribute [local irreducible] Program.fetch Program.externAt?

/-! ## Generated `fnSize` and `frameBytes` lemmas -/

example : fnFrameBytes cExamplesObj "c_arith_shift" = 0 := by simp
example : fnFrameBytes cExamplesImage "c_swap_u64" = 0 := by simp
example : Obj.fnSize cExamplesImage "c_swap_u64" = 20 := by simp
example : fnFrameBytes cExamplesObj "c_swap_u64" = 0 := by simp

/-! ## `stackFrameAt` and `stackFrameFor` -/

example (sp : BitVec 64) : stackFrameAt sp 0 = emp := rfl
example (sp : BitVec 64) : stackFrameAt sp 16 = memRegion (sp - 16#64) 16 :=
  stackFrameAt_eq_memRegion sp 16
example (sp : BitVec 64) : stackFrameAt sp 32 = memRegion (sp - 32#64) 32 :=
  stackFrameAt_eq_memRegion sp 32

example (sp : BitVec 64) :
    stackFrameFor cExamplesObj "c_arith_shift" sp = emp := by
  simp

example (sp : BitVec 64) :
    cExamplesCode_frame "c_arith_shift" sp = emp := by
  simp

example (sp : BitVec 64) :
    stackFrameFor cExamplesImage "c_swap_u64" sp = emp := by
  simp

example (sp : BitVec 64) :
    stackFrameAt sp 16 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
        ((sp - 16#64) ↦₆₄ v0) ∗ ((sp - 8#64) ↦₆₄ v1)) := by
  simp only [wp_norm]

/-! ## `wp_entry` and `wp_init_fn` -/

def cArithShiftFrameSpec : Spec (BitVec 64) where
  pre  := fun x s0 => ⌜s0.readReg64 .x0 = x⌝ ∗ stackFrameFor cExamplesObj "c_arith_shift" s0.sp
  post := fun x _ sf => ⌜sf.readReg64 .x0 = 3#64 * (x + 42#64)⌝

theorem cArithShift_wp_entry_fnAddr (b : BitVec 64) (H : String → Option (State → State)) :
    (cExamplesCode.rebase b H).subroutineOk "c_arith_shift" cArithShiftFrameSpec := by
  wp_entry "c_arith_shift" x s0
  wp_steps
  have hmul : x + x <<< 1 + 126#64 = 3#64 * (x + 42#64) := by bv_lin
  rw [hmul]
  wp_done

theorem cArithShift_wp_entry_hex_zero (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok (cExamplesCode.rebase b H) (b + 0x0#64) cArithShiftSpec := by
  wp_entry "c_arith_shift" x s0
  wp_steps
  have hmul : x + x <<< 1 + 126#64 = 3#64 * (x + 42#64) := by bv_lin
  rw [hmul]
  wp_done

theorem cMaxU64_wp_init_fn_hex (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok (cExamplesCode.rebase b H) (b + 0xc#64) cMaxU64Spec := by
  wp_init_fn x s0
  obtain ⟨va, vb⟩ := x
  dsimp only at *
  wp_steps
  wp_done

theorem cSwapU64_wp_entry_inferred (b : BitVec 64) (H : String → Option (State → State)) :
    subroutine_ok (cExamplesCode.rebase b H) ((cExamplesCode.rebase b H).fnAddr "c_swap_u64")
      cSwapU64Spec := by
  wp_entry x s0
  obtain ⟨pa, pb, va, vb⟩ := x
  wp_steps
  wp_done

theorem cArithShift_wp_entry_callee_bridge (b : BitVec 64) (H : String → Option (State → State))
    (hcallee : subroutine_ok (cExamplesCode.rebase b H)
      ((cExamplesCode.rebase b H).fnAddr "c_max_u64") cMaxU64Spec) :
    subroutine_ok (cExamplesCode.rebase b H)
      ((cExamplesCode.rebase b H).fnAddr "c_arith_shift") cArithShiftSpec := by
  wp_entry "c_arith_shift" x s0
  have _ : subroutine_ok (cExamplesCode.rebase b H) (entry + 12#64) cMaxU64Spec := hcallee
  wp_steps
  have hmul : x + x <<< 1 + 126#64 = 3#64 * (x + 42#64) := by bv_lin
  rw [hmul]
  wp_done

theorem cArithShift_wp_entry_callee_bridge_hex (b : BitVec 64) (H : String → Option (State → State))
    (hcallee : subroutine_ok (cExamplesCode.rebase b H) (b + 0xc#64) cMaxU64Spec) :
    subroutine_ok (cExamplesCode.rebase b H)
      ((cExamplesCode.rebase b H).fnAddr "c_arith_shift") cArithShiftSpec := by
  wp_entry "c_arith_shift" x s0
  guard_hyp hcallee : subroutine_ok (cExamplesCode.rebase b H) (entry + 12#64) _
  have _ : subroutine_ok (cExamplesCode.rebase b H) (entry + 12#64) cMaxU64Spec := hcallee
  wp_steps
  have hmul : x + x <<< 1 + 126#64 = 3#64 * (x + 42#64) := by bv_lin
  rw [hmul]
  wp_done

-- Non-matching base `b'` is not bridged to `entry + 12#64`.
/-- error: Type mismatch
  _hother
has type
  subroutine_ok (cExamplesCode.rebase b H) (b' + 12#64)
    { pre := fun x s0 => ⌜s0.readReg64 Reg.x0 = x.fst ∧ s0.readReg64 Reg.x1 = x.snd⌝,
      post := fun x s0 sf => ⌜sf.readReg64 Reg.x0 = if x.snd.ult x.fst = true then x.fst else x.snd⌝ }
but is expected to have type
  subroutine_ok (cExamplesCode.rebase b H) (entry + 12#64) cMaxU64Spec -/
#guard_msgs (substring := true) in
example (b b' : BitVec 64) (H : String → Option (State → State))
    (_hother : subroutine_ok (cExamplesCode.rebase b H) (b' + 0xc#64) cMaxU64Spec) :
    subroutine_ok (cExamplesCode.rebase b H)
      ((cExamplesCode.rebase b H).fnAddr "c_arith_shift") cArithShiftSpec := by
  wp_entry "c_arith_shift" x s0
  guard_hyp _hother : subroutine_ok (cExamplesCode.rebase b H) (b' + 12#64) _
  have _ : subroutine_ok (cExamplesCode.rebase b H) (entry + 12#64) cMaxU64Spec := _hother
  wp_steps
  have hmul : x + x <<< 1 + 126#64 = 3#64 * (x + 42#64) := by bv_lin
  rw [hmul]
  wp_done

theorem frame32Branch_stackFrameFor_wp_entry [Frame32Placement] (b : BitVec 64)
    (H : String → Option (State → State)) :
    subroutine_ok (α := BitVec 64 × BitVec 64)
      (frame32Code.rebase b H) ((frame32Code.rebase b H).fnAddr "frame32_branch")
      { pre := fun (x, sp) s =>
          ⌜s.readReg64 .x0 = x ∧ s.sp = sp⌝ ∗ stackFrameAt sp 32
        post := fun (x, sp) _ s =>
          ⌜s.readReg64 .x0 = (if x == 0#64 then 1#64 else x + 1#64)⌝ ∗ stackFrameAt sp 32 } := by
  wp_entry x s0
  obtain ⟨x, sp⟩ := x
  dsimp only at *
  subst h
  wp_steps
  wp_if hb
  · wp_steps
    wp_done
  · wp_steps
    wp_done

end Testing.SymbolIndexEntry
