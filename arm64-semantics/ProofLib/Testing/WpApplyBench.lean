/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WP.Apply

/-!
# Synthetic Benchmarks for `wp_apply`

Compares three call-site styles over straight-line sequences of `k` (`2`, `4`, `8`) subroutine
calls whose contracts borrow a caller stack slot:
- `*_hand`: explicit `have` per callee contract and explicit ghost tuple (`wp_call h ⟨...⟩`);
- `*_named`: explicit `have` per callee contract with inferred ghost tuple (`wp_call h`);
- `*_auto`: automatic `@[wp_spec]` lookup and ghost inference (`wp_apply`).
-/

@[expose] public section

namespace Examples.Testing.ProofLib.WpApplyBench

open Arm64 _root_.ProofLib

/-- Ghost argument shared by the synthetic callees. -/
structure CalleeArgs where
  /-- object pointer, passed in `x0` -/
  p : BitVec 64
  /-- object contents -/
  v : BitVec 64
  /-- callee stack pointer at entry -/
  sp : BitVec 64
  /-- contents of the caller stack slot `sp - 16` lent to the callee -/
  w : BitVec 64

/-- Callee `i`: adds `i + 1` to the object at `x0`; borrows the stack slot below its `sp`. -/
abbrev calleeSpec (i : Nat) : Spec CalleeArgs where
  pre := fun a s =>
    ⌜s.readReg64 .x0 = a.p ∧ s.sp = a.sp⌝ ∗ (a.p ↦₆₄ a.v) ∗ ((a.sp - 16#64) ↦₆₄ a.w)
  post := fun a _ _ =>
    (a.p ↦₆₄ (a.v + BitVec.ofNat 64 (i + 1))) ∗ ((a.sp - 16#64) ↦₆₄ a.w)

/-- Bundled contracts for the eight synthetic callees. -/
structure Callees (prog : Program) : Prop where
  c0 : subroutine_ok prog 0x30000#64 (calleeSpec 0)
  c1 : subroutine_ok prog 0x30100#64 (calleeSpec 1)
  c2 : subroutine_ok prog 0x30200#64 (calleeSpec 2)
  c3 : subroutine_ok prog 0x30300#64 (calleeSpec 3)
  c4 : subroutine_ok prog 0x30400#64 (calleeSpec 4)
  c5 : subroutine_ok prog 0x30500#64 (calleeSpec 5)
  c6 : subroutine_ok prog 0x30600#64 (calleeSpec 6)
  c7 : subroutine_ok prog 0x30700#64 (calleeSpec 7)

theorem callee0_ok {prog : Program} (hC : Callees prog) :
    subroutine_ok prog 0x30000#64 (calleeSpec 0) := hC.c0
theorem callee1_ok {prog : Program} (hC : Callees prog) :
    subroutine_ok prog 0x30100#64 (calleeSpec 1) := hC.c1
theorem callee2_ok {prog : Program} (hC : Callees prog) :
    subroutine_ok prog 0x30200#64 (calleeSpec 2) := hC.c2
theorem callee3_ok {prog : Program} (hC : Callees prog) :
    subroutine_ok prog 0x30300#64 (calleeSpec 3) := hC.c3
theorem callee4_ok {prog : Program} (hC : Callees prog) :
    subroutine_ok prog 0x30400#64 (calleeSpec 4) := hC.c4
theorem callee5_ok {prog : Program} (hC : Callees prog) :
    subroutine_ok prog 0x30500#64 (calleeSpec 5) := hC.c5
theorem callee6_ok {prog : Program} (hC : Callees prog) :
    subroutine_ok prog 0x30600#64 (calleeSpec 6) := hC.c6
theorem callee7_ok {prog : Program} (hC : Callees prog) :
    subroutine_ok prog 0x30700#64 (calleeSpec 7) := hC.c7

attribute [local wp_spec] callee0_ok callee1_ok callee2_ok callee3_ok callee4_ok callee5_ok
  callee6_ok callee7_ok

/-! ## k = 2 -/

def caller2Code : FnCode :=
  .atAddr "caller2" 0x20000#64
    ("a9bf7bf3 " ++ -- 0x20000: stp x19, x30, [sp, #-16]!
     "91000013 " ++ -- 0x20004: add x19, x0, #0
     "91000260 " ++ -- 0x20008: add x0, x19, #0
     "94003ffd " ++ -- 0x2000c: bl 0x30000 (callee0)
     "91002260 " ++ -- 0x20010: add x0, x19, #8
     "9400403b " ++ -- 0x20014: bl 0x30100 (callee1)
     "a8c17bf3 " ++ -- 0x20018: ldp x19, x30, [sp], #16
     "d65f03c0") -- 0x2001c: ret

abbrev Caller2CodeAt (prog : Program) : Prop := caller2Code.holds prog

structure Caller2Args where
  base : BitVec 64
  v0 : BitVec 64
  v1 : BitVec 64
  w : BitVec 64

abbrev caller2Spec : Spec Caller2Args where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.base⌝ ∗ (a.base ↦₆₄ a.v0) ∗ ((a.base + 8#64) ↦₆₄ a.v1) ∗
    ((s0.sp - 32#64) ↦₆₄ a.w) ∗ stackFrame16 s0
  post := fun a s0 sf =>
    (a.base ↦₆₄ (a.v0 + 1#64)) ∗ ((a.base + 8#64) ↦₆₄ (a.v1 + 2#64)) ∗
    ((s0.sp - 32#64) ↦₆₄ a.w) ∗ stackFrame16 sf

theorem caller2_hand (prog : Program) (h_code : Caller2CodeAt prog) (hC : Callees prog) :
    prog.subroutineOk "caller2" caller2Spec := by
  have h0 := callee0_ok hC
  have h1 := callee1_ok hC
  wp_init a s0
  wp_steps
  wp_call h0 ⟨a.base, a.v0, s0.sp - 16#64, a.w⟩
  wp_steps
  wp_call h1 ⟨a.base + 8#64, a.v1, s0.sp - 16#64, a.w⟩
  wp_steps
  wp_done

theorem caller2_named (prog : Program) (h_code : Caller2CodeAt prog) (hC : Callees prog) :
    prog.subroutineOk "caller2" caller2Spec := by
  have h0 := callee0_ok hC
  have h1 := callee1_ok hC
  wp_init a s0
  wp_steps
  wp_call h0
  wp_steps
  wp_call h1
  wp_steps
  wp_done

theorem caller2_auto (prog : Program) (h_code : Caller2CodeAt prog) (hC : Callees prog) :
    prog.subroutineOk "caller2" caller2Spec := by
  wp_init a s0
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  wp_steps
  wp_done

/-! ## k = 4 -/

def caller4Code : FnCode :=
  .atAddr "caller4" 0x21000#64
    ("a9bf7bf3 " ++ -- 0x21000: stp x19, x30, [sp, #-16]!
     "91000013 " ++ -- 0x21004: add x19, x0, #0
     "91000260 " ++ -- 0x21008: add x0, x19, #0
     "94003bfd " ++ -- 0x2100c: bl 0x30000 (callee0)
     "91002260 " ++ -- 0x21010: add x0, x19, #8
     "94003c3b " ++ -- 0x21014: bl 0x30100 (callee1)
     "91004260 " ++ -- 0x21018: add x0, x19, #16
     "94003c79 " ++ -- 0x2101c: bl 0x30200 (callee2)
     "91006260 " ++ -- 0x21020: add x0, x19, #24
     "94003cb7 " ++ -- 0x21024: bl 0x30300 (callee3)
     "a8c17bf3 " ++ -- 0x21028: ldp x19, x30, [sp], #16
     "d65f03c0") -- 0x2102c: ret

abbrev Caller4CodeAt (prog : Program) : Prop := caller4Code.holds prog

structure Caller4Args where
  base : BitVec 64
  v0 : BitVec 64
  v1 : BitVec 64
  v2 : BitVec 64
  v3 : BitVec 64
  w : BitVec 64

abbrev caller4Spec : Spec Caller4Args where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.base⌝ ∗ (a.base ↦₆₄ a.v0) ∗ ((a.base + 8#64) ↦₆₄ a.v1) ∗ ((a.base + 16#64) ↦₆₄ a.v2) ∗ ((a.base + 24#64) ↦₆₄ a.v3) ∗
    ((s0.sp - 32#64) ↦₆₄ a.w) ∗ stackFrame16 s0
  post := fun a s0 sf =>
    (a.base ↦₆₄ (a.v0 + 1#64)) ∗ ((a.base + 8#64) ↦₆₄ (a.v1 + 2#64)) ∗ ((a.base + 16#64) ↦₆₄ (a.v2 + 3#64)) ∗ ((a.base + 24#64) ↦₆₄ (a.v3 + 4#64)) ∗
    ((s0.sp - 32#64) ↦₆₄ a.w) ∗ stackFrame16 sf

theorem caller4_hand (prog : Program) (h_code : Caller4CodeAt prog) (hC : Callees prog) :
    prog.subroutineOk "caller4" caller4Spec := by
  have h0 := callee0_ok hC
  have h1 := callee1_ok hC
  have h2 := callee2_ok hC
  have h3 := callee3_ok hC
  wp_init a s0
  wp_steps
  wp_call h0 ⟨a.base, a.v0, s0.sp - 16#64, a.w⟩
  wp_steps
  wp_call h1 ⟨a.base + 8#64, a.v1, s0.sp - 16#64, a.w⟩
  wp_steps
  wp_call h2 ⟨a.base + 16#64, a.v2, s0.sp - 16#64, a.w⟩
  wp_steps
  wp_call h3 ⟨a.base + 24#64, a.v3, s0.sp - 16#64, a.w⟩
  wp_steps
  wp_done

theorem caller4_named (prog : Program) (h_code : Caller4CodeAt prog) (hC : Callees prog) :
    prog.subroutineOk "caller4" caller4Spec := by
  have h0 := callee0_ok hC
  have h1 := callee1_ok hC
  have h2 := callee2_ok hC
  have h3 := callee3_ok hC
  wp_init a s0
  wp_steps
  wp_call h0
  wp_steps
  wp_call h1
  wp_steps
  wp_call h2
  wp_steps
  wp_call h3
  wp_steps
  wp_done

theorem caller4_auto (prog : Program) (h_code : Caller4CodeAt prog) (hC : Callees prog) :
    prog.subroutineOk "caller4" caller4Spec := by
  wp_init a s0
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  wp_steps
  wp_done

/-! ## k = 8 -/

def caller8Code : FnCode :=
  .atAddr "caller8" 0x22000#64
    ("a9bf7bf3 " ++ -- 0x22000: stp x19, x30, [sp, #-16]!
     "91000013 " ++ -- 0x22004: add x19, x0, #0
     "91000260 " ++ -- 0x22008: add x0, x19, #0
     "940037fd " ++ -- 0x2200c: bl 0x30000 (callee0)
     "91002260 " ++ -- 0x22010: add x0, x19, #8
     "9400383b " ++ -- 0x22014: bl 0x30100 (callee1)
     "91004260 " ++ -- 0x22018: add x0, x19, #16
     "94003879 " ++ -- 0x2201c: bl 0x30200 (callee2)
     "91006260 " ++ -- 0x22020: add x0, x19, #24
     "940038b7 " ++ -- 0x22024: bl 0x30300 (callee3)
     "91008260 " ++ -- 0x22028: add x0, x19, #32
     "940038f5 " ++ -- 0x2202c: bl 0x30400 (callee4)
     "9100a260 " ++ -- 0x22030: add x0, x19, #40
     "94003933 " ++ -- 0x22034: bl 0x30500 (callee5)
     "9100c260 " ++ -- 0x22038: add x0, x19, #48
     "94003971 " ++ -- 0x2203c: bl 0x30600 (callee6)
     "9100e260 " ++ -- 0x22040: add x0, x19, #56
     "940039af " ++ -- 0x22044: bl 0x30700 (callee7)
     "a8c17bf3 " ++ -- 0x22048: ldp x19, x30, [sp], #16
     "d65f03c0") -- 0x2204c: ret

abbrev Caller8CodeAt (prog : Program) : Prop := caller8Code.holds prog

structure Caller8Args where
  base : BitVec 64
  v0 : BitVec 64
  v1 : BitVec 64
  v2 : BitVec 64
  v3 : BitVec 64
  v4 : BitVec 64
  v5 : BitVec 64
  v6 : BitVec 64
  v7 : BitVec 64
  w : BitVec 64

abbrev caller8Spec : Spec Caller8Args where
  pre := fun a s0 =>
    ⌜s0.readReg64 .x0 = a.base⌝ ∗ (a.base ↦₆₄ a.v0) ∗ ((a.base + 8#64) ↦₆₄ a.v1) ∗ ((a.base + 16#64) ↦₆₄ a.v2) ∗ ((a.base + 24#64) ↦₆₄ a.v3) ∗ ((a.base + 32#64) ↦₆₄ a.v4) ∗ ((a.base + 40#64) ↦₆₄ a.v5) ∗ ((a.base + 48#64) ↦₆₄ a.v6) ∗ ((a.base + 56#64) ↦₆₄ a.v7) ∗
    ((s0.sp - 32#64) ↦₆₄ a.w) ∗ stackFrame16 s0
  post := fun a s0 sf =>
    (a.base ↦₆₄ (a.v0 + 1#64)) ∗ ((a.base + 8#64) ↦₆₄ (a.v1 + 2#64)) ∗ ((a.base + 16#64) ↦₆₄ (a.v2 + 3#64)) ∗ ((a.base + 24#64) ↦₆₄ (a.v3 + 4#64)) ∗ ((a.base + 32#64) ↦₆₄ (a.v4 + 5#64)) ∗ ((a.base + 40#64) ↦₆₄ (a.v5 + 6#64)) ∗ ((a.base + 48#64) ↦₆₄ (a.v6 + 7#64)) ∗ ((a.base + 56#64) ↦₆₄ (a.v7 + 8#64)) ∗
    ((s0.sp - 32#64) ↦₆₄ a.w) ∗ stackFrame16 sf

theorem caller8_hand (prog : Program) (h_code : Caller8CodeAt prog) (hC : Callees prog) :
    prog.subroutineOk "caller8" caller8Spec := by
  have h0 := callee0_ok hC
  have h1 := callee1_ok hC
  have h2 := callee2_ok hC
  have h3 := callee3_ok hC
  have h4 := callee4_ok hC
  have h5 := callee5_ok hC
  have h6 := callee6_ok hC
  have h7 := callee7_ok hC
  wp_init a s0
  wp_steps
  wp_call h0 ⟨a.base, a.v0, s0.sp - 16#64, a.w⟩
  wp_steps
  wp_call h1 ⟨a.base + 8#64, a.v1, s0.sp - 16#64, a.w⟩
  wp_steps
  wp_call h2 ⟨a.base + 16#64, a.v2, s0.sp - 16#64, a.w⟩
  wp_steps
  wp_call h3 ⟨a.base + 24#64, a.v3, s0.sp - 16#64, a.w⟩
  wp_steps
  wp_call h4 ⟨a.base + 32#64, a.v4, s0.sp - 16#64, a.w⟩
  wp_steps
  wp_call h5 ⟨a.base + 40#64, a.v5, s0.sp - 16#64, a.w⟩
  wp_steps
  wp_call h6 ⟨a.base + 48#64, a.v6, s0.sp - 16#64, a.w⟩
  wp_steps
  wp_call h7 ⟨a.base + 56#64, a.v7, s0.sp - 16#64, a.w⟩
  wp_steps
  wp_done

theorem caller8_named (prog : Program) (h_code : Caller8CodeAt prog) (hC : Callees prog) :
    prog.subroutineOk "caller8" caller8Spec := by
  have h0 := callee0_ok hC
  have h1 := callee1_ok hC
  have h2 := callee2_ok hC
  have h3 := callee3_ok hC
  have h4 := callee4_ok hC
  have h5 := callee5_ok hC
  have h6 := callee6_ok hC
  have h7 := callee7_ok hC
  wp_init a s0
  wp_steps
  wp_call h0
  wp_steps
  wp_call h1
  wp_steps
  wp_call h2
  wp_steps
  wp_call h3
  wp_steps
  wp_call h4
  wp_steps
  wp_call h5
  wp_steps
  wp_call h6
  wp_steps
  wp_call h7
  wp_steps
  wp_done

theorem caller8_auto (prog : Program) (h_code : Caller8CodeAt prog) (hC : Callees prog) :
    prog.subroutineOk "caller8" caller8Spec := by
  wp_init a s0
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  wp_steps
  wp_apply
  wp_steps
  wp_done


/-! ## Axioms (standard only) -/

/--
info: 'Examples.Testing.ProofLib.WpApplyBench.caller2_hand' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms caller2_hand

/--
info: 'Examples.Testing.ProofLib.WpApplyBench.caller2_named' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms caller2_named

/--
info: 'Examples.Testing.ProofLib.WpApplyBench.caller2_auto' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms caller2_auto

/--
info: 'Examples.Testing.ProofLib.WpApplyBench.caller4_hand' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms caller4_hand

/--
info: 'Examples.Testing.ProofLib.WpApplyBench.caller4_named' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms caller4_named

/--
info: 'Examples.Testing.ProofLib.WpApplyBench.caller4_auto' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms caller4_auto

/--
info: 'Examples.Testing.ProofLib.WpApplyBench.caller8_hand' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms caller8_hand

/--
info: 'Examples.Testing.ProofLib.WpApplyBench.caller8_named' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms caller8_named

/--
info: 'Examples.Testing.ProofLib.WpApplyBench.caller8_auto' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms caller8_auto

end Examples.Testing.ProofLib.WpApplyBench
