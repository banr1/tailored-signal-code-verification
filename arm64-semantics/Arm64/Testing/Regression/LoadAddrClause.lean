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
# `load_addr` Specification Clause Tests

Regression tests for the `load_addr <ident>` binder in `c_spec` and `rust_spec` and for
`[ToBaseSpec S α]` instantiation across `Program.subroutineOk`, `Obj.LinkedImage.subroutineOk`,
`Spec.liftedSubroutineHook`, `#spec_lint!`, and `#spec_nonvacuous!`.
-/

@[expose] public section

namespace Testing.LoadAddrClause

open Arm64 ProofLib Testing.CExamplesFixture

c_spec loadAddrCtxSpec (ctx k : u64) (ctx n : Nat) (x : u64) : u64
  load_addr base
  returns x + base + k + BitVec.ofNat 64 n

c_spec loadAddrHeaderSpec (load_addr b) (ctx k : u64) (x : u64) : u64
  returns x + b + k

rust_spec loadAddrRustSpec (ctx k : u64) (x : u64) : u64
  load_addr b
  returns x + b + k

c_spec loadAddrOnlySpec (x : u64) : u64
  load_addr b
  returns x + b

example (k : BitVec 64) (n : Nat) : BaseSpec (BitVec 64) := loadAddrCtxSpec k n
example (k : BitVec 64) : BaseSpec (BitVec 64) := loadAddrHeaderSpec k
example (k : BitVec 64) : BaseSpec (BitVec 64) := loadAddrRustSpec k
example : BaseSpec (BitVec 64) := loadAddrOnlySpec

example : ToBaseSpec (BaseSpec (BitVec 64)) (BitVec 64) := inferInstance
example (k : BitVec 64) (n : Nat) (b : BitVec 64) :
    ToBaseSpec.toSpec (loadAddrCtxSpec k n) b = loadAddrCtxSpec k n b := rfl

/--
error: duplicate load address binding: at most one 'load_addr <ident>' may appear in a specification
-/
#guard_msgs in
c_spec dupLoadAddrSpec (x : u64) : u64
  load_addr b
  load_addr c
  returns x + b + c

/--
error: duplicate load address binding: at most one 'load_addr <ident>' may appear in a specification
-/
#guard_msgs in
c_spec dupLoadAddrHeaderSpec (load_addr b) (x : u64) : u64
  load_addr c
  returns x + b + c

section Judgments

variable (prog : Program) (k : BitVec 64) (n : Nat)

example : prog.subroutineOk "f" (loadAddrCtxSpec k n) ↔
    subroutine_ok prog (prog.fnAddr "f") (loadAddrCtxSpec k n prog.base) := Iff.rfl

example : prog.rawSubroutineOk "f" (loadAddrCtxSpec k n) ↔
    raw_subroutine_ok prog (prog.fnAddr "f") (loadAddrCtxSpec k n prog.base) := Iff.rfl

example : prog.safeSubroutineOk "f" (loadAddrCtxSpec k n) ↔
    safe_subroutine_ok prog (prog.fnAddr "f") (loadAddrCtxSpec k n prog.base) := Iff.rfl

example : fn_subroutine_ok prog "f" (loadAddrRustSpec k) ↔
    subroutine_ok prog (prog.fnAddr "f") (loadAddrRustSpec k prog.base) := Iff.rfl

example : prog.subroutineOk "c_arith_shift" cArithShiftSpec ↔
    subroutine_ok prog (prog.fnAddr "c_arith_shift") cArithShiftSpec := Iff.rfl

example (b : BitVec 64) (H : String → Option (State → State)) :
    (cExamplesCode.rebase b H).subroutineOk "f" (loadAddrHeaderSpec k) ↔
      subroutine_ok (cExamplesCode.rebase b H) ((cExamplesCode.rebase b H).fnAddr "f")
        (loadAddrHeaderSpec k b) := by
  simp only [Program.subroutineOk, ToBaseSpec.toSpec, Program.rebase_base]

example (li : Obj.LinkedImage) : li.subroutineOk "f" (loadAddrCtxSpec k n) ↔
    ∀ img, Obj.Loads li img →
      (Program.ofImage img).subroutineOk "f" (loadAddrCtxSpec k n img.base) := Iff.rfl

example : Spec.liftedSubroutineHook prog "f" (loadAddrCtxSpec k n) =
    Spec.liftedSubroutineHook prog "f" (loadAddrCtxSpec k n prog.base) := rfl

example : (Spec.liftedSubroutineHook prog "c_arith_shift" cArithShiftSpec).pre =
    fun y s0 => memRegion prog.base prog.code.length ∗
      cArithShiftSpec.pre y (subroutineHookEntry prog (prog.fnAddr "c_arith_shift") s0) := rfl

end Judgments

/-- `c_arith_shift` computes `3 * (x + 42)`, stated with canceling `load_addr` terms. -/
c_spec cArithShiftLoadAddrSpec (x : u64) : u64
  load_addr b
  returns (b + 3#64 * (x + 42#64)) - b

theorem cArithShift_loadAddr (b : BitVec 64) (H : String → Option (State → State)) :
    (cExamplesCode.rebase b H).subroutineOk "c_arith_shift" cArithShiftLoadAddrSpec := by
  wp_entry "c_arith_shift" x s0
  wp_steps
  have hmul : x + x <<< 1 + 126#64 = b + 3#64 * (x + 42#64) - b := by bv_lin
  rw [hmul]
  wp_done

#spec_lint! loadAddrCtxSpec
#spec_nonvacuous! loadAddrCtxSpec
#spec_lint! cArithShiftLoadAddrSpec
#spec_nonvacuous! cArithShiftLoadAddrSpec

end Testing.LoadAddrClause
