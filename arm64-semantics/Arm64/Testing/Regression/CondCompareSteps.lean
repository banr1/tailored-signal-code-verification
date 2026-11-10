/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import Arm64
public meta import Arm64
public import ProofLib
public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.SymWP.InsnSteps

/-!
# Conditional Compare Step Rules

Regression tests for the conditional-compare step rules `SepWP.step_ccmp_reg`,
`SepWP.step_ccmp_imm`, `SepWP.step_ccmn_reg`, and `SepWP.step_ccmn_imm` (`SepWP.step_condCompare`),
which push symbolic conditions into the `PState` update so `wp_sym_steps` and `wp_steps` step
through `cmp; ccmp|ccmn; cset` sequences via `conditionHolds_ite`. Also tests `.condCompare` rule
classification and `conditionHolds_hi_addsPState64` for `HI` after a 64-bit `CMN`.
-/

@[expose] public section

namespace Testing.CondCompareSteps

open Arm64 ProofLib

/-! ## `classifyInsnStepRule` coverage -/

public meta section Classifier
open Lean Meta

/-- Decode `w` and return its `Instr` as an `Expr`. -/
def decodeWordExpr (w : BitVec 32) : MetaM Expr := do
  let r ← withTransparency .all (reduce (mkApp (mkConst ``Arm64.decode) (toExpr w)))
  if r.isAppOfArity ``Option.some 2 then
    return r.getArg! 1
  throwError "decodeWordExpr: failed to decode {w}"

/-- Every `CCMP`/`CCMN` form classifies to `.condCompare`; neighbours stay `.pureStep`. -/
def testCondCompareClassifier : MetaM Unit := do
  let check (label : String) (w : BitVec 32) (expected : SymInsnStepRule) : MetaM Unit := do
    let (rule, _) := classifyInsnStepRule (← decodeWordExpr w)
    unless rule == expected do
      throwError "classifyInsnStepRule [{label}]: got theorems {rule.theoremNames}, expected {expected.theoremNames}"
  check "CCMP X2, X3, #0, NE"  0xfa431040#32 .condCompare
  check "CCMP W2, W3, #0, NE"  0x7a431040#32 .condCompare
  check "CCMP X2, #5, #0, NE"  0xfa451840#32 .condCompare
  check "CCMP W2, #5, #4, EQ"  0x7a450844#32 .condCompare
  check "CCMN X2, X3, #0, NE"  0xba431040#32 .condCompare
  check "CCMN W2, W3, #0, NE"  0x3a431040#32 .condCompare
  check "CCMN X2, #3, #0, NE"  0xba431840#32 .condCompare
  check "CCMN W2, #3, #8, LT"  0x3a43b848#32 .condCompare
  check "CMP X0, X1"           0xeb01001f#32 .pureStep
  check "CSEL X0, X1, X2, EQ"  0x9a820020#32 .pureStep

#eval testCondCompareClassifier

end Classifier

/-! ## End-to-end `wp_sym_steps` and `wp_steps` proofs -/

section EndToEnd

set_option maxHeartbeats 400000
arm64_proof_prelude

@[simp, arm64_norm] def cc_addr : BitVec 64 := 0x60000#64

/-- `cmp x0, x1; ccmp x2, x3, #0, ne; cset w0, eq; ret`: computes `x0 != x1 && x2 == x3`. -/
def ccmpXCode : FnCode :=
  .atAddr "ccmp_x" cc_addr ("eb01001f " ++ "fa431040 " ++ "1a9f17e0 " ++ "d65f03c0")

/-- `w0 = 1` iff `x0 ≠ x1 ∧ x2 = x3`: when `x0 = x1` the `CCMP` forces `NZCV = 0` (so `Z = 0`). -/
abbrev ccmpXSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 =
      if (if (s0.readReg64 .x0 != s0.readReg64 .x1) = true then
            s0.readReg64 .x2 != s0.readReg64 .x3
          else true) = true
      then 0#64 else 1#64⌝

/-- `CCMP Xn, Xm` with a symbolic condition (`SepWP.step_ccmp_reg`, `w = .W64`). -/
theorem ccmp_x_sym_ok (prog : Program) (h : ccmpXCode.holds prog) :
    prog.subroutineOk "ccmp_x" ccmpXSpec := by
  wp_init g s0
  wp_sym_steps
  wp_done

theorem ccmp_x_wp_ok (prog : Program) (h : ccmpXCode.holds prog) :
    prog.subroutineOk "ccmp_x" ccmpXSpec := by
  wp_init g s0
  wp_steps
  wp_done

/-- When the precondition fixes `x0 ≠ x1`, the condition resolves and the result is `x2 == x3`. -/
theorem ccmp_x_resolved_ok (prog : Program) (h : ccmpXCode.holds prog) :
    prog.subroutineOk "ccmp_x"
      ({ pre := fun (_ : Unit) s0 => ⌜s0.readReg64 .x0 ≠ s0.readReg64 .x1⌝
         post := fun _ s0 sf =>
           ⌜sf.readReg64 .x0 =
             if (s0.readReg64 .x2 != s0.readReg64 .x3) = true then 0#64 else 1#64⌝ } : Spec _) := by
  wp_init g s0
  wp_sym_steps
  wp_done

/-- `cmp w0, w1; ccmp w2, #5, #4, eq; cset w0, eq; ret`: computes `w0 != w1 || w2 == 5`. -/
def ccmpWImmCode : FnCode :=
  .atAddr "ccmp_w_imm" cc_addr ("6b01001f " ++ "7a450844 " ++ "1a9f17e0 " ++ "d65f03c0")

/-- `CCMP Wn, #imm` (`SepWP.step_ccmp_imm`, `w = .W32`); the false branch sets `Z` (`#4`), so
    `NE` (the inverted `cset eq` condition) is `false` there. -/
abbrev ccmpWImmSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 =
      if (if (s0.readReg32 .x0 == s0.readReg32 .x1) = true then
            s0.readReg32 .x2 != 5#32
          else false) = true
      then 0#64 else 1#64⌝

theorem ccmp_w_imm_sym_ok (prog : Program) (h : ccmpWImmCode.holds prog) :
    prog.subroutineOk "ccmp_w_imm" ccmpWImmSpec := by
  wp_init g s0
  wp_sym_steps
  wp_done

theorem ccmp_w_imm_wp_ok (prog : Program) (h : ccmpWImmCode.holds prog) :
    prog.subroutineOk "ccmp_w_imm" ccmpWImmSpec := by
  wp_init g s0
  wp_steps
  wp_done

/-- `cmp x0, x1; ccmn x2, x3, #0, ne; cset w0, eq; ret`: computes `x0 != x1 && x2 + x3 == 0`. -/
def ccmnXCode : FnCode :=
  .atAddr "ccmn_x" cc_addr ("eb01001f " ++ "ba431040 " ++ "1a9f17e0 " ++ "d65f03c0")

abbrev ccmnXSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 =
      if (if (s0.readReg64 .x0 != s0.readReg64 .x1) = true then
            s0.readReg64 .x2 + s0.readReg64 .x3 != 0#64
          else true) = true
      then 0#64 else 1#64⌝

/-- `CCMN Xn, Xm` (`SepWP.step_ccmn_reg`, `w = .W64`). -/
theorem ccmn_x_sym_ok (prog : Program) (h : ccmnXCode.holds prog) :
    prog.subroutineOk "ccmn_x" ccmnXSpec := by
  wp_init g s0
  wp_sym_steps
  wp_done

theorem ccmn_x_wp_ok (prog : Program) (h : ccmnXCode.holds prog) :
    prog.subroutineOk "ccmn_x" ccmnXSpec := by
  wp_init g s0
  wp_steps
  wp_done

/-- `cmp w0, w1; ccmn w2, #3, #0, ne; cset w0, eq; ret`: computes `w0 != w1 && w2 + 3 == 0`. -/
def ccmnWImmCode : FnCode :=
  .atAddr "ccmn_w_imm" cc_addr ("6b01001f " ++ "3a431840 " ++ "1a9f17e0 " ++ "d65f03c0")

abbrev ccmnWImmSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 =
      if (if (s0.readReg32 .x0 != s0.readReg32 .x1) = true then
            s0.readReg32 .x2 + 3#32 != 0#32
          else true) = true
      then 0#64 else 1#64⌝

/-- `CCMN Wn, #imm` (`SepWP.step_ccmn_imm`, `w = .W32`). -/
theorem ccmn_w_imm_sym_ok (prog : Program) (h : ccmnWImmCode.holds prog) :
    prog.subroutineOk "ccmn_w_imm" ccmnWImmSpec := by
  wp_init g s0
  wp_sym_steps
  wp_done

theorem ccmn_w_imm_wp_ok (prog : Program) (h : ccmnWImmCode.holds prog) :
    prog.subroutineOk "ccmn_w_imm" ccmnWImmSpec := by
  wp_init g s0
  wp_steps
  wp_done

end EndToEnd

/-! ## Negative test -/

section Negative

set_option maxHeartbeats 200000
arm64_proof_prelude

/-- Claims the result is just `x2 == x3`, ignoring that `x0 = x1` forces `Z = 0`. -/
abbrev ccmpWrongSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf =>
    ⌜sf.readReg64 .x0 = if (s0.readReg64 .x2 != s0.readReg64 .x3) = true then 0#64 else 1#64⌝

/--
error: wp_done: postcondition value mismatch:
  actual:   if
    (if (s0.readReg64 (Reg.gpr 0#5) != s0.readReg64 (Reg.gpr 1#5)) = true then
        s0.readReg64 (Reg.gpr 2#5) != s0.readReg64 (Reg.gpr 3#5)
      else true) =
      true then
  0#64
else 1#64
  expected: if (s0.readReg64 (Reg.gpr 2#5) != s0.readReg64 (Reg.gpr 3#5)) = true then 0#64 else 1#64
-/
#guard_msgs (error) in
example (prog : Program) (h : ccmpXCode.holds prog) :
    prog.subroutineOk "ccmp_x" ccmpWrongSpec := by
  wp_init g s0
  wp_sym_steps
  wp_done

end Negative

/-! ## `HI` after a 64-bit `CMN` -/

section HiAfterCmn

/-- The `HI` condition after `CMN x, y` rewrites to "carry out and nonzero sum". -/
example (x y : BitVec 64) :
    ConditionHolds .HI (addsPState64 x y) = (BitVec.ult (x + y) x && (x + y != 0#64)) :=
  conditionHolds_hi_addsPState64 x y

/-- Typical use: the `cmn x, #4096; b.hi` errno check is not taken for a small return value. -/
example : ConditionHolds .HI (addsPState64 5#64 0x1000#64) = false := by
  rw [conditionHolds_hi_addsPState64]; decide

/-- The `cmn x, #4096; b.hi` check is taken for `-1` (carry out, nonzero sum). -/
example : ConditionHolds .HI (addsPState64 (-1#64) 0x1000#64) = true := by
  rw [conditionHolds_hi_addsPState64]; decide

end HiAfterCmn

end Testing.CondCompareSteps
