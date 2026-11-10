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
public import ProofLib.SepLogic.SymWP

/-!
# Regression Tests for 64-Bit and 32-Bit SIMD `LDR`/`STR`/`LDP`/`STP` Step Rules

Tests the D-register and S-register SIMD memory step rules (`SepWP.step_ldrSimd64`,
`SepWP.step_strSimd64`, `SepWP.step_ldrSimd32`, `SepWP.step_strSimd32`, `SepWP.step_ldpSimd64`,
`SepWP.step_stpSimd64`), their `classifyInsnStepRule` classification, end-to-end `wp_sym_steps`
and `wp_steps` proofs across offset, pre-index, and post-index addressing modes, and failure
reporting when a points-to cell is missing.
-/

@[expose] public section

namespace Testing.SimdScalarSteps

open Arm64 ProofLib

public meta section Classifier
open Lean Meta

/-- Decode `w` and return its `Instr` as an `Expr`. -/
def decodeWordExpr (w : BitVec 32) : MetaM Expr := do
  let r ← withTransparency .all (reduce (mkApp (mkConst ``Arm64.decode) (toExpr w)))
  if r.isAppOfArity ``Option.some 2 then
    return r.getArg! 1
  throwError "decodeWordExpr: failed to decode {w}"

/-- Verify `classifyInsnStepRule` on 64-bit/32-bit SIMD load/store forms, 128-bit `Q` forms,
    and unsupported `B8`/`H16` forms. -/
def testSimdScalarClassifier : MetaM Unit := do
  let check (label : String) (w : BitVec 32) (expected : SymInsnStepRule) : MetaM Unit := do
    let (rule, _) := classifyInsnStepRule (← decodeWordExpr w)
    unless rule == expected do
      throwError "classifyInsnStepRule [{label}]: got theorems {rule.theoremNames}, expected {expected.theoremNames}"
  check "STR D8, [SP, #-64]!"     0xfc1c0fe8#32 .strSimdDS
  check "LDR D8, [SP], #64"       0xfc4407e8#32 .ldrSimdDS
  check "LDR D0, [X23]"           0xfd4002e0#32 .ldrSimdDS
  check "STR D0, [X0, #8]"        0xfd000400#32 .strSimdDS
  check "LDR S1, [X23, #8]"       0xbd400ae1#32 .ldrSimdDS
  check "STR S1, [X0, #16]"       0xbd001001#32 .strSimdDS
  check "STP D9, D10, [SP, #16]"  0x6d012be9#32 .stpSimd64
  check "LDP D9, D10, [SP, #16]"  0x6d412be9#32 .ldpSimd64
  check "STP D8, D9, [SP, #-16]!" 0x6dbf27e8#32 .stpSimd64
  check "LDP D8, D9, [SP], #16"   0x6cc127e8#32 .ldpSimd64
  check "LDR Q0, [X1]"            0x3dc00020#32 .ldrSimd128
  check "LDR B0, [X1]"            0x3d400020#32 .otherMemOrSpecial
  check "LDR H0, [X1]"            0x7d400020#32 .otherMemOrSpecial

#eval testSimdScalarClassifier

end Classifier

section EndToEnd

set_option maxHeartbeats 400000
arm64_proof_prelude

/-- Fold restored low-64-bit lanes `V8..V10` back into the `calleeSavedVRegs` snapshot. -/
@[local simp, local arm64_norm, local wp_norm]
theorem truncate_read_v8 (s : State) : (s.readVReg128 8#5).truncate 64 = (calleeSavedVRegs s).1 := rfl
@[local simp, local arm64_norm, local wp_norm]
theorem truncate_read_v9 (s : State) : (s.readVReg128 9#5).truncate 64 = (calleeSavedVRegs s).2.1 := rfl
@[local simp, local arm64_norm, local wp_norm]
theorem truncate_read_v10 (s : State) :
    (s.readVReg128 10#5).truncate 64 = (calleeSavedVRegs s).2.2.1 := rfl

@[simp, arm64_norm] def simd_ds_addr : BitVec 64 := 0x40000#64

/-- Subroutine exercising offset, pre-index, and post-index forms of the D/S SIMD step rules. -/
def simdDsCode : FnCode :=
  .atAddr "simd_ds" simd_ds_addr
    ("fc1c0fe8 " ++ -- 0x40000: str d8, [sp, #-64]!
     "6d012be9 " ++ -- 0x40004: stp d9, d10, [sp, #16]
     "fd4002e0 " ++ -- 0x40008: ldr d0, [x23]
     "fd000400 " ++ -- 0x4000c: str d0, [x0, #8]
     "bd400ae1 " ++ -- 0x40010: ldr s1, [x23, #8]
     "bd001001 " ++ -- 0x40014: str s1, [x0, #16]
     "6d412be9 " ++ -- 0x40018: ldp d9, d10, [sp, #16]
     "fc4407e8 " ++ -- 0x4001c: ldr d8, [sp], #64
     "6dbf27e8 " ++ -- 0x40020: stp d8, d9, [sp, #-16]!
     "6cc127e8 " ++ -- 0x40024: ldp d8, d9, [sp], #16
     "d65f03c0")    -- 0x40028: ret

structure SimdDsGhost where
  p   : BitVec 64
  q   : BitVec 64
  f   : BitVec 64
  w   : BitVec 32
  o1  : BitVec 64
  o2  : BitVec 32
  s0  : BitVec 64
  s1  : BitVec 64
  s2  : BitVec 64
  s3  : BitVec 64
  s4  : BitVec 64

abbrev simdDsSpec : Spec SimdDsGhost where
  pre := fun g s0 =>
    ⌜s0.readReg64 .x0 = g.p ∧ s0.readReg64 .x23 = g.q⌝ ∗
    (g.q ↦₆₄ g.f) ∗ ((g.q + 8#64) ↦₃₂ g.w) ∗
    ((g.p + 8#64) ↦₆₄ g.o1) ∗ ((g.p + 16#64) ↦₃₂ g.o2) ∗
    ((s0.sp - 64#64) ↦₆₄ g.s0) ∗ ((s0.sp - 48#64) ↦₆₄ g.s1) ∗ ((s0.sp - 40#64) ↦₆₄ g.s2) ∗
    ((s0.sp - 16#64) ↦₆₄ g.s4) ∗ ((s0.sp - 8#64) ↦₆₄ g.s3)
  post := fun g s0 sf =>
    ⌜sf.sp = s0.sp ∧
     sf.readVReg128 0#5 = g.f.zeroExtend 128 ∧
     sf.readVReg128 1#5 = g.w.zeroExtend 128 ∧
     sf.readVReg128 8#5 = ((s0.readVReg128 8#5).extractLsb' 0 64).zeroExtend 128 ∧
     sf.readVReg128 9#5 = ((s0.readVReg128 9#5).extractLsb' 0 64).zeroExtend 128 ∧
     sf.readVReg128 10#5 = ((s0.readVReg128 10#5).extractLsb' 0 64).zeroExtend 128⌝ ∗
    (g.q ↦₆₄ g.f) ∗ ((g.q + 8#64) ↦₃₂ g.w) ∗
    ((g.p + 8#64) ↦₆₄ g.f) ∗ ((g.p + 16#64) ↦₃₂ g.w) ∗
    ((s0.sp - 64#64) ↦₆₄ (s0.readVReg128 8#5).extractLsb' 0 64) ∗
    ((s0.sp - 48#64) ↦₆₄ (s0.readVReg128 9#5).extractLsb' 0 64) ∗
    ((s0.sp - 40#64) ↦₆₄ (s0.readVReg128 10#5).extractLsb' 0 64) ∗
    ((s0.sp - 16#64) ↦₆₄ (s0.readVReg128 8#5).extractLsb' 0 64) ∗
    ((s0.sp - 8#64) ↦₆₄ (s0.readVReg128 9#5).extractLsb' 0 64)

theorem simd_ds_sym_ok (prog : Program) (h_code : simdDsCode.holds prog) :
    prog.subroutineOk "simd_ds" simdDsSpec := by
  wp_init g s0
  wp_sym_steps
  wp_done

theorem simd_ds_wp_ok (prog : Program) (h_code : simdDsCode.holds prog) :
    prog.subroutineOk "simd_ds" simdDsSpec := by
  wp_init g s0
  wp_steps
  wp_done

end EndToEnd

section Negative

set_option maxHeartbeats 200000
arm64_proof_prelude

def simdLdrOnlyCode : FnCode :=
  .atAddr "simd_ldr_only" simd_ds_addr
    ("fd4002e0 " ++ -- 0x40000: ldr d0, [x23]
     "d65f03c0")    -- 0x40004: ret

/-- Specification omitting the `x23 ↦₆₄ _` cell so `SepWP.step_ldrSimd64` fails. -/
abbrev simdLdrMissingSpec : Spec (BitVec 64) where
  pre := fun q s0 => ⌜s0.readReg64 .x23 = q⌝
  post := fun _ _ _ => emp

/--
error: wp_step: no step rule succeeded for instruction `Instr.ldrSimd SimdMemSize.D64 (0#5)
  (AddrMode.Offset (Reg.gpr 23#5)
    0#64)` (full: `Instr.ldrSimd SimdMemSize.D64 (0#5)
  (AddrMode.Offset (Reg.gpr 23#5) 0#64)`) at PC `prog.fnAddr "simd_ldr_only"`
spatial context points-to atoms: (none)
(detail: wp_sep_access: no cell at q in
  emp)
-/
#guard_msgs (error) in
example (prog : Program) (h_code : simdLdrOnlyCode.holds prog) :
    prog.subroutineOk "simd_ldr_only" simdLdrMissingSpec := by
  wp_init q s0
  wp_step

end Negative

end Testing.SimdScalarSteps
