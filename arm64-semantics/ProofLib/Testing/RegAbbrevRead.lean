/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import ProofLib.VCGen
public meta import ProofLib.VCGen

/-!
# Regression Tests for Register Reads Across Abbreviation Writes

Tests that `evalRegKindPure?` and `evalRegKind?` classify `Reg.x<n>`, `Reg.lr`, `Reg.fp`, `Reg.sp`,
`Reg.xzr`, `Reg.fromZRBits`, and `Reg.fromSPBits` so that `reduceStateReadReg64`,
`reduceStateReadReg32`, and `reduceStateReadReg` walk symbolic register write chains without
blocking on ground abbreviations, while stopping at writes to non-ground registers.
-/

@[expose] public section

namespace Testing.RegAbbrevRead

open Arm64 ProofLib Lean

/-! ## Classifier -/

meta def classify (e : Expr) : Meta.MetaM (Option Reg × Option Reg) := do
  return (evalRegKindPure? e, ← evalRegKind? e)

/-- info: (some (Reg.gpr 8#5), some (Reg.gpr 8#5)) -/
#guard_msgs in
#eval classify (mkConst ``Reg.x8)

/-- info: (some (Reg.gpr 30#5), some (Reg.gpr 30#5)) -/
#guard_msgs in
#eval classify (mkConst ``Reg.lr)

/-- info: (some Reg.xzr, some Reg.xzr) -/
#guard_msgs in
#eval classify (mkConst ``Reg.xzr)

/-- info: (some Reg.sp, some Reg.sp) -/
#guard_msgs in
#eval classify (mkConst ``Reg.sp)

/-- info: (some (Reg.gpr 0#5), some (Reg.gpr 0#5)) -/
#guard_msgs in
#eval classify (mkConst ``Reg.x0)

/-! ## `State.readReg64` / `readReg32` / `readReg` across abbreviation writes -/

variable (s : State) (a b c : BitVec 64) (w : BitVec 32)

example : (State.writeReg64 s Reg.x8 a).readReg64 (.gpr 8#5) = a := by
  simp only [reduceStateReadReg64]

example : (((s.writeReg64 Reg.x8 a).writeReg64 Reg.x9 b).writeReg64
    Reg.x10 c).readReg64 Reg.x8 = a := by
  simp only [reduceStateReadReg64]

example : ((s.writeReg64 Reg.x8 a).writeReg32 Reg.x9 w).readReg64 Reg.x8 = a := by
  simp only [reduceStateReadReg64]

example : ((s.writeReg64 Reg.x8 a).writeReg64 Reg.xzr b).readReg64 Reg.x8 = a := by
  simp only [reduceStateReadReg64]

example : ((s.writeReg64 Reg.x3 a).writeReg64 Reg.sp b).readReg64
    Reg.x3 = a := by
  simp only [reduceStateReadReg64]

example : ((s.writeReg64 Reg.x8 a).writeReg64 Reg.x9 b).readReg64 (.gpr 7#5) =
    s.readReg64 (.gpr 7#5) := by
  simp only [reduceStateReadReg64]

example : ((s.writeReg32 Reg.x8 w).writeReg64 Reg.x9 b).readReg32
    Reg.x8 = (BitVec.zeroExtend 64 w).truncate 32 := by
  simp only [reduceStateReadReg32]

example : ((s.writeReg .W64 Reg.x8 a).writeReg .W32 Reg.x9 b).readReg .W64
    Reg.x8 = a := by
  simp only [reduceStateReadReg]

/-- A user-defined operand abbreviation, resolved by the `whnf` fallback of `evalRegKind?`. -/
abbrev ctxReg : Reg := .gpr 19#5

example : ((s.writeReg64 ctxReg a).writeReg64 Reg.x9 b).readReg64 (.gpr 19#5) = a := by
  simp only [reduceStateReadReg64]

/-- A user-defined `BitVec 5` abbreviation nested inside `Reg.gpr`,
    exercising the `whnf r` fallback. -/
abbrev innerRegIdx : BitVec 5 := 20#5

/-- info: (none, some (Reg.gpr 20#5)) -/
#guard_msgs in
#eval classify (mkApp (mkConst ``Reg.gpr) (mkConst ``innerRegIdx))

example : ((s.writeReg64 (Reg.gpr innerRegIdx) a).writeReg64
    Reg.x9 b).readReg64 (.gpr 20#5) = a := by
  simp only [reduceStateReadReg64]

/-- `State.readReg64` and `State.sp` across `Reg.x<n>` / `Reg.sp` writes and a
    large symbolic `State.setPC (pc + 0x100000#64)` offset (regression test against kernel
    structure-eta expansion on symbolic states). -/
example (pc : BitVec 64) :
    ((((s.writeReg64 Reg.x8 a).setPC (pc + 0x100000#64)).writeReg64
      Reg.sp b).writeReg64 Reg.x9 c).readReg64 Reg.x8 = a := by
  simp only [reduceStateReadReg64]

example (pc : BitVec 64) :
    ((((s.writeReg64 Reg.sp a).setPC (pc + 0x100000#64)).writeReg64
      Reg.x8 b).writeReg64 Reg.x9 c).sp = a := by
  simp only [reduceStateSP]

/-! ## Negative: a write to a non-ground register blocks the walk -/

/-- error: `simp` made no progress -/
#guard_msgs in
example (r : Reg) : ((s.writeReg64 Reg.x8 a).writeReg64 r b).readReg64 (.gpr 8#5) = a := by
  simp only [reduceStateReadReg64]

end Testing.RegAbbrevRead
