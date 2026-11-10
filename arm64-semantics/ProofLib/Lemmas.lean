/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public meta import Arm64.Trusted.ISA.Syntax
public import Std.Tactic.BVDecide
public import Arm64
public import ProofLib.CoreLemmas
public import ProofLib.SyscallModels
public import ProofLib.SimpAttrs
import Arm64.Trusted.Spec.SepLogic

/-!
# ARM64 Normalization and Algebraic Simplification Lemmas

Registers literal-reduction simprocs and `@[arm64_norm]` / `@[wp_norm]` rewrite rules for
`Arm64.execInst`, condition flags, bitvector arithmetic, register files, memory accesses,
SIMD lane operations, calling-convention preservation, and Linux AArch64 syscall transitions.
-/

namespace ProofLib

open Arm64

public meta section

/-- Register `builtin_simproc` / `builtin_dsimproc` declarations (from `Lean.Meta.Tactic.Simp.BuiltinSimprocs`)
    into custom `register_simp_attr` sets inside a `module`.
    In Lean 4.34, `builtin_simproc_decl` / `builtin_dsimproc_decl` expand to plain `def` (so core
    simprocs are compiled into `libleanshared` and not marked `meta`), whereas `addSimprocAttr`
    checks `ensureAttrDeclIsMeta` (`isMarkedMeta`) without exempting `isBuiltinSimproc`. This command
    verifies `isBuiltinSimproc` and registers the entry via `addSimprocAttrCore`. -/
scoped elab "attribute_builtin_simproc " "[" attrs:ident,* "]" ids:(ppSpace ident)+ : command =>
  Lean.Elab.Command.liftCoreM do
    let decls ← ids.mapM fun id => Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
    for declName in decls do
      unless ← Lean.Meta.Simp.isBuiltinSimproc declName do
        throwError "`{.ofConstName declName}` is not a `builtin_simproc`; use `attribute` instead"
    for attrId in attrs.getElems do
      let attrName := attrId.getId
      let some ext ← Lean.Meta.Simp.getSimprocExtension? attrName
        | throwError "unknown simproc extension `{attrName}`"
      for declName in decls do
        Lean.Meta.Simp.addSimprocAttrCore ext declName .global (post := true)

attribute_builtin_simproc [arm64_norm, wp_norm]
  Nat.reduceSucc Nat.reduceAdd Nat.reduceSub Nat.reduceMul Nat.reduceDiv Nat.reduceMod Nat.reducePow
  Nat.reduceAnd Nat.reduceXor Nat.reduceOr
  Nat.reduceShiftLeft Nat.reduceShiftRight
  Nat.reduceBEq Nat.reduceBNe Nat.reduceEqDiff Nat.reduceBeqDiff Nat.reduceBneDiff
  Nat.reduceLT Nat.reduceGT Nat.reduceLeDiff Nat.reduceSubDiff Nat.reduceDvd
  BitVec.reduceNot
  BitVec.reduceAnd
  BitVec.reduceOr
  BitVec.reduceXOr
  BitVec.reduceShiftLeft
  BitVec.reduceUShiftRight
  BitVec.reduceSShiftRight
  BitVec.reduceHShiftLeft
  BitVec.reduceHShiftLeft'
  BitVec.reduceHShiftRight
  BitVec.reduceHShiftRight'
  BitVec.reduceShiftLeftShiftLeft
  BitVec.reduceShiftRightShiftRight
  BitVec.reduceShiftLeftZeroExtend
  BitVec.reduceRotateLeft
  BitVec.reduceRotateRight
  BitVec.reduceSetWidth
  BitVec.reduceSetWidth'
  BitVec.reduceZeroExtend
  BitVec.reduceSignExtend
  BitVec.reduceExtractLsb
  BitVec.reduceExtractLsb'
  BitVec.reduceAppend
  BitVec.reduceCast
  BitVec.reduceMul
  BitVec.reduceSub
  BitVec.reduceAdd
  BitVec.reduceOfNat
  BitVec.reduceOfInt
  BitVec.reduceToNat
  BitVec.reduceToInt
  BitVec.reduceBitVecOfFin
  BitVec.reduceBitVecToFin
  BitVec.reduceDiv
  BitVec.reduceUDiv
  BitVec.reduceSDiv
  BitVec.reduceMod
  BitVec.reduceUMod
  BitVec.reduceSMod
  BitVec.reduceSRem
  BitVec.reduceAllOnes
  BitVec.reduceGetLsb
  BitVec.reduceGetMsb
  BitVec.reduceGetElem
  BitVec.reduceBEq
  BitVec.reduceBNe
  BitVec.reduceEq
  BitVec.reduceNe
  BitVec.reduceULT
  BitVec.reduceULE
  BitVec.reduceSLT
  BitVec.reduceSLE
  BitVec.reduceLT
  BitVec.reduceLE
  BitVec.reduceGT
  BitVec.reduceGE
  BitVec.reduceClz
  BitVec.reduceCpop
  BitVec.reduceAbs
  BitVec.reduceReplicate

/-- Reduce `-x` on concrete `BitVec` literals, except for 64-bit small negative offsets `-(k#64)`
    (`0 < k ≤ 2^32`) produced by `cleanReducedExpr` so `bitvec_add_neg_eq_sub` (`base + (-k) = base - k`)
    can rewrite them into subtraction. -/
dsimproc [arm64_norm, wp_norm] reduceBitVecNeg ((- _ : BitVec _)) := fun e => do
  unless e.isAppOfArity ``Neg.neg 3 do return .continue
  let some ⟨w, bv⟩ ← Lean.Meta.getBitVecValue? e.appArg! | return .continue
  if w == 64 && 0 < bv.toNat && bv.toNat <= (1 <<< 32) then
    return .continue
  return .done (Lean.toExpr (-bv))

/-- Reduce `BitVec.truncate n x` on concrete `BitVec` literals `x` and `Nat` widths `n`.
    (`BitVec.truncate` is a `def`, so `BitVec.reduceSetWidth` does not match its head symbol.) -/
dsimproc [arm64_norm, wp_norm] reduceBitVecTruncate (BitVec.truncate _ _) := fun e => do
  let_expr BitVec.truncate _ v x := e | return .continue
  let some n ← Lean.Nat.fromExpr? v | return .continue
  let some ⟨_, bv⟩ ← Lean.Meta.getBitVecValue? x | return .continue
  return .done (Lean.toExpr (bv.truncate n))

dsimproc [arm64_norm, wp_norm] reduceBitVecMsb (BitVec.msb _) := fun e => do
  let_expr BitVec.msb _ x := e | return .continue
  let some ⟨_, bv⟩ ← Lean.Meta.getBitVecValue? x | return .continue
  return .done (Lean.toExpr bv.msb)

dsimproc [arm64_norm, wp_norm] reduceBitVecSShiftRight' (BitVec.sshiftRight' _ _) := fun e => do
  let_expr BitVec.sshiftRight' _ _ a s := e | return .continue
  let some ⟨_, bvA⟩ ← Lean.Meta.getBitVecValue? a | return .continue
  let some ⟨_, bvS⟩ ← Lean.Meta.getBitVecValue? s | return .continue
  return .done (Lean.toExpr (bvA.sshiftRight' bvS))

dsimproc [arm64_norm, wp_norm] reduceBitVecTwoPow (BitVec.twoPow _ _) := fun e => do
  let_expr BitVec.twoPow w i := e | return .continue
  let some wn ← Lean.Nat.fromExpr? w | return .continue
  let some inat ← Lean.Nat.fromExpr? i | return .continue
  return .done (Lean.toExpr (BitVec.twoPow wn inat))

dsimproc [arm64_norm, wp_norm] reduceBitVecOfBool (BitVec.ofBool _) := fun e => do
  let_expr BitVec.ofBool b := e | return .continue
  if b.isConstOf ``Bool.true then return .done (Lean.toExpr (1#1))
  if b.isConstOf ``Bool.false then return .done (Lean.toExpr (0#1))
  return .continue

end

@[expose] public section

@[simp, arm64_norm]
theorem State.readReg_w32 (s : State) (r : Reg) :
    s.readReg .W32 r = (s.readReg32 r).zeroExtend 64 :=
  State.readReg.eq_1 s r

@[simp, arm64_norm]
theorem State.readReg_w64 (s : State) (r : Reg) :
    s.readReg .W64 r = s.readReg64 r :=
  State.readReg.eq_2 s r

@[simp, arm64_norm]
theorem State.writeReg_w32 (s : State) (r : Reg) (val : BitVec 64) :
    s.writeReg .W32 r val = s.writeReg64 r ((val.truncate 32).zeroExtend 64) :=
  State.writeReg.eq_1 s r val

@[simp, arm64_norm]
theorem State.writeReg_w64 (s : State) (r : Reg) (val : BitVec 64) :
    s.writeReg .W64 r val = s.writeReg64 r val :=
  State.writeReg.eq_2 s r val

attribute [arm64_norm]
  Arm64.StackPreserved.refl_iff
  Arm64.CalleeSavedPreserved.rfl
  Arm64.CallingConventionPreserved.rfl
  eq_self
  beq_self_eq_true
  bne_self_eq_false
  Bool.bne_false Bool.bne_true
  ite_true ite_false dite_true dite_false
  decide_true decide_false
  true_and false_and and_true and_false
  true_or false_or or_true or_false
  not_true not_false_eq_true
  Bool.true_and Bool.false_and Bool.and_true Bool.and_false
  Bool.true_or Bool.false_or Bool.or_true Bool.or_false
  Bool.not_true Bool.not_false
  State.readReg32.eq_1
  State.writeReg32.eq_1
  State.readReg64_xzr
  State.readReg64_sp
  State.writeReg64_xzr
  State.readReg32_xzr
  State.writeReg32_xzr
  State.pc_writeReg64
  State.pc_writeReg32
  State.pc_writeReg
  State.pstate_writeReg64
  State.pstate_writeReg32
  State.pstate_writeReg
  State.mem_writeReg64
  State.mem_writeReg32
  State.mem_writeReg
  State.status_writeReg64
  State.status_writeReg32
  State.status_writeReg
  State.sp_writeReg64_gpr
  State.spAligned.eq_1
  State.readReg64_advancePC
  State.readReg64_setPC
  State.readReg64_setPState
  State.readReg64_setMem
  State.readReg64_writeReg64
  Reg.fromZRBits
  Reg.fromSPBits
  Reg.x0 Reg.x1 Reg.x2 Reg.x3 Reg.x4 Reg.x5 Reg.x6 Reg.x7
  Reg.x8 Reg.x9 Reg.x10 Reg.x11 Reg.x12 Reg.x13 Reg.x14 Reg.x15
  Reg.x16 Reg.x17 Reg.x18 Reg.x19 Reg.x20 Reg.x21 Reg.x22 Reg.x23
  Reg.x24 Reg.x25 Reg.x26 Reg.x27 Reg.x28 Reg.x29 Reg.x30
  Reg.fp Reg.lr
  PState.zero
  PState.ofBits4
  PState.toBits4
  CondCode.ofBits
  ShiftType.ofBits
  ExtendType.ofBits
  Memory.readSized
  Memory.writeSized
  Memory.read128
  Memory.write128
  Memory.readSimdSized
  Memory.writeSimdSized
  Memory.read8_write8
  Memory.read8_write8_same
  Memory.readBytes_zero
  Memory.readBytes_succ
  Memory.readBytes_length
  Memory.read16_write16_same
  Memory.read32_write32_same
  Memory.read64_write64_same
  Memory.read8_write16_same
  Memory.read8_write32_same
  Memory.read8_write64_same
  Memory.read16_write32_same
  Memory.read16_write64_same
  Memory.read32_write64_same
  Memory.read64_write64_base_zero_add8
  Memory.read64_write64_base_add8_zero
  Memory.add_eq_add_left
  Memory.add_eq_self_left
  Memory.self_eq_add_left
  OutputStream.ofFd
  TraceEvent.ofBytes
  TraceEvent.stdout
  TraceEvent.stderr
  List.map
  List.append_assoc
  List.nil_append
  List.append_nil
  List.filterMap_append
  List.filterMap_cons
  List.filterMap_nil
  shift32
  shift64
  shiftVal
  extendVal
  evalLogical
  evalBitfield
  evalAddrMode
  AddrMode.baseReg
  checkRegSPAligned
  checkAddrSPAligned
  MemWidth.isAligned
  State.readVReg64.eq_1
  State.writeVReg64.eq_1
  State.readVReg32.eq_1
  State.writeVReg32.eq_1
  getSimdLane
  Option.isSome
  execAddSubImm
  execAddSubExt
  execAddSubShift
  execAddSubCarry
  execLogicalImm
  execLogicalShift
  execMoveWide
  execBitfield
  execCondSelect
  execCondCompare
  execDataProc1
  execDataProc2
  execDataProc3
  execLdr
  execLdrLit
  execStr
  execLdp
  execStp

@[simp, arm64_norm]
theorem BitVec_allOnes_64 : BitVec.allOnes 64 = 0xffffffffffffffff#64 := rfl

@[simp, arm64_norm]
theorem BitVec_allOnes_32 : BitVec.allOnes 32 = 0xffffffff#32 := rfl

@[simp, arm64_norm]
theorem State.pc_advancePC (s : State) : s.advancePC.pc = s.pc + 4#64 := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.pc_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).pc = pc := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.pstate_setPState (s : State) (ps : PState) : (s.setPState ps).pstate = ps := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.sp_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).sp = if r = .sp then v else s.sp := by
  cases s; cases r <;> rfl

@[simp, arm64_norm]
theorem State.sp_advancePC (s : State) : s.advancePC.sp = s.sp := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.sp_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).sp = s.sp := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.sp_setPState (s : State) (ps : PState) : (s.setPState ps).sp = s.sp := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.sp_setMem (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.mem_advancePC (s : State) : s.advancePC.mem = s.mem := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.mem_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).mem = s.mem := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.mem_setPState (s : State) (ps : PState) : (s.setPState ps).mem = s.mem := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.pstate_advancePC (s : State) : s.advancePC.pstate = s.pstate := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.pstate_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).pstate = s.pstate := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.pstate_setMem (s : State) (m : Memory) : (s.setMem m).pstate = s.pstate := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.status_advancePC (s : State) : s.advancePC.status = s.status := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.status_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).status = s.status := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.status_setPState (s : State) (ps : PState) : (s.setPState ps).status = s.status := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.status_setMem (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.pc_setPState (s : State) (ps : PState) : (s.setPState ps).pc = s.pc := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.pc_setMem (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl

/-! ## Relational Condition-Flag Lemmas -/

private theorem not_ule_eq_ult_64 (x y : BitVec 64) : (!BitVec.ule y x) = BitVec.ult x y := by
  bv_decide

private theorem not_ult_eq_ule_64 (x y : BitVec 64) : (!BitVec.ult y x) = BitVec.ule x y := by
  bv_decide

private theorem not_ule_eq_ult_32 (x y : BitVec 32) : (!BitVec.ule y x) = BitVec.ult x y := by
  bv_decide

private theorem not_ult_eq_ule_32 (x y : BitVec 32) : (!BitVec.ult y x) = BitVec.ule x y := by
  bv_decide

private theorem ule_and_not_beq_eq_ult_64 (x y : BitVec 64) :
    (BitVec.ule y x && !(x == y)) = BitVec.ult y x := by
  rw [Bool.eq_iff_iff]; simp [BitVec.ule, BitVec.ult, ← BitVec.toNat_inj]; omega

private theorem not_sle_eq_slt_64 (x y : BitVec 64) : (!BitVec.sle y x) = BitVec.slt x y := by
  rw [Bool.eq_iff_iff]; simp [BitVec.sle, BitVec.slt]

private theorem not_beq_and_sle_eq_slt_64 (x y : BitVec 64) :
    (!(x == y) && BitVec.sle y x) = BitVec.slt y x := by
  rw [Bool.eq_iff_iff]; simp [BitVec.sle, BitVec.slt, ← BitVec.toInt_inj]; omega

private theorem not_slt_eq_sle_64 (x y : BitVec 64) : (!BitVec.slt y x) = BitVec.sle x y := by
  rw [Bool.eq_iff_iff]; simp [BitVec.sle, BitVec.slt]

private theorem ule_and_not_beq_eq_ult_32 (x y : BitVec 32) :
    (BitVec.ule y x && !(x == y)) = BitVec.ult y x := by
  rw [Bool.eq_iff_iff]; simp [BitVec.ule, BitVec.ult, ← BitVec.toNat_inj]; omega

private theorem not_sle_eq_slt_32 (x y : BitVec 32) : (!BitVec.sle y x) = BitVec.slt x y := by
  rw [Bool.eq_iff_iff]; simp [BitVec.sle, BitVec.slt]

private theorem not_beq_and_sle_eq_slt_32 (x y : BitVec 32) :
    (!(x == y) && BitVec.sle y x) = BitVec.slt y x := by
  rw [Bool.eq_iff_iff]; simp [BitVec.sle, BitVec.slt, ← BitVec.toInt_inj]; omega

private theorem not_slt_eq_sle_32 (x y : BitVec 32) : (!BitVec.slt y x) = BitVec.sle x y := by
  rw [Bool.eq_iff_iff]; simp [BitVec.sle, BitVec.slt]

@[simp, arm64_norm]
theorem conditionHolds_eq_subs64 (x y : BitVec 64) :
    ConditionHolds .EQ (AddWithCarry64 x (~~~y) true).2 = (x == y) := by
  dsimp only [ConditionHolds, AddWithCarry64]; bv_bits

@[simp, arm64_norm]
theorem conditionHolds_ne_subs64 (x y : BitVec 64) :
    ConditionHolds .NE (AddWithCarry64 x (~~~y) true).2 = (x != y) :=
  congrArg not (conditionHolds_eq_subs64 x y)

@[simp, arm64_norm]
theorem conditionHolds_cs_subs64 (x y : BitVec 64) :
    ConditionHolds .CS (AddWithCarry64 x (~~~y) true).2 = BitVec.ule y x := by
  dsimp only [ConditionHolds, AddWithCarry64]; bv_bits

@[simp, arm64_norm]
theorem conditionHolds_cc_subs64 (x y : BitVec 64) :
    ConditionHolds .CC (AddWithCarry64 x (~~~y) true).2 = BitVec.ult x y := by
  show (!ConditionHolds .CS (AddWithCarry64 x (~~~y) true).2) = BitVec.ult x y
  rw [conditionHolds_cs_subs64, not_ule_eq_ult_64]

@[simp, arm64_norm]
theorem conditionHolds_hi_subs64 (x y : BitVec 64) :
    ConditionHolds .HI (AddWithCarry64 x (~~~y) true).2 = BitVec.ult y x := by
  show (ConditionHolds .CS (AddWithCarry64 x (~~~y) true).2 &&
    !ConditionHolds .EQ (AddWithCarry64 x (~~~y) true).2) = BitVec.ult y x
  rw [conditionHolds_cs_subs64, conditionHolds_eq_subs64, ule_and_not_beq_eq_ult_64]

@[simp, arm64_norm]
theorem conditionHolds_ls_subs64 (x y : BitVec 64) :
    ConditionHolds .LS (AddWithCarry64 x (~~~y) true).2 = BitVec.ule x y := by
  show (!ConditionHolds .HI (AddWithCarry64 x (~~~y) true).2) = BitVec.ule x y
  rw [conditionHolds_hi_subs64, not_ult_eq_ule_64]

@[simp, arm64_norm]
theorem conditionHolds_ge_subs64 (x y : BitVec 64) :
    ConditionHolds .GE (AddWithCarry64 x (~~~y) true).2 = BitVec.sle y x := by
  dsimp only [ConditionHolds, AddWithCarry64]
  have key : ∀ a b : Bool, (a == (b != a)) = !b := by decide
  rw [key, Bool.eq_iff_iff]
  have hxl := x.isLt; have hyl := y.isLt
  by_cases hx : 9223372036854775808 ≤ x.toNat <;> by_cases hy : 9223372036854775808 ≤ y.toNat <;>
  simp [BitVec.sle, BitVec.toInt_eq_toNat_cond, BitVec.msb_eq_decide, BitVec.toNat_signExtend,
    BitVec.toNat_add, BitVec.toNat_not, hx, hy] <;>
  (repeat' split) <;> omega

@[simp, arm64_norm]
theorem conditionHolds_lt_subs64 (x y : BitVec 64) :
    ConditionHolds .LT (AddWithCarry64 x (~~~y) true).2 = BitVec.slt x y := by
  show (!ConditionHolds .GE (AddWithCarry64 x (~~~y) true).2) = BitVec.slt x y
  rw [conditionHolds_ge_subs64, not_sle_eq_slt_64]

@[simp, arm64_norm]
theorem conditionHolds_gt_subs64 (x y : BitVec 64) :
    ConditionHolds .GT (AddWithCarry64 x (~~~y) true).2 = BitVec.slt y x := by
  show (!ConditionHolds .EQ (AddWithCarry64 x (~~~y) true).2 &&
    ConditionHolds .GE (AddWithCarry64 x (~~~y) true).2) = BitVec.slt y x
  rw [conditionHolds_eq_subs64, conditionHolds_ge_subs64, not_beq_and_sle_eq_slt_64]

@[simp, arm64_norm]
theorem conditionHolds_le_subs64 (x y : BitVec 64) :
    ConditionHolds .LE (AddWithCarry64 x (~~~y) true).2 = BitVec.sle x y := by
  show (!ConditionHolds .GT (AddWithCarry64 x (~~~y) true).2) = BitVec.sle x y
  rw [conditionHolds_gt_subs64, not_slt_eq_sle_64]

@[simp, arm64_norm]
theorem addWithCarry64_sub_fst (x y : BitVec 64) :
    (AddWithCarry64 x (~~~y) true).1 = x - y := by
  dsimp only [AddWithCarry64]; bv_bits

@[simp, arm64_norm]
theorem addWithCarry64_add_fst (x y : BitVec 64) :
    (AddWithCarry64 x y false).1 = x + y := by
  dsimp only [AddWithCarry64]; bv_decide

@[simp, arm64_norm]
theorem addWithCarry32_sub_fst (x y : BitVec 32) :
    (AddWithCarry32 x (~~~y) true).1 = x - y := by
  dsimp only [AddWithCarry32]; bv_bits

@[simp, arm64_norm]
theorem addWithCarry32_add_fst (x y : BitVec 32) :
    (AddWithCarry32 x y false).1 = x + y := by
  dsimp only [AddWithCarry32]; bv_decide

/-- Flag state produced by 64-bit `SUBS` (`CMP`). Keeping `x` and `y` un-inverted prevents
    `simp (config := { decide := true })` from reducing `~~~0#64` before `ConditionHolds` rewrites fire. -/
def subsPState64 (x y : BitVec 64) : PState := (AddWithCarry64 x (~~~y) true).2

/-- Flag state produced by 64-bit `ADDS` (`CMN`). -/
def addsPState64 (x y : BitVec 64) : PState := (AddWithCarry64 x y false).2

@[simp, arm64_norm]
theorem evalAddSub_w64_add (x y : BitVec 64) :
    evalAddSub .W64 .ADD x y none = (x + y, none) := by
  simp only [evalAddSub, Bool.false_eq_true, ↓reduceIte, addWithCarry64_add_fst]

@[simp, arm64_norm]
theorem evalAddSub_w64_adds (x y : BitVec 64) :
    evalAddSub .W64 .ADDS x y none = (x + y, some (addsPState64 x y)) := by
  simp only [evalAddSub, Bool.false_eq_true, ↓reduceIte, addsPState64, addWithCarry64_add_fst]

@[simp, arm64_norm]
theorem evalAddSub_w64_sub (x y : BitVec 64) :
    evalAddSub .W64 .SUB x y none = (x - y, none) := by
  simp only [evalAddSub, Bool.false_eq_true, ↓reduceIte, addWithCarry64_sub_fst]

@[simp, arm64_norm]
theorem evalAddSub_w64_subs (x y : BitVec 64) :
    evalAddSub .W64 .SUBS x y none = (x - y, some (subsPState64 x y)) := by
  simp only [evalAddSub, ↓reduceIte, subsPState64, addWithCarry64_sub_fst]

@[simp, arm64_norm]
theorem evalAddSub_w64_sub_zero (x : BitVec 64) :
    evalAddSub .W64 .SUB x 0#64 none = (x, none) := by
  rw [evalAddSub_w64_sub, BitVec.sub_zero]

@[simp, arm64_norm]
theorem evalAddSub_w64_subs_zero (x : BitVec 64) :
    evalAddSub .W64 .SUBS x 0#64 none = (x, some (subsPState64 x 0#64)) := by
  rw [evalAddSub_w64_subs, BitVec.sub_zero]

@[simp, arm64_norm]
theorem addWithCarry64_adc_fst (x y : BitVec 64) (c : Bool) :
    (AddWithCarry64 x y c).1 = x + y + (if c then 1#64 else 0#64) := by
  cases c <;> (dsimp only [AddWithCarry64]; bv_decide)

@[simp, arm64_norm]
theorem addWithCarry64_sbc_fst (x y : BitVec 64) (c : Bool) :
    (AddWithCarry64 x (~~~y) c).1 = x - y - (if c then 0#64 else 1#64) := by
  cases c <;> (simp only [AddWithCarry64, Bool.false_eq_true, ite_false, ite_true]; bv_bits)

@[simp, arm64_norm]
theorem evalAddSub_w64_adc (x y : BitVec 64) (c : Bool) :
    evalAddSub .W64 .ADD x y (some c) = (x + y + (if c then 1#64 else 0#64), none) := by
  simp only [evalAddSub, Bool.false_eq_true, ↓reduceIte, addWithCarry64_adc_fst]

@[simp, arm64_norm]
theorem evalAddSub_w64_adcs (x y : BitVec 64) (c : Bool) :
    evalAddSub .W64 .ADDS x y (some c) = (x + y + (if c then 1#64 else 0#64), some (AddWithCarry64 x y c).2) := by
  simp only [evalAddSub, Bool.false_eq_true, ↓reduceIte, addWithCarry64_adc_fst]

@[simp, arm64_norm]
theorem evalAddSub_w64_sbc (x y : BitVec 64) (c : Bool) :
    evalAddSub .W64 .SUB x y (some c) = (x - y - (if c then 0#64 else 1#64), none) := by
  simp only [evalAddSub, Bool.false_eq_true, ↓reduceIte, addWithCarry64_sbc_fst]

@[simp, arm64_norm]
theorem evalAddSub_w64_sbcs (x y : BitVec 64) (c : Bool) :
    evalAddSub .W64 .SUBS x y (some c) = (x - y - (if c then 0#64 else 1#64), some (AddWithCarry64 x (~~~y) c).2) := by
  simp only [evalAddSub, ↓reduceIte, addWithCarry64_sbc_fst]

@[simp, arm64_norm]
theorem evalAddSub_w32_add (x y : BitVec 64) :
    evalAddSub .W32 .ADD x y none = (((x.truncate 32) + (y.truncate 32)).zeroExtend 64, none) := by
  simp only [evalAddSub, Bool.false_eq_true, ↓reduceIte, addWithCarry32_add_fst]

@[simp, arm64_norm]
theorem evalAddSub_w32_sub (x y : BitVec 64) :
    evalAddSub .W32 .SUB x y none = (((x.truncate 32) - (y.truncate 32)).zeroExtend 64, none) := by
  simp only [evalAddSub, Bool.false_eq_true, ↓reduceIte, addWithCarry32_sub_fst]

/-- Flag state produced by 32-bit `SUBS` (`CMP` on `W` registers). As with `subsPState64`,
    `x` and `y` are kept un-inverted so that `ConditionHolds` rewrites can fire. -/
def subsPState32 (x y : BitVec 32) : PState := (AddWithCarry32 x (~~~y) true).2

/-- Flag state produced by 32-bit `ADDS` (`CMN` on `W` registers). -/
def addsPState32 (x y : BitVec 32) : PState := (AddWithCarry32 x y false).2

@[simp, arm64_norm]
theorem evalAddSub_w32_subs (x y : BitVec 64) :
    evalAddSub .W32 .SUBS x y none =
      (((x.truncate 32) - (y.truncate 32)).zeroExtend 64,
        some (subsPState32 (x.truncate 32) (y.truncate 32))) := by
  simp only [evalAddSub, ↓reduceIte, subsPState32, addWithCarry32_sub_fst]

@[simp, arm64_norm]
theorem evalAddSub_w32_adds (x y : BitVec 64) :
    evalAddSub .W32 .ADDS x y none =
      (((x.truncate 32) + (y.truncate 32)).zeroExtend 64,
        some (addsPState32 (x.truncate 32) (y.truncate 32))) := by
  simp only [evalAddSub, Bool.false_eq_true, ↓reduceIte, addsPState32, addWithCarry32_add_fst]

@[simp, arm64_norm]
theorem conditionHolds_eq_subs32 (x y : BitVec 32) :
    ConditionHolds .EQ (AddWithCarry32 x (~~~y) true).2 = (x == y) := by
  dsimp only [ConditionHolds, AddWithCarry32]; bv_bits

@[simp, arm64_norm]
theorem conditionHolds_ne_subs32 (x y : BitVec 32) :
    ConditionHolds .NE (AddWithCarry32 x (~~~y) true).2 = (x != y) :=
  congrArg not (conditionHolds_eq_subs32 x y)

@[simp, arm64_norm]
theorem conditionHolds_cs_subs32 (x y : BitVec 32) :
    ConditionHolds .CS (AddWithCarry32 x (~~~y) true).2 = BitVec.ule y x := by
  dsimp only [ConditionHolds, AddWithCarry32]; bv_bits

@[simp, arm64_norm]
theorem conditionHolds_cc_subs32 (x y : BitVec 32) :
    ConditionHolds .CC (AddWithCarry32 x (~~~y) true).2 = BitVec.ult x y := by
  show (!ConditionHolds .CS (AddWithCarry32 x (~~~y) true).2) = BitVec.ult x y
  rw [conditionHolds_cs_subs32, not_ule_eq_ult_32]

@[simp, arm64_norm]
theorem conditionHolds_hi_subs32 (x y : BitVec 32) :
    ConditionHolds .HI (AddWithCarry32 x (~~~y) true).2 = BitVec.ult y x := by
  show (ConditionHolds .CS (AddWithCarry32 x (~~~y) true).2 &&
    !ConditionHolds .EQ (AddWithCarry32 x (~~~y) true).2) = BitVec.ult y x
  rw [conditionHolds_cs_subs32, conditionHolds_eq_subs32, ule_and_not_beq_eq_ult_32]

@[simp, arm64_norm]
theorem conditionHolds_ls_subs32 (x y : BitVec 32) :
    ConditionHolds .LS (AddWithCarry32 x (~~~y) true).2 = BitVec.ule x y := by
  show (!ConditionHolds .HI (AddWithCarry32 x (~~~y) true).2) = BitVec.ule x y
  rw [conditionHolds_hi_subs32, not_ult_eq_ule_32]

@[simp, arm64_norm]
theorem conditionHolds_ge_subs32 (x y : BitVec 32) :
    ConditionHolds .GE (AddWithCarry32 x (~~~y) true).2 = BitVec.sle y x := by
  dsimp only [ConditionHolds, AddWithCarry32]
  have key : ∀ a b : Bool, (a == (b != a)) = !b := by decide
  rw [key, Bool.eq_iff_iff]
  have hxl := x.isLt; have hyl := y.isLt
  by_cases hx : 2147483648 ≤ x.toNat <;> by_cases hy : 2147483648 ≤ y.toNat <;>
  simp [BitVec.sle, BitVec.toInt_eq_toNat_cond, BitVec.msb_eq_decide, BitVec.toNat_signExtend,
    BitVec.toNat_add, BitVec.toNat_not, hx, hy] <;>
  (repeat' split) <;> omega

@[simp, arm64_norm]
theorem conditionHolds_lt_subs32 (x y : BitVec 32) :
    ConditionHolds .LT (AddWithCarry32 x (~~~y) true).2 = BitVec.slt x y := by
  show (!ConditionHolds .GE (AddWithCarry32 x (~~~y) true).2) = BitVec.slt x y
  rw [conditionHolds_ge_subs32, not_sle_eq_slt_32]

@[simp, arm64_norm]
theorem conditionHolds_gt_subs32 (x y : BitVec 32) :
    ConditionHolds .GT (AddWithCarry32 x (~~~y) true).2 = BitVec.slt y x := by
  show (!ConditionHolds .EQ (AddWithCarry32 x (~~~y) true).2 &&
    ConditionHolds .GE (AddWithCarry32 x (~~~y) true).2) = BitVec.slt y x
  rw [conditionHolds_eq_subs32, conditionHolds_ge_subs32, not_beq_and_sle_eq_slt_32]

@[simp, arm64_norm]
theorem conditionHolds_le_subs32 (x y : BitVec 32) :
    ConditionHolds .LE (AddWithCarry32 x (~~~y) true).2 = BitVec.sle x y := by
  show (!ConditionHolds .GT (AddWithCarry32 x (~~~y) true).2) = BitVec.sle x y
  rw [conditionHolds_gt_subs32, not_slt_eq_sle_32]

@[simp, arm64_norm]
theorem conditionHolds_eq_subsPState32 (x y : BitVec 32) :
    ConditionHolds .EQ (subsPState32 x y) = (x == y) :=
  conditionHolds_eq_subs32 x y

@[simp, arm64_norm]
theorem conditionHolds_ne_subsPState32 (x y : BitVec 32) :
    ConditionHolds .NE (subsPState32 x y) = (x != y) :=
  conditionHolds_ne_subs32 x y

@[simp, arm64_norm]
theorem conditionHolds_cs_subsPState32 (x y : BitVec 32) :
    ConditionHolds .CS (subsPState32 x y) = BitVec.ule y x :=
  conditionHolds_cs_subs32 x y

@[simp, arm64_norm]
theorem conditionHolds_cc_subsPState32 (x y : BitVec 32) :
    ConditionHolds .CC (subsPState32 x y) = BitVec.ult x y :=
  conditionHolds_cc_subs32 x y

@[simp, arm64_norm]
theorem conditionHolds_hi_subsPState32 (x y : BitVec 32) :
    ConditionHolds .HI (subsPState32 x y) = BitVec.ult y x :=
  conditionHolds_hi_subs32 x y

@[simp, arm64_norm]
theorem conditionHolds_ls_subsPState32 (x y : BitVec 32) :
    ConditionHolds .LS (subsPState32 x y) = BitVec.ule x y :=
  conditionHolds_ls_subs32 x y

@[simp, arm64_norm]
theorem conditionHolds_ge_subsPState32 (x y : BitVec 32) :
    ConditionHolds .GE (subsPState32 x y) = BitVec.sle y x :=
  conditionHolds_ge_subs32 x y

@[simp, arm64_norm]
theorem conditionHolds_lt_subsPState32 (x y : BitVec 32) :
    ConditionHolds .LT (subsPState32 x y) = BitVec.slt x y :=
  conditionHolds_lt_subs32 x y

@[simp, arm64_norm]
theorem conditionHolds_gt_subsPState32 (x y : BitVec 32) :
    ConditionHolds .GT (subsPState32 x y) = BitVec.slt y x :=
  conditionHolds_gt_subs32 x y

@[simp, arm64_norm]
theorem conditionHolds_le_subsPState32 (x y : BitVec 32) :
    ConditionHolds .LE (subsPState32 x y) = BitVec.sle x y :=
  conditionHolds_le_subs32 x y

@[simp, arm64_norm]
theorem subsPState32_c (x y : BitVec 32) :
    (subsPState32 x y).c = BitVec.ule y x :=
  conditionHolds_cs_subs32 x y

@[simp, arm64_norm]
theorem addsPState32_c (x y : BitVec 32) :
    (addsPState32 x y).c = (AddWithCarry32 x y false).2.c := rfl

@[simp, arm64_norm]
theorem conditionHolds_eq_adds32 (x y : BitVec 32) :
    ConditionHolds .EQ (AddWithCarry32 x y false).2 = (x + y == 0#32) := by
  simp only [ConditionHolds, AddWithCarry32, Bool.false_eq_true, ite_false]; bv_bits

@[simp, arm64_norm]
theorem conditionHolds_ne_adds32 (x y : BitVec 32) :
    ConditionHolds .NE (AddWithCarry32 x y false).2 = (x + y != 0#32) :=
  congrArg not (conditionHolds_eq_adds32 x y)

@[simp, arm64_norm]
theorem conditionHolds_cs_adds32 (x y : BitVec 32) :
    ConditionHolds .CS (AddWithCarry32 x y false).2 = BitVec.ult (x + y) x := by
  simp only [ConditionHolds, AddWithCarry32, Bool.false_eq_true, ite_false]; bv_bits

@[simp, arm64_norm]
theorem conditionHolds_cc_adds32 (x y : BitVec 32) :
    ConditionHolds .CC (AddWithCarry32 x y false).2 = BitVec.ule x (x + y) := by
  show (!ConditionHolds .CS (AddWithCarry32 x y false).2) = BitVec.ule x (x + y)
  rw [conditionHolds_cs_adds32, not_ult_eq_ule_32]

@[simp, arm64_norm]
theorem conditionHolds_eq_addsPState32 (x y : BitVec 32) :
    ConditionHolds .EQ (addsPState32 x y) = (x + y == 0#32) :=
  conditionHolds_eq_adds32 x y

@[simp, arm64_norm]
theorem conditionHolds_ne_addsPState32 (x y : BitVec 32) :
    ConditionHolds .NE (addsPState32 x y) = (x + y != 0#32) :=
  conditionHolds_ne_adds32 x y

@[simp, arm64_norm]
theorem conditionHolds_cs_addsPState32 (x y : BitVec 32) :
    ConditionHolds .CS (addsPState32 x y) = BitVec.ult (x + y) x :=
  conditionHolds_cs_adds32 x y

@[simp, arm64_norm]
theorem conditionHolds_cc_addsPState32 (x y : BitVec 32) :
    ConditionHolds .CC (addsPState32 x y) = BitVec.ule x (x + y) :=
  conditionHolds_cc_adds32 x y

@[simp, arm64_norm]
theorem conditionHolds_eq_subsPState64 (x y : BitVec 64) :
    ConditionHolds .EQ (subsPState64 x y) = (x == y) :=
  conditionHolds_eq_subs64 x y

@[simp, arm64_norm]
theorem conditionHolds_ne_subsPState64 (x y : BitVec 64) :
    ConditionHolds .NE (subsPState64 x y) = (x != y) :=
  conditionHolds_ne_subs64 x y

@[simp, arm64_norm]
theorem conditionHolds_cs_subsPState64 (x y : BitVec 64) :
    ConditionHolds .CS (subsPState64 x y) = BitVec.ule y x :=
  conditionHolds_cs_subs64 x y

@[simp, arm64_norm]
theorem conditionHolds_cc_subsPState64 (x y : BitVec 64) :
    ConditionHolds .CC (subsPState64 x y) = BitVec.ult x y :=
  conditionHolds_cc_subs64 x y

@[simp, arm64_norm]
theorem conditionHolds_hi_subsPState64 (x y : BitVec 64) :
    ConditionHolds .HI (subsPState64 x y) = BitVec.ult y x :=
  conditionHolds_hi_subs64 x y

@[simp, arm64_norm]
theorem conditionHolds_ls_subsPState64 (x y : BitVec 64) :
    ConditionHolds .LS (subsPState64 x y) = BitVec.ule x y :=
  conditionHolds_ls_subs64 x y

@[simp, arm64_norm]
theorem conditionHolds_ge_subsPState64 (x y : BitVec 64) :
    ConditionHolds .GE (subsPState64 x y) = BitVec.sle y x :=
  conditionHolds_ge_subs64 x y

@[simp, arm64_norm]
theorem conditionHolds_lt_subsPState64 (x y : BitVec 64) :
    ConditionHolds .LT (subsPState64 x y) = BitVec.slt x y :=
  conditionHolds_lt_subs64 x y

@[simp, arm64_norm]
theorem conditionHolds_gt_subsPState64 (x y : BitVec 64) :
    ConditionHolds .GT (subsPState64 x y) = BitVec.slt y x :=
  conditionHolds_gt_subs64 x y

@[simp, arm64_norm]
theorem conditionHolds_le_subsPState64 (x y : BitVec 64) :
    ConditionHolds .LE (subsPState64 x y) = BitVec.sle x y :=
  conditionHolds_le_subs64 x y

@[simp, arm64_norm]
theorem subsPState64_c (x y : BitVec 64) :
    (subsPState64 x y).c = BitVec.ule y x :=
  conditionHolds_cs_subs64 x y

@[simp, arm64_norm]
theorem addsPState64_c (x y : BitVec 64) :
    (addsPState64 x y).c = (AddWithCarry64 x y false).2.c := rfl

@[simp, arm64_norm]
theorem conditionHolds_eq_adds64 (x y : BitVec 64) :
    ConditionHolds .EQ (AddWithCarry64 x y false).2 = (x + y == 0#64) := by
  simp only [ConditionHolds, AddWithCarry64, Bool.false_eq_true, ite_false]; bv_bits

@[simp, arm64_norm]
theorem conditionHolds_ne_adds64 (x y : BitVec 64) :
    ConditionHolds .NE (AddWithCarry64 x y false).2 = (x + y != 0#64) :=
  congrArg not (conditionHolds_eq_adds64 x y)

@[simp, arm64_norm]
theorem conditionHolds_cs_adds64 (x y : BitVec 64) :
    ConditionHolds .CS (AddWithCarry64 x y false).2 = BitVec.ult (x + y) x := by
  simp only [ConditionHolds, AddWithCarry64, Bool.false_eq_true, ite_false]; bv_bits

@[simp, arm64_norm]
theorem conditionHolds_cc_adds64 (x y : BitVec 64) :
    ConditionHolds .CC (AddWithCarry64 x y false).2 = BitVec.ule x (x + y) := by
  show (!ConditionHolds .CS (AddWithCarry64 x y false).2) = BitVec.ule x (x + y)
  rw [conditionHolds_cs_adds64, not_ult_eq_ule_64]

@[simp, arm64_norm]
theorem conditionHolds_eq_addsPState64 (x y : BitVec 64) :
    ConditionHolds .EQ (addsPState64 x y) = (x + y == 0#64) :=
  conditionHolds_eq_adds64 x y

@[simp, arm64_norm]
theorem conditionHolds_ne_addsPState64 (x y : BitVec 64) :
    ConditionHolds .NE (addsPState64 x y) = (x + y != 0#64) :=
  conditionHolds_ne_adds64 x y

@[simp, arm64_norm]
theorem conditionHolds_cs_addsPState64 (x y : BitVec 64) :
    ConditionHolds .CS (addsPState64 x y) = BitVec.ult (x + y) x :=
  conditionHolds_cs_adds64 x y

@[simp, arm64_norm]
theorem conditionHolds_cc_addsPState64 (x y : BitVec 64) :
    ConditionHolds .CC (addsPState64 x y) = BitVec.ule x (x + y) :=
  conditionHolds_cc_adds64 x y

/-- After `ADDS`/`CMN x, y`, `ConditionHolds .HI` is "carry out and nonzero result". Not a `simp`
    lemma; `rw` with it when a branch on `b.hi` follows a 64-bit `CMN`. -/
theorem conditionHolds_hi_addsPState64 (x y : BitVec 64) :
    ConditionHolds .HI (addsPState64 x y) = (BitVec.ult (x + y) x && (x + y != 0#64)) := by
  change (ConditionHolds .CS (addsPState64 x y) && ConditionHolds .NE (addsPState64 x y)) = _
  rw [conditionHolds_cs_addsPState64, conditionHolds_ne_addsPState64]

@[simp, arm64_norm]
theorem conditionHolds_eq_mk (n z c v : Bool) :
    ConditionHolds .EQ { n, z, c, v } = z := rfl

@[simp, arm64_norm]
theorem conditionHolds_ne_mk (n z c v : Bool) :
    ConditionHolds .NE { n, z, c, v } = !z := rfl

@[simp, arm64_norm]
theorem conditionHolds_mi_mk (n z c v : Bool) :
    ConditionHolds .MI { n, z, c, v } = n := rfl

@[simp, arm64_norm]
theorem conditionHolds_pl_mk (n z c v : Bool) :
    ConditionHolds .PL { n, z, c, v } = !n := rfl

@[simp, arm64_norm]
theorem conditionHolds_mi_subs32 (x y : BitVec 32) :
    ConditionHolds .MI (AddWithCarry32 x (~~~y) true).2 = (x - y).msb := by
  show (AddWithCarry32 x (~~~y) true).1.msb = _
  rw [addWithCarry32_sub_fst]

@[simp, arm64_norm]
theorem conditionHolds_pl_subs32 (x y : BitVec 32) :
    ConditionHolds .PL (AddWithCarry32 x (~~~y) true).2 = !(x - y).msb :=
  congrArg not (conditionHolds_mi_subs32 x y)

theorem conditionHolds_mi_subsPState32 (x y : BitVec 32) :
    ConditionHolds .MI (subsPState32 x y) = (x - y).msb :=
  conditionHolds_mi_subs32 x y

theorem conditionHolds_pl_subsPState32 (x y : BitVec 32) :
    ConditionHolds .PL (subsPState32 x y) = !(x - y).msb :=
  conditionHolds_pl_subs32 x y

@[simp, arm64_norm]
theorem conditionHolds_mi_adds32 (x y : BitVec 32) :
    ConditionHolds .MI (AddWithCarry32 x y false).2 = (x + y).msb := by
  show (AddWithCarry32 x y false).1.msb = _
  rw [addWithCarry32_add_fst]

@[simp, arm64_norm]
theorem conditionHolds_pl_adds32 (x y : BitVec 32) :
    ConditionHolds .PL (AddWithCarry32 x y false).2 = !(x + y).msb :=
  congrArg not (conditionHolds_mi_adds32 x y)

theorem conditionHolds_mi_addsPState32 (x y : BitVec 32) :
    ConditionHolds .MI (addsPState32 x y) = (x + y).msb :=
  conditionHolds_mi_adds32 x y

theorem conditionHolds_pl_addsPState32 (x y : BitVec 32) :
    ConditionHolds .PL (addsPState32 x y) = !(x + y).msb :=
  conditionHolds_pl_adds32 x y

@[simp, arm64_norm]
theorem conditionHolds_mi_subs64 (x y : BitVec 64) :
    ConditionHolds .MI (AddWithCarry64 x (~~~y) true).2 = (x - y).msb := by
  show (AddWithCarry64 x (~~~y) true).1.msb = _
  rw [addWithCarry64_sub_fst]

@[simp, arm64_norm]
theorem conditionHolds_pl_subs64 (x y : BitVec 64) :
    ConditionHolds .PL (AddWithCarry64 x (~~~y) true).2 = !(x - y).msb :=
  congrArg not (conditionHolds_mi_subs64 x y)

theorem conditionHolds_mi_subsPState64 (x y : BitVec 64) :
    ConditionHolds .MI (subsPState64 x y) = (x - y).msb :=
  conditionHolds_mi_subs64 x y

theorem conditionHolds_pl_subsPState64 (x y : BitVec 64) :
    ConditionHolds .PL (subsPState64 x y) = !(x - y).msb :=
  conditionHolds_pl_subs64 x y

@[simp, arm64_norm]
theorem conditionHolds_mi_adds64 (x y : BitVec 64) :
    ConditionHolds .MI (AddWithCarry64 x y false).2 = (x + y).msb := by
  show (AddWithCarry64 x y false).1.msb = _
  rw [addWithCarry64_add_fst]

@[simp, arm64_norm]
theorem conditionHolds_pl_adds64 (x y : BitVec 64) :
    ConditionHolds .PL (AddWithCarry64 x y false).2 = !(x + y).msb :=
  congrArg not (conditionHolds_mi_adds64 x y)

theorem conditionHolds_mi_addsPState64 (x y : BitVec 64) :
    ConditionHolds .MI (addsPState64 x y) = (x + y).msb :=
  conditionHolds_mi_adds64 x y

theorem conditionHolds_pl_addsPState64 (x y : BitVec 64) :
    ConditionHolds .PL (addsPState64 x y) = !(x + y).msb :=
  conditionHolds_pl_adds64 x y

@[simp, arm64_norm]
theorem addWithCarry64_n_false (x y : BitVec 64) :
    (AddWithCarry64 x y false).2.n = (x + y).getLsbD 63 := by
  change ConditionHolds .MI (AddWithCarry64 x y false).2 = (x + y).getLsbD 63
  rw [conditionHolds_mi_adds64, BitVec.msb_eq_getLsbD_last]

@[simp, arm64_norm]
theorem addWithCarry32_n_false (x y : BitVec 32) :
    (AddWithCarry32 x y false).2.n = (x + y).getLsbD 31 := by
  change ConditionHolds .MI (AddWithCarry32 x y false).2 = (x + y).getLsbD 31
  rw [conditionHolds_mi_adds32, BitVec.msb_eq_getLsbD_last]

set_option allowUnsafeReducibility true in
attribute [irreducible] evalAddSub subsPState64 addsPState64 subsPState32 addsPState32

@[simp, arm64_norm]
theorem bitvec_zero_sub_64 (x : BitVec 64) :
    0#64 - x = -x := by
  bv_decide

@[simp, arm64_norm]
theorem bitvec_zero_add_64 (x : BitVec 64) :
    0#64 + x = x := by
  bv_decide

@[simp, arm64_norm]
theorem bitvec_zero_or_64 (x : BitVec 64) :
    0#64 ||| x = x := by
  bv_decide

@[simp, arm64_norm]
theorem nat_zero_mod_64 : 0 % 64 = 0 := rfl

@[simp, arm64_norm]
theorem nat_one_mod_64 : 1 % 64 = 1 := rfl

@[simp, arm64_norm]
theorem truncate_32_zeroExtend_64 {w : Nat} (x : BitVec w) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 x) = BitVec.zeroExtend 32 x := by
  ext i hi
  simp

@[simp, arm64_norm]
theorem truncate_16_zeroExtend_64 {w : Nat} (x : BitVec w) :
    BitVec.truncate 16 (BitVec.zeroExtend 64 x) = BitVec.zeroExtend 16 x := by
  ext i hi
  simp

@[simp, arm64_norm]
theorem truncate_8_zeroExtend_64 {w : Nat} (x : BitVec w) :
    BitVec.truncate 8 (BitVec.zeroExtend 64 x) = BitVec.zeroExtend 8 x := by
  ext i hi
  simp

@[simp, arm64_norm]
theorem truncate_8_zeroExtend_32 {w : Nat} (x : BitVec w) :
    BitVec.truncate 8 (BitVec.zeroExtend 32 x) = BitVec.zeroExtend 8 x := by
  ext i hi
  simp

@[simp, arm64_norm]
theorem zeroExtend_self {w : Nat} (x : BitVec w) :
    BitVec.zeroExtend w x = x :=
  BitVec.setWidth_eq x

@[simp, arm64_norm]
theorem zeroExtend_8_xor_64 (x y : BitVec 64) :
    BitVec.zeroExtend 8 (x ^^^ y) = BitVec.zeroExtend 8 x ^^^ BitVec.zeroExtend 8 y := by
  bv_decide

attribute [arm64_norm] List.cons_append

@[simp, arm64_norm]
theorem zeroExtend_64_zeroExtend_32_8 (x : BitVec 8) :
    BitVec.zeroExtend 64 (BitVec.zeroExtend 32 x) = BitVec.zeroExtend 64 x := by
  bv_decide

@[simp, arm64_norm]
theorem zeroExtend_64_zeroExtend_32_16 (x : BitVec 16) :
    BitVec.zeroExtend 64 (BitVec.zeroExtend 32 x) = BitVec.zeroExtend 64 x := by
  bv_decide

@[simp, arm64_norm]
theorem truncate_8_xor_32 (x y : BitVec 32) :
    BitVec.truncate 8 (x ^^^ y) = BitVec.truncate 8 x ^^^ BitVec.truncate 8 y := by
  bv_decide

@[simp, arm64_norm]
theorem truncate_8_add_32 (x y : BitVec 32) :
    BitVec.truncate 8 (x + y) = BitVec.truncate 8 x + BitVec.truncate 8 y := by
  bv_decide

@[simp, arm64_norm]
theorem bitvec_sub_zero_64 (x : BitVec 64) :
    x - 0#64 = x := by
  bv_decide

@[simp, arm64_norm]
theorem bitvec_shiftLeft_zero (x : BitVec 64) :
    x <<< 0 = x := by
  bv_decide

@[simp, arm64_norm]
theorem bitvec32_shiftLeft_zero (x : BitVec 32) :
    x <<< 0 = x := by
  bv_decide

@[simp, arm64_norm]
theorem bitvec32_and_zeroExtend64 (x y : BitVec 32) :
    ((x.zeroExtend 64) &&& (y.zeroExtend 64)).truncate 32 = x &&& y := by
  simp

@[simp, arm64_norm]
theorem bitvec32_or_zeroExtend64 (x y : BitVec 32) :
    ((x.zeroExtend 64) ||| (y.zeroExtend 64)).truncate 32 = x ||| y := by
  simp

@[simp, arm64_norm]
theorem bitvec32_xor_zeroExtend64 (x y : BitVec 32) :
    ((x.zeroExtend 64) ^^^ (y.zeroExtend 64)).truncate 32 = x ^^^ y := by
  simp

@[simp, arm64_norm]
theorem bitvec32_bic_zeroExtend64 (x y : BitVec 32) :
    ((x.zeroExtend 64) &&& ~~~(y.zeroExtend 64)).truncate 32 = x &&& ~~~y := by
  simp

@[simp, arm64_norm]
theorem bitvec32_orn_zeroExtend64 (x y : BitVec 32) :
    ((x.zeroExtend 64) ||| ~~~(y.zeroExtend 64)).truncate 32 = x ||| ~~~y := by
  simp

@[simp, arm64_norm]
theorem bitvec32_eon_zeroExtend64 (x y : BitVec 32) :
    ((x.zeroExtend 64) ^^^ ~~~(y.zeroExtend 64)).truncate 32 = x ^^^ ~~~y := by
  simp

private theorem add_24_eq_add_16_add_8 (a : BitVec 64) : a + 24#64 = (a + 16#64) + 8#64 := by
  bv_decide

@[simp, arm64_norm]
theorem read64_write64_of_disjoint128_0_24_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : Memory.Disjoint128 a1 (a2 + 16#64)) :
    (m.write64 a1 v).read64 (a2 + 24#64) = m.read64 (a2 + 24#64) := by
  rw [add_24_eq_add_16_add_8 a2]
  exact Memory.read64_write64_of_disjoint128_0_8_l m a1 (a2 + 16#64) v h

@[simp, arm64_norm]
theorem read64_write64_of_disjoint128_8_24_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : Memory.Disjoint128 a1 (a2 + 16#64)) :
    (m.write64 (a1 + 8#64) v).read64 (a2 + 24#64) = m.read64 (a2 + 24#64) := by
  rw [add_24_eq_add_16_add_8 a2]
  exact Memory.read64_write64_of_disjoint128_8_8_l m a1 (a2 + 16#64) v h

@[simp, arm64_norm]
theorem read64_write64_of_disjoint128_24_0_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : Memory.Disjoint128 a2 (a1 + 16#64)) :
    (m.write64 (a1 + 24#64) v).read64 a2 = m.read64 a2 := by
  rw [add_24_eq_add_16_add_8 a1]
  exact Memory.read64_write64_of_disjoint128_8_0_r m (a1 + 16#64) a2 v h

@[simp, arm64_norm]
theorem read64_write64_of_disjoint128_24_8_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : Memory.Disjoint128 a2 (a1 + 16#64)) :
    (m.write64 (a1 + 24#64) v).read64 (a2 + 8#64) = m.read64 (a2 + 8#64) := by
  rw [add_24_eq_add_16_add_8 a1]
  exact Memory.read64_write64_of_disjoint128_8_8_r m (a1 + 16#64) a2 v h

attribute [arm64_norm]
  Memory.read64_write64_of_disjoint64_left
  Memory.read64_write64_of_disjoint64_right
  Memory.read64_write64_of_disjoint128_0_0_l
  Memory.read64_write64_of_disjoint128_0_0_r
  Memory.read64_write64_of_disjoint128_8_0_l
  Memory.read64_write64_of_disjoint128_8_0_r
  Memory.read64_write64_of_disjoint128_0_8_l
  Memory.read64_write64_of_disjoint128_0_8_r
  Memory.read64_write64_of_disjoint128_8_8_l
  Memory.read64_write64_of_disjoint128_8_8_r

/-! ## Offset Addressing and Page-Offset Reconstruction -/

@[simp, arm64_norm]
theorem evalAddrMode_offset (s : State) (base : Reg) (off : BitVec 64) :
    evalAddrMode s (.Offset base off) = (s.readReg64 base + off, none) := by
  cases s; rfl

@[simp, arm64_norm]
theorem evalAddrMode_unscaled (s : State) (base : Reg) (off : BitVec 64) :
    evalAddrMode s (.UnscaledOffset base off) = (s.readReg64 base + off, none) := by
  cases s; rfl

@[simp, arm64_norm]
theorem evalAddrMode_unscaled_zero (s : State) (base : Reg) :
    evalAddrMode s (.UnscaledOffset base 0#64) = (s.readReg64 base, none) := by
  simp only [evalAddrMode, BitVec.add_zero]

/-- Negative unscaled offsets are written `base + (-k)` by `evalAddrMode`; rewrite them into the
    `base - k` form the `Memory.Disjoint64`/`Memory.Disjoint128` framing lemmas expect. -/
@[simp, arm64_norm, wp_norm]
theorem bitvec_add_neg_eq_sub (x k : BitVec 64) : x + (-k) = x - k := by
  bv_arith

/-- Reconstruct a 64-bit address from its page-aligned high 52 bits (`ADRP`, `R_AARCH64_ADR_PREL_PG_HI21`)
    and its low 12 bits (`ADD :lo12:`, `R_AARCH64_ADD_ABS_LO12_NC`). -/
@[simp, arm64_norm]
theorem page_hi21_add_lo12 (addr : BitVec 64) :
    (addr &&& 0xfffffffffffff000#64) + (addr &&& 0xfff#64) = addr := by
  bv_bits

@[simp, arm64_norm]
theorem Program.fnAddr_with_externs (prog : Program)
    (ext : String → Option (State → State)) (name : String) :
    ({ prog with externs := ext } : Program).fnAddr name = prog.fnAddr name := by
  cases prog; rfl

@[simp, arm64_norm]
theorem Program.fnAddr_with_overrides (prog : Program)
    (ovr : String → Option (State → State)) (name : String) :
    ({ prog with overrides := ovr } : Program).fnAddr name = prog.fnAddr name := by
  cases prog; rfl

/-! ## Acquire/Release Accesses, Exclusives, and Barriers -/

@[simp, arm64_norm]
theorem sp_and_15_add_aligned (sp k : BitVec 64)
    (hk : decide ((k &&& 0b1111#64) == 0#64) = true) :
    ((sp + k) &&& 0b1111#64) = (sp &&& 0b1111#64) := by
  have hk' : (k &&& 0b1111#64) == 0#64 := of_decide_eq_true hk
  revert hk'
  bv_bits

@[simp, arm64_norm]
theorem sp_and_15_sub_aligned (sp k : BitVec 64)
    (hk : decide ((k &&& 0b1111#64) == 0#64) = true) :
    ((sp - k) &&& 0b1111#64) = (sp &&& 0b1111#64) := by
  have hk' : (k &&& 0b1111#64) == 0#64 := of_decide_eq_true hk
  revert hk'
  bv_bits

@[simp, arm64_norm]
theorem execInst_ldar_x64 (rn rt : Reg) (s : State)
    (hsp : checkRegSPAligned s rn = true)
    (halign : MemWidth.X64.isAligned (s.readReg64 rn) = true)
    (hr : s.mem.canRead (s.readReg64 rn) 8 = true) :
    execInst (.ldarStlr .X64 true rn rt) s =
      (s.writeReg .W64 rt (s.mem.readSized .X64 false (s.readReg64 rn))).advancePC := by
  dsimp only [execInst, execInstWithSvc]
  simp only [hsp, halign, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [MemWidth.bytes, hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

@[simp, arm64_norm]
theorem execInst_ldar_w32 (rn rt : Reg) (s : State)
    (hsp : checkRegSPAligned s rn = true)
    (halign : MemWidth.W32.isAligned (s.readReg64 rn) = true)
    (hr : s.mem.canRead (s.readReg64 rn) 4 = true) :
    execInst (.ldarStlr .W32 true rn rt) s =
      (s.writeReg .W32 rt (s.mem.readSized .W32 false (s.readReg64 rn))).advancePC := by
  dsimp only [execInst, execInstWithSvc]
  simp only [hsp, halign, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [MemWidth.bytes, hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

@[simp, arm64_norm]
theorem execInst_ldar_h16 (rn rt : Reg) (s : State)
    (hsp : checkRegSPAligned s rn = true)
    (halign : MemWidth.H16.isAligned (s.readReg64 rn) = true)
    (hr : s.mem.canRead (s.readReg64 rn) 2 = true) :
    execInst (.ldarStlr .H16 true rn rt) s =
      (s.writeReg .W32 rt (s.mem.readSized .H16 false (s.readReg64 rn))).advancePC := by
  dsimp only [execInst, execInstWithSvc]
  simp only [hsp, halign, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [MemWidth.bytes, hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

@[simp, arm64_norm]
theorem execInst_ldar_b8 (rn rt : Reg) (s : State)
    (hsp : checkRegSPAligned s rn = true)
    (hr : s.mem.canRead (s.readReg64 rn) 1 = true) :
    execInst (.ldarStlr .B8 true rn rt) s =
      (s.writeReg .W32 rt (s.mem.readSized .B8 false (s.readReg64 rn))).advancePC := by
  dsimp only [execInst, execInstWithSvc, MemWidth.isAligned]
  simp only [hsp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [MemWidth.bytes, hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

@[simp, arm64_norm]
theorem execInst_stlr (size : MemWidth) (rn rt : Reg) (s : State)
    (hsp : checkRegSPAligned s rn = true)
    (halign : size.isAligned (s.readReg64 rn) = true)
    (hw : s.mem.canWrite (s.readReg64 rn) size.bytes = true) :
    execInst (.ldarStlr size false rn rt) s =
      (s.setMem (s.mem.writeSized size (s.readReg64 rn) (s.readReg64 rt))).advancePC := by
  dsimp only [execInst, execInstWithSvc]
  simp only [hsp, halign, hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

@[simp, arm64_norm]
theorem execInst_ldxr_x64 (acq : Bool) (rn rt : Reg) (s : State)
    (hsp : checkRegSPAligned s rn = true)
    (halign : MemWidth.X64.isAligned (s.readReg64 rn) = true)
    (hr : s.mem.canRead (s.readReg64 rn) 8 = true) :
    execInst (.ldxr .X64 acq rn rt) s =
      (s.writeReg .W64 rt (s.mem.readSized .X64 false (s.readReg64 rn))).advancePC := by
  dsimp only [execInst, execInstWithSvc]
  simp only [hsp, halign, MemWidth.bytes, hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

@[simp, arm64_norm]
theorem execInst_ldxr_w32 (acq : Bool) (rn rt : Reg) (s : State)
    (hsp : checkRegSPAligned s rn = true)
    (halign : MemWidth.W32.isAligned (s.readReg64 rn) = true)
    (hr : s.mem.canRead (s.readReg64 rn) 4 = true) :
    execInst (.ldxr .W32 acq rn rt) s =
      (s.writeReg .W32 rt (s.mem.readSized .W32 false (s.readReg64 rn))).advancePC := by
  dsimp only [execInst, execInstWithSvc]
  simp only [hsp, halign, MemWidth.bytes, hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

@[simp, arm64_norm]
theorem execInst_stxr (size : MemWidth) (rel : Bool) (rs rn rt : Reg) (s : State)
    (hsp : checkRegSPAligned s rn = true)
    (halign : size.isAligned (s.readReg64 rn) = true)
    (hw : s.mem.canWrite (s.readReg64 rn) size.bytes = true) :
    execInst (.stxr size rel rs rn rt) s =
      if s.exclWillFail then
        ((s.stepExclOracle).writeReg .W32 rs 1#64).advancePC
      else
        (((s.stepExclOracle).setMem (s.mem.writeSized size (s.readReg64 rn) (s.readReg64 rt))).writeReg .W32 rs
          0#64).advancePC := by
  dsimp only [execInst, execInstWithSvc]
  simp only [hsp, halign, hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- `DMB`/`DSB`/`ISB`/`CLREX` are pure `PC` advances in the sequentially consistent memory model. -/
@[simp, arm64_norm]
theorem execInst_barrier (crm : BitVec 4) (op2 : BitVec 3) (s : State) :
    execInst (.barrier crm op2) s = s.advancePC := by
  cases s; rfl

/-! ## System Register Access and Instruction Evaluation -/

/-- Stable head symbol for `MSR tpidr_el0, xt` updates so `State` framing lemmas continue to
    match across subsequent field updates. -/
def setTpidrEl0 (s : State) (v : BitVec 64) : State := { s with tpidrEl0 := v }

@[simp, arm64_norm]
theorem execInst_mrs_tpidr (rt : Reg) (s : State) :
    execInst (.sysReg true 0x5e82#15 rt) s = (s.writeReg64 rt s.tpidrEl0).advancePC := by
  cases s; rfl

@[simp, arm64_norm]
theorem execInst_msr_tpidr (rt : Reg) (s : State) :
    execInst (.sysReg false 0x5e82#15 rt) s = (setTpidrEl0 s (s.readReg64 rt)).advancePC := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem tpidrEl0_setTpidrEl0 (s : State) (v : BitVec 64) : (setTpidrEl0 s v).tpidrEl0 = v := by
  cases s; rfl

@[simp, arm64_norm]
theorem readReg64_setTpidrEl0 (s : State) (v : BitVec 64) (r : Reg) :
    (setTpidrEl0 s v).readReg64 r = s.readReg64 r := by
  cases s; cases r <;> rfl

@[simp, arm64_norm]
theorem mem_setTpidrEl0 (s : State) (v : BitVec 64) : (setTpidrEl0 s v).mem = s.mem := by
  cases s; rfl

@[simp, arm64_norm]
theorem sp_setTpidrEl0 (s : State) (v : BitVec 64) : (setTpidrEl0 s v).sp = s.sp := by
  cases s; rfl

@[simp, arm64_norm]
theorem pc_setTpidrEl0 (s : State) (v : BitVec 64) : (setTpidrEl0 s v).pc = s.pc := by
  cases s; rfl

@[simp, arm64_norm]
theorem pstate_setTpidrEl0 (s : State) (v : BitVec 64) : (setTpidrEl0 s v).pstate = s.pstate := by
  cases s; rfl

@[simp, arm64_norm]
theorem status_setTpidrEl0 (s : State) (v : BitVec 64) : (setTpidrEl0 s v).status = s.status := by
  cases s; rfl

@[simp, arm64_norm]
theorem readVReg128_setTpidrEl0 (s : State) (v : BitVec 64) (idx : BitVec 5) :
    (setTpidrEl0 s v).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem fpsr_setTpidrEl0 (s : State) (v : BitVec 64) :
    (setTpidrEl0 s v).fpsr = s.fpsr := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.tpidrEl0_advancePC (s : State) : s.advancePC.tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.tpidrEl0_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.tpidrEl0_setMem (s : State) (m : Memory) : (s.setMem m).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.tpidrEl0_setPState (s : State) (ps : PState) : (s.setPState ps).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.tpidrEl0_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).tpidrEl0 = s.tpidrEl0 := by
  cases s; cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.tpidrEl0_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).tpidrEl0 = s.tpidrEl0 := by
  cases s; cases w <;> cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.tpidrEl0_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.tpidrEl0_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 idx v).tpidrEl0 = s.tpidrEl0 :=
  State.tpidrEl0_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm, wp_norm]
theorem State.tpidrEl0_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 idx v).tpidrEl0 = s.tpidrEl0 :=
  State.tpidrEl0_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm, wp_norm]
theorem State.tpidrEl0_setFpsr (s : State) (f : BitVec 32) :
    (s.setFpsr f).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.tpidrEl0_orFpsr (s : State) (f : BitVec 32) :
    (s.orFpsr f).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.tpidrEl0_panicked (s : State) :
    (Rust.panicked s).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

/-- `MRS rt, fpcr` returns `0#64` (pinned `FPCR = 0`: RNE, no FZ, DN = 0, no traps). -/
@[simp, arm64_norm]
theorem execInst_mrs_fpcr (rt : Reg) (s : State) :
    execInst (.sysReg true 0x5a20#15 rt) s =
      (s.writeReg64 rt 0#64).advancePC := by
  cases s; rfl

/-- `true` iff `inst` is `SVC #0` (`Instr.system false 0#16`), the only instruction whose semantics
    consults `Program.svc`. -/
def _root_.Arm64.Instr.isSvc0Instr : Instr → Bool
  | .system false 0#16 => true
  | _ => false

theorem _root_.Arm64.Program.evalInst_of_isSvc0Instr_false (prog : Program) (inst : Instr)
    (s : State) (h : inst.isSvc0Instr = false) :
    prog.evalInst inst s = execInst inst s := by
  cases inst with
  | system isHalt imm =>
    cases isHalt
    · by_cases himm : imm == 0#16
      · have heq : imm = 0#16 := of_decide_eq_true himm
        subst heq; simp [_root_.Arm64.Instr.isSvc0Instr] at h
      · simp [Program.evalInst, execInst, execInstWithSvc, himm]
    · rfl
  | _ => rfl

@[simp, arm64_norm]
theorem _root_.Arm64.Program.evalInst_svc0 (prog : Program) (s : State) :
    prog.evalInst (.system false 0#16) s = evalSvc prog.svc s := by
  cases s; rfl

@[simp, arm64_norm]
theorem _root_.Arm64.Program.evalInst_sysReg (prog : Program) (isRead : Bool)
    (sysreg : BitVec 15) (rt : Reg) (s : State) :
    prog.evalInst (.sysReg isRead sysreg rt) s = execInst (.sysReg isRead sysreg rt) s := by
  cases s; rfl

@[simp, arm64_norm]
theorem _root_.Arm64.Program.evalInst_system_halt (prog : Program) (imm : BitVec 16) (s : State) :
    prog.evalInst (.system true imm) s = execInst (.system true imm) s := by
  cases s; rfl

@[simp, arm64_norm]
theorem _root_.Arm64.Program.evalInst_system_non_svc0 (prog : Program) (imm : BitVec 16)
    (s : State) (h : (imm == 0#16) = false) :
    prog.evalInst (.system false imm) s = execInst (.system false imm) s := by
  simp [Program.evalInst, execInst, execInstWithSvc, h]

section EvalInstNonSystemSimp
open Lean Meta Elab Command in
run_cmd do
  let ConstantInfo.inductInfo indVal ← getConstInfo ``Instr | unreachable!
  for ctorName in indVal.ctors do
    if ctorName == ``Instr.system || ctorName == ``Instr.sysReg then continue
    let ctorInfo ← getConstInfoCtor ctorName
    let cmd ← liftTermElabM do
      forallTelescopeReducing ctorInfo.type fun args _ => do
        let binderIdents : Array (TSyntax `ident) ← args.mapIdxM fun idx _ =>
          pure (mkIdent (Name.mkSimple s!"a{idx}"))
        let binderTerms : Array Term := binderIdents.map fun id => ⟨id.raw⟩
        let ctorTerm : Term := Syntax.mkApp (mkIdent ctorName) binderTerms
        let thmIdent := mkIdent (Name.str `_root_.Arm64.Program ("evalInst_" ++ ctorName.getString!))
        `(command|
          @[simp, arm64_norm]
          public theorem $thmIdent (prog : _root_.Arm64.Program) $binderIdents* (s : _root_.Arm64.State) :
              _root_.Arm64.Program.evalInst prog $ctorTerm s = _root_.Arm64.execInst $ctorTerm s := by
            cases s; rfl)
    elabCommand cmd
end EvalInstNonSystemSimp

@[simp, arm64_norm]
theorem execInst_msr_fpcr (rt : Reg) (s : State) :
    execInst (.sysReg false 0x5a20#15 rt) s =
      (if s.readReg64 rt == 0#64 then s.advancePC
       else { s with status := .Exception "unsupported FPCR value" }) := by
  simp only [execInst, execInstWithSvc, BitVec.reduceBEq, Bool.false_eq_true, ↓reduceIte]

@[simp, arm64_norm]
theorem execInst_mrs_fpsr (rt : Reg) (s : State) :
    execInst (.sysReg true 0x5a21#15 rt) s =
      (s.writeReg64 rt (s.fpsr.zeroExtend 64)).advancePC := by
  cases s; rfl

/-- `MSR fpsr, rt` writes `rt` masked to `fpsrMask` (`0x0800009f#32`) into `fpsr`. -/
@[simp, arm64_norm]
theorem execInst_msr_fpsr (rt : Reg) (s : State) :
    execInst (.sysReg false 0x5a21#15 rt) s =
      (s.setFpsr ((s.readReg64 rt).truncate 32 &&& fpsrMask)).advancePC := by
  cases s; rfl

/-- `MRS rt, dczid_el0` returns `4#64` (`DCZID_EL0.BS = 4`, 64-byte `DC ZVA` block size). -/
@[simp, arm64_norm]
theorem execInst_mrs_dczid_el0 (rt : Reg) (s : State) :
    execInst (.sysReg true 0x5807#15 rt) s =
      (s.writeReg64 rt 4#64).advancePC := by
  cases s; rfl

@[simp, arm64_norm]
theorem execInst_dcZva (rt : Reg) (s : State) :
    execInst (.dcZva rt) s =
      let ea := s.readReg64 rt &&& ~~~63#64
      if !s.mem.canWrite ea 64 then
        s.setStatus (.Exception "permission fault")
      else
        (s.setMem ((((s.mem.write128 ea 0#128).write128 (ea + 16#64) 0#128).write128
          (ea + 16#64 + 16#64) 0#128).write128 (ea + 16#64 + 16#64 + 16#64) 0#128)).advancePC := by
  cases s; rfl

/-! ## SIMD/FP Register File Framing -/

theorem VRegFile.write_write_same (vf : VRegFile) (idx : BitVec 5) (v1 v2 : BitVec 128) :
    (vf.write idx v1).write idx v2 = vf.write idx v2 := by
  apply VRegFile.ext
  funext j
  by_cases h : j = idx <;> simp [VRegFile.write, h]

@[simp, arm64_norm]
theorem State.readVReg128_writeVReg128 (s : State) (idx1 idx2 : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx1 v).readVReg128 idx2 =
      if idx2 = idx1 then v else s.readVReg128 idx2 := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.readVReg128_writeVReg128_same (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).readVReg128 idx = v := by
  simp [State.readVReg128, State.writeVReg128]

@[simp, arm64_norm]
theorem BitVec.truncate_64_zeroExtend_128 (x : BitVec 64) :
    (x.zeroExtend 128).truncate 64 = x := by
  bv_omega

@[simp, arm64_norm]
theorem BitVec.truncate_64_extractLsb_zeroExtend_128 (x : BitVec 128) :
    ((x.extractLsb' 0 64).zeroExtend 128).truncate 64 = x.truncate 64 := by
  rw [BitVec.truncate_64_zeroExtend_128]; rfl

@[simp, arm64_norm]
theorem State.readVReg64_writeVReg128 (s : State) (idx1 idx2 : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx1 v).readVReg64 idx2 =
      if idx2 = idx1 then v.truncate 64 else s.readVReg64 idx2 := by
  cases s; simp [State.readVReg64, State.readVReg128, State.writeVReg128]; split <;> rfl

@[simp, arm64_norm]
theorem State.readVReg64_writeVReg64 (s : State) (idx1 idx2 : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 idx1 v).readVReg64 idx2 =
      if idx2 = idx1 then v else s.readVReg64 idx2 := by
  simp [State.writeVReg64]

@[arm64_norm]
theorem State.readVReg128_writeReg32 (s : State) (r : Reg) (v : BitVec 32) (idx : BitVec 5) :
    (s.writeReg32 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm]
theorem State.readVReg64_writeReg64 (s : State) (r : Reg) (v : BitVec 64) (idx : BitVec 5) :
    (s.writeReg64 r v).readVReg64 idx = s.readVReg64 idx := by
  cases s; rfl

@[arm64_norm]
theorem State.readVReg64_advancePC (s : State) (idx : BitVec 5) :
    s.advancePC.readVReg64 idx = s.readVReg64 idx := by
  cases s; rfl

@[arm64_norm]
theorem State.readVReg64_setPC (s : State) (pc : BitVec 64) (idx : BitVec 5) :
    (s.setPC pc).readVReg64 idx = s.readVReg64 idx := by
  cases s; rfl

@[arm64_norm]
theorem State.readVReg64_setMem (s : State) (m : Memory) (idx : BitVec 5) :
    (s.setMem m).readVReg64 idx = s.readVReg64 idx := by
  cases s; rfl

@[arm64_norm]
theorem State.readVReg64_setPState (s : State) (ps : PState) (idx : BitVec 5) :
    (s.setPState ps).readVReg64 idx = s.readVReg64 idx := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.writeVReg128_writeVReg128_same (s : State) (idx : BitVec 5) (v1 v2 : BitVec 128) :
    (s.writeVReg128 idx v1).writeVReg128 idx v2 = s.writeVReg128 idx v2 := by
  show { s with vregs := (s.vregs.write idx v1).write idx v2 }
       = { s with vregs := s.vregs.write idx v2 }
  rw [VRegFile.write_write_same]

@[simp, arm64_norm]
theorem State.pc_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).pc = s.pc := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.sp_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).sp = s.sp := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.mem_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).mem = s.mem := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.pstate_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).pstate = s.pstate := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.status_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).status = s.status := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.pc_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 idx v).pc = s.pc :=
  State.pc_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm]
theorem State.pc_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 idx v).pc = s.pc :=
  State.pc_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm]
theorem State.sp_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 idx v).sp = s.sp :=
  State.sp_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm]
theorem State.sp_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 idx v).sp = s.sp :=
  State.sp_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm]
theorem State.mem_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 idx v).mem = s.mem :=
  State.mem_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm]
theorem State.mem_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 idx v).mem = s.mem :=
  State.mem_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm]
theorem State.pstate_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 idx v).pstate = s.pstate :=
  State.pstate_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm]
theorem State.pstate_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 idx v).pstate = s.pstate :=
  State.pstate_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm]
theorem State.status_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 idx v).status = s.status :=
  State.status_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm]
theorem State.status_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 idx v).status = s.status :=
  State.status_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm]
theorem State.readReg64_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) (r : Reg) :
    (s.writeVReg128 idx v).readReg64 r = s.readReg64 r := by
  cases s; cases r <;> rfl

@[simp, arm64_norm]
theorem State.readVReg128_writeReg64 (s : State) (r : Reg) (v : BitVec 64) (idx : BitVec 5) :
    (s.writeReg64 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[simp, arm64_norm]
theorem State.readVReg128_advancePC (s : State) (idx : BitVec 5) :
    s.advancePC.readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.readVReg128_setPC (s : State) (pc : BitVec 64) (idx : BitVec 5) :
    (s.setPC pc).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.readVReg128_setMem (s : State) (m : Memory) (idx : BitVec 5) :
    (s.setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.readVReg128_setPState (s : State) (ps : PState) (idx : BitVec 5) :
    (s.setPState ps).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

/-! ## 128-Bit and Cross-Width Memory Forwarding -/

@[simp, arm64_norm]
theorem bitvec_concat_extract_128 (v : BitVec 128) :
    v.extractLsb' 64 64 ++ v.extractLsb' 0 64 = v := by
  bv_decide

@[simp, arm64_norm]
theorem read128_write128_same (m : Memory) (addr : BitVec 64) (v : BitVec 128) :
    (m.write128 addr v).read128 addr = v := by
  simp only [Memory.read128, Memory.write128, Memory.read64_write64_same,
    Memory.read64_write64_base_zero_add8]
  exact bitvec_concat_extract_128 v

@[simp, arm64_norm]
theorem read64_write128_of_disjoint128_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 128)
    (h : Memory.Disjoint128 a1 a2) :
    (m.write128 a1 v).read64 a2 = m.read64 a2 := by
  simp only [Memory.write128]
  rw [Memory.read64_write64_of_disjoint64_left _ _ _ _ h.disjoint64_8_0,
    Memory.read64_write64_of_disjoint64_left _ _ _ _ h.disjoint64_0_0]

@[simp, arm64_norm]
theorem read64_write128_of_disjoint128_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 128)
    (h : Memory.Disjoint128 a2 a1) :
    (m.write128 a1 v).read64 a2 = m.read64 a2 := by
  simp only [Memory.write128]
  rw [Memory.read64_write64_of_disjoint64_right _ _ _ _ h.disjoint64_0_8,
    Memory.read64_write64_of_disjoint64_right _ _ _ _ h.disjoint64_0_0]

@[simp, arm64_norm]
theorem read128_write128_of_disjoint128 (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 128)
    (h : Memory.Disjoint128 a1 a2) :
    (m.write128 a1 v).read128 a2 = m.read128 a2 := by
  have hlo : (m.write128 a1 v).read64 a2 = m.read64 a2 :=
    read64_write128_of_disjoint128_l m a1 a2 v h
  have hhi : (m.write128 a1 v).read64 (a2 + 8#64) = m.read64 (a2 + 8#64) := by
    simp only [Memory.write128]
    rw [Memory.read64_write64_of_disjoint64_left _ _ _ _ h.disjoint64_8_8,
      Memory.read64_write64_of_disjoint64_left _ _ _ _ h.disjoint64_0_8]
  simp only [Memory.read128, hlo, hhi]

@[simp, arm64_norm]
theorem read128_write128_of_disjoint128_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 128)
    (h : Memory.Disjoint128 a2 a1) :
    (m.write128 a1 v).read128 a2 = m.read128 a2 :=
  read128_write128_of_disjoint128 m a1 a2 v ⟨h.2, h.1⟩

@[simp, arm64_norm]
theorem read8_write128_of_disjointRegions_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 128)
    (h : DisjointRegions a1 16 a2 1) :
    (m.write128 a1 v).read8 a2 = m.read8 a2 := by
  simp only [Memory.write128,
    Memory.read8_write64_of_disjointRegions128_8_l _ a1 a2 _ h,
    Memory.read8_write64_of_disjointRegions128_0_l _ a1 a2 _ h]

@[simp, arm64_norm]
theorem read8_write128_of_disjointRegions_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 128)
    (h : DisjointRegions a2 1 a1 16) :
    (m.write128 a1 v).read8 a2 = m.read8 a2 :=
  read8_write128_of_disjointRegions_l m a1 a2 v ⟨h.2, h.1⟩

@[simp, arm64_norm]
theorem read16_write128_of_disjointRegions_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 128)
    (h : DisjointRegions a1 16 a2 2) :
    (m.write128 a1 v).read16 a2 = m.read16 a2 := by
  simp only [Memory.write128,
    Memory.read16_write64_of_disjointRegions128_8_l _ a1 a2 _ h,
    Memory.read16_write64_of_disjointRegions128_0_l _ a1 a2 _ h]

@[simp, arm64_norm]
theorem read16_write128_of_disjointRegions_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 128)
    (h : DisjointRegions a2 2 a1 16) :
    (m.write128 a1 v).read16 a2 = m.read16 a2 :=
  read16_write128_of_disjointRegions_l m a1 a2 v ⟨h.2, h.1⟩

@[simp, arm64_norm]
theorem read32_write128_of_disjointRegions_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 128)
    (h : DisjointRegions a1 16 a2 4) :
    (m.write128 a1 v).read32 a2 = m.read32 a2 := by
  simp only [Memory.write128,
    Memory.read32_write64_of_disjointRegions128_8_l _ a1 a2 _ h,
    Memory.read32_write64_of_disjointRegions128_0_l _ a1 a2 _ h]

@[simp, arm64_norm]
theorem read32_write128_of_disjointRegions_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 128)
    (h : DisjointRegions a2 4 a1 16) :
    (m.write128 a1 v).read32 a2 = m.read32 a2 :=
  read32_write128_of_disjointRegions_l m a1 a2 v ⟨h.2, h.1⟩

@[simp, arm64_norm]
theorem read64_write128_of_disjointRegions_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 128)
    (h : DisjointRegions a1 16 a2 8) :
    (m.write128 a1 v).read64 a2 = m.read64 a2 := by
  simp only [Memory.write128,
    Memory.read64_write64_of_disjointRegions128_8_8_l _ a1 a2 _ h,
    Memory.read64_write64_of_disjointRegions128_8_0_l _ a1 a2 _ h]

@[simp, arm64_norm]
theorem read64_write128_of_disjointRegions_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 128)
    (h : DisjointRegions a2 8 a1 16) :
    (m.write128 a1 v).read64 a2 = m.read64 a2 :=
  read64_write128_of_disjointRegions_l m a1 a2 v ⟨h.2, h.1⟩

@[simp, arm64_norm]
theorem read128_write8_of_disjointRegions_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (h : DisjointRegions a1 1 a2 16) :
    (m.write8 a1 v).read128 a2 = m.read128 a2 := by
  simp only [Memory.read128,
    Memory.read64_write8_of_disjointRegions128_8_l m a1 a2 v h,
    Memory.read64_write8_of_disjointRegions128_0_l m a1 a2 v h]

@[simp, arm64_norm]
theorem read128_write8_of_disjointRegions_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 8)
    (h : DisjointRegions a2 16 a1 1) :
    (m.write8 a1 v).read128 a2 = m.read128 a2 :=
  read128_write8_of_disjointRegions_l m a1 a2 v ⟨h.2, h.1⟩

@[simp, arm64_norm]
theorem read128_write16_of_disjointRegions_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h : DisjointRegions a1 2 a2 16) :
    (m.write16 a1 v).read128 a2 = m.read128 a2 := by
  simp only [Memory.read128,
    Memory.read64_write16_of_disjointRegions128_8_l m a1 a2 v h,
    Memory.read64_write16_of_disjointRegions128_0_l m a1 a2 v h]

@[simp, arm64_norm]
theorem read128_write16_of_disjointRegions_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 16)
    (h : DisjointRegions a2 16 a1 2) :
    (m.write16 a1 v).read128 a2 = m.read128 a2 :=
  read128_write16_of_disjointRegions_l m a1 a2 v ⟨h.2, h.1⟩

@[simp, arm64_norm]
theorem read128_write32_of_disjointRegions_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h : DisjointRegions a1 4 a2 16) :
    (m.write32 a1 v).read128 a2 = m.read128 a2 := by
  simp only [Memory.read128,
    Memory.read64_write32_of_disjointRegions128_8_l m a1 a2 v h,
    Memory.read64_write32_of_disjointRegions128_0_l m a1 a2 v h]

@[simp, arm64_norm]
theorem read128_write32_of_disjointRegions_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 32)
    (h : DisjointRegions a2 16 a1 4) :
    (m.write32 a1 v).read128 a2 = m.read128 a2 :=
  read128_write32_of_disjointRegions_l m a1 a2 v ⟨h.2, h.1⟩

@[simp, arm64_norm]
theorem read128_write64_of_disjointRegions_l (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a1 8 a2 16) :
    (m.write64 a1 v).read128 a2 = m.read128 a2 := by
  simp only [Memory.read128,
    Memory.read64_write64_of_disjointRegions8_128_8_l m a1 a2 v h,
    Memory.read64_write64_of_disjointRegions8_128_0_l m a1 a2 v h]

@[simp, arm64_norm]
theorem read128_write64_of_disjointRegions_r (m : Memory) (a1 a2 : BitVec 64) (v : BitVec 64)
    (h : DisjointRegions a2 16 a1 8) :
    (m.write64 a1 v).read128 a2 = m.read128 a2 :=
  read128_write64_of_disjointRegions_l m a1 a2 v ⟨h.2, h.1⟩

/-- Low 64-bit slice of a 128-bit concatenation (`Memory.read128` followed by `Memory.write128`),
    preventing exponential duplication across unaligned SIMD spill/reload pairs (`STUR q` / `LDUR q`). -/
@[simp, arm64_norm]
theorem extractLsb_low64_append (hi lo : BitVec 64) :
    BitVec.extractLsb' 0 64 (hi ++ lo) = lo := by
  bv_decide

@[simp, arm64_norm]
theorem extractLsb_high64_append (hi lo : BitVec 64) :
    BitVec.extractLsb' 64 64 (hi ++ lo) = hi := by
  bv_decide

attribute [simp, arm64_norm]
  -- In-bounds sub-slice extraction across constant offsets
  Memory.read8_write16_base_off_inbounds
  Memory.read8_write16_base_off_zero_inbounds
  Memory.read8_write16_base_zero_off_inbounds
  Memory.read8_write32_base_off_inbounds
  Memory.read8_write32_base_off_zero_inbounds
  Memory.read8_write32_base_zero_off_inbounds
  Memory.read8_write64_base_off_inbounds
  Memory.read8_write64_base_off_zero_inbounds
  Memory.read8_write64_base_zero_off_inbounds
  Memory.read16_write32_base_off_inbounds
  Memory.read16_write32_base_off_zero_inbounds
  Memory.read16_write32_base_zero_off_inbounds
  Memory.read16_write64_base_off_inbounds
  Memory.read16_write64_base_off_zero_inbounds
  Memory.read16_write64_base_zero_off_inbounds
  Memory.read32_write64_base_off_inbounds
  Memory.read32_write64_base_off_zero_inbounds
  Memory.read32_write64_base_zero_off_inbounds
  -- Adjacent narrow writes read by wider load
  Memory.read16_write8_write8_adjacent
  Memory.read16_write8_write8_base_off_adjacent
  Memory.read32_write16_write16_adjacent
  Memory.read32_write16_write16_base_off_adjacent
  Memory.read64_write32_write32_adjacent
  Memory.read64_write32_write32_base_off_adjacent
  -- Constant-offset cross-width disjoint read-over-write (`{8, 16, 32, 64}` pairs)
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write16_base_off_disjoint
  Memory.read8_write16_base_zero_off
  Memory.read8_write16_base_off_zero
  Memory.read8_write32_base_off_disjoint
  Memory.read8_write32_base_zero_off
  Memory.read8_write32_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read16_write8_base_off_disjoint
  Memory.read16_write8_base_zero_off
  Memory.read16_write8_base_off_zero
  Memory.read16_write16_base_off_disjoint
  Memory.read16_write16_base_zero_off
  Memory.read16_write16_base_off_zero
  Memory.read16_write32_base_off_disjoint
  Memory.read16_write32_base_zero_off
  Memory.read16_write32_base_off_zero
  Memory.read16_write64_base_off_disjoint
  Memory.read16_write64_base_zero_off
  Memory.read16_write64_base_off_zero
  Memory.read32_write8_base_off_disjoint
  Memory.read32_write8_base_zero_off
  Memory.read32_write8_base_off_zero
  Memory.read32_write16_base_off_disjoint
  Memory.read32_write16_base_zero_off
  Memory.read32_write16_base_off_zero
  Memory.read32_write32_base_off_disjoint
  Memory.read32_write32_base_zero_off
  Memory.read32_write32_base_off_zero
  Memory.read32_write64_base_off_disjoint
  Memory.read32_write64_base_zero_off
  Memory.read32_write64_base_off_zero
  Memory.read64_write8_base_off_disjoint
  Memory.read64_write8_base_zero_off
  Memory.read64_write8_base_off_zero
  Memory.read64_write16_base_off_disjoint
  Memory.read64_write16_base_zero_off
  Memory.read64_write16_base_off_zero
  Memory.read64_write32_base_off_disjoint
  Memory.read64_write32_base_zero_off
  Memory.read64_write32_base_off_zero
  Memory.read64_write64_base_off_disjoint
  Memory.read64_write64_base_zero_off
  Memory.read64_write64_base_off_zero
  -- DisjointRegions cross-width read-over-write
  Memory.read8_write8_of_disjointRegions_left
  Memory.read8_write8_of_disjointRegions_right
  Memory.read8_write16_of_disjointRegions_left
  Memory.read8_write16_of_disjointRegions_right
  Memory.read8_write32_of_disjointRegions_left
  Memory.read8_write32_of_disjointRegions_right
  Memory.read8_write64_of_disjointRegions_left
  Memory.read8_write64_of_disjointRegions_right
  Memory.read16_write8_of_disjointRegions_left
  Memory.read16_write8_of_disjointRegions_right
  Memory.read16_write16_of_disjointRegions_left
  Memory.read16_write16_of_disjointRegions_right
  Memory.read16_write32_of_disjointRegions_left
  Memory.read16_write32_of_disjointRegions_right
  Memory.read16_write64_of_disjointRegions_left
  Memory.read16_write64_of_disjointRegions_right
  Memory.read32_write8_of_disjointRegions_left
  Memory.read32_write8_of_disjointRegions_right
  Memory.read32_write16_of_disjointRegions_left
  Memory.read32_write16_of_disjointRegions_right
  Memory.read32_write32_of_disjointRegions_left
  Memory.read32_write32_of_disjointRegions_right
  Memory.read32_write64_of_disjointRegions_left
  Memory.read32_write64_of_disjointRegions_right
  Memory.read64_write8_of_disjointRegions_left
  Memory.read64_write8_of_disjointRegions_right
  Memory.read64_write16_of_disjointRegions_left
  Memory.read64_write16_of_disjointRegions_right
  Memory.read64_write32_of_disjointRegions_left
  Memory.read64_write32_of_disjointRegions_right
  Memory.read8_write64_of_disjointRegions128_0_l
  Memory.read8_write64_of_disjointRegions128_0_r
  Memory.read8_write64_of_disjointRegions128_8_l
  Memory.read8_write64_of_disjointRegions128_8_r
  Memory.read16_write64_of_disjointRegions128_0_l
  Memory.read16_write64_of_disjointRegions128_0_r
  Memory.read16_write64_of_disjointRegions128_8_l
  Memory.read16_write64_of_disjointRegions128_8_r
  Memory.read32_write64_of_disjointRegions128_0_l
  Memory.read32_write64_of_disjointRegions128_0_r
  Memory.read32_write64_of_disjointRegions128_8_l
  Memory.read32_write64_of_disjointRegions128_8_r
  Memory.read64_write64_of_disjointRegions128_8_0_l
  Memory.read64_write64_of_disjointRegions128_8_0_r
  Memory.read64_write64_of_disjointRegions128_8_8_l
  Memory.read64_write64_of_disjointRegions128_8_8_r
  Memory.read64_write8_of_disjointRegions128_0_l
  Memory.read64_write8_of_disjointRegions128_0_r
  Memory.read64_write8_of_disjointRegions128_8_l
  Memory.read64_write8_of_disjointRegions128_8_r
  Memory.read64_write16_of_disjointRegions128_0_l
  Memory.read64_write16_of_disjointRegions128_0_r
  Memory.read64_write16_of_disjointRegions128_8_l
  Memory.read64_write16_of_disjointRegions128_8_r
  Memory.read64_write32_of_disjointRegions128_0_l
  Memory.read64_write32_of_disjointRegions128_0_r
  Memory.read64_write32_of_disjointRegions128_8_l
  Memory.read64_write32_of_disjointRegions128_8_r
  Memory.read64_write64_of_disjointRegions8_128_0_l
  Memory.read64_write64_of_disjointRegions8_128_0_r
  Memory.read64_write64_of_disjointRegions8_128_8_l
  Memory.read64_write64_of_disjointRegions8_128_8_r

@[simp, arm64_norm]
theorem bitvec_sub_add_cancel_64 (x k : BitVec 64) :
    (x - k) + k = x := by
  bv_arith

/-- Fold chained constant offsets `(x + a) + b = x + (a + b) % 2^64`, canonicalizing derived
    frame pointers and unaligned stack slot offsets (including negative `simm9` offsets represented
    as `2^64 - k`) into a single `base + offset` form.
    NOTE: Do NOT mark this theorem `@[simp]` or `@[arm64_norm]` directly; an unguarded rewrite rule
    fires on non-literal `Nat` terms (such as an irreducible `Program.fnOff`), producing
    `(a + b) % 18446744073709551616` on symbolic `Nat`s that later triggers unary `Nat.rec` unfolding.
    Use `reduceBitVecAddOfNat64` below, which checks `Lean.Nat.fromExpr?` on both operands first. -/
theorem bitvec_add_ofNat_add_ofNat_64 (x : BitVec 64) (a b : Nat) :
    (x + BitVec.ofNat 64 a) + BitVec.ofNat 64 b =
      x + BitVec.ofNat 64 ((a + b) % 18446744073709551616) := by
  bv_arith

end

public meta section

open Lean Meta Simp in
/-- Guarded simproc replacement for `bitvec_add_ofNat_add_ofNat_64`: only fires when both `a` and `b`
    are syntactic `Nat` numeral literals (`Lean.Nat.fromExpr?`). -/
def reduceBitVecAddOfNat64Core (e : Expr) : SimpM Simp.Step := do
  if !e.isAppOfArity ``HAdd.hAdd 6 then return .continue
  let lhs := e.getArg! 4
  let r2 := e.getArg! 5
  if !lhs.isAppOfArity ``HAdd.hAdd 6 then return .continue
  let x := lhs.getArg! 4
  let r1 := lhs.getArg! 5
  let some (w1, aExpr) := r1.app2? ``BitVec.ofNat | return .continue
  let some (w2, bExpr) := r2.app2? ``BitVec.ofNat | return .continue
  let some 64 ← Lean.Nat.fromExpr? w1 | return .continue
  let some 64 ← Lean.Nat.fromExpr? w2 | return .continue
  let some _ ← Lean.Nat.fromExpr? aExpr | return .continue
  let some _ ← Lean.Nat.fromExpr? bExpr | return .continue
  let prf ← Lean.Meta.mkAppM ``bitvec_add_ofNat_add_ofNat_64 #[x, aExpr, bExpr]
  let some (_, _, rhs) := (← Lean.Meta.inferType prf).eq? | return .continue
  return .visit { expr := rhs, proof? := some prf }

simproc ↓ [simp, arm64_norm, wp_norm] reduceBitVecAddOfNat64
    ((_ : BitVec 64) + BitVec.ofNat 64 _ + BitVec.ofNat 64 _) := reduceBitVecAddOfNat64Core

simproc [simp, arm64_norm, wp_norm] reduceBitVecAddOfNat64Post
    ((_ : BitVec 64) + BitVec.ofNat 64 _ + BitVec.ofNat 64 _) := reduceBitVecAddOfNat64Core

end

@[expose] public section

export Memory (read32_write64_disjoint read32_write64_base_off_disjoint
               read64_write32_disjoint read64_write32_base_off_disjoint)

@[simp, arm64_norm]
theorem State.setMem_setMem (s : State) (m1 m2 : Memory) :
    (s.setMem m1).setMem m2 = s.setMem m2 := by
  cases s; simp [State.setMem]

@[simp, arm64_norm]
theorem State.setMem_advancePC (s : State) (m : Memory) :
    (s.setMem m).advancePC = s.advancePC.setMem m := by
  cases s; simp [State.setMem, State.advancePC]

@[simp, arm64_norm]
theorem State.setMem_setPC (s : State) (m : Memory) (pc : BitVec 64) :
    (s.setMem m).setPC pc = (s.setPC pc).setMem m := by
  cases s; simp [State.setMem, State.setPC]

@[simp, arm64_norm]
theorem State.setMem_setPState (s : State) (m : Memory) (ps : PState) :
    (s.setMem m).setPState ps = (s.setPState ps).setMem m := by
  cases s; simp [State.setMem, State.setPState]

@[simp, arm64_norm]
theorem State.setMem_writeReg64 (s : State) (m : Memory) (r : Reg) (v : BitVec 64) :
    (s.setMem m).writeReg64 r v = (s.writeReg64 r v).setMem m := by
  cases s; cases r <;> simp [State.setMem, State.writeReg64]

@[simp, arm64_norm]
theorem State.setMem_writeVReg128 (s : State) (m : Memory) (r : BitVec 5) (v : BitVec 128) :
    (s.setMem m).writeVReg128 r v = (s.writeVReg128 r v).setMem m := by
  cases s; simp [State.setMem, State.writeVReg128]

/-! ## SIMD Lane Helpers -/

/-- The `esize`-bit lane mask (`(1 <<< esize) - 1`) used by the SIMD lane helpers. -/
def laneMask (esize : Nat) : BitVec 128 := (1#128 <<< esize) - 1#128

@[simp, arm64_norm] theorem laneMask_8 : laneMask 8 = 0xff#128 := by decide
@[simp, arm64_norm] theorem laneMask_16 : laneMask 16 = 0xffff#128 := by decide
@[simp, arm64_norm] theorem laneMask_32 : laneMask 32 = 0xffffffff#128 := by decide
@[simp, arm64_norm] theorem laneMask_64 : laneMask 64 = 0xffffffffffffffff#128 := by decide

/-- Structural-recursion unrolling of `Arm64.mapSimdLanes` over the low `n` lanes of `esize` bits,
    allowing `simp [arm64_norm]` to unroll SIMD lane operations when `f` is symbolic. -/
def mapLanes (esize : Nat) (v : BitVec 128) (f : BitVec 128 → BitVec 128) : Nat → BitVec 128
  | 0 => 0#128
  | n + 1 =>
    mapLanes esize v f n |||
      ((f ((v >>> (n * esize)) &&& laneMask esize)) &&& laneMask esize) <<< (n * esize)

/-- Structural-recursion unrolling of `Arm64.zipSimdLanes` over the low `n` lanes of `esize` bits. -/
def zipLanes (esize : Nat) (vn vm : BitVec 128) (f : BitVec 128 → BitVec 128 → BitVec 128) :
    Nat → BitVec 128
  | 0 => 0#128
  | n + 1 =>
    zipLanes esize vn vm f n |||
      ((f ((vn >>> (n * esize)) &&& laneMask esize) ((vm >>> (n * esize)) &&& laneMask esize)) &&&
        laneMask esize) <<< (n * esize)

attribute [arm64_norm] mapLanes zipLanes

macro "simd_lanes_simp" : tactic =>
  `(tactic| (simp only [mapSimdLanes, zipSimdLanes, Std.Legacy.Range.forIn_eq_forIn_range']; rfl))

@[simp, arm64_norm]
theorem mapSimdLanes_true_8 (v : BitVec 128) (f : BitVec 128 → BitVec 128) :
    mapSimdLanes true 8 v f = mapLanes 8 v f 16 := by simd_lanes_simp

@[simp, arm64_norm]
theorem mapSimdLanes_true_16 (v : BitVec 128) (f : BitVec 128 → BitVec 128) :
    mapSimdLanes true 16 v f = mapLanes 16 v f 8 := by simd_lanes_simp

@[simp, arm64_norm]
theorem mapSimdLanes_true_32 (v : BitVec 128) (f : BitVec 128 → BitVec 128) :
    mapSimdLanes true 32 v f = mapLanes 32 v f 4 := by simd_lanes_simp

@[simp, arm64_norm]
theorem mapSimdLanes_true_64 (v : BitVec 128) (f : BitVec 128 → BitVec 128) :
    mapSimdLanes true 64 v f = mapLanes 64 v f 2 := by simd_lanes_simp

@[simp, arm64_norm]
theorem mapSimdLanes_false_8 (v : BitVec 128) (f : BitVec 128 → BitVec 128) :
    mapSimdLanes false 8 v f = mapLanes 8 v f 8 := by simd_lanes_simp

@[simp, arm64_norm]
theorem mapSimdLanes_false_16 (v : BitVec 128) (f : BitVec 128 → BitVec 128) :
    mapSimdLanes false 16 v f = mapLanes 16 v f 4 := by simd_lanes_simp

@[simp, arm64_norm]
theorem mapSimdLanes_false_32 (v : BitVec 128) (f : BitVec 128 → BitVec 128) :
    mapSimdLanes false 32 v f = mapLanes 32 v f 2 := by simd_lanes_simp

@[simp, arm64_norm]
theorem mapSimdLanes_false_64 (v : BitVec 128) (f : BitVec 128 → BitVec 128) :
    mapSimdLanes false 64 v f = mapLanes 64 v f 1 := by simd_lanes_simp

@[simp, arm64_norm]
theorem zipSimdLanes_true_8 (vn vm : BitVec 128) (f : BitVec 128 → BitVec 128 → BitVec 128) :
    zipSimdLanes true 8 vn vm f = zipLanes 8 vn vm f 16 := by simd_lanes_simp

@[simp, arm64_norm]
theorem zipSimdLanes_true_16 (vn vm : BitVec 128) (f : BitVec 128 → BitVec 128 → BitVec 128) :
    zipSimdLanes true 16 vn vm f = zipLanes 16 vn vm f 8 := by simd_lanes_simp

@[simp, arm64_norm]
theorem zipSimdLanes_true_32 (vn vm : BitVec 128) (f : BitVec 128 → BitVec 128 → BitVec 128) :
    zipSimdLanes true 32 vn vm f = zipLanes 32 vn vm f 4 := by simd_lanes_simp

@[simp, arm64_norm]
theorem zipSimdLanes_true_64 (vn vm : BitVec 128) (f : BitVec 128 → BitVec 128 → BitVec 128) :
    zipSimdLanes true 64 vn vm f = zipLanes 64 vn vm f 2 := by simd_lanes_simp

@[simp, arm64_norm]
theorem zipSimdLanes_false_8 (vn vm : BitVec 128) (f : BitVec 128 → BitVec 128 → BitVec 128) :
    zipSimdLanes false 8 vn vm f = zipLanes 8 vn vm f 8 := by simd_lanes_simp

@[simp, arm64_norm]
theorem zipSimdLanes_false_16 (vn vm : BitVec 128) (f : BitVec 128 → BitVec 128 → BitVec 128) :
    zipSimdLanes false 16 vn vm f = zipLanes 16 vn vm f 4 := by simd_lanes_simp

@[simp, arm64_norm]
theorem zipSimdLanes_false_32 (vn vm : BitVec 128) (f : BitVec 128 → BitVec 128 → BitVec 128) :
    zipSimdLanes false 32 vn vm f = zipLanes 32 vn vm f 2 := by simd_lanes_simp

@[simp, arm64_norm]
theorem zipSimdLanes_false_64 (vn vm : BitVec 128) (f : BitVec 128 → BitVec 128 → BitVec 128) :
    zipSimdLanes false 64 vn vm f = zipLanes 64 vn vm f 1 := by simd_lanes_simp

/-! ## Calling-Convention and Callee-Saved Preservation -/

/-- True iff `r` is one of the AAPCS64 callee-saved GPRs `X19..X28` or `X29` (`fp`). -/
def isCalleeSavedReg : Reg → Bool
  | .gpr idx => decide (19 ≤ idx.toNat ∧ idx.toNat ≤ 29)
  | _ => false

/-- True iff `r` is `Reg.sp` or one of the AAPCS64 callee-saved GPRs `X19..X29`. -/
def isCalleeSavedOrSPReg : Reg → Bool
  | .sp => true
  | .gpr idx => decide (19 ≤ idx.toNat ∧ idx.toNat ≤ 29)
  | _ => false

theorem ne_callee_saved_of_isCalleeSavedReg_false {r : Reg} (h : isCalleeSavedReg r = false)
    (idx : BitVec 5) (h_lo : 19 ≤ idx.toNat) (h_hi : idx.toNat ≤ 29) :
    Reg.gpr idx ≠ r := by
  intro h_eq
  subst h_eq
  simp [isCalleeSavedReg, h_lo, h_hi] at h

theorem isCalleeSavedReg_false_of_isCalleeSavedOrSPReg_false {r : Reg} (h : isCalleeSavedOrSPReg r = false) :
    isCalleeSavedReg r = false := by
  cases r <;> simp_all [isCalleeSavedReg, isCalleeSavedOrSPReg]

theorem State.sp_writeReg64_of_isCalleeSavedOrSPReg_false (s : State) (r : Reg) (val : BitVec 64)
    (h : isCalleeSavedOrSPReg r = false := by decide) :
    (s.writeReg64 r val).sp = s.sp := by
  cases r with
  | sp => simp [isCalleeSavedOrSPReg] at h
  | xzr => simp [State.writeReg64_xzr]
  | gpr i => exact State.sp_writeReg64_gpr s i val

@[simp, arm64_norm]
theorem SubroutinePost_def {α : Type} (spec : Spec α) (x : α) (R : SepProp) (s0 sf : State) :
    SubroutinePost spec x R s0 sf = ((sf.mem ⊨ spec.post x s0 sf ∗ R) ∧ CallingConventionPreserved s0 sf) := by
  cases s0; rfl

@[simp, arm64_norm]
theorem CalleeSavedPreserved_advancePC (s0 s : State) :
    CalleeSavedPreserved s0 s.advancePC ↔ CalleeSavedPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_setPC (s0 s : State) (pc : BitVec 64) :
    CalleeSavedPreserved s0 (s.setPC pc) ↔ CalleeSavedPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_setMem (s0 s : State) (m : Memory) :
    CalleeSavedPreserved s0 (s.setMem m) ↔ CalleeSavedPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_setPState (s0 s : State) (ps : PState) :
    CalleeSavedPreserved s0 (s.setPState ps) ↔ CalleeSavedPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem calleeSavedVRegs_setTpidrEl0 (s : State) (val : BitVec 64) :
    calleeSavedVRegs (setTpidrEl0 s val) = calleeSavedVRegs s := by
  cases s; rfl

@[simp, arm64_norm]
theorem CalleeSavedVRegsPreserved_setTpidrEl0 (s0 s : State) (val : BitVec 64) :
    CalleeSavedVRegsPreserved s0 (setTpidrEl0 s val) ↔ CalleeSavedVRegsPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedVRegsPreserved_setTpidrEl0_left (s0 s : State) (val : BitVec 64) :
    CalleeSavedVRegsPreserved (setTpidrEl0 s0 val) s ↔ CalleeSavedVRegsPreserved s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm, wp_norm]
theorem CalleeSavedVRegsPreserved_setFpsr (s0 s : State) (f : BitVec 32) :
    CalleeSavedVRegsPreserved s0 (s.setFpsr f) ↔ CalleeSavedVRegsPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm, wp_norm]
theorem CalleeSavedVRegsPreserved_orFpsr (s0 s : State) (f : BitVec 32) :
    CalleeSavedVRegsPreserved s0 (s.orFpsr f) ↔ CalleeSavedVRegsPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm, wp_norm]
theorem CalleeSavedVRegsPreserved_setFpsr_left (s0 s : State) (f : BitVec 32) :
    CalleeSavedVRegsPreserved (s0.setFpsr f) s ↔ CalleeSavedVRegsPreserved s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm, wp_norm]
theorem CalleeSavedVRegsPreserved_orFpsr_left (s0 s : State) (f : BitVec 32) :
    CalleeSavedVRegsPreserved (s0.orFpsr f) s ↔ CalleeSavedVRegsPreserved s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_writeVReg128 (s0 s : State) (v : BitVec 5) (val : BitVec 128)
    (h : isCalleeSavedVReg v = false := by decide) :
    CalleeSavedPreserved s0 (s.writeVReg128 v val) ↔ CalleeSavedPreserved s0 s := by
  simp only [CalleeSavedPreserved, calleeSavedVRegs_writeVReg128 s v val h]
  cases s; rfl

@[simp, arm64_norm]
theorem CalleeSavedPreserved_writeVReg64 (s0 s : State) (v : BitVec 5) (val : BitVec 64)
    (h : isCalleeSavedVReg v = false := by decide) :
    CalleeSavedPreserved s0 (s.writeVReg64 v val) ↔ CalleeSavedPreserved s0 s :=
  CalleeSavedPreserved_writeVReg128 s0 s v (val.zeroExtend 128) h

@[simp, arm64_norm]
theorem CalleeSavedPreserved_writeVReg32 (s0 s : State) (v : BitVec 5) (val : BitVec 32)
    (h : isCalleeSavedVReg v = false := by decide) :
    CalleeSavedPreserved s0 (s.writeVReg32 v val) ↔ CalleeSavedPreserved s0 s :=
  CalleeSavedPreserved_writeVReg128 s0 s v (val.zeroExtend 128) h

@[simp, arm64_norm]
theorem CalleeSavedPreserved_setTpidrEl0 (s0 s : State) (val : BitVec 64) :
    CalleeSavedPreserved s0 (setTpidrEl0 s val) ↔ CalleeSavedPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm, wp_norm]
theorem CalleeSavedPreserved_setFpsr (s0 s : State) (f : BitVec 32) :
    CalleeSavedPreserved s0 (s.setFpsr f) ↔ CalleeSavedPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm, wp_norm]
theorem CalleeSavedPreserved_orFpsr (s0 s : State) (f : BitVec 32) :
    CalleeSavedPreserved s0 (s.orFpsr f) ↔ CalleeSavedPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_advancePC_left (s0 s : State) :
    CalleeSavedPreserved s0.advancePC s ↔ CalleeSavedPreserved s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_setPC_left (s0 s : State) (pc : BitVec 64) :
    CalleeSavedPreserved (s0.setPC pc) s ↔ CalleeSavedPreserved s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_setMem_left (s0 s : State) (m : Memory) :
    CalleeSavedPreserved (s0.setMem m) s ↔ CalleeSavedPreserved s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_setPState_left (s0 s : State) (ps : PState) :
    CalleeSavedPreserved (s0.setPState ps) s ↔ CalleeSavedPreserved s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_writeVReg128_left (s0 s : State) (v : BitVec 5) (val : BitVec 128)
    (h : isCalleeSavedVReg v = false := by decide) :
    CalleeSavedPreserved (s0.writeVReg128 v val) s ↔ CalleeSavedPreserved s0 s := by
  simp only [CalleeSavedPreserved, calleeSavedVRegs_writeVReg128 s0 v val h]
  cases s0; rfl

@[simp, arm64_norm]
theorem CalleeSavedPreserved_writeVReg64_left (s0 s : State) (v : BitVec 5) (val : BitVec 64)
    (h : isCalleeSavedVReg v = false := by decide) :
    CalleeSavedPreserved (s0.writeVReg64 v val) s ↔ CalleeSavedPreserved s0 s :=
  CalleeSavedPreserved_writeVReg128_left s0 s v (val.zeroExtend 128) h

@[simp, arm64_norm]
theorem CalleeSavedPreserved_writeVReg32_left (s0 s : State) (v : BitVec 5) (val : BitVec 32)
    (h : isCalleeSavedVReg v = false := by decide) :
    CalleeSavedPreserved (s0.writeVReg32 v val) s ↔ CalleeSavedPreserved s0 s :=
  CalleeSavedPreserved_writeVReg128_left s0 s v (val.zeroExtend 128) h

@[simp, arm64_norm]
theorem CalleeSavedPreserved_setTpidrEl0_left (s0 s : State) (val : BitVec 64) :
    CalleeSavedPreserved (setTpidrEl0 s0 val) s ↔ CalleeSavedPreserved s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm, wp_norm]
theorem CalleeSavedPreserved_setFpsr_left (s0 s : State) (f : BitVec 32) :
    CalleeSavedPreserved (s0.setFpsr f) s ↔ CalleeSavedPreserved s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm, wp_norm]
theorem CalleeSavedPreserved_orFpsr_left (s0 s : State) (f : BitVec 32) :
    CalleeSavedPreserved (s0.orFpsr f) s ↔ CalleeSavedPreserved s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm]
theorem CallingConventionPreserved_setTpidrEl0 (s0 s : State) (val : BitVec 64) :
    CallingConventionPreserved s0 (setTpidrEl0 s val) ↔ CallingConventionPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm, wp_norm]
theorem CallingConventionPreserved_setFpsr (s0 s : State) (f : BitVec 32) :
    CallingConventionPreserved s0 (s.setFpsr f) ↔ CallingConventionPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm, wp_norm]
theorem CallingConventionPreserved_orFpsr (s0 s : State) (f : BitVec 32) :
    CallingConventionPreserved s0 (s.orFpsr f) ↔ CallingConventionPreserved s0 s := by
  cases s; constructor <;> exact id

theorem readReg64_writeReg64_callee_saved (s : State) (r : Reg) (val : BitVec 64)
    (h : isCalleeSavedReg r = false) (idx : BitVec 5)
    (h_lo : 19 ≤ idx.toNat) (h_hi : idx.toNat ≤ 29) :
    (s.writeReg64 r val).readReg64 (.gpr idx) = s.readReg64 (.gpr idx) := by
  have hne := ne_callee_saved_of_isCalleeSavedReg_false h idx h_lo h_hi
  simp [State.readReg64_writeReg64, hne]

@[simp, arm64_norm]
theorem CalleeSavedPreserved_writeReg64_caller (s0 s : State) (r : Reg) (val : BitVec 64)
    (h : isCalleeSavedReg r = false := by decide) :
    CalleeSavedPreserved s0 (s.writeReg64 r val) ↔ CalleeSavedPreserved s0 s := by
  have h19 := readReg64_writeReg64_callee_saved s r val h 19#5 (by decide) (by decide)
  have h20 := readReg64_writeReg64_callee_saved s r val h 20#5 (by decide) (by decide)
  have h21 := readReg64_writeReg64_callee_saved s r val h 21#5 (by decide) (by decide)
  have h22 := readReg64_writeReg64_callee_saved s r val h 22#5 (by decide) (by decide)
  have h23 := readReg64_writeReg64_callee_saved s r val h 23#5 (by decide) (by decide)
  have h24 := readReg64_writeReg64_callee_saved s r val h 24#5 (by decide) (by decide)
  have h25 := readReg64_writeReg64_callee_saved s r val h 25#5 (by decide) (by decide)
  have h26 := readReg64_writeReg64_callee_saved s r val h 26#5 (by decide) (by decide)
  have h27 := readReg64_writeReg64_callee_saved s r val h 27#5 (by decide) (by decide)
  have h28 := readReg64_writeReg64_callee_saved s r val h 28#5 (by decide) (by decide)
  have h29 := readReg64_writeReg64_callee_saved s r val h 29#5 (by decide) (by decide)
  dsimp [CalleeSavedPreserved]
  rw [h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
  cases s; rfl

@[simp, arm64_norm]
theorem CalleeSavedPreserved_writeReg32_caller (s0 s : State) (r : Reg) (val : BitVec 32)
    (h : isCalleeSavedReg r = false := by decide) :
    CalleeSavedPreserved s0 (s.writeReg32 r val) ↔ CalleeSavedPreserved s0 s :=
  CalleeSavedPreserved_writeReg64_caller s0 s r (val.zeroExtend 64) h

@[simp, arm64_norm]
theorem CalleeSavedPreserved_writeReg_caller (s0 s : State) (w : Width) (r : Reg) (val : BitVec 64)
    (h : isCalleeSavedReg r = false := by decide) :
    CalleeSavedPreserved s0 (s.writeReg w r val) ↔ CalleeSavedPreserved s0 s := by
  cases w <;> simp [State.writeReg, CalleeSavedPreserved_writeReg64_caller, h]

@[simp, arm64_norm]
theorem CalleeSavedPreserved_writeReg64_caller_left (s0 s : State) (r : Reg) (val : BitVec 64)
    (h : isCalleeSavedReg r = false := by decide) :
    CalleeSavedPreserved (s0.writeReg64 r val) s ↔ CalleeSavedPreserved s0 s := by
  have h19 := readReg64_writeReg64_callee_saved s0 r val h 19#5 (by decide) (by decide)
  have h20 := readReg64_writeReg64_callee_saved s0 r val h 20#5 (by decide) (by decide)
  have h21 := readReg64_writeReg64_callee_saved s0 r val h 21#5 (by decide) (by decide)
  have h22 := readReg64_writeReg64_callee_saved s0 r val h 22#5 (by decide) (by decide)
  have h23 := readReg64_writeReg64_callee_saved s0 r val h 23#5 (by decide) (by decide)
  have h24 := readReg64_writeReg64_callee_saved s0 r val h 24#5 (by decide) (by decide)
  have h25 := readReg64_writeReg64_callee_saved s0 r val h 25#5 (by decide) (by decide)
  have h26 := readReg64_writeReg64_callee_saved s0 r val h 26#5 (by decide) (by decide)
  have h27 := readReg64_writeReg64_callee_saved s0 r val h 27#5 (by decide) (by decide)
  have h28 := readReg64_writeReg64_callee_saved s0 r val h 28#5 (by decide) (by decide)
  have h29 := readReg64_writeReg64_callee_saved s0 r val h 29#5 (by decide) (by decide)
  dsimp [CalleeSavedPreserved]
  rw [h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29]
  cases s0; rfl

@[simp, arm64_norm]
theorem CalleeSavedPreserved_writeReg32_caller_left (s0 s : State) (r : Reg) (val : BitVec 32)
    (h : isCalleeSavedReg r = false := by decide) :
    CalleeSavedPreserved (s0.writeReg32 r val) s ↔ CalleeSavedPreserved s0 s :=
  CalleeSavedPreserved_writeReg64_caller_left s0 s r (val.zeroExtend 64) h

@[simp, arm64_norm]
theorem CalleeSavedPreserved_writeReg_caller_left (s0 s : State) (w : Width) (r : Reg) (val : BitVec 64)
    (h : isCalleeSavedReg r = false := by decide) :
    CalleeSavedPreserved (s0.writeReg w r val) s ↔ CalleeSavedPreserved s0 s := by
  cases w <;> simp [State.writeReg, CalleeSavedPreserved_writeReg64_caller_left, h]

theorem _root_.Arm64.CalleeSavedPreserved.restore {s0 s0' s1 s2 : State} {r : Reg} {v : BitVec 64}
    (hcs : CalleeSavedPreserved (s0'.writeReg64 r v) s1)
    (h0 : CalleeSavedPreserved s0 s0' := by simp (config := { decide := true }) only [arm64_norm])
    (h12 : CalleeSavedPreserved s1 s2 := by simp (config := { decide := true }) only [arm64_norm]) :
    CalleeSavedPreserved s0 (s2.writeReg64 r (s0.readReg64 r)) := by
  have hreg : ∀ (idx : BitVec 5), idx ≠ 31#5 →
      s0'.readReg64 (.gpr idx) = s0.readReg64 (.gpr idx) →
      s1.readReg64 (.gpr idx) = (s0'.writeReg64 r v).readReg64 (.gpr idx) →
      s2.readReg64 (.gpr idx) = s1.readReg64 (.gpr idx) →
      (s2.writeReg64 r (s0.readReg64 r)).readReg64 (.gpr idx) = s0.readReg64 (.gpr idx) := by
    intro idx hne31 h0_idx hcs_idx h12_idx
    rcases r with idx_r | _ | _
    · by_cases heq : idx = idx_r
      · subst heq; simp [State.readReg64_writeReg64, hne31]
      · simp [State.readReg64_writeReg64, heq] at hcs_idx ⊢; rw [h12_idx, hcs_idx, h0_idx]
    · simp [State.readReg64_writeReg64] at hcs_idx ⊢; rw [h12_idx, hcs_idx, h0_idx]
    · simp [State.writeReg64_xzr] at hcs_idx ⊢; rw [h12_idx, hcs_idx, h0_idx]
  rcases h0 with ⟨a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, av⟩
  rcases hcs with ⟨b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, bv⟩
  rcases h12 with ⟨c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, cv⟩
  exact ⟨hreg 19#5 (by decide) a19 b19 c19, hreg 20#5 (by decide) a20 b20 c20,
         hreg 21#5 (by decide) a21 b21 c21, hreg 22#5 (by decide) a22 b22 c22,
         hreg 23#5 (by decide) a23 b23 c23, hreg 24#5 (by decide) a24 b24 c24,
         hreg 25#5 (by decide) a25 b25 c25, hreg 26#5 (by decide) a26 b26 c26,
         hreg 27#5 (by decide) a27 b27 c27, hreg 28#5 (by decide) a28 b28 c28,
         hreg 29#5 (by decide) a29 b29 c29,
         by simpa [calleeSavedVRegs_writeReg64] using Eq.trans cv (Eq.trans (by simpa [calleeSavedVRegs_writeReg64] using bv) av)⟩

@[simp, arm64_norm]
theorem CallingConventionPreserved_advancePC (s0 s : State) :
    CallingConventionPreserved s0 s.advancePC ↔ CallingConventionPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CallingConventionPreserved_setPC (s0 s : State) (pc : BitVec 64) :
    CallingConventionPreserved s0 (s.setPC pc) ↔ CallingConventionPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CallingConventionPreserved_setMem (s0 s : State) (m : Memory) :
    CallingConventionPreserved s0 (s.setMem m) ↔ CallingConventionPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CallingConventionPreserved_setPState (s0 s : State) (ps : PState) :
    CallingConventionPreserved s0 (s.setPState ps) ↔ CallingConventionPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_setSigAction (s0 s : State) (signum : BitVec 32) (act : SigAction) :
    CalleeSavedPreserved s0 (s.setSigAction signum act) ↔ CalleeSavedPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CallingConventionPreserved_setSigAction (s0 s : State) (signum : BitVec 32) (act : SigAction) :
    CallingConventionPreserved s0 (s.setSigAction signum act) ↔ CallingConventionPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm, wp_norm]
theorem CalleeSavedPreserved_setSigAltStack (s0 s : State) (sas : SigAltStack) :
    CalleeSavedPreserved s0 (s.setSigAltStack sas) ↔ CalleeSavedPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm, wp_norm]
theorem CalleeSavedPreserved_setSigAltStack_left (s0 s : State) (sas : SigAltStack) :
    CalleeSavedPreserved (s0.setSigAltStack sas) s ↔ CalleeSavedPreserved s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm, wp_norm]
theorem CallingConventionPreserved_setSigAltStack (s0 s : State) (sas : SigAltStack) :
    CallingConventionPreserved s0 (s.setSigAltStack sas) ↔ CallingConventionPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm, wp_norm]
theorem CallingConventionPreserved_setSigAltStack_left (s0 s : State) (sas : SigAltStack) :
    CallingConventionPreserved (s0.setSigAltStack sas) s ↔ CallingConventionPreserved s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm, wp_norm]
theorem Returned_setSigAltStack (s0 s : State) (sas : SigAltStack) :
    Returned s0 (s.setSigAltStack sas) ↔ Returned s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm, wp_norm]
theorem Returned_setSigAltStack_left (s0 s : State) (sas : SigAltStack) :
    Returned (s0.setSigAltStack sas) s ↔ Returned s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm]
theorem CallingConventionPreserved_writeVReg128 (s0 s : State) (v : BitVec 5) (val : BitVec 128)
    (h : isCalleeSavedVReg v = false := by decide) :
    CallingConventionPreserved s0 (s.writeVReg128 v val) ↔ CallingConventionPreserved s0 s := by
  have hv := CalleeSavedPreserved_writeVReg128 s0 s v val h
  dsimp [CallingConventionPreserved]
  rw [hv]
  cases s; rfl

@[simp, arm64_norm]
theorem CallingConventionPreserved_writeVReg64 (s0 s : State) (v : BitVec 5) (val : BitVec 64)
    (h : isCalleeSavedVReg v = false := by decide) :
    CallingConventionPreserved s0 (s.writeVReg64 v val) ↔ CallingConventionPreserved s0 s :=
  CallingConventionPreserved_writeVReg128 s0 s v (val.zeroExtend 128) h

@[simp, arm64_norm]
theorem CallingConventionPreserved_writeVReg32 (s0 s : State) (v : BitVec 5) (val : BitVec 32)
    (h : isCalleeSavedVReg v = false := by decide) :
    CallingConventionPreserved s0 (s.writeVReg32 v val) ↔ CallingConventionPreserved s0 s :=
  CallingConventionPreserved_writeVReg128 s0 s v (val.zeroExtend 128) h

@[simp, arm64_norm]
theorem CallingConventionPreserved_writeReg64_caller (s0 s : State)
    (r : Reg) (val : BitVec 64) (h : isCalleeSavedOrSPReg r = false := by decide) :
    CallingConventionPreserved s0 (s.writeReg64 r val) ↔ CallingConventionPreserved s0 s := by
  have hsp := State.sp_writeReg64_of_isCalleeSavedOrSPReg_false s r val h
  have hcs := CalleeSavedPreserved_writeReg64_caller s0 s r val (isCalleeSavedReg_false_of_isCalleeSavedOrSPReg_false h)
  dsimp [CallingConventionPreserved]
  rw [hsp, hcs]

@[simp, arm64_norm]
theorem CallingConventionPreserved_writeReg32_caller (s0 s : State)
    (r : Reg) (val : BitVec 32) (h : isCalleeSavedOrSPReg r = false := by decide) :
    CallingConventionPreserved s0 (s.writeReg32 r val) ↔ CallingConventionPreserved s0 s :=
  CallingConventionPreserved_writeReg64_caller s0 s r (val.zeroExtend 64) h

@[simp, arm64_norm]
theorem CallingConventionPreserved_writeReg_caller (s0 s : State)
    (w : Width) (r : Reg) (val : BitVec 64) (h : isCalleeSavedOrSPReg r = false := by decide) :
    CallingConventionPreserved s0 (s.writeReg w r val) ↔ CallingConventionPreserved s0 s := by
  cases w <;> simp [State.writeReg, CallingConventionPreserved_writeReg64_caller, h]

/-! ## Linux AArch64 Syscall Dispatch and State Framing -/

attribute [arm64_norm]
  execInstWithSvc

attribute [simp, arm64_norm]
  SYS_READ SYS_WRITE SYS_READV SYS_WRITEV SYS_EXIT SYS_EXIT_GROUP
  SYS_FCNTL SYS_IOCTL SYS_OPENAT SYS_CLOSE SYS_LSEEK SYS_PREAD64 SYS_FSTAT
  SYS_PPOLL
  SYS_BRK SYS_MUNMAP SYS_MREMAP SYS_MMAP SYS_MPROTECT SYS_MADVISE
  SYS_TKILL SYS_TGKILL SYS_SIGALTSTACK SYS_RT_SIGACTION SYS_RT_SIGPROCMASK
  SYS_CLOCK_GETTIME SYS_GETRANDOM
  SYS_SET_TID_ADDRESS SYS_SCHED_GETAFFINITY SYS_GETPID SYS_GETTID

@[simp, arm64_norm]
theorem execInstWithSvc_svc0 (svc : State → State) (s : State) :
    execInstWithSvc svc (.system false 0#16) s = svc s := by
  cases s; rfl

@[simp, arm64_norm]
theorem execInst_svc0 (s : State) :
    execInst (.system false 0#16) s = execSyscall s := by
  cases s; rfl

@[simp, arm64_norm]
theorem dispatch_nil (s : State) :
    Syscall.dispatch [] s = s.setStatus (.Exception "unmodeled syscall (svc)") := by
  cases s; rfl

@[simp, arm64_norm]
theorem dispatch_cons_eq (nr : BitVec 64) (fn : State → State)
    (rest : List (BitVec 64 × (State → State))) (s : State)
    (h : s.readReg64 .x8 = nr) :
    Syscall.dispatch ((nr, fn) :: rest) s = fn s := by
  simp [Syscall.dispatch, h]

@[simp, arm64_norm]
theorem dispatch_cons_ne (nr : BitVec 64) (fn : State → State)
    (rest : List (BitVec 64 × (State → State))) (s : State)
    (h : s.readReg64 .x8 ≠ nr) :
    Syscall.dispatch ((nr, fn) :: rest) s = Syscall.dispatch rest s := by
  have hbeq : (nr == s.readReg64 .x8) = false := beq_false_of_ne h.symm
  simp [Syscall.dispatch, hbeq]

local macro "prove_execSyscall_nr" : tactic =>
  `(tactic| (
    simp [execSyscall, Syscall.standard, Syscall.standardTable,
      Syscall.stdioTable, Syscall.fileIoOnlyTable, Syscall.pollTable, Syscall.allocTable,
      Syscall.signalsTable, Syscall.timeTable, Syscall.randomTable, Syscall.miscTable,
      execRead, execPread64, execExit,
      SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, SYS_EXIT, SYS_EXIT_GROUP,
      SYS_FCNTL, SYS_IOCTL, SYS_OPENAT, SYS_CLOSE, SYS_LSEEK,
      SYS_PREAD64, SYS_FSTAT, SYS_PPOLL,
      SYS_BRK, SYS_MUNMAP, SYS_MREMAP, SYS_MMAP, SYS_MPROTECT, SYS_MADVISE,
      SYS_SIGALTSTACK, SYS_RT_SIGACTION, SYS_RT_SIGPROCMASK, SYS_TKILL, SYS_TGKILL,
      SYS_CLOCK_GETTIME, SYS_GETRANDOM,
      SYS_SET_TID_ADDRESS, SYS_SCHED_GETAFFINITY, SYS_GETPID, SYS_GETTID, *]))

@[simp, arm64_norm]
theorem execSyscall_fcntl (s : State) (h : s.readReg64 .x8 = 25#64) :
    execSyscall s = execFcntl s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_ioctl (s : State) (h : s.readReg64 .x8 = 29#64) :
    execSyscall s = execIoctl s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_openat (s : State) (h : s.readReg64 .x8 = 56#64) :
    execSyscall s = execOpenat s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_close (s : State) (h : s.readReg64 .x8 = 57#64) :
    execSyscall s = execClose s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_lseek (s : State) (h : s.readReg64 .x8 = 62#64) :
    execSyscall s = execLseek s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_read (s : State) (h : s.readReg64 .x8 = 63#64) :
    execSyscall s = execReadCommon s false := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_write (s : State) (h : s.readReg64 .x8 = 64#64) :
    execSyscall s = execWrite s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_readv (s : State) (h : s.readReg64 .x8 = 65#64) :
    execSyscall s = execReadv s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_writev (s : State) (h : s.readReg64 .x8 = 66#64) :
    execSyscall s = execWritev s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem stdioCli_readv (s : State) (h : s.readReg64 .x8 = 65#64) :
    Syscall.stdioCli s = execReadv s := by
  simp [Syscall.stdioCli, Syscall.stdioTable, SYS_READ, SYS_WRITE, SYS_READV, h]

@[simp, arm64_norm]
theorem stdioCli_writev (s : State) (h : s.readReg64 .x8 = 66#64) :
    Syscall.stdioCli s = execWritev s := by
  simp [Syscall.stdioCli, Syscall.stdioTable, SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, h]

@[simp, arm64_norm]
theorem fileIo_readv (s : State) (h : s.readReg64 .x8 = 65#64) :
    Syscall.fileIo s = execReadv s := by
  simp [Syscall.fileIo, Syscall.fileIoTable, Syscall.stdioTable, SYS_READ, SYS_WRITE, SYS_READV, h]

@[simp, arm64_norm]
theorem fileIo_writev (s : State) (h : s.readReg64 .x8 = 66#64) :
    Syscall.fileIo s = execWritev s := by
  simp [Syscall.fileIo, Syscall.fileIoTable, Syscall.stdioTable,
    SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, h]

@[simp, arm64_norm]
theorem stdioWrite_write (s : State) (h : s.readReg64 .x8 = 64#64) :
    Syscall.stdioWrite s = execWrite s := by
  simp [Syscall.stdioWrite, Syscall.stdioWriteTable, SYS_WRITE, h]

@[simp, arm64_norm]
theorem stdioCli_read (s : State) (h : s.readReg64 .x8 = 63#64) :
    Syscall.stdioCli s = execReadCommon s false := by
  simp [Syscall.stdioCli, Syscall.stdioTable, SYS_READ, execRead, h]

@[simp, arm64_norm]
theorem stdioCli_write (s : State) (h : s.readReg64 .x8 = 64#64) :
    Syscall.stdioCli s = execWrite s := by
  simp [Syscall.stdioCli, Syscall.stdioTable, SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, h]

@[simp, arm64_norm]
theorem stdioCli_exit (s : State) (h : s.readReg64 .x8 = 93#64) :
    Syscall.stdioCli s = execExit s := by
  simp [Syscall.stdioCli, Syscall.stdioTable, SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, SYS_EXIT, h]

@[simp, arm64_norm]
theorem stdioCli_exit_group (s : State) (h : s.readReg64 .x8 = 94#64) :
    Syscall.stdioCli s = execExit s := by
  simp [Syscall.stdioCli, Syscall.stdioTable, SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, SYS_EXIT, SYS_EXIT_GROUP, h]

@[simp, arm64_norm]
theorem fileIo_fcntl (s : State) (h : s.readReg64 .x8 = 25#64) :
    Syscall.fileIo s = execFcntl s := by
  simp [Syscall.fileIo, Syscall.fileIoTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, SYS_EXIT, SYS_EXIT_GROUP, SYS_FCNTL, h]

@[simp, arm64_norm]
theorem fileIo_ioctl (s : State) (h : s.readReg64 .x8 = 29#64) :
    Syscall.fileIo s = execIoctl s := by
  simp [Syscall.fileIo, Syscall.fileIoTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, SYS_EXIT, SYS_EXIT_GROUP, SYS_FCNTL, SYS_IOCTL, h]

@[simp, arm64_norm]
theorem fileIo_openat (s : State) (h : s.readReg64 .x8 = 56#64) :
    Syscall.fileIo s = execOpenat s := by
  simp [Syscall.fileIo, Syscall.fileIoTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, SYS_EXIT, SYS_EXIT_GROUP, SYS_FCNTL, SYS_IOCTL, SYS_OPENAT, h]

@[simp, arm64_norm]
theorem fileIo_close (s : State) (h : s.readReg64 .x8 = 57#64) :
    Syscall.fileIo s = execClose s := by
  simp [Syscall.fileIo, Syscall.fileIoTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, SYS_EXIT, SYS_EXIT_GROUP, SYS_FCNTL, SYS_IOCTL, SYS_OPENAT, SYS_CLOSE, h]

@[simp, arm64_norm]
theorem fileIo_lseek (s : State) (h : s.readReg64 .x8 = 62#64) :
    Syscall.fileIo s = execLseek s := by
  simp [Syscall.fileIo, Syscall.fileIoTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, SYS_EXIT, SYS_EXIT_GROUP, SYS_FCNTL, SYS_IOCTL, SYS_OPENAT, SYS_CLOSE,
    SYS_LSEEK, h]

@[simp, arm64_norm]
theorem fileIo_read (s : State) (h : s.readReg64 .x8 = 63#64) :
    Syscall.fileIo s = execReadCommon s false := by
  simp [Syscall.fileIo, Syscall.fileIoTable, Syscall.stdioTable, SYS_READ, execRead, h]

@[simp, arm64_norm]
theorem fileIo_write (s : State) (h : s.readReg64 .x8 = 64#64) :
    Syscall.fileIo s = execWrite s := by
  simp [Syscall.fileIo, Syscall.fileIoTable, Syscall.stdioTable, SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, h]

@[simp, arm64_norm]
theorem fileIo_pread64 (s : State) (h : s.readReg64 .x8 = 67#64) :
    Syscall.fileIo s = execReadCommon s true := by
  simp [Syscall.fileIo, Syscall.fileIoTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, SYS_EXIT, SYS_EXIT_GROUP, SYS_FCNTL, SYS_IOCTL, SYS_OPENAT, SYS_CLOSE,
    SYS_LSEEK, SYS_PREAD64, execPread64, h]

@[simp, arm64_norm]
theorem fileIo_fstat (s : State) (h : s.readReg64 .x8 = 80#64) :
    Syscall.fileIo s = execFstat s := by
  simp [Syscall.fileIo, Syscall.fileIoTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, SYS_EXIT, SYS_EXIT_GROUP, SYS_FCNTL, SYS_IOCTL, SYS_OPENAT, SYS_CLOSE,
    SYS_LSEEK, SYS_PREAD64, SYS_FSTAT, h]

@[simp, arm64_norm]
theorem fileIo_exit (s : State) (h : s.readReg64 .x8 = 93#64) :
    Syscall.fileIo s = execExit s := by
  simp [Syscall.fileIo, Syscall.fileIoTable, Syscall.stdioTable,
    SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, SYS_EXIT, h]

@[simp, arm64_norm]
theorem fileIo_exit_group (s : State) (h : s.readReg64 .x8 = 94#64) :
    Syscall.fileIo s = execExit s := by
  simp [Syscall.fileIo, Syscall.fileIoTable, Syscall.stdioTable,
    SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, SYS_EXIT, SYS_EXIT_GROUP, h]

@[simp, arm64_norm]
theorem alloc_brk (s : State) (h : s.readReg64 .x8 = 214#64) :
    Syscall.alloc s = execBrk s := by
  simp [Syscall.alloc, Syscall.allocTable, SYS_BRK, h]

@[simp, arm64_norm]
theorem poll_ppoll (s : State) (h : s.readReg64 .x8 = 73#64) :
    Syscall.poll s = execPpoll s := by
  simp [Syscall.poll, Syscall.pollTable, SYS_PPOLL, h]

@[simp, arm64_norm]
theorem alloc_munmap (s : State) (h : s.readReg64 .x8 = 215#64) :
    Syscall.alloc s = execMunmap s := by
  simp [Syscall.alloc, Syscall.allocTable, SYS_BRK, SYS_MUNMAP, h]

@[simp, arm64_norm]
theorem alloc_mremap (s : State) (h : s.readReg64 .x8 = 216#64) :
    Syscall.alloc s = execMremap s := by
  simp [Syscall.alloc, Syscall.allocTable, SYS_BRK, SYS_MUNMAP, SYS_MREMAP, h]

@[simp, arm64_norm]
theorem alloc_mmap (s : State) (h : s.readReg64 .x8 = 222#64) :
    Syscall.alloc s = execMmap s := by
  simp [Syscall.alloc, Syscall.allocTable, SYS_BRK, SYS_MUNMAP, SYS_MREMAP, SYS_MMAP, h]

@[simp, arm64_norm]
theorem alloc_mprotect (s : State) (h : s.readReg64 .x8 = 226#64) :
    Syscall.alloc s = execMprotect s := by
  simp [Syscall.alloc, Syscall.allocTable, SYS_BRK, SYS_MUNMAP, SYS_MREMAP, SYS_MMAP, SYS_MPROTECT, h]

@[simp, arm64_norm]
theorem alloc_madvise (s : State) (h : s.readReg64 .x8 = 233#64) :
    Syscall.alloc s = execMadvise s := by
  simp [Syscall.alloc, Syscall.allocTable, SYS_BRK, SYS_MUNMAP, SYS_MREMAP, SYS_MMAP, SYS_MPROTECT,
    SYS_MADVISE, h]

@[simp, arm64_norm]
theorem time_clock_gettime (s : State) (h : s.readReg64 .x8 = 113#64) :
    Syscall.time s = execClockGettime s := by
  simp [Syscall.time, Syscall.timeTable, SYS_CLOCK_GETTIME, h]

@[simp, arm64_norm]
theorem execWrite_stdout (s : State) (hfd : s.readReg64 .x0 = 1#64) :
    execWrite s =
      let buf := s.readReg64 .x1
      let count := s.readReg64 .x2
      if decide (buf.toNat + count.toNat > USER_VA_LIMIT) then
        (s.writeReg64 .x0 EFAULT_RET).advancePC
      else if count == 0#64 then
        (s.writeReg64 .x0 0#64).advancePC
      else
        let count' := min count.toNat MAX_RW_COUNT
        if s.mem.canRead buf count' then
          let events := TraceEvent.ofBytes .stdout (s.mem.readBytes buf count')
          ((s.appendTrace events).writeReg64 .x0 (BitVec.ofNat 64 count')).advancePC
        else if !s.mem.allPerm (·.r) buf 1 then
          (s.writeReg64 .x0 EFAULT_RET).advancePC
        else if !s.mem.allPerm (·.r) buf count' then
          s.setStatus (.Exception "unmodeled partial-fault short write")
        else
          s.setStatus (.Exception "write from lazy-free memory") := by
  simp [execWrite, State.readReg32, OutputStream.ofFd, hfd]

@[simp, arm64_norm]
theorem execWrite_stderr (s : State) (hfd : s.readReg64 .x0 = 2#64) :
    execWrite s =
      let buf := s.readReg64 .x1
      let count := s.readReg64 .x2
      if decide (buf.toNat + count.toNat > USER_VA_LIMIT) then
        (s.writeReg64 .x0 EFAULT_RET).advancePC
      else if count == 0#64 then
        (s.writeReg64 .x0 0#64).advancePC
      else
        let count' := min count.toNat MAX_RW_COUNT
        if s.mem.canRead buf count' then
          let events := TraceEvent.ofBytes .stderr (s.mem.readBytes buf count')
          ((s.appendTrace events).writeReg64 .x0 (BitVec.ofNat 64 count')).advancePC
        else if !s.mem.allPerm (·.r) buf 1 then
          (s.writeReg64 .x0 EFAULT_RET).advancePC
        else if !s.mem.allPerm (·.r) buf count' then
          s.setStatus (.Exception "unmodeled partial-fault short write")
        else
          s.setStatus (.Exception "write from lazy-free memory") := by
  simp [execWrite, State.readReg32, OutputStream.ofFd, hfd]

@[simp, arm64_norm]
theorem execSyscall_pread64 (s : State) (h : s.readReg64 .x8 = 67#64) :
    execSyscall s = execReadCommon s true := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_fstat (s : State) (h : s.readReg64 .x8 = 80#64) :
    execSyscall s = execFstat s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_set_tid_address (s : State) (h : s.readReg64 .x8 = 96#64) :
    execSyscall s = execSetTidAddress s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_clock_gettime (s : State) (h : s.readReg64 .x8 = 113#64) :
    execSyscall s = execClockGettime s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_sched_getaffinity (s : State) (h : s.readReg64 .x8 = 123#64) :
    execSyscall s = execSchedGetaffinity s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_tkill (s : State) (h : s.readReg64 .x8 = 130#64) :
    execSyscall s = execTkill s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_tgkill (s : State) (h : s.readReg64 .x8 = 131#64) :
    execSyscall s = execTgkill s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_sigaltstack (s : State) (h : s.readReg64 .x8 = 132#64) :
    execSyscall s = execSigaltstack s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_rt_sigaction (s : State) (h : s.readReg64 .x8 = 134#64) :
    execSyscall s = execRtSigaction s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_rt_sigprocmask (s : State) (h : s.readReg64 .x8 = 135#64) :
    execSyscall s = execRtSigprocmask s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_getpid (s : State) (h : s.readReg64 .x8 = 172#64) :
    execSyscall s = execGetpid s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_gettid (s : State) (h : s.readReg64 .x8 = 178#64) :
    execSyscall s = execGetpid s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem encodeTimespec_length (ts : Timespec) : (encodeTimespec ts).length = 16 := rfl

@[simp, arm64_norm]
theorem Timespec.toNat_nsec_ofNat (ts : Timespec) :
    (BitVec.ofNat 64 ts.nsec.val).toNat = ts.nsec.val :=
  Nat.mod_eq_of_lt (Nat.lt_trans ts.nsec.isLt (by decide))

theorem Timespec.toNat_nsec_ofNat_lt (ts : Timespec) :
    (BitVec.ofNat 64 ts.nsec.val).toNat < 1000000000 := by
  rw [Timespec.toNat_nsec_ofNat]
  exact ts.nsec.isLt

@[simp, arm64_norm]
theorem execClockGettime_ok (s : State)
    (hclk : (s.readReg32 .x0).toNat ≤ 7)
    (hcw : s.mem.canWrite (s.readReg64 .x1) 16 = true) :
    execClockGettime s =
      let tp := s.readReg64 .x1
      let ts := s.oracle.clockGettime s.oracleIdx
      (((s.setMem (s.mem.writeBytes tp (encodeTimespec ts))).nextOracle).writeReg64
        .x0 0#64).advancePC := by
  unfold execClockGettime
  have hnot : ¬((s.readReg32 .x0).toNat > 7) := by omega
  simp [hnot, hcw]

@[simp, arm64_norm]
theorem execSyscall_brk (s : State) (h : s.readReg64 .x8 = 214#64) :
    execSyscall s = execBrk s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_ppoll (s : State) (h : s.readReg64 .x8 = 73#64) :
    execSyscall s = execPpoll s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_munmap (s : State) (h : s.readReg64 .x8 = 215#64) :
    execSyscall s = execMunmap s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_mremap (s : State) (h : s.readReg64 .x8 = 216#64) :
    execSyscall s = execMremap s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_mmap (s : State) (h : s.readReg64 .x8 = 222#64) :
    execSyscall s = execMmap s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_mprotect (s : State) (h : s.readReg64 .x8 = 226#64) :
    execSyscall s = execMprotect s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_madvise (s : State) (h : s.readReg64 .x8 = 233#64) :
    execSyscall s = execMadvise s := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_getrandom (s : State) (h : s.readReg64 .x8 = 278#64) :
    execSyscall s =
      let buf := s.readReg64 .x0
      let count := s.readReg64 .x1
      let flags := s.readReg32 .x2
      if (flags &&& ~~~GRND_KNOWN_MASK) != 0#32 ||
          (flags &&& (GRND_RANDOM ||| GRND_INSECURE)) == (GRND_RANDOM ||| GRND_INSECURE) ||
          count.toNat > MAX_RW_COUNT then
        (s.writeReg64 .x0 (-EINVAL)).advancePC
      else if !s.mem.canWrite buf count.toNat then
        (s.writeReg64 .x0 EFAULT_RET).advancePC
      else
        let bytes := (List.range count.toNat).map (s.oracle.getrandom s.oracleIdx)
        (((s.setMem (s.mem.writeBytes buf bytes)).nextOracle).writeReg64 .x0 count).advancePC := by
  have heq : execSyscall s = execGetrandom s := by prove_execSyscall_nr
  rw [heq]; rfl

@[simp, arm64_norm]
theorem Memory.countPerm_zero (m : Memory) (p : Option Perm → Bool) (addr : BitVec 64) :
    m.countPerm p addr 0 = 0 := rfl

@[simp, arm64_norm]
theorem Memory.countRw_zero (m : Memory) (addr : BitVec 64) :
    m.countRw addr 0 = 0 := rfl

theorem Memory.countPerm_le (m : Memory) (p : Option Perm → Bool) (addr : BitVec 64) :
    ∀ n : Nat, m.countPerm p addr n ≤ n
  | 0 => Nat.le_refl 0
  | n + 1 => by
    simp only [Memory.countPerm]
    have ih := Memory.countPerm_le m p (addr + 1#64) n
    split <;> omega

theorem Memory.countRw_le (m : Memory) (addr : BitVec 64) (n : Nat) :
    m.countRw addr n ≤ n :=
  Memory.countPerm_le m (· == some Perm.rw) addr n

theorem Memory.countPerm_eq_of_allPerm (m : Memory) (p : Option Perm → Bool) :
    ∀ (addr : BitVec 64) (n : Nat), m.allPerm p addr n = true → m.countPerm p addr n = n
  | _, 0, _ => rfl
  | addr, n + 1, h => by
    simp only [Memory.allPerm, Bool.and_eq_true] at h
    simp only [Memory.countPerm, h.1, ↓reduceIte,
      Memory.countPerm_eq_of_allPerm m p (addr + 1#64) n h.2]
    omega

theorem Memory.countRw_eq_of_allPerm_rw (m : Memory) (addr : BitVec 64) (n : Nat)
    (h : m.allPerm (· == some Perm.rw) addr n = true) :
    m.countRw addr n = n :=
  Memory.countPerm_eq_of_allPerm m (· == some Perm.rw) addr n h

theorem Memory.countPerm_eq_zero_of_allPerm_not (m : Memory) (p : Option Perm → Bool) :
    ∀ (addr : BitVec 64) (n : Nat),
      m.allPerm (fun q => !p q) addr n = true → m.countPerm p addr n = 0
  | _, 0, _ => rfl
  | addr, n + 1, h => by
    simp only [Memory.allPerm, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp only [Memory.countPerm, h.1, Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
      Memory.countPerm_eq_zero_of_allPerm_not m p (addr + 1#64) n h.2]

theorem Memory.countRw_eq_zero_of_canMap (m : Memory) (addr : BitVec 64) (n : Nat)
    (h : m.canMap addr n = true) :
    m.countRw addr n = 0 := by
  unfold Memory.countRw
  refine Memory.countPerm_eq_zero_of_allPerm_not m (· == some Perm.rw) addr n ?_
  rw [Memory.canMap, Memory.allPerm_iff] at h
  rw [Memory.allPerm_iff]
  intro i hi
  have hi' := h i hi
  cases hp : m.perm (addr + BitVec.ofNat 64 i) with
  | none => rfl
  | some q => rw [hp] at hi'; cases hi'

@[simp, arm64_norm]
theorem Memory.mapZero_zero (m : Memory) (base : BitVec 64) :
    m.mapZero base 0 = m := by
  simp [Memory.mapZero]

@[simp, arm64_norm]
theorem Memory.unmapWritable_zero (m : Memory) (base : BitVec 64) :
    m.unmapWritable base 0 = m := by
  simp [Memory.unmapWritable]

theorem execMmap_fixed_protNone_ok (s : State)
    (hprot : s.readReg64 .x2 = 0#64) (hflags : s.readReg64 .x3 = 0x32#64)
    (hoff : s.readReg64 .x5 = 0#64) (hlen : s.readReg64 .x1 ≠ 0#64)
    (hal : (s.readReg64 .x0).toNat % PAGE_SIZE = 0)
    (hmin : MMAP_MIN_ADDR ≤ (s.readReg64 .x0).toNat)
    (hfit : (s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ 2 ^ 48)
    (hfrz : s.mem.allPerm (fun p => !p.frozen) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true) :
    execMmap s =
      (((s.setMem ((((s.mem.unmapNonFrozen (s.readReg64 .x0) (pageAlignUp (s.readReg64 .x1).toNat)).mapZero
          (s.readReg64 .x0) (pageAlignUp (s.readReg64 .x1).toNat)).setPermNonFrozen (s.readReg64 .x0)
          (pageAlignUp (s.readReg64 .x1).toNat) Perm.protNone))).setPhysMemAvail
          (s.physMemAvail + s.mem.countRw (s.readReg64 .x0)
            (pageAlignUp (s.readReg64 .x1).toNat))).writeReg64
        .x0 (s.readReg64 .x0)).advancePC := by
  have hlen' : (s.readReg64 .x1).toNat ≠ 0 := by
    intro h; exact hlen (BitVec.eq_of_toNat_eq (by simpa using h))
  have hmin' : ¬ (s.readReg64 .x0).toNat < MMAP_MIN_ADDR := by omega
  simp [execMmap, MMAP_PROT_RW, MMAP_PROT_NONE, MMAP_FLAGS_PRIVATE_ANON,
    MMAP_FLAGS_PRIVATE_ANON_STACK, MMAP_FLAGS_PRIVATE_ANON_FIXED, hprot, hflags, hoff, hlen',
    hal, hmin', hfit, hfrz]

theorem execMmap_ok (s : State)
    (hprot : s.readReg64 .x2 = 3#64) (hflags : s.readReg64 .x3 = 0x22#64)
    (hoff : s.readReg64 .x5 = 0#64) (hlen : s.readReg64 .x1 ≠ 0#64)
    (hmin : MMAP_MIN_ADDR ≤ (s.oracle.mmap s.oracleIdx).toNat)
    (hal : (s.oracle.mmap s.oracleIdx).toNat % PAGE_SIZE = 0)
    (hfit : (s.oracle.mmap s.oracleIdx).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ 2 ^ 48)
    (hmap : s.mem.canMap (s.oracle.mmap s.oracleIdx) (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hphys : pageAlignUp (s.readReg64 .x1).toNat ≤ s.physMemAvail) :
    execMmap s =
      ((((s.setMem (s.mem.mapZero (s.oracle.mmap s.oracleIdx)
          (pageAlignUp (s.readReg64 .x1).toNat))).setPhysMemAvail
          (s.physMemAvail - pageAlignUp (s.readReg64 .x1).toNat)).nextOracle).writeReg64
        .x0 (s.oracle.mmap s.oracleIdx)).advancePC := by
  have hlen' : (s.readReg64 .x1).toNat ≠ 0 := by
    intro h; exact hlen (BitVec.eq_of_toNat_eq (by simpa using h))
  have hpos := pageAlignUp_pos_of_ne_zero hlen'
  have hsan := sanitizeMmapAddr_eq_some_of_valid (by omega)
    (pageAlignUp_mod_pageSize _) hmin hal (by simpa [USER_VA_LIMIT] using hfit) hmap
  exact execMmap_sanitized_ok s hprot hflags hoff hlen hsan hphys

theorem execMmap_anon_oom (s : State)
    (hprot : s.readReg64 .x2 = 3#64)
    (hflags : s.readReg64 .x3 = 0x22#64 ∨ s.readReg64 .x3 = 0x20022#64)
    (hoff : s.readReg64 .x5 = 0#64) (hlen : s.readReg64 .x1 ≠ 0#64)
    (hfail : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x1).toNat) = none) :
    execMmap s = s.setStatus .OutOfMemory := by
  have hlen' : (s.readReg64 .x1).toNat ≠ 0 := by
    intro h; exact hlen (BitVec.eq_of_toNat_eq (by simpa using h))
  dsimp (config := { zetaHave := true }) only [execMmap]
  rcases hflags with hf | hf <;>
    simp [MMAP_PROT_RW, MMAP_PROT_NONE, MMAP_FLAGS_PRIVATE_ANON, MMAP_FLAGS_PRIVATE_ANON_STACK,
      MMAP_FLAGS_PRIVATE_ANON_FIXED, hprot, hf, hoff, hlen', hfail]

theorem execMmap_oom (s : State)
    (hprot : s.readReg64 .x2 = 3#64) (hflags : s.readReg64 .x3 = 0x22#64)
    (hoff : s.readReg64 .x5 = 0#64) (hlen : s.readReg64 .x1 ≠ 0#64)
    (hfail : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (pageAlignUp (s.readReg64 .x1).toNat) = none) :
    execMmap s = s.setStatus .OutOfMemory :=
  execMmap_anon_oom s hprot (Or.inl hflags) hoff hlen hfail

theorem execMunmap_ok (s : State)
    (hal : (s.readReg64 .x0).toNat % PAGE_SIZE = 0)
    (hlen : s.readReg64 .x1 ≠ 0#64)
    (hfit : (s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ 2 ^ 48)
    (hfrz : s.mem.allPerm (fun p => !p.frozen) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true) :
    execMunmap s =
      (((s.setMem (s.mem.unmapNonFrozen (s.readReg64 .x0)
          (pageAlignUp (s.readReg64 .x1).toNat))).setPhysMemAvail
          (s.physMemAvail + s.mem.countRw (s.readReg64 .x0)
            (pageAlignUp (s.readReg64 .x1).toNat))).writeReg64 .x0 0#64).advancePC := by
  have hlen' : (s.readReg64 .x1).toNat ≠ 0 := by
    intro h; exact hlen (BitVec.eq_of_toNat_eq (by simpa using h))
  simp [execMunmap, hal, hlen', hfit, hfrz]

theorem execMprotect_ok (s : State)
    (hprot : s.readReg64 .x2 = 0#64 ∨ s.readReg64 .x2 = 3#64)
    (hal : (s.readReg64 .x0).toNat % PAGE_SIZE = 0)
    (hlen : s.readReg64 .x1 ≠ 0#64)
    (hfit : (s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ 2 ^ 48)
    (hfrz : s.mem.allPerm (fun p => !p.frozen) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hmap : s.mem.allPerm (·.mapped) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hphys : s.readReg64 .x2 = 3#64 →
      pageAlignUp (s.readReg64 .x1).toNat -
        s.mem.countRw (s.readReg64 .x0) (pageAlignUp (s.readReg64 .x1).toNat) ≤
        s.physMemAvail) :
    execMprotect s =
      (((s.setMem (s.mem.setPermNonFrozen (s.readReg64 .x0)
          (pageAlignUp (s.readReg64 .x1).toNat)
          (if s.readReg64 .x2 == 0#64 then Perm.protNone else Perm.rw))).setPhysMemAvail
          (if s.readReg64 .x2 == 0#64 then
            s.physMemAvail
          else
            s.physMemAvail - (pageAlignUp (s.readReg64 .x1).toNat -
              s.mem.countRw (s.readReg64 .x0)
                (pageAlignUp (s.readReg64 .x1).toNat)))).writeReg64
        .x0 0#64).advancePC := by
  have hlen' : (s.readReg64 .x1).toNat ≠ 0 := by
    intro h; exact hlen (BitVec.eq_of_toNat_eq (by simpa using h))
  rcases hprot with hp | hp
  · cases s
    simp [execMprotect, MMAP_PROT_NONE, MMAP_PROT_RW, hp, hal, hlen', hfit, hfrz, hmap,
      State.setMem, State.setPhysMemAvail]
  · have hphys' := hphys hp
    simp [execMprotect, MMAP_PROT_NONE, MMAP_PROT_RW, hp, hal, hlen', hfit, hfrz, hmap, hphys']

theorem execMprotect_rw_oom (s : State)
    (hprot : s.readReg64 .x2 = 3#64)
    (hal : (s.readReg64 .x0).toNat % PAGE_SIZE = 0)
    (hlen : s.readReg64 .x1 ≠ 0#64)
    (hfit : (s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ 2 ^ 48)
    (hfrz : s.mem.allPerm (fun p => !p.frozen) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hmap : s.mem.allPerm (·.mapped) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hphys : ¬ (pageAlignUp (s.readReg64 .x1).toNat -
      s.mem.countRw (s.readReg64 .x0) (pageAlignUp (s.readReg64 .x1).toNat) ≤
      s.physMemAvail)) :
    execMprotect s = s.setStatus .OutOfMemory := by
  have hlen' : (s.readReg64 .x1).toNat ≠ 0 := by
    intro h; exact hlen (BitVec.eq_of_toNat_eq (by simpa using h))
  simp [execMprotect, MMAP_PROT_NONE, MMAP_PROT_RW, hprot, hal, hlen', hfit, hfrz, hmap, hphys]

theorem execMadvise_dontneed_ok (s : State)
    (hadv : s.readReg64 .x2 = 4#64)
    (hal : (s.readReg64 .x0).toNat % PAGE_SIZE = 0)
    (hlen : s.readReg64 .x1 ≠ 0#64)
    (hfit : (s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ 2 ^ 48)
    (hfrz : s.mem.allPerm (fun p => !p.frozen) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hmap : s.mem.allPerm (·.mapped) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hanon : s.mem.allAnon (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true) :
    execMadvise s =
      ((s.setMem (s.mem.zeroNonFrozen (s.readReg64 .x0)
          (pageAlignUp (s.readReg64 .x1).toNat))).writeReg64 .x0 0#64).advancePC := by
  have hlen' : (s.readReg64 .x1).toNat ≠ 0 := by
    intro h; exact hlen (BitVec.eq_of_toNat_eq (by simpa using h))
  have hfit64 : (s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ 2 ^ 64 := by omega
  simp [execMadvise, MADV_DONTNEED, MADV_FREE, hadv, hal, hlen', hfit, hfit64, hfrz, hmap, hanon]

theorem execMadvise_free_ok (s : State)
    (hadv : s.readReg64 .x2 = 8#64)
    (hal : (s.readReg64 .x0).toNat % PAGE_SIZE = 0)
    (hlen : s.readReg64 .x1 ≠ 0#64)
    (hfit : (s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ 2 ^ 48)
    (hfrz : s.mem.allPerm (fun p => !p.frozen) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hmap : s.mem.allPerm (·.mapped) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hanon : s.mem.allAnon (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true) :
    execMadvise s =
      ((s.setMem (s.mem.madvFreeNonFrozen (s.readReg64 .x0)
          (pageAlignUp (s.readReg64 .x1).toNat))).writeReg64 .x0 0#64).advancePC := by
  have hlen' : (s.readReg64 .x1).toNat ≠ 0 := by
    intro h; exact hlen (BitVec.eq_of_toNat_eq (by simpa using h))
  have hfit64 : (s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ 2 ^ 64 := by omega
  simp [execMadvise, MADV_DONTNEED, MADV_FREE, hadv, hal, hlen', hfit, hfit64, hfrz, hmap, hanon]

theorem execMadvise_noop_ok (s : State)
    (hadv : (s.readReg64 .x2 == MADV_NORMAL || s.readReg64 .x2 == MADV_RANDOM ||
      s.readReg64 .x2 == MADV_SEQUENTIAL || s.readReg64 .x2 == MADV_WILLNEED ||
      s.readReg64 .x2 == MADV_HUGEPAGE || s.readReg64 .x2 == MADV_NOHUGEPAGE ||
      s.readReg64 .x2 == MADV_DONTDUMP || s.readReg64 .x2 == MADV_DODUMP) = true)
    (hal : (s.readReg64 .x0).toNat % PAGE_SIZE = 0)
    (hlen : s.readReg64 .x1 ≠ 0#64)
    (hfit : (s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ 2 ^ 48)
    (hfrz : s.mem.allPerm (fun p => !p.frozen) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true)
    (hmap : s.mem.allPerm (·.mapped) (s.readReg64 .x0)
      (pageAlignUp (s.readReg64 .x1).toNat) = true) :
    execMadvise s = (s.writeReg64 .x0 0#64).advancePC := by
  have hlen' : (s.readReg64 .x1).toNat ≠ 0 := by
    intro h; exact hlen (BitVec.eq_of_toNat_eq (by simpa using h))
  have hfit64 : (s.readReg64 .x0).toNat + pageAlignUp (s.readReg64 .x1).toNat ≤ 2 ^ 64 := by omega
  have hnd : (s.readReg64 .x2 == MADV_DONTNEED) = false ∧
      (s.readReg64 .x2 == MADV_FREE) = false := by
    have hadv' := hadv
    simp only [MADV_NORMAL, MADV_RANDOM, MADV_SEQUENTIAL, MADV_WILLNEED,
      MADV_HUGEPAGE, MADV_NOHUGEPAGE, MADV_DONTDUMP, MADV_DODUMP,
      Bool.or_eq_true, beq_iff_eq] at hadv'
    rcases hadv' with ((((((h | h) | h) | h) | h) | h) | h) | h <;>
      simp [h, MADV_DONTNEED, MADV_FREE]
  simp [execMadvise, hadv, hnd.1, hnd.2, hal, hlen', hfit, hfit64, hfrz, hmap]

@[simp, arm64_norm]
theorem Memory.canMap_zero (m : Memory) (base : BitVec 64) : m.canMap base 0 = true := rfl

@[simp, arm64_norm]
theorem Memory.allPerm_zero (m : Memory) (p : Option Perm → Bool) (base : BitVec 64) :
    m.allPerm p base 0 = true := rfl

theorem ult_eq_false_of_ule {a b : BitVec 64} (h : b.ule a = true) : a.ult b = false := by
  simp only [BitVec.ule, BitVec.ult, decide_eq_true_eq, decide_eq_false_iff_not] at *; omega

@[arm64_norm]
theorem add_ult_eq_false_of_ule {x c b : BitVec 64} (h : b.ule (x + c) = true) :
    (x + c).ult b = false :=
  ult_eq_false_of_ule h

theorem execBrk_query (s : State) (h : s.readReg64 .x0 = 0#64) :
    execBrk s = (s.writeReg64 .x0 s.brk).advancePC := by
  simp [execBrk, h]

theorem execBrk_grow_ok (s : State)
    (hne : s.readReg64 .x0 ≠ 0#64)
    (hmin : s.brkStart.ule (s.readReg64 .x0) = true)
    (hfit : pageAlignUp s.brk.toNat < pageAlignUp (s.readReg64 .x0).toNat →
      pageAlignUp (s.readReg64 .x0).toNat + BRK_GUARD_GAP ≤ USER_VA_LIMIT)
    (hle : pageAlignUp s.brk.toNat ≤ pageAlignUp (s.readReg64 .x0).toNat)
    (hmap : pageAlignUp s.brk.toNat < pageAlignUp (s.readReg64 .x0).toNat →
      s.mem.canMap (BitVec.ofNat 64 (pageAlignUp s.brk.toNat))
        (pageAlignUp (s.readReg64 .x0).toNat - pageAlignUp s.brk.toNat + BRK_GUARD_GAP) = true)
    (hphys : pageAlignUp (s.readReg64 .x0).toNat - pageAlignUp s.brk.toNat ≤ s.physMemAvail) :
    execBrk s =
      ((((s.setBrk (s.readReg64 .x0)).setMem
          (s.mem.mapZero (BitVec.ofNat 64 (pageAlignUp s.brk.toNat))
            (pageAlignUp (s.readReg64 .x0).toNat - pageAlignUp s.brk.toNat))).setPhysMemAvail
          (s.physMemAvail -
            (pageAlignUp (s.readReg64 .x0).toNat - pageAlignUp s.brk.toNat))).writeReg64
        .x0 (s.readReg64 .x0)).advancePC := by
  have hult : (s.readReg64 .x0).ult s.brkStart = false := ult_eq_false_of_ule hmin
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · simp [execBrk, hne, hult, heq]
  · have hnotle : ¬ (pageAlignUp (s.readReg64 .x0).toNat ≤ pageAlignUp s.brk.toNat) := by omega
    have hfit' := hfit hlt
    have hmap' := hmap hlt
    simp [execBrk, hne, hult, hnotle, hfit', hmap', hphys]

theorem execBrk_fail (s : State)
    (hne : s.readReg64 .x0 ≠ 0#64)
    (hfail : (s.readReg64 .x0).ult s.brkStart = true ∨
      (pageAlignUp s.brk.toNat < pageAlignUp (s.readReg64 .x0).toNat ∧
        (¬ (pageAlignUp (s.readReg64 .x0).toNat + BRK_GUARD_GAP ≤ USER_VA_LIMIT) ∨
         s.mem.canMap (BitVec.ofNat 64 (pageAlignUp s.brk.toNat))
           (pageAlignUp (s.readReg64 .x0).toNat - pageAlignUp s.brk.toNat + BRK_GUARD_GAP) = false))) :
    execBrk s = (s.writeReg64 .x0 s.brk).advancePC := by
  unfold execBrk
  rcases hfail with hult | ⟨hlt, hbad⟩
  · simp [hult]
  · have hnotle : ¬ (pageAlignUp (s.readReg64 .x0).toNat ≤ pageAlignUp s.brk.toNat) := by omega
    by_cases hult : (s.readReg64 .x0).ult s.brkStart = true
    · simp [hult]
    · rcases hbad with hfit | hmap
      · simp [hne, hult, hnotle, hfit]
      · simp [hne, hult, hnotle, hmap]

theorem execBrk_oom (s : State)
    (hne : s.readReg64 .x0 ≠ 0#64)
    (hmin : s.brkStart.ule (s.readReg64 .x0) = true)
    (hlt : pageAlignUp s.brk.toNat < pageAlignUp (s.readReg64 .x0).toNat)
    (hfit : pageAlignUp (s.readReg64 .x0).toNat + BRK_GUARD_GAP ≤ USER_VA_LIMIT)
    (hmap : s.mem.canMap (BitVec.ofNat 64 (pageAlignUp s.brk.toNat))
      (pageAlignUp (s.readReg64 .x0).toNat - pageAlignUp s.brk.toNat + BRK_GUARD_GAP) = true)
    (hphys : ¬ (pageAlignUp (s.readReg64 .x0).toNat - pageAlignUp s.brk.toNat ≤ s.physMemAvail)) :
    execBrk s = s.setStatus .OutOfMemory := by
  have hult : (s.readReg64 .x0).ult s.brkStart = false := ult_eq_false_of_ule hmin
  have hnotle : ¬ (pageAlignUp (s.readReg64 .x0).toNat ≤ pageAlignUp s.brk.toNat) := by omega
  simp [execBrk, hne, hult, hnotle, hfit, hmap, hphys]

theorem pageAlignUp_le (n : Nat) : n ≤ pageAlignUp n := by
  unfold pageAlignUp PAGE_SIZE; omega

theorem pageAlignUp_lt (n : Nat) : pageAlignUp n < n + 4096 := by
  unfold pageAlignUp PAGE_SIZE; omega

theorem pageAlignUp_dvd (n : Nat) : 4096 ∣ pageAlignUp n := by
  unfold pageAlignUp PAGE_SIZE; exact Nat.dvd_mul_left _ _

@[simp, arm64_norm]
theorem pageAlignUp_of_dvd {n : Nat} (h : 4096 ∣ n) : pageAlignUp n = n := by
  unfold pageAlignUp PAGE_SIZE; omega

@[simp, arm64_norm]
theorem pageAlignUp_toNat_add_of_le_taskSize {x c : BitVec 64}
    (hdvd : 4096 ∣ x.toNat) (hc0 : c ≠ 0#64) (hc : c.toNat ≤ 4096)
    (hfit : x.toNat ≤ 281474976706560) :
    pageAlignUp (x + c).toNat = x.toNat + 4096 := by
  have hpos : 0 < c.toNat := by
    rcases Nat.eq_zero_or_pos c.toNat with h0 | hpos
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hc0
    · exact hpos
  have hadd : (x + c).toNat = x.toNat + c.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  rw [hadd]
  unfold pageAlignUp PAGE_SIZE at *
  omega

@[simp, arm64_norm]
theorem add_beq_zero_of_le_taskSize {x c : BitVec 64}
    (hc0 : c ≠ 0#64) (hc : c.toNat ≤ 4096) (hfit : x.toNat ≤ 281474976706560) :
    (x + c == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have hpos : 0 < c.toNat := by
    rcases Nat.eq_zero_or_pos c.toNat with h0 | hpos
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hc0
    · exact hpos
  have hadd : (x + c).toNat = x.toNat + c.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have h0 : (x + c).toNat = 0 := by rw [h]; rfl
  omega

@[simp, arm64_norm]
theorem decide_add_pageSize_le_taskSize {n : Nat} (h : n ≤ 281474976706560) :
    decide (n + 4096 ≤ 281474976710656) = true := by
  simp only [decide_eq_true_eq]; omega

@[simp, arm64_norm]
theorem decide_add_pageSize_le_two_pow_48 {n : Nat} (h : n ≤ 281474976706560) :
    decide (n + 4096 ≤ 2 ^ 48) = true := by
  simp only [decide_eq_true_eq]; omega

@[simp, arm64_norm]
theorem decide_add_pageSize_le_userVaLimit {n : Nat} (h : n ≤ 281474976706560) :
    decide (n + 4096 ≤ USER_VA_LIMIT) = true := by
  unfold USER_VA_LIMIT; simp only [decide_eq_true_eq]; omega

@[simp, arm64_norm]
theorem decide_add_le_userVaLimit_of_le_two_pow_48 {n m : Nat} (h : n + m ≤ 2 ^ 48) :
    decide (n + m ≤ USER_VA_LIMIT) = true := by
  unfold USER_VA_LIMIT; exact decide_eq_true h

@[simp, arm64_norm]
theorem sanitizeMmapAddr_page_of_valid (m : Memory) (base : BitVec 64)
    (hmin : decide (MMAP_MIN_ADDR ≤ base.toNat) = true)
    (halign : base.toNat % PAGE_SIZE = 0)
    (hva : decide (base.toNat + 4096 ≤ USER_VA_LIMIT) = true)
    (hmap : m.canMap base 4096 = true) :
    sanitizeMmapAddr m base 4096 = some base := by
  have h4096 : 4096 % PAGE_SIZE = 0 := rfl
  unfold sanitizeMmapAddr
  simp [h4096, hmin, halign, hva, hmap]

@[simp, arm64_norm]
theorem pageAlignUp_toNat_add_of_dvd {x c : BitVec 64}
    (hdvd : 4096 ∣ x.toNat) (hfit : x.toNat + pageAlignUp c.toNat ≤ 2 ^ 48) :
    pageAlignUp (x + c).toNat = x.toNat + pageAlignUp c.toNat := by
  have hc : c.toNat ≤ pageAlignUp c.toNat := pageAlignUp_le c.toNat
  have hadd : (x + c).toNat = x.toNat + c.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  rw [hadd]
  unfold pageAlignUp PAGE_SIZE at *
  omega

@[simp, arm64_norm]
theorem add_beq_zero_of_fit {x c : BitVec 64}
    (hc : c ≠ 0#64) (hfit : x.toNat + pageAlignUp c.toNat ≤ 2 ^ 48) :
    (x + c == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have hc0 : 0 < c.toNat := by
    rcases Nat.eq_zero_or_pos c.toNat with h0 | hpos
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hc
    · exact hpos
  have hle : c.toNat ≤ pageAlignUp c.toNat := pageAlignUp_le c.toNat
  have hadd : (x + c).toNat = x.toNat + c.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have h0 : (x + c).toNat = 0 := by rw [h]; rfl
  omega

@[simp, arm64_norm]
theorem mod_pageSize_eq_zero_of_dvd {n : Nat} (h : 4096 ∣ n) : n % PAGE_SIZE = 0 := by
  unfold PAGE_SIZE; exact Nat.mod_eq_zero_of_dvd h

@[simp, arm64_norm]
theorem bne_zero_of_ne {x : BitVec 64} (h : ¬ x = 0#64) : (x != 0#64) = true :=
  bne_iff_ne.2 h

-- `vcgen` support for `mmap`, `brk`, `munmap`, `mprotect`, and `madvise`:
-- `execMmap`, `execBrk`, `execMunmap`, `execMprotect`, and `execMadvise` unfold to their `if`
-- chains, whose conditions are decided from the argument registers and state hypotheses;
-- `pageAlignUp` stays folded except on literals (`reducePageAlignUp` in `ProofLib.VCGen`) or aligned sums.
attribute [arm64_norm]
  execMmap execBrk execMunmap execMprotect execMadvise
  MMAP_PROT_NONE MMAP_PROT_RW MMAP_FLAGS_PRIVATE_ANON MMAP_FLAGS_PRIVATE_ANON_STACK
  MMAP_FLAGS_PRIVATE_ANON_FIXED MMAP_MIN_ADDR
  MADV_NORMAL MADV_RANDOM MADV_SEQUENTIAL MADV_WILLNEED MADV_DONTNEED MADV_FREE
  MADV_HUGEPAGE MADV_NOHUGEPAGE MADV_DONTDUMP MADV_DODUMP
  GRND_NONBLOCK GRND_RANDOM GRND_INSECURE GRND_KNOWN_MASK MAX_RW_COUNT
  EINVAL ENOMEM
  Nat.le_add_right Nat.add_sub_cancel_left
  Memory.canMap_write8 Memory.canMap_write16 Memory.canMap_write32
  Memory.canMap_write64 Memory.canMap_write128
  Memory.allPerm_r_of_canRead Memory.allNoLazyFree_of_canRead

@[arm64_norm]
theorem BitVec.ofNat_toNat_self (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  simp

@[arm64_norm]
theorem BitVec.ofNat_toNat_add (x : BitVec 64) (k : Nat) :
    BitVec.ofNat 64 (x.toNat + k) = x + BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

@[simp, arm64_norm]
theorem execSyscall_exit (s : State) (h : s.readReg64 .x8 = 93#64) :
    execSyscall s = s.setStatus (.Exited (s.readReg64 .x0)) := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem execSyscall_exit_group (s : State) (h : s.readReg64 .x8 = 94#64) :
    execSyscall s = s.setStatus (.Exited (s.readReg64 .x0)) := by prove_execSyscall_nr

@[simp, arm64_norm]
theorem State.setBrk_self (s : State) : s.setBrk s.brk = s := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.setBrk_setBrk (s : State) (b1 b2 : BitVec 64) :
    (s.setBrk b1).setBrk b2 = s.setBrk b2 := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.setFs_self (s : State) : s.setFs s.fs = s := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.setFs_setFs (s : State) (f1 f2 : FsState) :
    (s.setFs f1).setFs f2 = s.setFs f2 := by
  cases s; rfl

@[simp, arm64_norm] theorem State.readReg64_setFs (s : State) (f : FsState) (r : Reg) :
    (s.setFs f).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp, arm64_norm] theorem State.readReg32_setFs (s : State) (f : FsState) (r : Reg) :
    (s.setFs f).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl
@[simp, arm64_norm] theorem State.readVReg128_setFs (s : State) (f : FsState) (idx : BitVec 5) :
    (s.setFs f).readVReg128 idx = s.readVReg128 idx := by cases s; rfl
@[simp, arm64_norm] theorem State.pc_setFs (s : State) (f : FsState) : (s.setFs f).pc = s.pc := by cases s; rfl
@[simp, arm64_norm] theorem State.sp_setFs (s : State) (f : FsState) : (s.setFs f).sp = s.sp := by cases s; rfl
@[simp, arm64_norm] theorem State.mem_setFs (s : State) (f : FsState) : (s.setFs f).mem = s.mem := by cases s; rfl
@[simp, arm64_norm] theorem State.pstate_setFs (s : State) (f : FsState) : (s.setFs f).pstate = s.pstate := by cases s; rfl
@[simp, arm64_norm] theorem State.status_setFs (s : State) (f : FsState) : (s.setFs f).status = s.status := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.tpidrEl0_setFs (s : State) (f : FsState) : (s.setFs f).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.brk_setFs (s : State) (f : FsState) : (s.setFs f).brk = s.brk := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_setFs (s : State) (f : FsState) : (s.setFs f).fs = f := by cases s; rfl
@[simp, arm64_norm] theorem State.calleeSavedVRegs_setFs (s : State) (f : FsState) :
    calleeSavedVRegs (s.setFs f) = calleeSavedVRegs s := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.oracle_setFs (s : State) (f : FsState) : (s.setFs f).oracle = s.oracle := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.oracleIdx_setFs (s : State) (f : FsState) : (s.setFs f).oracleIdx = s.oracleIdx := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.trace_setFs (s : State) (f : FsState) : (s.setFs f).trace = s.trace := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_writeReg32 (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).fs = s.fs := by simp [State.writeReg32]
@[simp, arm64_norm, wp_norm] theorem State.fs_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) : (s.writeReg w r v).fs = s.fs := by cases s; cases w <;> cases r <;> rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_writeVReg128 (s : State) (i : BitVec 5) (v : BitVec 128) : (s.writeVReg128 i v).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_writeVReg64 (s : State) (i : BitVec 5) (v : BitVec 64) : (s.writeVReg64 i v).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_writeVReg32 (s : State) (i : BitVec 5) (v : BitVec 32) : (s.writeVReg32 i v).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_advancePC (s : State) : s.advancePC.fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_setPC (s : State) (p : BitVec 64) : (s.setPC p).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_setPState (s : State) (ps : PState) : (s.setPState ps).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_setMem (s : State) (m : Memory) : (s.setMem m).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_setStatus (s : State) (st : ExecStatus) : (s.setStatus st).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_setBrk (s : State) (b : BitVec 64) : (s.setBrk b).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_nextOracle (s : State) : s.nextOracle.fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_appendTrace (s : State) (e : List TraceEvent) : (s.appendTrace e).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_setTpidrEl0 (s : State) (v : BitVec 64) : (setTpidrEl0 s v).fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_panicked (s : State) : (Rust.panicked s).fs = s.fs := by cases s; rfl

@[simp, arm64_norm]
theorem State.appendTrace_nil (s : State) : s.appendTrace [] = s := by
  simp [State.appendTrace]

@[simp, arm64_norm]
theorem State.appendTrace_appendTrace (s : State) (e1 e2 : List TraceEvent) :
    (s.appendTrace e1).appendTrace e2 = s.appendTrace (e1 ++ e2) := by
  simp [State.appendTrace]

@[simp, arm64_norm]
theorem State.readReg64_setBrk (s : State) (b : BitVec 64) (r : Reg) :
    (s.setBrk b).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl

@[simp, arm64_norm]
theorem State.readReg64_nextOracle (s : State) (r : Reg) :
    s.nextOracle.readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl

@[simp, arm64_norm]
theorem State.readReg64_appendTrace (s : State) (evs : List TraceEvent) (r : Reg) :
    (s.appendTrace evs).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl

@[simp, arm64_norm]
theorem State.readReg64_setStatus (s : State) (st : ExecStatus) (r : Reg) :
    (s.setStatus st).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl

@[simp, arm64_norm]
theorem State.readVReg128_setBrk (s : State) (b : BitVec 64) (idx : BitVec 5) :
    (s.setBrk b).readVReg128 idx = s.readVReg128 idx := by cases s; rfl

@[simp, arm64_norm]
theorem State.readVReg128_nextOracle (s : State) (idx : BitVec 5) :
    s.nextOracle.readVReg128 idx = s.readVReg128 idx := by cases s; rfl

@[simp, arm64_norm]
theorem State.readVReg128_appendTrace (s : State) (evs : List TraceEvent) (idx : BitVec 5) :
    (s.appendTrace evs).readVReg128 idx = s.readVReg128 idx := by cases s; rfl

@[simp, arm64_norm]
theorem State.readVReg128_setStatus (s : State) (st : ExecStatus) (idx : BitVec 5) :
    (s.setStatus st).readVReg128 idx = s.readVReg128 idx := by cases s; rfl

@[simp, arm64_norm]
theorem State.pc_setBrk (s : State) (b : BitVec 64) : (s.setBrk b).pc = s.pc := by cases s; rfl

@[simp, arm64_norm]
theorem State.pc_nextOracle (s : State) : s.nextOracle.pc = s.pc := by cases s; rfl

@[simp, arm64_norm]
theorem State.pc_appendTrace (s : State) (evs : List TraceEvent) : (s.appendTrace evs).pc = s.pc := by cases s; rfl

@[simp, arm64_norm]
theorem State.pc_setStatus (s : State) (st : ExecStatus) : (s.setStatus st).pc = s.pc := by cases s; rfl

@[simp, arm64_norm]
theorem State.sp_setBrk (s : State) (b : BitVec 64) : (s.setBrk b).sp = s.sp := by cases s; rfl

@[simp, arm64_norm]
theorem State.sp_nextOracle (s : State) : s.nextOracle.sp = s.sp := by cases s; rfl

@[simp, arm64_norm]
theorem State.sp_appendTrace (s : State) (evs : List TraceEvent) : (s.appendTrace evs).sp = s.sp := by cases s; rfl

@[simp, arm64_norm]
theorem State.sp_setStatus (s : State) (st : ExecStatus) : (s.setStatus st).sp = s.sp := by cases s; rfl

@[simp, arm64_norm]
theorem State.mem_setBrk (s : State) (b : BitVec 64) : (s.setBrk b).mem = s.mem := by cases s; rfl

@[simp, arm64_norm]
theorem State.mem_nextOracle (s : State) : s.nextOracle.mem = s.mem := by cases s; rfl

@[simp, arm64_norm]
theorem State.mem_appendTrace (s : State) (evs : List TraceEvent) : (s.appendTrace evs).mem = s.mem := by cases s; rfl

@[simp, arm64_norm]
theorem State.mem_setStatus (s : State) (st : ExecStatus) : (s.setStatus st).mem = s.mem := by cases s; rfl

@[simp, arm64_norm]
theorem State.pstate_setBrk (s : State) (b : BitVec 64) : (s.setBrk b).pstate = s.pstate := by cases s; rfl

@[simp, arm64_norm]
theorem State.pstate_nextOracle (s : State) : s.nextOracle.pstate = s.pstate := by cases s; rfl

@[simp, arm64_norm]
theorem State.pstate_appendTrace (s : State) (evs : List TraceEvent) : (s.appendTrace evs).pstate = s.pstate := by cases s; rfl

@[simp, arm64_norm]
theorem State.pstate_setStatus (s : State) (st : ExecStatus) : (s.setStatus st).pstate = s.pstate := by cases s; rfl

@[simp, arm64_norm]
theorem State.status_setBrk (s : State) (b : BitVec 64) : (s.setBrk b).status = s.status := by cases s; rfl

@[simp, arm64_norm]
theorem State.status_nextOracle (s : State) : s.nextOracle.status = s.status := by cases s; rfl

@[simp, arm64_norm]
theorem State.status_appendTrace (s : State) (evs : List TraceEvent) : (s.appendTrace evs).status = s.status := by cases s; rfl

@[simp, arm64_norm]
theorem State.status_setStatus (s : State) (st : ExecStatus) : (s.setStatus st).status = st := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.tpidrEl0_setBrk (s : State) (b : BitVec 64) : (s.setBrk b).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.tpidrEl0_nextOracle (s : State) : s.nextOracle.tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.tpidrEl0_appendTrace (s : State) (evs : List TraceEvent) : (s.appendTrace evs).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.tpidrEl0_setStatus (s : State) (st : ExecStatus) : (s.setStatus st).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brk_setBrk (s : State) (b : BitVec 64) : (s.setBrk b).brk = b := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brk_nextOracle (s : State) : s.nextOracle.brk = s.brk := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brk_appendTrace (s : State) (evs : List TraceEvent) : (s.appendTrace evs).brk = s.brk := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brk_setStatus (s : State) (st : ExecStatus) : (s.setStatus st).brk = s.brk := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brk_advancePC (s : State) : s.advancePC.brk = s.brk := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brk_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).brk = s.brk := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brk_setMem (s : State) (m : Memory) : (s.setMem m).brk = s.brk := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brk_setPState (s : State) (ps : PState) : (s.setPState ps).brk = s.brk := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brk_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).brk = s.brk := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brk_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).brk = s.brk := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brk_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).brk = s.brk := by
  cases s; cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.brk_writeReg32 (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).brk = s.brk := by
  cases s; cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.brk_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) : (s.writeReg w r v).brk = s.brk := by
  cases s; cases w <;> cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.brk_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) : (s.writeVReg128 idx v).brk = s.brk := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brk_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) : (s.writeVReg64 idx v).brk = s.brk :=
  State.brk_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm, wp_norm]
theorem State.brk_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) : (s.writeVReg32 idx v).brk = s.brk :=
  State.brk_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm, wp_norm]
theorem State.brk_setTpidrEl0 (s : State) (v : BitVec 64) : (setTpidrEl0 s v).brk = s.brk := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brk_panicked (s : State) : (Rust.panicked s).brk = s.brk := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_setBrk (s : State) (b : BitVec 64) : (s.setBrk b).brkStart = s.brkStart := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_setFs (s : State) (f : FsState) : (s.setFs f).brkStart = s.brkStart := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_nextOracle (s : State) : s.nextOracle.brkStart = s.brkStart := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_appendTrace (s : State) (evs : List TraceEvent) : (s.appendTrace evs).brkStart = s.brkStart := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_setStatus (s : State) (st : ExecStatus) : (s.setStatus st).brkStart = s.brkStart := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_advancePC (s : State) : s.advancePC.brkStart = s.brkStart := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).brkStart = s.brkStart := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_setMem (s : State) (m : Memory) : (s.setMem m).brkStart = s.brkStart := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_setPState (s : State) (ps : PState) : (s.setPState ps).brkStart = s.brkStart := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).brkStart = s.brkStart := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).brkStart = s.brkStart := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).brkStart = s.brkStart := by
  cases s; cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_writeReg32 (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).brkStart = s.brkStart := by
  cases s; cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) : (s.writeReg w r v).brkStart = s.brkStart := by
  cases s; cases w <;> cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) : (s.writeVReg128 idx v).brkStart = s.brkStart := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) : (s.writeVReg64 idx v).brkStart = s.brkStart :=
  State.brkStart_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) : (s.writeVReg32 idx v).brkStart = s.brkStart :=
  State.brkStart_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_setTpidrEl0 (s : State) (v : BitVec 64) : (setTpidrEl0 s v).brkStart = s.brkStart := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.brkStart_panicked (s : State) : (Rust.panicked s).brkStart = s.brkStart := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracle_nextOracle (s : State) : s.nextOracle.oracle = s.oracle := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_nextOracle (s : State) : s.nextOracle.oracleIdx = s.oracleIdx + 1 := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracle_setBrk (s : State) (b : BitVec 64) : (s.setBrk b).oracle = s.oracle := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracle_appendTrace (s : State) (evs : List TraceEvent) : (s.appendTrace evs).oracle = s.oracle := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracle_setStatus (s : State) (st : ExecStatus) : (s.setStatus st).oracle = s.oracle := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracle_advancePC (s : State) : s.advancePC.oracle = s.oracle := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracle_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).oracle = s.oracle := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracle_setMem (s : State) (m : Memory) : (s.setMem m).oracle = s.oracle := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracle_setPState (s : State) (ps : PState) : (s.setPState ps).oracle = s.oracle := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracle_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).oracle = s.oracle := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracle_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).oracle = s.oracle := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracle_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).oracle = s.oracle := by
  cases s; cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracle_writeReg32 (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).oracle = s.oracle := by
  cases s; cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracle_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) : (s.writeReg w r v).oracle = s.oracle := by
  cases s; cases w <;> cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracle_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) : (s.writeVReg128 idx v).oracle = s.oracle := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracle_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) : (s.writeVReg64 idx v).oracle = s.oracle :=
  State.oracle_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm, wp_norm]
theorem State.oracle_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) : (s.writeVReg32 idx v).oracle = s.oracle :=
  State.oracle_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm, wp_norm]
theorem State.oracle_setTpidrEl0 (s : State) (v : BitVec 64) : (setTpidrEl0 s v).oracle = s.oracle := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracle_panicked (s : State) : (Rust.panicked s).oracle = s.oracle := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_setBrk (s : State) (b : BitVec 64) : (s.setBrk b).oracleIdx = s.oracleIdx := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_appendTrace (s : State) (evs : List TraceEvent) : (s.appendTrace evs).oracleIdx = s.oracleIdx := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_setStatus (s : State) (st : ExecStatus) : (s.setStatus st).oracleIdx = s.oracleIdx := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_advancePC (s : State) : s.advancePC.oracleIdx = s.oracleIdx := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).oracleIdx = s.oracleIdx := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_setMem (s : State) (m : Memory) : (s.setMem m).oracleIdx = s.oracleIdx := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_setPState (s : State) (ps : PState) : (s.setPState ps).oracleIdx = s.oracleIdx := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).oracleIdx = s.oracleIdx := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).oracleIdx = s.oracleIdx := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).oracleIdx = s.oracleIdx := by
  cases s; cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_writeReg32 (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).oracleIdx = s.oracleIdx := by
  cases s; cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) : (s.writeReg w r v).oracleIdx = s.oracleIdx := by
  cases s; cases w <;> cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) : (s.writeVReg128 idx v).oracleIdx = s.oracleIdx := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) : (s.writeVReg64 idx v).oracleIdx = s.oracleIdx :=
  State.oracleIdx_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) : (s.writeVReg32 idx v).oracleIdx = s.oracleIdx :=
  State.oracleIdx_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_setTpidrEl0 (s : State) (v : BitVec 64) : (setTpidrEl0 s v).oracleIdx = s.oracleIdx := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.oracleIdx_panicked (s : State) : (Rust.panicked s).oracleIdx = s.oracleIdx := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.trace_appendTrace (s : State) (evs : List TraceEvent) : (s.appendTrace evs).trace = s.trace ++ evs := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.trace_setBrk (s : State) (b : BitVec 64) : (s.setBrk b).trace = s.trace := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.trace_nextOracle (s : State) : s.nextOracle.trace = s.trace := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.trace_setStatus (s : State) (st : ExecStatus) : (s.setStatus st).trace = s.trace := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.trace_advancePC (s : State) : s.advancePC.trace = s.trace := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.trace_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).trace = s.trace := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.trace_setMem (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.trace_setPState (s : State) (ps : PState) : (s.setPState ps).trace = s.trace := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.trace_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).trace = s.trace := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.trace_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).trace = s.trace := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.trace_writeReg64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).trace = s.trace := by
  cases s; cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.trace_writeReg32 (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).trace = s.trace := by
  cases s; cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.trace_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) : (s.writeReg w r v).trace = s.trace := by
  cases s; cases w <;> cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.trace_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) : (s.writeVReg128 idx v).trace = s.trace := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.trace_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) : (s.writeVReg64 idx v).trace = s.trace :=
  State.trace_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm, wp_norm]
theorem State.trace_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) : (s.writeVReg32 idx v).trace = s.trace :=
  State.trace_writeVReg128 s idx (v.zeroExtend 128)

@[simp, arm64_norm, wp_norm]
theorem State.trace_setTpidrEl0 (s : State) (v : BitVec 64) : (setTpidrEl0 s v).trace = s.trace := by
  cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.trace_panicked (s : State) : (Rust.panicked s).trace = s.trace := by cases s; rfl

-- `@[simp]` counterparts for `sigActions` and `sigAltStack` live in `ProofLib.StdStartup.NonVmSteps`.
@[arm64_norm, wp_norm] theorem State.sigActions_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).sigActions = s.sigActions := by cases s; cases r <;> rfl
@[arm64_norm, wp_norm] theorem State.sigActions_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).sigActions = s.sigActions := State.sigActions_writeReg64 s r _
@[arm64_norm, wp_norm] theorem State.sigActions_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).sigActions = s.sigActions := State.sigActions_writeReg64 s r _
@[arm64_norm, wp_norm] theorem State.sigActions_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 idx v).sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 idx v).sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_advancePC (s : State) :
    s.advancePC.sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_setPState (s : State) (ps : PState) :
    (s.setPState ps).sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_setFpsr (s : State) (f : BitVec 32) :
    (s.setFpsr f).sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_orFpsr (s : State) (f : BitVec 32) :
    (s.orFpsr f).sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_setMem (s : State) (m : Memory) :
    (s.setMem m).sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_setFs (s : State) (f : FsState) :
    (s.setFs f).sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_setStatus (s : State) (st : ExecStatus) :
    (s.setStatus st).sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_setBrk (s : State) (b : BitVec 64) :
    (s.setBrk b).sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_nextOracle (s : State) :
    s.nextOracle.sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_appendTrace (s : State) (evs : List TraceEvent) :
    (s.appendTrace evs).sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_stepExclOracle (s : State) :
    s.stepExclOracle.sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_stepExclLoop (s : State) :
    s.stepExclLoop.sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_setTpidrEl0 (s : State) (v : BitVec 64) :
    (setTpidrEl0 s v).sigActions = s.sigActions := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigActions_panicked (s : State) :
    (Rust.panicked s).sigActions = s.sigActions := by cases s; rfl

@[arm64_norm, wp_norm] theorem State.sigAltStack_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).sigAltStack = s.sigAltStack := by cases s; cases r <;> rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).sigAltStack = s.sigAltStack := State.sigAltStack_writeReg64 s r _
@[arm64_norm, wp_norm] theorem State.sigAltStack_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).sigAltStack = s.sigAltStack := State.sigAltStack_writeReg64 s r _
@[arm64_norm, wp_norm] theorem State.sigAltStack_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 idx v).sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 idx v).sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_advancePC (s : State) :
    s.advancePC.sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_setPState (s : State) (ps : PState) :
    (s.setPState ps).sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_setFpsr (s : State) (f : BitVec 32) :
    (s.setFpsr f).sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_orFpsr (s : State) (f : BitVec 32) :
    (s.orFpsr f).sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_setMem (s : State) (m : Memory) :
    (s.setMem m).sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_setFs (s : State) (f : FsState) :
    (s.setFs f).sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_setStatus (s : State) (st : ExecStatus) :
    (s.setStatus st).sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_setBrk (s : State) (b : BitVec 64) :
    (s.setBrk b).sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_nextOracle (s : State) :
    s.nextOracle.sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_appendTrace (s : State) (evs : List TraceEvent) :
    (s.appendTrace evs).sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_stepExclOracle (s : State) :
    s.stepExclOracle.sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_stepExclLoop (s : State) :
    s.stepExclLoop.sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_setTpidrEl0 (s : State) (v : BitVec 64) :
    (setTpidrEl0 s v).sigAltStack = s.sigAltStack := by cases s; rfl
@[arm64_norm, wp_norm] theorem State.sigAltStack_panicked (s : State) :
    (Rust.panicked s).sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm]
theorem State.stdoutBytes_def (s : State) :
    s.stdoutBytes = s.trace.filterMap (fun | .writeByte .stdout b => some b | _ => none) := by
  cases s; rfl

@[simp, arm64_norm]
theorem State.stderrBytes_def (s : State) :
    s.stderrBytes = s.trace.filterMap (fun | .writeByte .stderr b => some b | _ => none) := by
  cases s; rfl

@[simp, arm64_norm]
theorem CalleeSavedPreserved_setBrk (s0 s : State) (b : BitVec 64) :
    CalleeSavedPreserved s0 (s.setBrk b) ↔ CalleeSavedPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_setFs (s0 s : State) (f : FsState) :
    CalleeSavedPreserved s0 (s.setFs f) ↔ CalleeSavedPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_setFs_left (s0 s : State) (f : FsState) :
    CalleeSavedPreserved (s0.setFs f) s ↔ CalleeSavedPreserved s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm]
theorem CallingConventionPreserved_setFs (s0 s : State) (f : FsState) :
    CallingConventionPreserved s0 (s.setFs f) ↔ CallingConventionPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_nextOracle (s0 s : State) :
    CalleeSavedPreserved s0 s.nextOracle ↔ CalleeSavedPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_appendTrace (s0 s : State) (evs : List TraceEvent) :
    CalleeSavedPreserved s0 (s.appendTrace evs) ↔ CalleeSavedPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_setStatus (s0 s : State) (st : ExecStatus) :
    CalleeSavedPreserved s0 (s.setStatus st) ↔ CalleeSavedPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_setBrk_left (s0 s : State) (b : BitVec 64) :
    CalleeSavedPreserved (s0.setBrk b) s ↔ CalleeSavedPreserved s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_nextOracle_left (s0 s : State) :
    CalleeSavedPreserved s0.nextOracle s ↔ CalleeSavedPreserved s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_appendTrace_left (s0 s : State) (evs : List TraceEvent) :
    CalleeSavedPreserved (s0.appendTrace evs) s ↔ CalleeSavedPreserved s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm]
theorem CalleeSavedPreserved_setStatus_left (s0 s : State) (st : ExecStatus) :
    CalleeSavedPreserved (s0.setStatus st) s ↔ CalleeSavedPreserved s0 s := by
  cases s0; constructor <;> exact id

@[simp, arm64_norm]
theorem CallingConventionPreserved_setBrk (s0 s : State) (b : BitVec 64) :
    CallingConventionPreserved s0 (s.setBrk b) ↔ CallingConventionPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CallingConventionPreserved_nextOracle (s0 s : State) :
    CallingConventionPreserved s0 s.nextOracle ↔ CallingConventionPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CallingConventionPreserved_appendTrace (s0 s : State) (evs : List TraceEvent) :
    CallingConventionPreserved s0 (s.appendTrace evs) ↔ CallingConventionPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm]
theorem CallingConventionPreserved_setStatus (s0 s : State) (st : ExecStatus) :
    CallingConventionPreserved s0 (s.setStatus st) ↔ CallingConventionPreserved s0 s := by
  cases s; constructor <;> exact id

@[simp, arm64_norm, wp_norm] theorem State.fs_stepExclOracle (s : State) : s.stepExclOracle.fs = s.fs := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_stepExclLoop (s : State) : s.stepExclLoop.fs = s.fs := by cases s; rfl
@[simp, arm64_norm] theorem State.readReg64_stepExclOracle (s : State) (r : Reg) :
    s.stepExclOracle.readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp, arm64_norm] theorem State.readReg64_stepExclLoop (s : State) (r : Reg) :
    s.stepExclLoop.readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp, arm64_norm] theorem State.readVReg128_stepExclOracle (s : State) (idx : BitVec 5) :
    s.stepExclOracle.readVReg128 idx = s.readVReg128 idx := by cases s; rfl
@[simp, arm64_norm] theorem State.readVReg128_stepExclLoop (s : State) (idx : BitVec 5) :
    s.stepExclLoop.readVReg128 idx = s.readVReg128 idx := by cases s; rfl
@[simp, arm64_norm] theorem State.pc_stepExclOracle (s : State) : s.stepExclOracle.pc = s.pc := by cases s; rfl
@[simp, arm64_norm] theorem State.pc_stepExclLoop (s : State) : s.stepExclLoop.pc = s.pc := by cases s; rfl
@[simp, arm64_norm] theorem State.sp_stepExclOracle (s : State) : s.stepExclOracle.sp = s.sp := by cases s; rfl
@[simp, arm64_norm] theorem State.sp_stepExclLoop (s : State) : s.stepExclLoop.sp = s.sp := by cases s; rfl
@[simp, arm64_norm] theorem State.mem_stepExclOracle (s : State) : s.stepExclOracle.mem = s.mem := by cases s; rfl
@[simp, arm64_norm] theorem State.mem_stepExclLoop (s : State) : s.stepExclLoop.mem = s.mem := by cases s; rfl
@[simp, arm64_norm] theorem State.pstate_stepExclOracle (s : State) : s.stepExclOracle.pstate = s.pstate := by cases s; rfl
@[simp, arm64_norm] theorem State.pstate_stepExclLoop (s : State) : s.stepExclLoop.pstate = s.pstate := by cases s; rfl
@[simp, arm64_norm] theorem State.status_stepExclOracle (s : State) : s.stepExclOracle.status = s.status := by cases s; rfl
@[simp, arm64_norm] theorem State.status_stepExclLoop (s : State) : s.stepExclLoop.status = s.status := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.tpidrEl0_stepExclOracle (s : State) : s.stepExclOracle.tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.tpidrEl0_stepExclLoop (s : State) : s.stepExclLoop.tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.brk_stepExclOracle (s : State) : s.stepExclOracle.brk = s.brk := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.brk_stepExclLoop (s : State) : s.stepExclLoop.brk = s.brk := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.brkStart_stepExclOracle (s : State) : s.stepExclOracle.brkStart = s.brkStart := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.brkStart_stepExclLoop (s : State) : s.stepExclLoop.brkStart = s.brkStart := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.oracle_stepExclOracle (s : State) : s.stepExclOracle.oracle = s.oracle := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.oracle_stepExclLoop (s : State) : s.stepExclLoop.oracle = s.oracle := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.oracleIdx_stepExclOracle (s : State) : s.stepExclOracle.oracleIdx = s.oracleIdx := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.oracleIdx_stepExclLoop (s : State) : s.stepExclLoop.oracleIdx = s.oracleIdx := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.trace_stepExclOracle (s : State) : s.stepExclOracle.trace = s.trace := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.trace_stepExclLoop (s : State) : s.stepExclLoop.trace = s.trace := by cases s; rfl
@[simp, arm64_norm] theorem State.exclFails_stepExclOracle (s : State) : s.stepExclOracle.exclFails = s.exclFails.tail := by cases s; rfl
@[simp, arm64_norm] theorem State.exclFails_stepExclLoop (s : State) :
    s.stepExclLoop.exclFails = (s.exclFails.dropWhile (· == true)).tail := by cases s; rfl
@[simp, arm64_norm] theorem State.exclFails_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).exclFails = s.exclFails := by cases s; cases r <;> rfl
@[simp, arm64_norm] theorem State.exclFails_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).exclFails = s.exclFails := by cases s; cases r <;> rfl
@[simp, arm64_norm] theorem State.exclFails_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).exclFails = s.exclFails := by cases s; cases w <;> cases r <;> rfl
@[simp, arm64_norm] theorem State.exclFails_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).exclFails = s.exclFails := by cases s; rfl
@[simp, arm64_norm] theorem State.exclFails_advancePC (s : State) : s.advancePC.exclFails = s.exclFails := by cases s; rfl
@[simp, arm64_norm] theorem State.exclFails_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).exclFails = s.exclFails := by cases s; rfl
@[simp, arm64_norm] theorem State.exclFails_setMem (s : State) (m : Memory) : (s.setMem m).exclFails = s.exclFails := by cases s; rfl
@[simp, arm64_norm] theorem State.exclFails_setPState (s : State) (ps : PState) : (s.setPState ps).exclFails = s.exclFails := by cases s; rfl
@[simp, arm64_norm] theorem State.exclFails_setStatus (s : State) (st : ExecStatus) : (s.setStatus st).exclFails = s.exclFails := by cases s; rfl
@[simp, arm64_norm] theorem State.exclFails_setBrk (s : State) (b : BitVec 64) : (s.setBrk b).exclFails = s.exclFails := by cases s; rfl
@[simp, arm64_norm] theorem State.exclFails_setFs (s : State) (f : FsState) : (s.setFs f).exclFails = s.exclFails := by cases s; rfl
@[simp, arm64_norm] theorem State.exclFails_nextOracle (s : State) : s.nextOracle.exclFails = s.exclFails := by cases s; rfl
@[simp, arm64_norm] theorem State.exclFails_appendTrace (s : State) (evs : List TraceEvent) : (s.appendTrace evs).exclFails = s.exclFails := by cases s; rfl
@[simp, arm64_norm] theorem State.exclFails_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).exclFails = s.exclFails := by cases s; rfl
@[simp, arm64_norm] theorem State.exclFails_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).exclFails = s.exclFails := by cases s; rfl
@[simp, arm64_norm] theorem State.exclFails_setTpidrEl0 (s : State) (v : BitVec 64) : (setTpidrEl0 s v).exclFails = s.exclFails := by cases s; rfl
@[simp, arm64_norm] theorem CalleeSavedPreserved_stepExclOracle (s0 s : State) :
    CalleeSavedPreserved s0 s.stepExclOracle ↔ CalleeSavedPreserved s0 s := by cases s; constructor <;> exact id
@[simp, arm64_norm] theorem CalleeSavedPreserved_stepExclLoop (s0 s : State) :
    CalleeSavedPreserved s0 s.stepExclLoop ↔ CalleeSavedPreserved s0 s := by cases s; constructor <;> exact id
@[simp, arm64_norm] theorem CalleeSavedPreserved_stepExclOracle_left (s0 s : State) :
    CalleeSavedPreserved s0.stepExclOracle s ↔ CalleeSavedPreserved s0 s := by cases s0; constructor <;> exact id
@[simp, arm64_norm] theorem CalleeSavedPreserved_stepExclLoop_left (s0 s : State) :
    CalleeSavedPreserved s0.stepExclLoop s ↔ CalleeSavedPreserved s0 s := by cases s0; constructor <;> exact id
@[simp, arm64_norm] theorem CallingConventionPreserved_stepExclOracle (s0 s : State) :
    CallingConventionPreserved s0 s.stepExclOracle ↔ CallingConventionPreserved s0 s := by cases s; constructor <;> exact id
@[simp, arm64_norm] theorem CallingConventionPreserved_stepExclLoop (s0 s : State) :
    CallingConventionPreserved s0 s.stepExclLoop ↔ CallingConventionPreserved s0 s := by cases s; constructor <;> exact id

@[simp, arm64_norm] theorem State.setPhysMemAvail_self (s : State) :
    s.setPhysMemAvail s.physMemAvail = s := by cases s; rfl
@[simp, arm64_norm] theorem State.setPhysMemAvail_setPhysMemAvail (s : State) (n1 n2 : Nat) :
    (s.setPhysMemAvail n1).setPhysMemAvail n2 = s.setPhysMemAvail n2 := by cases s; rfl
@[simp, arm64_norm] theorem State.physMemAvail_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).physMemAvail = n := by cases s; rfl
@[simp, arm64_norm] theorem State.readReg64_setPhysMemAvail (s : State) (n : Nat) (r : Reg) :
    (s.setPhysMemAvail n).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp, arm64_norm] theorem State.readReg32_setPhysMemAvail (s : State) (n : Nat) (r : Reg) :
    (s.setPhysMemAvail n).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl
@[simp, arm64_norm] theorem State.readReg_setPhysMemAvail (s : State) (n : Nat) (w : Width) (r : Reg) :
    (s.setPhysMemAvail n).readReg w r = s.readReg w r := by cases s; cases w <;> cases r <;> rfl
@[simp, arm64_norm] theorem State.readVReg128_setPhysMemAvail (s : State) (n : Nat) (idx : BitVec 5) :
    (s.setPhysMemAvail n).readVReg128 idx = s.readVReg128 idx := by cases s; rfl
@[simp, arm64_norm] theorem State.pc_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).pc = s.pc := by cases s; rfl
@[simp, arm64_norm] theorem State.sp_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).sp = s.sp := by cases s; rfl
@[simp, arm64_norm] theorem State.mem_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).mem = s.mem := by cases s; rfl
@[simp, arm64_norm] theorem State.pstate_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).pstate = s.pstate := by cases s; rfl
@[simp, arm64_norm] theorem State.status_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).status = s.status := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.tpidrEl0_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.brk_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).brk = s.brk := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.brkStart_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).brkStart = s.brkStart := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.fs_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).fs = s.fs := by cases s; rfl
@[simp, arm64_norm] theorem State.calleeSavedVRegs_setPhysMemAvail (s : State) (n : Nat) :
    calleeSavedVRegs (s.setPhysMemAvail n) = calleeSavedVRegs s := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.oracle_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).oracle = s.oracle := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.oracleIdx_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).oracleIdx = s.oracleIdx := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.trace_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).trace = s.trace := by cases s; rfl
@[simp, arm64_norm] theorem State.exclFails_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).exclFails = s.exclFails := by cases s; rfl
@[simp, arm64_norm] theorem State.symtab_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).symtab = s.symtab := by cases s; rfl
@[simp, arm64_norm] theorem State.spAligned_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).spAligned = s.spAligned := by cases s; rfl
@[simp, arm64_norm] theorem checkAddrSPAligned_setPhysMemAvail (s : State) (n : Nat) (am : AddrMode) :
    checkAddrSPAligned (s.setPhysMemAvail n) am = checkAddrSPAligned s am := by cases s; rfl
@[simp, arm64_norm] theorem State.physMemAvail_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).physMemAvail = s.physMemAvail := by cases s; cases r <;> rfl
@[simp, arm64_norm] theorem State.physMemAvail_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).physMemAvail = s.physMemAvail := by cases s; cases r <;> rfl
@[simp, arm64_norm] theorem State.physMemAvail_writeReg (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).physMemAvail = s.physMemAvail := by cases s; cases w <;> cases r <;> rfl
@[simp, arm64_norm] theorem State.physMemAvail_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).physMemAvail = s.physMemAvail := by cases s; rfl
@[simp, arm64_norm] theorem State.physMemAvail_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 idx v).physMemAvail = s.physMemAvail :=
  State.physMemAvail_writeVReg128 s idx (v.zeroExtend 128)
@[simp, arm64_norm] theorem State.physMemAvail_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 idx v).physMemAvail = s.physMemAvail :=
  State.physMemAvail_writeVReg128 s idx (v.zeroExtend 128)
@[simp, arm64_norm] theorem State.physMemAvail_advancePC (s : State) :
    s.advancePC.physMemAvail = s.physMemAvail := by cases s; rfl
@[simp, arm64_norm] theorem State.physMemAvail_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).physMemAvail = s.physMemAvail := by cases s; rfl
@[simp, arm64_norm] theorem State.physMemAvail_setMem (s : State) (m : Memory) :
    (s.setMem m).physMemAvail = s.physMemAvail := by cases s; rfl
@[simp, arm64_norm] theorem State.physMemAvail_setPState (s : State) (ps : PState) :
    (s.setPState ps).physMemAvail = s.physMemAvail := by cases s; rfl
@[simp, arm64_norm] theorem State.physMemAvail_setFpsr (s : State) (f : BitVec 32) :
    (s.setFpsr f).physMemAvail = s.physMemAvail := by cases s; rfl
@[simp, arm64_norm] theorem State.physMemAvail_orFpsr (s : State) (f : BitVec 32) :
    (s.orFpsr f).physMemAvail = s.physMemAvail := by cases s; rfl
@[simp, arm64_norm] theorem State.physMemAvail_setStatus (s : State) (st : ExecStatus) :
    (s.setStatus st).physMemAvail = s.physMemAvail := by cases s; rfl
@[simp, arm64_norm] theorem State.physMemAvail_setBrk (s : State) (b : BitVec 64) :
    (s.setBrk b).physMemAvail = s.physMemAvail := by cases s; rfl
@[simp, arm64_norm] theorem State.physMemAvail_setFs (s : State) (f : FsState) :
    (s.setFs f).physMemAvail = s.physMemAvail := by cases s; rfl
@[simp, arm64_norm] theorem State.physMemAvail_nextOracle (s : State) :
    s.nextOracle.physMemAvail = s.physMemAvail := by cases s; rfl
@[simp, arm64_norm] theorem State.physMemAvail_appendTrace (s : State) (evs : List TraceEvent) :
    (s.appendTrace evs).physMemAvail = s.physMemAvail := by cases s; rfl
@[simp, arm64_norm] theorem State.physMemAvail_setTpidrEl0 (s : State) (v : BitVec 64) :
    (setTpidrEl0 s v).physMemAvail = s.physMemAvail := by cases s; rfl
@[simp, arm64_norm] theorem State.physMemAvail_stepExclOracle (s : State) :
    s.stepExclOracle.physMemAvail = s.physMemAvail := by cases s; rfl
@[simp, arm64_norm] theorem State.physMemAvail_stepExclLoop (s : State) :
    s.stepExclLoop.physMemAvail = s.physMemAvail := by cases s; rfl
@[simp, arm64_norm] theorem State.physMemAvail_setSigAction (s : State) (sig : BitVec 32) (act : SigAction) :
    (s.setSigAction sig act).physMemAvail = s.physMemAvail := by cases s; rfl
@[simp, arm64_norm, wp_norm] theorem State.physMemAvail_setSigAltStack (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).physMemAvail = s.physMemAvail := by cases s; rfl
@[simp, arm64_norm] theorem CalleeSavedPreserved_setPhysMemAvail (s0 s : State) (n : Nat) :
    CalleeSavedPreserved s0 (s.setPhysMemAvail n) ↔ CalleeSavedPreserved s0 s := by cases s; constructor <;> exact id
@[simp, arm64_norm] theorem CalleeSavedPreserved_setPhysMemAvail_left (s0 s : State) (n : Nat) :
    CalleeSavedPreserved (s0.setPhysMemAvail n) s ↔ CalleeSavedPreserved s0 s := by cases s0; constructor <;> exact id
@[simp, arm64_norm] theorem CallingConventionPreserved_setPhysMemAvail (s0 s : State) (n : Nat) :
    CallingConventionPreserved s0 (s.setPhysMemAvail n) ↔ CallingConventionPreserved s0 s := by cases s; constructor <;> exact id
@[simp, arm64_norm] theorem CallingConventionPreserved_setPhysMemAvail_left (s0 s : State) (n : Nat) :
    CallingConventionPreserved (s0.setPhysMemAvail n) s ↔ CallingConventionPreserved s0 s := by cases s0; constructor <;> exact id
@[simp, arm64_norm] theorem Returned_setPhysMemAvail (s0 s : State) (n : Nat) :
    Returned s0 (s.setPhysMemAvail n) ↔ Returned s0 s := by cases s; constructor <;> exact id
@[simp, arm64_norm] theorem Returned_setPhysMemAvail_left (s0 s : State) (n : Nat) :
    Returned (s0.setPhysMemAvail n) s ↔ Returned s0 s := by cases s0; constructor <;> exact id

@[simp, arm64_norm]
theorem execInst_brk1 (s : State) :
    execInst (.system true 1#16) s = s.setStatus (.Exited 101#64) := by
  cases s; rfl

/-! ## BitVec Arithmetic, Width Conversions, and Bit Manipulation -/

@[simp, arm64_norm]
theorem _root_.BitVec.xor_cancel_right {w : Nat} (m ks : BitVec w) :
    (m ^^^ ks) ^^^ ks = m := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

@[simp, arm64_norm]
theorem _root_.BitVec.add_one_beq_zero_false_of_ne_max {x : BitVec 64}
    (h : x ≠ 0xffffffffffffffff#64) :
    (x + 1#64 == 0#64) = false := by
  revert h; bv_decide

theorem bv_ult_toNat {a b : BitVec 64}
    (h : BitVec.ult a b = true) :
    a.toNat < b.toNat := by
  simp only [BitVec.ult] at h
  exact of_decide_eq_true h

theorem msub_udiv_toNat {w : Nat} (a b : BitVec w) :
    (a - (a / b) * b).toNat = a.toNat % b.toNat := by
  have hle : (a.toNat / b.toNat) * b.toNat ≤ a.toNat := Nat.div_mul_le_self a.toNat b.toNat
  have hmul : ((a / b) * b).toNat = (a.toNat / b.toNat) * b.toNat := by
    rw [BitVec.toNat_mul, BitVec.toNat_udiv]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle a.isLt)
  have hsub : (a - (a / b) * b).toNat = a.toNat - ((a / b) * b).toNat := by
    rw [BitVec.toNat_sub_of_le]
    rw [BitVec.le_def, hmul]
    exact hle
  have hdivmod : b.toNat * (a.toNat / b.toNat) + a.toNat % b.toNat = a.toNat :=
    Nat.div_add_mod a.toNat b.toNat
  have hcomm : (a.toNat / b.toNat) * b.toNat = b.toNat * (a.toNat / b.toNat) :=
    Nat.mul_comm _ _
  omega

theorem sub_udiv_mul_eq_umod {w : Nat} (a b : BitVec w) :
    a - (a / b) * b = a % b :=
  BitVec.eq_of_toNat_eq (by rw [msub_udiv_toNat, BitVec.toNat_umod])

theorem evalAesOp_aese_comm (x y : BitVec 128) :
    evalAesOp .AESE x y = evalAesOp .AESE y x := by
  have h : x ^^^ y = y ^^^ x := by bv_decide
  simp only [evalAesOp, h]

@[simp, arm64_norm]
theorem cbz_zero_eq_zero (v : BitVec 64) :
    (if v == 0#64 then 0#64 else v) = v := by
  by_cases h : v = 0#64 <;> simp [h]

@[simp, arm64_norm]
theorem cbnz_zero_eq_zero (v : BitVec 64) :
    (if v != 0#64 then v else 0#64) = v := by
  by_cases h : v = 0#64 <;> simp [h]

@[simp, arm64_norm] theorem bitvec_ule_self {w : Nat} (x : BitVec w) : x.ule x = true := by
  simp [BitVec.ule_eq_decide]

theorem bitvec_ult_self {w : Nat} (x : BitVec w) : x.ult x = false := by
  simp [BitVec.ult_eq_decide]

theorem bitvec_sle_self {w : Nat} (x : BitVec w) : x.sle x = true := by
  simp [BitVec.sle_eq_decide]

theorem bitvec_slt_self {w : Nat} (x : BitVec w) : x.slt x = false := by
  simp [BitVec.slt_eq_decide]

theorem zeroExtend64_eq_zero_iff_32 (x : BitVec 32) :
    (BitVec.zeroExtend 64 x = 0#64) ↔ (x = 0#32) := by
  bv_bits

theorem zeroExtend64_eq_zero_iff_16 (x : BitVec 16) :
    (BitVec.zeroExtend 64 x = 0#64) ↔ (x = 0#16) := by
  bv_bits

theorem zeroExtend64_eq_zero_iff_8 (x : BitVec 8) :
    (BitVec.zeroExtend 64 x = 0#64) ↔ (x = 0#8) := by
  bv_bits

theorem zeroExtend32_eq_zero_iff_16 (x : BitVec 16) :
    (BitVec.zeroExtend 32 x = 0#32) ↔ (x = 0#16) := by
  bv_bits

theorem zeroExtend32_eq_zero_iff_8 (x : BitVec 8) :
    (BitVec.zeroExtend 32 x = 0#32) ↔ (x = 0#8) := by
  bv_bits

@[simp, arm64_norm] theorem Memory.mapFresh_zero (m : Memory) (base : BitVec 64) (p : Perm) :
    m.mapFresh base 0 p = m := by
  simp [Memory.mapFresh]

@[simp, arm64_norm] theorem Memory.mapFresh_sub_self (m : Memory) (base : BitVec 64) (p : Perm) :
    m.mapFresh base (base - base).toNat p = m := by
  simp [Memory.mapFresh]

@[simp, arm64_norm]
theorem truncate_16_zeroExtend_32 (x : BitVec 16) :
    BitVec.truncate 16 (BitVec.zeroExtend 32 x) = x := by
  ext i hi
  simp

@[simp, arm64_norm]
theorem truncate32_zeroExtend64 (x : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 x) = x := by
  rw [truncate_32_zeroExtend_64, zeroExtend_self]

theorem truncate32_ofNat64 (n : Nat) :
    BitVec.truncate 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd n (by decide)

theorem truncate8_ofNat64 (n : Nat) :
    BitVec.truncate 8 (BitVec.ofNat 64 n) = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd n (by decide)

theorem toNat_zeroExtend64_32 (w : BitVec 32) :
    (BitVec.zeroExtend 64 w).toNat = w.toNat :=
  BitVec.toNat_setWidth_of_le (by decide)

theorem zeroExtend64_truncate32_eq_and (v : BitVec 64) :
    (v.truncate 32).zeroExtend 64 = v &&& 0xffffffff#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_setWidth,
      ProofLib.BV.Arith.node_and_mask v 0xffffffff#64 32 rfl rfl]

theorem zeroExtend64_truncate32_of_ushiftRight32_eq_zero {x : BitVec 64}
    (hx : x >>> 32 = 0#64) :
    (x.truncate 32).zeroExtend 64 = x := by
  apply BitVec.eq_of_toNat_eq
  have h1 := congrArg BitVec.toNat hx
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat] at h1
  rw [BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_setWidth]
  omega

theorem ushiftRight32_eq_zero_iff (v : BitVec 64) :
    (v >>> 32 = 0#64) ↔ v.toNat < 2 ^ 32 := by
  constructor
  · intro h
    have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat] at h1
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    omega

theorem extractLsb'_zero_32_eq_truncate32 (v : BitVec 64) :
    v.extractLsb' 0 32 = v.truncate 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

@[simp, arm64_norm]
theorem extractLsb'_hi32_append (hi lo : BitVec 32) :
    (hi ++ lo).extractLsb' 32 32 = hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi_lt
  have h1 : ¬ (32 + i < 32) := by omega
  have h2 : 32 + i - 32 = i := by omega
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi_lt, decide_true,
    Bool.true_and, h1, ↓reduceIte, h2]

@[simp, arm64_norm]
theorem truncate32_add_zeroExtend64 (u l : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 u + BitVec.zeroExtend 64 l) = u + l := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64)]
  exact Nat.mod_mod_of_dvd (u.toNat + l.toNat) (by decide)

theorem truncate32_and_zeroExtend64 (b : BitVec 8) (m : BitVec 64) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 b &&& m) =
      BitVec.zeroExtend 32 b &&& BitVec.truncate 32 m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem signExtend64_eq_zeroExtend64_of_msb_false (w : BitVec 32) (h : w.msb = false) :
    BitVec.signExtend 64 w = BitVec.zeroExtend 64 w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth]
  by_cases h32 : i < 32
  · simp [hi, h32]
  · simp [hi, h32, h, BitVec.getLsbD_of_ge w i (by omega)]

theorem signExtend64_eq_zeroExtend64_of_lt (w : BitVec 32) (hw : w.toNat < 2 ^ 31) :
    BitVec.signExtend 64 w = BitVec.zeroExtend 64 w := by
  apply signExtend64_eq_zeroExtend64_of_msb_false
  rw [BitVec.msb_eq_decide, decide_eq_false_iff_not]
  omega

theorem sxtw_of_getLsbD31_false {len32 : BitVec 32} (h : len32.getLsbD 31 = false) :
    (BitVec.zeroExtend 64 len32 >>> 0 &&& 4294967295#64 |||
      (if (BitVec.zeroExtend 64 len32).getLsbD 31 = true then 18446744073709551615#64 else 0#64) &&&
        18446744069414584320#64) = BitVec.zeroExtend 64 len32 := by
  have h31 : (BitVec.zeroExtend 64 len32).getLsbD 31 = false := by
    rw [BitVec.getLsbD_setWidth]
    simp only [h, Bool.and_false]
  rw [h31]
  simp only [Bool.false_eq_true, ↓reduceIte, BitVec.zero_and, BitVec.or_zero, BitVec.ushiftRight_zero]
  rw [← zeroExtend64_truncate32_eq_and, truncate32_zeroExtend64]

theorem zeroExtend64_shiftLeft_eq_ofNat (x : BitVec 32) (k : Nat) (hk : k ≤ 32) :
    (BitVec.zeroExtend 64 x <<< k) = BitVec.ofNat 64 (2 ^ k * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hpow : 2 ^ k ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hk
  have hlt : x.toNat * 2 ^ k < 2 ^ 64 := by
    calc x.toNat * 2 ^ k < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_lt_of_le hx hpow (by decide)
      _ = 2 ^ 64 := by decide
  rw [BitVec.toNat_shiftLeft, toNat_zeroExtend64_32, Nat.shiftLeft_eq,
      BitVec.toNat_ofNat, Nat.mul_comm (2 ^ k) x.toNat,
      Nat.mod_eq_of_lt hlt]

theorem bv_ule_false_of_ult {w : Nat} {a b : BitVec w} (h : BitVec.ult a b = true) :
    BitVec.ule b a = false := by
  simp only [BitVec.ult, BitVec.ule, decide_eq_true_eq, decide_eq_false_iff_not] at *; omega

theorem bv_ult_false_of_ule {w : Nat} {a b : BitVec w} (h : BitVec.ule b a = true) :
    BitVec.ult a b = false := by
  simp only [BitVec.ult, BitVec.ule, decide_eq_true_eq, decide_eq_false_iff_not] at *; omega

theorem bv_ule_of_ult {w : Nat} {a b : BitVec w} (h : BitVec.ult a b = true) :
    BitVec.ule a b = true := by
  simp only [BitVec.ult, BitVec.ule, decide_eq_true_eq] at *; omega

theorem add64_no_overflow_iff_ule (a b : BitVec 64) :
    (b.ule (b + a) = true) ↔ a.toNat + b.toNat < 2 ^ 64 := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [BitVec.ule, BitVec.toNat_add, decide_eq_true_eq]
  omega

theorem csel_ult_of_le {w : Nat} {a b : BitVec w} (h : a.toNat ≤ b.toNat) :
    (if a.ult b = true then a else b) = a := by
  by_cases hlt : a.ult b = true
  · simp [hlt]
  · simp only [hlt, Bool.false_eq_true, ↓reduceIte]
    simp only [BitVec.ult, decide_eq_true_eq] at hlt
    exact BitVec.eq_of_toNat_eq (by omega)

/-- Pack two 32-bit words `lo` (bits `0..31`) and `hi` (bits `32..63`) into a 64-bit word. -/
def pack32Pair (lo hi : BitVec 32) : BitVec 64 :=
  lo.zeroExtend 64 ||| (hi.zeroExtend 64 <<< 32)

@[simp, arm64_norm]
theorem pack32Pair_truncate32 (lo hi : BitVec 32) :
    (pack32Pair lo hi).truncate 32 = lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi_lt
  simp [pack32Pair, hi_lt]

@[simp, arm64_norm]
theorem pack32Pair_ushiftRight32_truncate32 (lo hi : BitVec 32) :
    ((pack32Pair lo hi) >>> 32).truncate 32 = hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi_lt
  have h1 : ¬ (32 + i < 32) := by omega
  have h3 : 32 + i < 64 := by omega
  have h4 : 32 + i - 32 = i := by omega
  simp [pack32Pair, hi_lt, h1, h3, h4]

@[simp, arm64_norm]
theorem pack32Pair_extractLsb'_hi (lo hi : BitVec 32) :
    (pack32Pair lo hi).extractLsb' 32 32 = hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi_lt
  have h1 : ¬ (32 + i < 32) := by omega
  have h3 : 32 + i < 64 := by omega
  have h4 : 32 + i - 32 = i := by omega
  simp [pack32Pair, hi_lt, h1, h3, h4]

private theorem getLsbD_mask_hi32_fin :
    ∀ i : Fin 64, (0xffffffff00000000#64).getLsbD i.val = decide (32 ≤ i.val) := by
  decide

private theorem getLsbD_mask_hi32 (i : Nat) (hi : i < 64) :
    (0xffffffff00000000#64).getLsbD i = decide (32 ≤ i) :=
  getLsbD_mask_hi32_fin ⟨i, hi⟩

@[simp, arm64_norm]
theorem pack32Pair_update_lo (lo hi newLo : BitVec 32) :
    ((pack32Pair lo hi &&& 0xffffffff00000000#64) ||| newLo.zeroExtend 64) =
      pack32Pair newLo hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi_lt
  simp only [pack32Pair, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, getLsbD_mask_hi32 i hi_lt]
  by_cases h32 : i < 32
  · have hle : ¬ (32 ≤ i) := by omega
    simp [hi_lt, h32, hle]
  · have hle : 32 ≤ i := by omega
    simp [hi_lt, h32, hle]

@[simp, arm64_norm]
theorem mask_hi32_truncate32 (w : BitVec 64) :
    (w &&& 0xffffffff00000000#64).truncate 32 = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi_lt
  have hm := getLsbD_mask_hi32 i (by omega)
  have hle : decide (32 ≤ i) = false := decide_eq_false (by omega)
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_zero,
    hi_lt, decide_true, hm, hle, Bool.and_false]

@[simp, arm64_norm]
theorem mask_hi32_extractLsb'_hi (w : BitVec 64) :
    (w &&& 0xffffffff00000000#64).extractLsb' 32 32 = w.extractLsb' 32 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi_lt
  have hm := getLsbD_mask_hi32 (32 + i) (by omega)
  have hle : decide (32 ≤ 32 + i) = true := decide_eq_true (by omega)
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and,
    hi_lt, decide_true, Bool.true_and, hm, hle, Bool.and_true]

/-- High 64 bits of an unsigned 64-by-64-to-128-bit product (`UMULH`). -/
def mulHi64 (x y : BitVec 64) : BitVec 64 :=
  ((x.zeroExtend 128 * y.zeroExtend 128) >>> 64).truncate 64

theorem fold_mulHi64 (x y : BitVec 64) :
    ((x.zeroExtend 128 * y.zeroExtend 128) >>> 64).truncate 64 = mulHi64 x y := rfl

theorem mulHi64_eq_zero_iff (x y : BitVec 64) :
    mulHi64 x y = 0#64 ↔ x.toNat * y.toNat < 2 ^ 64 := by
  have hx := x.isLt
  have hy := y.isLt
  have hprod : x.toNat * y.toNat < 2 ^ 128 := by
    calc x.toNat * y.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hx hy
      _ = 2 ^ 128 := by decide
  rw [← BitVec.toNat_inj]
  simp only [mulHi64, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 128),
    Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 128),
    Nat.mod_eq_of_lt hprod]
  have hdiv_lt : (x.toNat * y.toNat) / 2 ^ 64 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hdiv_lt]
  omega

theorem mul32_high_zero_iff (a b : BitVec 32) :
    ((a.zeroExtend 64 * b.zeroExtend 64) >>> 32 == 0#64) = true ↔
      a.toNat * b.toNat < 2 ^ 32 := by
  have ha := a.isLt
  have hb := b.isLt
  have hprod : a.toNat * b.toNat < 2 ^ 64 := by
    calc a.toNat * b.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 64 := by decide
  rw [beq_iff_eq, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega : a.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64),
    Nat.mod_eq_of_lt hprod]
  omega

theorem countLeadingZeros_loop_eq_clzAuxRec {w : Nat} (x : BitVec w) :
    ∀ k : Nat, BitVec.ofNat w (Arm64.countLeadingZeros.loop x (k + 1)) = x.clzAuxRec k
  | 0 => by
    rw [Arm64.countLeadingZeros.loop, BitVec.clzAuxRec_zero]
    split <;> rfl
  | k + 1 => by
    rw [Arm64.countLeadingZeros.loop, BitVec.clzAuxRec_succ]
    split
    · rfl
    · exact countLeadingZeros_loop_eq_clzAuxRec x k

@[simp, arm64_norm]
theorem ofNat_countLeadingZeros64 (x : BitVec 64) :
    BitVec.ofNat 64 (Arm64.countLeadingZeros x) = x.clz :=
  countLeadingZeros_loop_eq_clzAuxRec x 63

@[simp, arm64_norm]
theorem ofNat_countLeadingZeros32 (x : BitVec 32) :
    BitVec.ofNat 32 (Arm64.countLeadingZeros x) = x.clz :=
  countLeadingZeros_loop_eq_clzAuxRec x 31

@[simp, arm64_norm]
theorem truncate32_ofNat_countLeadingZeros32 (x : BitVec 32) :
    (BitVec.ofNat 64 (Arm64.countLeadingZeros x)).truncate 32 = x.clz := by
  rw [truncate32_ofNat64, ofNat_countLeadingZeros32]

theorem countLeadingZeros_loop_eq_log2 {w : Nat} (x : BitVec w) :
    ∀ k, k ≤ w → x.toNat < 2 ^ k → x.toNat ≠ 0 →
      Arm64.countLeadingZeros.loop x k = w - 1 - Nat.log2 x.toNat
  | 0, _, h, hne => by simp at h; omega
  | k + 1, hk, h, hne => by
    rw [Arm64.countLeadingZeros.loop]
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    have hdiv : x.toNat / 2 ^ k < 2 := by
      rw [Nat.div_lt_iff_lt_mul hpos]; rw [Nat.pow_succ] at h; omega
    rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
    by_cases hb : x.toNat / 2 ^ k = 1
    · have hge : 2 ^ k ≤ x.toNat := by
        have := (Nat.le_div_iff_mul_le hpos).mp (by omega : 1 ≤ x.toNat / 2 ^ k); omega
      have hlog : Nat.log2 x.toNat = k := (Nat.log2_eq_iff hne).mpr ⟨hge, h⟩
      simp [hb, hlog]
    · have h0 : x.toNat / 2 ^ k = 0 := by
        generalize x.toNat / 2 ^ k = d at hdiv hb ⊢; omega
      have hlt : x.toNat < 2 ^ k := by
        rcases Nat.lt_or_ge x.toNat (2 ^ k) with h' | h'
        · exact h'
        · have := Nat.div_pos h' hpos; omega
      simp only [h0, Nat.zero_mod, Nat.zero_ne_one, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact countLeadingZeros_loop_eq_log2 x k (by omega) hlt hne

theorem clz_eq_log2_64 (x : BitVec 64) (hx : x.toNat ≠ 0) :
    x.clz = BitVec.ofNat 64 (63 - Nat.log2 x.toNat) := by
  rw [← ofNat_countLeadingZeros64, Arm64.countLeadingZeros,
    countLeadingZeros_loop_eq_log2 x 64 (Nat.le_refl _) x.isLt hx]

theorem clz_eq_log2_32 (x : BitVec 32) (hx : x.toNat ≠ 0) :
    x.clz = BitVec.ofNat 32 (31 - Nat.log2 x.toNat) := by
  rw [← ofNat_countLeadingZeros32, Arm64.countLeadingZeros,
    countLeadingZeros_loop_eq_log2 x 32 (Nat.le_refl _) x.isLt hx]

private theorem countLeadingZeros_loop_or_one_le (x : BitVec 64) :
    ∀ k : Nat, k ≤ 63 → Arm64.countLeadingZeros.loop (x ||| 1#64) (k + 1) ≤ 63
  | 0, _ => by
    rw [Arm64.countLeadingZeros.loop]
    simp
  | k + 1, hk => by
    rw [Arm64.countLeadingZeros.loop]
    split
    · omega
    · exact countLeadingZeros_loop_or_one_le x k (by omega)

theorem clz_or_one_toNat_le (x : BitVec 64) :
    (x ||| 1#64).clz.toNat ≤ 63 := by
  rw [← ofNat_countLeadingZeros64]
  have hle : Arm64.countLeadingZeros (x ||| 1#64) ≤ 63 :=
    countLeadingZeros_loop_or_one_le x 63 (by omega)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact hle

theorem clz_or_one_le (x : BitVec 64) :
    (x ||| 1#64).clz ≤ 63#64 :=
  BitVec.le_def.mpr (clz_or_one_toNat_le x)

set_option linter.unusedSimpArgs false in
private theorem reverseBits_foldl_getLsbD (x : BitVec 64) (l : List Nat) (acc : BitVec 64)
    (hl : ∀ i ∈ l, i < 64) (j : Nat) (hj : j < 64) :
    (l.foldl (fun s i => if x.getLsbD i = true then s ||| 1#64 <<< (64 - 1 - i) else s) acc).getLsbD j
      = (acc.getLsbD j || l.any (fun i => x.getLsbD i && (63 - i == j))) := by
  induction l generalizing acc with
  | nil => simp
  | cons i l ih =>
    have hi : i < 64 := hl i (by simp)
    rw [List.foldl_cons, ih _ (fun a ha => hl a (by simp [ha]))]
    simp only [List.any_cons]
    by_cases hx : x.getLsbD i = true
    · simp only [hx, ite_true, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, Bool.true_and]
      by_cases hij : 63 - i = j
      · subst hij
        simp
        omega
      · have : (63 - i == j) = false := by simpa using hij
        simp only [this]
        have h0 : (decide (j < 64) && !decide (j < 63 - i) && decide (j - (63 - i) = 0)) = false := by
          cases h1 : decide (j < 63 - i) <;> simp_all <;> omega
        simp [BitVec.getLsbD_one, h0]
    · simp only [hx, Bool.false_and, Bool.false_or]
      simp

@[simp, arm64_norm]
theorem reverseBits_eq_reverse (x : BitVec 64) :
    Arm64.reverseBits x = x.reverse := by
  simp only [Arm64.reverseBits, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  have h : ∀ i (s : BitVec 64),
      (if x.getLsbD i = true then (pure (ForInStep.yield (s ||| 1#64 <<< (64 - 1 - i))) : Id _)
        else pure (ForInStep.yield s)) =
      pure (ForInStep.yield (if x.getLsbD i = true then s ||| 1#64 <<< (64 - 1 - i) else s)) := by
    intro i s; split <;> rfl
  simp only [h, List.forIn_pure_yield_eq_foldl, bind_pure, Id.run_pure]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [reverseBits_foldl_getLsbD x _ _ (by intro i hi; simp [List.mem_range'] at hi; omega) j hj]
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD]
  have h0 : BitVec.getLsbD (0 : BitVec 64) j = false := by simp
  rw [h0, Bool.false_or]
  simp only [hj, decide_true, Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range', Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨i, ⟨k, hk, rfl⟩, h1, h2⟩
    have : 64 - 1 - j = 0 + 1 * k := by omega
    rw [this]; exact h1
  · intro h1
    exact ⟨64 - 1 - j, ⟨64 - 1 - j, by omega, by omega⟩, h1, by omega⟩

theorem rotateRight64_eq_rotateLeft64 (x : BitVec 64) (r l : Nat)
    (hr : r < 64 := by decide) (hl : l < 64 := by decide)
    (h1 : 64 - r = l := by rfl) (h2 : 64 - l = r := by rfl) :
    x.rotateRight r = x.rotateLeft l := by
  rw [BitVec.rotateRight_eq_rotateRightAux_of_lt hr,
      BitVec.rotateLeft_eq_rotateLeftAux_of_lt hl]
  unfold BitVec.rotateRightAux BitVec.rotateLeftAux
  rw [h1, h2, BitVec.or_comm]

theorem setWidth64_append_ushiftRight_eq_rotateLeft (x : BitVec 64) (r l : Nat)
    (hl : l < 64 := by decide) (hrl : r + l = 64 := by rfl) :
    BitVec.setWidth 64 ((x ++ x) >>> r) = x.rotateLeft l := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append,
      BitVec.getLsbD_rotateLeft_of_le hl]
  simp only [hi, decide_true, Bool.true_and]
  by_cases hlt : i < l
  · have hlt2 : r + i < 64 := by omega
    simp only [hlt, hlt2, ↓reduceIte]
    congr 1
    omega
  · have hlt2 : ¬(r + i < 64) := by omega
    simp only [hlt, hlt2, ↓reduceIte]
    congr 1
    omega

theorem n_and_one_dichotomy64 (n : BitVec 64) :
    ((n &&& 1#64) != 0#64) = true ∧ n.toNat = 2 * (n >>> 1).toNat + 1 ∨
    ((n &&& 1#64) != 0#64) = false ∧ n.toNat = 2 * (n >>> 1).toNat := by
  have hand : (n &&& 1#64).toNat = n.toNat % 2 := by
    rw [BitVec.toNat_and]
    exact Nat.and_one_is_mod n.toNat
  have hshr : (n >>> 1).toNat = n.toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases hmod : n.toNat % 2 = 0
  · right
    have hzero : n &&& 1#64 = 0#64 := BitVec.eq_of_toNat_eq (by rw [hand, BitVec.toNat_ofNat]; omega)
    refine ⟨by simp [hzero], by omega⟩
  · left
    have hne : n &&& 1#64 ≠ 0#64 := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [hand, BitVec.toNat_ofNat] at this
      omega
    refine ⟨bne_iff_ne.mpr hne, by omega⟩

theorem toNat_addOfNat {x : BitVec 64} {xv i : Nat} (hx : x.toNat = xv)
    (hi : xv + i < 2 ^ 64) : (x + BitVec.ofNat 64 i).toNat = xv + i := by
  rw [BitVec.toNat_add, hx, BitVec.toNat_ofNat]; omega

theorem or_one_eq_add_one_of_getLsbD_false {x : BitVec 64} (hx : x.getLsbD 0 = false) :
    x ||| 1#64 = x + 1#64 := by
  have hand : x &&& 1#64 = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simpa using hx
    · simp [BitVec.getLsbD_and, BitVec.getLsbD_one, Nat.ne_of_gt hpos]
  exact (BitVec.add_eq_or_of_and_eq_zero x 1#64 hand).symm

theorem extract64_lo (a b : BitVec 64) : (b ++ a).extractLsb' 0 64 = a :=
  extractLsb_low64_append b a

theorem extract64_hi (a b : BitVec 64) : (b ++ a).extractLsb' 64 64 = b :=
  extractLsb_high64_append b a

end

public meta section

/-- Marks `Arm64.Program.fetch` and `Arm64.Program.externAt?` as `[local irreducible]` so
    `simp` and `whnf` rewrite through per-instruction `fetch_*` / `execAt_*` theorems without
    unfolding the instruction or extern tables on a symbolic `PC`.

    Do not mark `Arm64.Program.fnOff`, generated `*Code` definitions, `Arm64.Program.rebase`,
    or `Arm64.Program.fnAddr` as `[irreducible]`: `fnAddr_rebase` rewrites
    `(prog.rebase base).fnAddr name` to `base + BitVec.ofNat 64 (prog.fnOff name)`, and
    `prog.fnOff name` must reduce to a concrete `Nat` literal so `BitVec.reduceOfNat` and
    `reduceBitVecAddAssoc` fold PC and function-entry offsets into `BitVec 64` literals. -/
macro "arm64_proof_prelude" : command =>
  `(command|
    set_option allowUnsafeReducibility true in
    attribute [local irreducible] Arm64.Program.fetch Arm64.Program.externAt?)

end

end ProofLib


