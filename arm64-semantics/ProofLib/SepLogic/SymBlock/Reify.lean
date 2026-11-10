/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.SymBlock.Lower
public meta import ProofLib.SepLogic.SymBlock.Lower
public meta import Lean
import Arm64.Trusted.Spec.SepLogic

/-!
# Instruction Reification for Whole-Block Symbolic Execution

Defines `SymBlock.Reify.instr? : Expr → MetaM (Option Instr)`, which reifies elaborated `Instr`
terms (including coercions and `OfNat` literals) into native `Instr` values for the `sym_block`
advisor across the instruction subset supported by `SymBlock.lower`. Unsupported terms return
`none`, leaving soundness to the kernel check on `SymBlock.lower`.
-/

public meta section

namespace ProofLib.SymBlock.Reify

open Lean Meta Arm64

/-- Weak-head normalize to a constructor application; returns the constructor and its non-parameter
    arguments. -/
def ctor? (e : Expr) : MetaM (Option (ConstructorVal × Array Expr)) := do
  let e ← whnfD e
  let .const n _ := e.getAppFn | return none
  let some (.ctorInfo c) := (← getEnv).find? n | return none
  return some (c, e.getAppArgs.extract c.numParams e.getAppNumArgs)

def enumIdx? (e : Expr) : MetaM (Option Nat) := do
  return (← ctor? e).map (·.1.cidx)

def nat? (e : Expr) : MetaM (Option Nat) := do
  match ← whnfD e with
  | .lit (.natVal n) => return some n
  | _ => return none

def bv? (n : Nat) (e : Expr) : MetaM (Option (BitVec n)) := do
  return (← nat? (mkApp2 (mkConst ``BitVec.toNat) (mkNatLit n) e)).map (BitVec.ofNat n)

def bool? (e : Expr) : MetaM (Option Bool) := do
  let some (c, _) ← ctor? e | return none
  match c.name with
  | ``Bool.false => return some false
  | ``Bool.true => return some true
  | _ => return none

def width? (e : Expr) : MetaM (Option RegWidth) := do
  return (← enumIdx? e).map RegWidth.ofNat

def memSize? (e : Expr) : MetaM (Option MemWidth) := do
  let some (c, _) ← ctor? e | return none
  match c.name with
  | ``MemWidth.B8 => return some .B8
  | ``MemWidth.H16 => return some .H16
  | ``MemWidth.W32 => return some .W32
  | ``MemWidth.X64 => return some .X64
  | _ => return none

def simdMemSize? (e : Expr) : MetaM (Option SimdMemSize) := do
  let some (c, _) ← ctor? e | return none
  match c.name with
  | ``SimdMemSize.B8 => return some .B8
  | ``SimdMemSize.H16 => return some .H16
  | ``SimdMemSize.S32 => return some .S32
  | ``SimdMemSize.D64 => return some .D64
  | ``SimdMemSize.Q128 => return some .Q128
  | _ => return none

def extendType? (e : Expr) : MetaM (Option ExtendType) := do
  let some (c, _) ← ctor? e | return none
  match c.name with
  | ``ExtendType.UXTB => return some .UXTB
  | ``ExtendType.UXTH => return some .UXTH
  | ``ExtendType.UXTW => return some .UXTW
  | ``ExtendType.UXTX => return some .UXTX
  | ``ExtendType.SXTB => return some .SXTB
  | ``ExtendType.SXTH => return some .SXTH
  | ``ExtendType.SXTW => return some .SXTW
  | ``ExtendType.SXTX => return some .SXTX
  | _ => return none

def reg? (e : Expr) : MetaM (Option Reg) := do
  let some (c, args) ← ctor? e | return none
  match c.name with
  | ``Reg.gpr => return (← bv? 5 args[0]!).map .gpr
  | ``Reg.sp => return some .sp
  | ``Reg.xzr => return some .xzr
  | _ => return none

def addrMode? (e : Expr) : MetaM (Option AddrMode) := do
  let some (c, args) ← ctor? e | return none
  match c.name with
  | ``AddrMode.Offset =>
    let some base ← reg? args[0]! | return none
    let some offset ← bv? 64 args[1]! | return none
    return some (.Offset base offset)
  | ``AddrMode.UnscaledOffset =>
    let some base ← reg? args[0]! | return none
    let some offset ← bv? 64 args[1]! | return none
    return some (.UnscaledOffset base offset)
  | ``AddrMode.PreIndex =>
    let some base ← reg? args[0]! | return none
    let some offset ← bv? 64 args[1]! | return none
    return some (.PreIndex base offset)
  | ``AddrMode.PostIndex =>
    let some base ← reg? args[0]! | return none
    let some offset ← bv? 64 args[1]! | return none
    return some (.PostIndex base offset)
  | ``AddrMode.RegOffset =>
    let some base ← reg? args[0]! | return none
    let some index ← reg? args[1]! | return none
    let some ext ← extendType? args[2]! | return none
    let some amount ← nat? args[3]! | return none
    return some (.RegOffset base index ext amount)
  | _ => return none

def addSubOp? (e : Expr) : MetaM (Option AddSubOp) := do
  let some (c, _) ← ctor? e | return none
  match c.name with
  | ``AddSubOp.ADD => return some .ADD
  | ``AddSubOp.ADDS => return some .ADDS
  | ``AddSubOp.SUB => return some .SUB
  | ``AddSubOp.SUBS => return some .SUBS
  | _ => return none

def logicalOp? (e : Expr) : MetaM (Option LogicalOp) := do
  let some (c, _) ← ctor? e | return none
  match c.name with
  | ``LogicalOp.AND => return some .AND
  | ``LogicalOp.ORR => return some .ORR
  | ``LogicalOp.EOR => return some .EOR
  | ``LogicalOp.ANDS => return some .ANDS
  | ``LogicalOp.BIC => return some .BIC
  | ``LogicalOp.ORN => return some .ORN
  | ``LogicalOp.EON => return some .EON
  | ``LogicalOp.BICS => return some .BICS
  | _ => return none

def bitfieldOp? (e : Expr) : MetaM (Option BitfieldOp) := do
  let some (c, _) ← ctor? e | return none
  match c.name with
  | ``BitfieldOp.SBFM => return some .SBFM
  | ``BitfieldOp.BFM => return some .BFM
  | ``BitfieldOp.UBFM => return some .UBFM
  | _ => return none

def moveWideOp? (e : Expr) : MetaM (Option MoveWideOp) := do
  let some (c, _) ← ctor? e | return none
  match c.name with
  | ``MoveWideOp.MOVN => return some .MOVN
  | ``MoveWideOp.MOVZ => return some .MOVZ
  | ``MoveWideOp.MOVK => return some .MOVK
  | _ => return none

def condSelectOp? (e : Expr) : MetaM (Option CondSelectOp) := do
  let some (c, _) ← ctor? e | return none
  match c.name with
  | ``CondSelectOp.CSEL => return some .CSEL
  | ``CondSelectOp.CSINC => return some .CSINC
  | ``CondSelectOp.CSINV => return some .CSINV
  | ``CondSelectOp.CSNEG => return some .CSNEG
  | _ => return none

def dataProc1Op? (e : Expr) : MetaM (Option DataProc1Op) := do
  let some (c, _) ← ctor? e | return none
  match c.name with
  | ``DataProc1Op.RBIT => return some .RBIT
  | ``DataProc1Op.REV16 => return some .REV16
  | ``DataProc1Op.REV32 => return some .REV32
  | ``DataProc1Op.REV => return some .REV
  | ``DataProc1Op.CLZ => return some .CLZ
  | ``DataProc1Op.CLS => return some .CLS
  | _ => return none

def dataProc3Op? (e : Expr) : MetaM (Option DataProc3Op) := do
  let some (c, _) ← ctor? e | return none
  match c.name with
  | ``DataProc3Op.MADD => return some .MADD
  | ``DataProc3Op.MSUB => return some .MSUB
  | ``DataProc3Op.SMADDL => return some .SMADDL
  | ``DataProc3Op.SMSUBL => return some .SMSUBL
  | ``DataProc3Op.UMADDL => return some .UMADDL
  | ``DataProc3Op.UMSUBL => return some .UMSUBL
  | ``DataProc3Op.SMULH => return some .SMULH
  | ``DataProc3Op.UMULH => return some .UMULH
  | _ => return none

/-- Reify an elaborated `Instr` term (supported subset). -/
def instr? (e : Expr) : MetaM (Option Instr) := do
  let some (c, args) ← ctor? e | return none
  let a (i : Nat) : Expr := args[i]!
  match c.name with
  | ``Instr.ldr =>
    let some w ← width? (a 0) | return none
    let some sz ← memSize? (a 1) | return none
    let some signed ← bool? (a 2) | return none
    let some rt ← reg? (a 3) | return none
    let some am ← addrMode? (a 4) | return none
    return some (.ldr w sz signed rt am)
  | ``Instr.str =>
    let some sz ← memSize? (a 0) | return none
    let some rt ← reg? (a 1) | return none
    let some am ← addrMode? (a 2) | return none
    return some (.str sz rt am)
  | ``Instr.ldp =>
    let some w ← width? (a 0) | return none
    let some signed ← bool? (a 1) | return none
    let some rt1 ← reg? (a 2) | return none
    let some rt2 ← reg? (a 3) | return none
    let some am ← addrMode? (a 4) | return none
    return some (.ldp w signed rt1 rt2 am)
  | ``Instr.stp =>
    let some w ← width? (a 0) | return none
    let some rt1 ← reg? (a 1) | return none
    let some rt2 ← reg? (a 2) | return none
    let some am ← addrMode? (a 3) | return none
    return some (.stp w rt1 rt2 am)
  | ``Instr.ldrSimd =>
    let some sz ← simdMemSize? (a 0) | return none
    let some vt ← bv? 5 (a 1) | return none
    let some am ← addrMode? (a 2) | return none
    return some (.ldrSimd sz vt am)
  | ``Instr.strSimd =>
    let some sz ← simdMemSize? (a 0) | return none
    let some vt ← bv? 5 (a 1) | return none
    let some am ← addrMode? (a 2) | return none
    return some (.strSimd sz vt am)
  | ``Instr.ldpSimd =>
    let some sz ← simdMemSize? (a 0) | return none
    let some vt1 ← bv? 5 (a 1) | return none
    let some vt2 ← bv? 5 (a 2) | return none
    let some am ← addrMode? (a 3) | return none
    return some (.ldpSimd sz vt1 vt2 am)
  | ``Instr.stpSimd =>
    let some sz ← simdMemSize? (a 0) | return none
    let some vt1 ← bv? 5 (a 1) | return none
    let some vt2 ← bv? 5 (a 2) | return none
    let some am ← addrMode? (a 3) | return none
    return some (.stpSimd sz vt1 vt2 am)
  | ``Instr.addSubImm =>
    let some w ← width? (a 0) | return none
    let some op ← addSubOp? (a 1) | return none
    let some rd ← reg? (a 2) | return none
    let some rn ← reg? (a 3) | return none
    let some imm12 ← bv? 12 (a 4) | return none
    let some shift12 ← bool? (a 5) | return none
    return some (.addSubImm w op rd rn imm12 shift12)
  | ``Instr.addSubShift =>
    let some w ← width? (a 0) | return none
    let some op ← addSubOp? (a 1) | return none
    let some rd ← reg? (a 2) | return none
    let some rn ← reg? (a 3) | return none
    let some rm ← reg? (a 4) | return none
    let some sh ← enumIdx? (a 5) | return none
    let some amt ← nat? (a 6) | return none
    return some (.addSubShift w op rd rn rm (ShiftType.ofNat sh) amt)
  | ``Instr.addSubExt =>
    let some w ← width? (a 0) | return none
    let some op ← addSubOp? (a 1) | return none
    let some rd ← reg? (a 2) | return none
    let some rn ← reg? (a 3) | return none
    let some rm ← reg? (a 4) | return none
    let some ext ← extendType? (a 5) | return none
    let some amt ← nat? (a 6) | return none
    return some (.addSubExt w op rd rn rm ext amt)
  | ``Instr.logicalImm =>
    let some w ← width? (a 0) | return none
    let some op ← logicalOp? (a 1) | return none
    let some rd ← reg? (a 2) | return none
    let some rn ← reg? (a 3) | return none
    let some imm ← bv? 64 (a 4) | return none
    return some (.logicalImm w op rd rn imm)
  | ``Instr.logicalShift =>
    let some w ← width? (a 0) | return none
    let some op ← logicalOp? (a 1) | return none
    let some rd ← reg? (a 2) | return none
    let some rn ← reg? (a 3) | return none
    let some rm ← reg? (a 4) | return none
    let some sh ← enumIdx? (a 5) | return none
    let some amt ← nat? (a 6) | return none
    return some (.logicalShift w op rd rn rm (ShiftType.ofNat sh) amt)
  | ``Instr.bitfield =>
    let some w ← width? (a 0) | return none
    let some op ← bitfieldOp? (a 1) | return none
    let some rd ← reg? (a 2) | return none
    let some rn ← reg? (a 3) | return none
    let some r ← nat? (a 4) | return none
    let some s ← nat? (a 5) | return none
    return some (.bitfield w op rd rn r s)
  | ``Instr.moveWide =>
    let some w ← width? (a 0) | return none
    let some op ← moveWideOp? (a 1) | return none
    let some rd ← reg? (a 2) | return none
    let some imm16 ← bv? 16 (a 3) | return none
    let some hw ← nat? (a 4) | return none
    return some (.moveWide w op rd imm16 hw)
  | ``Instr.condSelect =>
    let some w ← width? (a 0) | return none
    let some op ← condSelectOp? (a 1) | return none
    let some rd ← reg? (a 2) | return none
    let some rn ← reg? (a 3) | return none
    let some rm ← reg? (a 4) | return none
    let some cc ← enumIdx? (a 5) | return none
    return some (.condSelect w op rd rn rm (CondCode.ofNat cc))
  | ``Instr.dataProc1 =>
    let some w ← width? (a 0) | return none
    let some op ← dataProc1Op? (a 1) | return none
    let some rd ← reg? (a 2) | return none
    let some rn ← reg? (a 3) | return none
    return some (.dataProc1 w op rd rn)
  | ``Instr.dataProc3 =>
    let some w ← width? (a 0) | return none
    let some op ← dataProc3Op? (a 1) | return none
    let some rd ← reg? (a 2) | return none
    let some rn ← reg? (a 3) | return none
    let some rm ← reg? (a 4) | return none
    let some ra ← reg? (a 5) | return none
    return some (.dataProc3 w op rd rn rm ra)
  | ``Instr.b =>
    return (← bv? 64 (a 0)).map .b
  | ``Instr.bCond =>
    let some cc ← enumIdx? (a 0) | return none
    return (← bv? 64 (a 1)).map (.bCond (CondCode.ofNat cc) ·)
  | ``Instr.cbz =>
    let some w ← width? (a 0) | return none
    let some isNonZero ← bool? (a 1) | return none
    let some rt ← reg? (a 2) | return none
    let some target ← bv? 64 (a 3) | return none
    return some (.cbz w isNonZero rt target)
  | ``Instr.tbz =>
    let some w ← width? (a 0) | return none
    let some isNonZero ← bool? (a 1) | return none
    let some rt ← reg? (a 2) | return none
    let some bitPos ← nat? (a 3) | return none
    let some target ← bv? 64 (a 4) | return none
    return some (.tbz w isNonZero rt bitPos target)
  | ``Instr.ret =>
    return (← reg? (a 0)).map .ret
  | ``Instr.adr =>
    let some page ← bool? (a 0) | return none
    let some rd ← reg? (a 1) | return none
    let some target ← bv? 64 (a 2) | return none
    return some (.adr page rd target)
  | ``Instr.nop =>
    return some .nop
  | ``Instr.hint =>
    return (← bv? 7 (a 0)).map .hint
  | ``Instr.barrier =>
    let some crm ← bv? 4 (a 0) | return none
    let some op2 ← bv? 3 (a 1) | return none
    return some (.barrier crm op2)
  | ``Instr.prfm =>
    let some prfop ← bv? 5 (a 0) | return none
    let some am ← addrMode? (a 1) | return none
    return some (.prfm prfop am)
  | ``Instr.prfmLit =>
    let some prfop ← bv? 5 (a 0) | return none
    let some target ← bv? 64 (a 1) | return none
    return some (.prfmLit prfop target)
  | ``Instr.sysReg =>
    let some isRead ← bool? (a 0) | return none
    let some sr ← bv? 15 (a 1) | return none
    let some rt ← reg? (a 2) | return none
    return some (.sysReg isRead sr rt)
  | _ => return none

end ProofLib.SymBlock.Reify
