/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.SymBlock.Core
import Arm64.Trusted.Spec.SepLogic

/-!
# Reflective Block Symbolic Execution: Micro-Ops and Lowering

Defines the micro-operation type `MOp` and its concrete semantics `MOp.exec`, together with the
total instruction lowering `lower : Instr -> Option MOp` and soundness theorem `lower_sound`
(`lower i = some op -> prog.evalInst i s = op.exec s`).
-/

@[expose] public section

namespace ProofLib.SymBlock

open Arm64

/-- Concrete execution of `LDR Qt, addr` (`SimdMemSize.Q128`). -/
@[simp, reducible] def execLdrSimdQ (vt : VReg) (addr : AddrMode) (s : State) : State :=
  if !checkAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := evalAddrMode s addr
    if !s.mem.canRead ea 16 then
      s.setStatus (.Exception "permission fault")
    else
    let val := s.mem.read128 ea
    let s1 := match wb with | some (base, newBase) => s.writeReg64 base newBase | none => s
    (s1.writeVReg128 vt val).advancePC

/-- Concrete execution of `STR Qt, addr` (`SimdMemSize.Q128`). -/
@[simp, reducible] def execStrSimdQ (vt : VReg) (addr : AddrMode) (s : State) : State :=
  if !checkAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := evalAddrMode s addr
    if !s.mem.canWrite ea 16 then
      s.setStatus (.Exception "permission fault")
    else
    let val := s.readVReg128 vt
    let s1 := s.setMem (s.mem.write128 ea val)
    let s2 := match wb with | some (base, newBase) => s1.writeReg64 base newBase | none => s1
    s2.advancePC

/-- Concrete execution of `LDP Qt1, Qt2, addr` (`SimdMemSize.Q128`). -/
@[simp, reducible] def execLdpSimdQ (vt1 vt2 : VReg) (addr : AddrMode) (s : State) : State :=
  if !checkAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := evalAddrMode s addr
    if !(s.mem.canRead ea 16 && s.mem.canRead (ea + 16#64) 16) then
      s.setStatus (.Exception "permission fault")
    else
    let v1 := s.mem.read128 ea
    let v2 := s.mem.read128 (ea + 16#64)
    let s1 := match wb with | some (base, newBase) => s.writeReg64 base newBase | none => s
    let s2 := s1.writeVReg128 vt1 v1
    let s3 := s2.writeVReg128 vt2 v2
    s3.advancePC

/-- Concrete execution of `STP Qt1, Qt2, addr` (`SimdMemSize.Q128`). -/
@[simp, reducible] def execStpSimdQ (vt1 vt2 : VReg) (addr : AddrMode) (s : State) : State :=
  if !checkAddrSPAligned s addr then
    s.setStatus (.Exception "SP alignment fault")
  else
    let (ea, wb) := evalAddrMode s addr
    if !(s.mem.canWrite ea 16 && s.mem.canWrite (ea + 16#64) 16) then
      s.setStatus (.Exception "permission fault")
    else
    let v1 := s.readVReg128 vt1
    let v2 := s.readVReg128 vt2
    let m1 := s.mem.write128 ea v1
    let m2 := m1.write128 (ea + 16#64) v2
    let s1 := s.setMem m2
    let s2 := match wb with | some (base, newBase) => s1.writeReg64 base newBase | none => s1
    s2.advancePC

/-- `MemWidth` corresponding to a sub-doubleword `CW` (`B8`, `H16`, `W32`; `X64` for `b128`). -/
def CW.size : CW → MemWidth
  | .b8 => .B8
  | .b16 => .H16
  | .b32 => .W32
  | .b128 => .X64

/-- Micro-operations supported by the reflective block executor. -/
inductive MOp where
  | ldr (w : Width) (sz : MemWidth) (rt : Reg) (am : AddrMode)
  | str (sz : MemWidth) (rt : Reg) (am : AddrMode)
  | ldp (w : Width) (signed : Bool) (rt1 rt2 : Reg) (am : AddrMode)
  | stp (w : Width) (rt1 rt2 : Reg) (am : AddrMode)
  | ldrSimdQ (vt : VReg) (am : AddrMode)
  | strSimdQ (vt : VReg) (am : AddrMode)
  | ldpSimdQ (vt1 vt2 : VReg) (am : AddrMode)
  | stpSimdQ (vt1 vt2 : VReg) (am : AddrMode)
  | addSubImm (w : Width) (op : AddSubOp) (rd rn : Reg) (imm12 : BitVec 12) (shift12 : Bool)
  | addSubShift (w : Width) (op : AddSubOp) (rd rn rm : Reg) (shift : ShiftType) (amount : Nat)
  | addSubExt (w : Width) (op : AddSubOp) (rd rn rm : Reg) (ext : ExtendType) (amount : Nat)
  | logicalImm (w : Width) (op : LogicalOp) (rd rn : Reg) (imm : BitVec 64)
  | logicalShift (w : Width) (op : LogicalOp) (rd rn rm : Reg) (shift : ShiftType) (amount : Nat)
  | bitfield (w : Width) (op : BitfieldOp) (rd rn : Reg) (immr imms : Nat)
  | movWide (w : Width) (op : MoveWideOp) (rd : Reg) (imm16 : BitVec 16) (hw : Nat)
  | condSelect (w : Width) (op : CondSelectOp) (rd rn rm : Reg) (cond : CondCode)
  | dataProc1 (w : Width) (op : DataProc1Op) (rd rn : Reg)
  | dataProc3 (w : Width) (op : DataProc3Op) (rd rn rm ra : Reg)
  | b (target : BitVec 64)
  | bcond (cond : CondCode) (target : BitVec 64)
  | cbz (w : Width) (rt : Reg) (target : BitVec 64)
  | cbnz (w : Width) (rt : Reg) (target : BitVec 64)
  | tbz (isNonZero : Bool) (rt : Reg) (bitPos : Nat) (target : BitVec 64)
  | ret (rn : Reg)
  | adr (rd : Reg) (target : BitVec 64)
  | adrp (rd : Reg) (target : BitVec 64)
  | nop
  | mrsTpidr (rt : Reg)
  | msrTpidr (rt : Reg)
  | mrsDczid (rt : Reg)
  | ldrN (w : Width) (cw : CW) (rt : Reg) (am : AddrMode)
  | ldrS (w : Width) (cw : CW) (rt : Reg) (am : AddrMode)
  | strN (cw : CW) (rt : Reg) (am : AddrMode)

/-- Concrete semantics of a micro-op: exactly the corresponding `execInst` arm. -/
def MOp.exec : MOp → State → State
  | .ldr w sz rt am, s => execLdr w sz false rt am s
  | .str sz rt am, s => execStr sz rt am s
  | .ldp w signed rt1 rt2 am, s => execLdp w signed rt1 rt2 am s
  | .stp w rt1 rt2 am, s => execStp w rt1 rt2 am s
  | .ldrSimdQ vt am, s => execLdrSimdQ vt am s
  | .strSimdQ vt am, s => execStrSimdQ vt am s
  | .ldpSimdQ vt1 vt2 am, s => execLdpSimdQ vt1 vt2 am s
  | .stpSimdQ vt1 vt2 am, s => execStpSimdQ vt1 vt2 am s
  | .addSubImm w op rd rn imm12 shift12, s => execAddSubImm w op rd rn imm12 shift12 s
  | .addSubShift w op rd rn rm shift amount, s => execAddSubShift w op rd rn rm shift amount s
  | .addSubExt w op rd rn rm ext amount, s => execAddSubExt w op rd rn rm ext amount s
  | .logicalImm w op rd rn imm, s => execLogicalImm w op rd rn imm s
  | .logicalShift w op rd rn rm shift amount, s => execLogicalShift w op rd rn rm shift amount s
  | .bitfield w op rd rn immr imms, s => execBitfield w op rd rn immr imms s
  | .movWide w op rd imm16 hw, s => execMoveWide w op rd imm16 hw s
  | .condSelect w op rd rn rm cond, s => execCondSelect w op rd rn rm cond s
  | .dataProc1 w op rd rn, s => execDataProc1 w op rd rn s
  | .dataProc3 w op rd rn rm ra, s => execDataProc3 w op rd rn rm ra s
  | .b target, s => s.setPC (s.pc + target)
  | .bcond cond target, s =>
    if ConditionHolds cond s.pstate then s.setPC (s.pc + target) else s.advancePC
  | .cbz w rt target, s =>
    if s.readReg w rt == 0#64 then s.setPC (s.pc + target) else s.advancePC
  | .cbnz w rt target, s =>
    if (s.readReg w rt == 0#64) != true then s.setPC (s.pc + target) else s.advancePC
  | .tbz isNonZero rt bitPos target, s =>
    if (s.readReg64 rt).getLsbD bitPos == isNonZero then s.setPC (s.pc + target) else s.advancePC
  | .ret rn, s => s.setPC (s.readReg64 rn)
  | .adr rd target, s =>
    (s.writeReg64 rd (s.pc + target)).advancePC
  | .adrp rd target, s =>
    (s.writeReg64 rd ((s.pc &&& 0xfffffffffffff000#64) + target)).advancePC
  | .nop, s => s.advancePC
  | .mrsTpidr rt, s => (s.writeReg64 rt s.tpidrEl0).advancePC
  | .msrTpidr rt, s => ({ s with tpidrEl0 := s.readReg64 rt }).advancePC
  | .mrsDczid rt, s => (s.writeReg64 rt 4#64).advancePC
  | .ldrN w cw rt am, s => execLdr w cw.size false rt am s
  | .ldrS w cw rt am, s => execLdr w cw.size true rt am s
  | .strN cw rt am, s => execStr cw.size rt am s

def lowerLdr : Width → MemWidth → Bool → Reg → AddrMode → Option MOp
  | .W64, .X64, false, dst, a => some (.ldr .W64 .X64 dst a)
  | w, .W32, false, dst, a => some (.ldrN w .b32 dst a)
  | w, .H16, false, dst, a => some (.ldrN w .b16 dst a)
  | w, .B8, false, dst, a => some (.ldrN w .b8 dst a)
  | w, .W32, true, dst, a => some (.ldrS w .b32 dst a)
  | w, .H16, true, dst, a => some (.ldrS w .b16 dst a)
  | w, .B8, true, dst, a => some (.ldrS w .b8 dst a)
  | _, _, _, _, _ => none

def lowerStr : MemWidth → Reg → AddrMode → Option MOp
  | .X64, src, dst => some (.str .X64 src dst)
  | .W32, src, dst => some (.strN .b32 src dst)
  | .H16, src, dst => some (.strN .b16 src dst)
  | .B8, src, dst => some (.strN .b8 src dst)

def lowerLdp : Width → Bool → Reg → Reg → AddrMode → Option MOp
  | w, false, d1, d2, src => some (.ldp w false d1 d2 src)
  | .W64, true, d1, d2, src => some (.ldp .W64 true d1 d2 src)
  | .W32, true, _, _, _ => none

def lowerStp (w : Width) (s1 s2 : Reg) (dst : AddrMode) : Option MOp :=
  some (.stp w s1 s2 dst)

def lowerSysReg (isRead : Bool) (sysreg : BitVec 15) (rt : Reg) : Option MOp :=
  if sysreg == 0x5e82#15 then
    some (if isRead then .mrsTpidr rt else .msrTpidr rt)
  else if sysreg == 0x5807#15 && isRead then
    some (.mrsDczid rt)
  else
    none

/-- Lower a decoded instruction to a micro-op, returning `none` for unsupported instructions. -/
def lower : Instr → Option MOp
  | .ldr w sz sgn dst a => lowerLdr w sz sgn dst a
  | .str sz src dst => lowerStr sz src dst
  | .ldp w sgn d1 d2 src => lowerLdp w sgn d1 d2 src
  | .stp w s1 s2 dst => lowerStp w s1 s2 dst
  | .ldrSimd .Q128 vt a => some (.ldrSimdQ vt a)
  | .ldrSimd _ _ _ => none
  | .strSimd .Q128 vt a => some (.strSimdQ vt a)
  | .strSimd _ _ _ => none
  | .ldpSimd .Q128 vt1 vt2 a => some (.ldpSimdQ vt1 vt2 a)
  | .ldpSimd _ _ _ _ => none
  | .stpSimd .Q128 vt1 vt2 a => some (.stpSimdQ vt1 vt2 a)
  | .stpSimd _ _ _ _ => none
  | .addSubImm w op d n imm12 shift12 => some (.addSubImm w op d n imm12 shift12)
  | .addSubShift w op d n m sh amt => some (.addSubShift w op d n m sh amt)
  | .addSubExt w op d n m ext amt => some (.addSubExt w op d n m ext amt)
  | .logicalImm w op d n imm => some (.logicalImm w op d n imm)
  | .logicalShift w op d n m sh amt => some (.logicalShift w op d n m sh amt)
  | .bitfield w op d n immr imms => some (.bitfield w op d n immr imms)
  | .moveWide w op d imm16 hw => some (.movWide w op d imm16 hw)
  | .condSelect w op d n m cond => some (.condSelect w op d n m cond)
  | .dataProc1 w op d n => some (.dataProc1 w op d n)
  | .dataProc3 w op d n m a => some (.dataProc3 w op d n m a)
  | .b target => some (.b target)
  | .bCond cond target => some (.bcond cond target)
  | .cbz w isNz r target => some (if isNz then .cbnz w r target else .cbz w r target)
  | .tbz _ isNonZero r bitPos target => some (.tbz isNonZero r bitPos target)
  | .ret r => some (.ret r)
  | .adr page d target => some (if page then .adrp d target else .adr d target)
  | .nop => some .nop
  | .hint _ => some .nop
  | .barrier _ _ => some .nop
  | .prfm _ _ => some .nop
  | .prfmLit _ _ => some .nop
  | .sysReg isRead sysreg rt => lowerSysReg isRead sysreg rt
  | _ => none

/-- Lowering is sound: the micro-op has exactly the semantics of the instruction. -/
theorem lower_sound {prog : Program} {i : Instr} {op : MOp} (h : lower i = some op) (s : State) :
    prog.evalInst i s = op.exec s := by
  cases i <;> dsimp only [lower] at h
  case ldr w sz sgn dst a =>
    cases w <;> cases sz <;> cases sgn <;> dsimp only [lowerLdr] at h <;> cases h <;> rfl
  case str sz src dst =>
    cases sz <;> dsimp only [lowerStr] at h <;> cases h <;> rfl
  case ldp w sgn d1 d2 src =>
    cases w <;> cases sgn <;> dsimp only [lowerLdp] at h <;> cases h <;> rfl
  case stp w s1 s2 dst =>
    dsimp only [lowerStp] at h; cases h; rfl
  case ldrSimd sz vt a =>
    cases sz <;> cases h <;> rfl
  case strSimd sz vt a =>
    cases sz <;> cases h <;> rfl
  case ldpSimd sz vt1 vt2 a =>
    cases sz <;> cases h <;> rfl
  case stpSimd sz vt1 vt2 a =>
    cases sz <;> cases h <;> rfl
  case cbz w isNz r target =>
    cases isNz <;> cases h <;> rfl
  case adr page d target =>
    cases page <;> cases h <;> rfl
  case sysReg isRead sysreg rt =>
    dsimp only [lowerSysReg] at h
    split at h
    · rename_i h1
      have h1' : sysreg = 0x5e82#15 := by simpa using h1
      subst h1'
      cases isRead <;> cases h <;> rfl
    · split at h
      · rename_i _ h2
        simp only [Bool.and_eq_true] at h2
        have h2a : sysreg = 0x5807#15 := by simpa using h2.1
        have h2b : isRead = true := h2.2
        subst h2a; subst h2b
        cases h; rfl
      · cases h
  all_goals { cases h; try rfl }

end ProofLib.SymBlock
