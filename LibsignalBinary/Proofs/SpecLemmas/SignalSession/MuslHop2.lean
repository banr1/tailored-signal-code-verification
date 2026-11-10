/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.CFG

@[expose] public section

set_option autoImplicit false

/-!
# musl Startup Hop 2 (`__init_libc` Prologue and `memset`)

Verifies hop 2 (`B + 0x5f4` to `B + 0x618`) of musl's startup path symbolically in base
`B` for every 16-byte-aligned initial stack pointer `sp0`, proving that
`memset(sp0 - 368, 0, 304)` zeroes all 38 64-bit `aux` slots across all four cache-line
residue classes `sp0 &&& 63#64 ∈ {0, 16, 32, 48}` under `DCZID_EL0 = 4`.
-/

namespace CryptoVerification.SignalSession.MuslStart

open Arm64 ProofLib

/-- Instruction decodes of musl's AArch64 `memset` (`B + 0x1e0 .. B + 0x2e0`, 65 words). -/
def MuslMemsetFetch (Q : Program) (B : BitVec 64) : Prop :=
  Q.fetch (B + 0x1e0#64) = some (Arm64.Instr.simdInsDup true false 0x01#5 0x1#4 0x01#5 0x00#5) ∧
  Q.fetch (B + 0x1e4#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x1e8#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x02#5) 0x060#12 false) ∧
  Q.fetch (B + 0x1ec#64) = some (Arm64.Instr.bCond (Arm64.CondCode.HI) 0x0000000000000074#64) ∧
  Q.fetch (B + 0x1f0#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x02#5) 0x010#12 false) ∧
  Q.fetch (B + 0x1f4#64) = some (Arm64.Instr.bCond (Arm64.CondCode.CS) 0x0000000000000040#64) ∧
  Q.fetch (B + 0x1f8#64) = some (Arm64.Instr.simdInsDup true false 0x08#5 0x7#4 0x00#5 0x01#5) ∧
  Q.fetch (B + 0x1fc#64) = some (Arm64.Instr.tbz (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x02#5) 3 0x0000000000000014#64) ∧
  Q.fetch (B + 0x200#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x01#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000000#64)) ∧
  Q.fetch (B + 0x204#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x01#5) (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x04#5) 0xfffffffffffffff8#64)) ∧
  Q.fetch (B + 0x208#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) ∧
  Q.fetch (B + 0x20c#64) = some (Arm64.Instr.nop) ∧
  Q.fetch (B + 0x210#64) = some (Arm64.Instr.tbz (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x02#5) 2 0x0000000000000010#64) ∧
  Q.fetch (B + 0x214#64) = some (Arm64.Instr.str (Arm64.MemWidth.W32) (Arm64.Reg.gpr 0x01#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000000#64)) ∧
  Q.fetch (B + 0x218#64) = some (Arm64.Instr.str (Arm64.MemWidth.W32) (Arm64.Reg.gpr 0x01#5) (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x04#5) 0xfffffffffffffffc#64)) ∧
  Q.fetch (B + 0x21c#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) ∧
  Q.fetch (B + 0x220#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x02#5) 0x0000000000000010#64) ∧
  Q.fetch (B + 0x224#64) = some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x01#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000000#64)) ∧
  Q.fetch (B + 0x228#64) = some (Arm64.Instr.tbz (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x02#5) 1 0x0000000000000008#64) ∧
  Q.fetch (B + 0x22c#64) = some (Arm64.Instr.str (Arm64.MemWidth.H16) (Arm64.Reg.gpr 0x01#5) (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x04#5) 0xfffffffffffffffe#64)) ∧
  Q.fetch (B + 0x230#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) ∧
  Q.fetch (B + 0x234#64) = some (Arm64.Instr.strSimd (Arm64.SimdMemSize.Q128) 0x00#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000000#64)) ∧
  Q.fetch (B + 0x238#64) = some (Arm64.Instr.tbz (Arm64.RegWidth.W32) true (Arm64.Reg.gpr 0x02#5) 6 0x0000000000000018#64) ∧
  Q.fetch (B + 0x23c#64) = some (Arm64.Instr.strSimd (Arm64.SimdMemSize.Q128) 0x00#5 (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x04#5) 0xfffffffffffffff0#64)) ∧
  Q.fetch (B + 0x240#64) = some (Arm64.Instr.tbz (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x02#5) 5 0x000000000000000c#64) ∧
  Q.fetch (B + 0x244#64) = some (Arm64.Instr.strSimd (Arm64.SimdMemSize.Q128) 0x00#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0x248#64) = some (Arm64.Instr.strSimd (Arm64.SimdMemSize.Q128) 0x00#5 (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x04#5) 0xffffffffffffffe0#64)) ∧
  Q.fetch (B + 0x24c#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) ∧
  Q.fetch (B + 0x250#64) = some (Arm64.Instr.strSimd (Arm64.SimdMemSize.Q128) 0x00#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0x254#64) = some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x00#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000020#64)) ∧
  Q.fetch (B + 0x258#64) = some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x00#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x04#5) 0xffffffffffffffe0#64)) ∧
  Q.fetch (B + 0x25c#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) ∧
  Q.fetch (B + 0x260#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W32) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x01#5) 0x000000ff000000ff#64) ∧
  Q.fetch (B + 0x264#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x00#5) 0xfffffffffffffff0#64) ∧
  Q.fetch (B + 0x268#64) = some (Arm64.Instr.strSimd (Arm64.SimdMemSize.Q128) 0x00#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000000#64)) ∧
  Q.fetch (B + 0x26c#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x02#5) 0x0a0#12 false) ∧
  Q.fetch (B + 0x270#64) = some (Arm64.Instr.condCompareImm (Arm64.RegWidth.W32) true (Arm64.Reg.gpr 0x01#5) 0x00#5 0x0#4 (Arm64.CondCode.CS)) ∧
  Q.fetch (B + 0x274#64) = some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0x0000000000000048#64) ∧
  Q.fetch (B + 0x278#64) = some (Arm64.Instr.sysReg true 0x5807#15 (Arm64.Reg.gpr 0x05#5)) ∧
  Q.fetch (B + 0x27c#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x05#5) 0x000000000000001f#64) ∧
  Q.fetch (B + 0x280#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x05#5) 0x004#12 false) ∧
  Q.fetch (B + 0x284#64) = some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0x0000000000000038#64) ∧
  Q.fetch (B + 0x288#64) = some (Arm64.Instr.strSimd (Arm64.SimdMemSize.Q128) 0x00#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x03#5) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0x28c#64) = some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x00#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x03#5) 0x0000000000000020#64)) ∧
  Q.fetch (B + 0x290#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) 0xffffffffffffffc0#64) ∧
  Q.fetch (B + 0x294#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x298#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) 0x080#12 false) ∧
  Q.fetch (B + 0x29c#64) = some (Arm64.Instr.nop) ∧
  Q.fetch (B + 0x2a0#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) 0x040#12 false) ∧
  Q.fetch (B + 0x2a4#64) = some (Arm64.Instr.dcZva (Arm64.Reg.gpr 0x03#5)) ∧
  Q.fetch (B + 0x2a8#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) 0x040#12 false) ∧
  Q.fetch (B + 0x2ac#64) = some (Arm64.Instr.bCond (Arm64.CondCode.HI) 0xfffffffffffffff4#64) ∧
  Q.fetch (B + 0x2b0#64) = some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x00#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x04#5) 0xffffffffffffffc0#64)) ∧
  Q.fetch (B + 0x2b4#64) = some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x00#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x04#5) 0xffffffffffffffe0#64)) ∧
  Q.fetch (B + 0x2b8#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) ∧
  Q.fetch (B + 0x2bc#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x03#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x2c0#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) 0x010#12 false) ∧
  Q.fetch (B + 0x2c4#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) 0x050#12 false) ∧
  Q.fetch (B + 0x2c8#64) = some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x00#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x03#5) 0x0000000000000020#64)) ∧
  Q.fetch (B + 0x2cc#64) = some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x00#5 (Arm64.AddrMode.PreIndex (Arm64.Reg.gpr 0x03#5) 0x0000000000000040#64)) ∧
  Q.fetch (B + 0x2d0#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x02#5) 0x040#12 false) ∧
  Q.fetch (B + 0x2d4#64) = some (Arm64.Instr.bCond (Arm64.CondCode.HI) 0xfffffffffffffff4#64) ∧
  Q.fetch (B + 0x2d8#64) = some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x00#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x04#5) 0xffffffffffffffc0#64)) ∧
  Q.fetch (B + 0x2dc#64) = some (Arm64.Instr.stpSimd (Arm64.SimdMemSize.Q128) 0x00#5 0x00#5 (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x04#5) 0xffffffffffffffe0#64)) ∧
  Q.fetch (B + 0x2e0#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5))

/-- Hop 2 fetches: `__init_libc` prologue (`B + 0x5f4 .. B + 0x614`) and `MuslMemsetFetch Q B`. -/
def MuslHop2Fetch (Q : Program) (B : BitVec 64) : Prop :=
  Q.fetch (B + 0x5f4#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.sp) (Arm64.Reg.sp) 0x180#12 false) ∧
  Q.fetch (B + 0x5f8#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000160#64)) ∧
  Q.fetch (B + 0x5fc#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000170#64)) ∧
  Q.fetch (B + 0x600#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x604#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x608#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x030#12 false) ∧
  Q.fetch (B + 0x60c#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W32) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x610#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x02#5) 0x0130#16 0) ∧
  Q.fetch (B + 0x614#64) = some (Arm64.Instr.bl 0xfffffffffffffbcc#64) ∧
  MuslMemsetFetch Q B

def Hop2Regs (sp0 envp p m : BitVec 64)
    (fs0 : FsState) (tr0 : List TraceEvent) (s : State) : Prop :=
  s.sp = sp0 - 416#64 ∧ s.readReg64 .x19 = p ∧ s.readReg64 .x20 = envp ∧ s.readReg64 .x21 = m ∧
  s.fs = fs0 ∧ s.trace = tr0

private theorem sub32_align16 {sp0 : BitVec 64} (h : (sp0 &&& 15#64 == 0#64) = true) :
    ((sp0 - 32#64) &&& 15#64 == 0#64) = true := by
  revert h; bv_bits

private theorem sub368_and_neg16 {sp0 : BitVec 64} (h : (sp0 &&& 15#64 == 0#64) = true) :
    (sp0 - 368#64) &&& 0xfffffffffffffff0#64 = sp0 - 368#64 := by
  revert h; bv_bits

private theorem align16_mod64 {sp0 : BitVec 64} (h : (sp0 &&& 15#64 == 0#64) = true) :
    sp0 &&& 63#64 = 0#64 ∨ sp0 &&& 63#64 = 16#64 ∨
    sp0 &&& 63#64 = 32#64 ∨ sp0 &&& 63#64 = 48#64 := by
  revert h; bv_bits

private theorem align64_r0 {sp0 : BitVec 64} (h : sp0 &&& 63#64 = 0#64) :
    (sp0 - 368#64) &&& 0xffffffffffffffc0#64 = sp0 - 384#64 ∧
    (sp0 - 384#64) &&& 63#64 = 0#64 := by
  revert h; bv_bits

private theorem align64_r16 {sp0 : BitVec 64} (h : sp0 &&& 63#64 = 16#64) :
    (sp0 - 368#64) &&& 0xffffffffffffffc0#64 = sp0 - 400#64 ∧
    (sp0 - 400#64) &&& 63#64 = 0#64 := by
  revert h; bv_bits

private theorem align64_r32 {sp0 : BitVec 64} (h : sp0 &&& 63#64 = 32#64) :
    (sp0 - 368#64) &&& 0xffffffffffffffc0#64 = sp0 - 416#64 ∧
    (sp0 - 416#64) &&& 63#64 = 0#64 := by
  revert h; bv_bits

private theorem align64_r48 {sp0 : BitVec 64} (h : sp0 &&& 63#64 = 48#64) :
    (sp0 - 368#64) &&& 0xffffffffffffffc0#64 = sp0 - 368#64 ∧
    (sp0 - 368#64) &&& 63#64 = 0#64 := by
  revert h; bv_bits

set_option maxHeartbeats 1200000 in
private theorem memset304_tail_r0 (Q : Program) (B : BitVec 64) (hf : MuslMemsetFetch Q B)
    (s1 : State) {fs0 : FsState} {tr0 : List TraceEvent} (sp0 envp p m : BitVec 64) (F : SepProp)
    (hpc : s1.pc = B + 0x294#64) (hrun : s1.status = .Running)
    (hfs : s1.fs = fs0) (htr : s1.trace = tr0) (hsp : s1.sp = sp0 - 416#64)
    (hq0 : s1.readVReg128 0#5 = 0#128) (hx4 : s1.readReg64 .x4 = sp0 - 64#64)
    (hx3 : s1.readReg64 .x3 = sp0 - 384#64) (h64 : (sp0 - 384#64) &&& 63#64 = 0#64)
    (hlr : s1.readReg64 .lr = B + 0x618#64)
    (h19 : s1.readReg64 .x19 = p) (h20 : s1.readReg64 .x20 = envp) (h21 : s1.readReg64 .x21 = m)
    (m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37 : BitVec 64) :
    SepWP Q (B + 0x618#64) s1
      (((sp0 - 368#64) ↦₆₄ 0#64) ∗ ((sp0 - 360#64) ↦₆₄ 0#64) ∗
       ((sp0 - 352#64) ↦₆₄ 0#64) ∗ ((sp0 - 344#64) ↦₆₄ 0#64) ∗
       ((sp0 - 336#64) ↦₆₄ 0#64) ∗ ((sp0 - 328#64) ↦₆₄ 0#64) ∗
       ((sp0 - 320#64) ↦₆₄ 0#64) ∗ ((sp0 - 312#64) ↦₆₄ 0#64) ∗
       ((sp0 - 304#64) ↦₆₄ m8) ∗ ((sp0 - 296#64) ↦₆₄ m9) ∗
       ((sp0 - 288#64) ↦₆₄ m10) ∗ ((sp0 - 280#64) ↦₆₄ m11) ∗
       ((sp0 - 272#64) ↦₆₄ m12) ∗ ((sp0 - 264#64) ↦₆₄ m13) ∗
       ((sp0 - 256#64) ↦₆₄ m14) ∗ ((sp0 - 248#64) ↦₆₄ m15) ∗
       ((sp0 - 240#64) ↦₆₄ m16) ∗ ((sp0 - 232#64) ↦₆₄ m17) ∗
       ((sp0 - 224#64) ↦₆₄ m18) ∗ ((sp0 - 216#64) ↦₆₄ m19) ∗
       ((sp0 - 208#64) ↦₆₄ m20) ∗ ((sp0 - 200#64) ↦₆₄ m21) ∗
       ((sp0 - 192#64) ↦₆₄ m22) ∗ ((sp0 - 184#64) ↦₆₄ m23) ∗
       ((sp0 - 176#64) ↦₆₄ m24) ∗ ((sp0 - 168#64) ↦₆₄ m25) ∗
       ((sp0 - 160#64) ↦₆₄ m26) ∗ ((sp0 - 152#64) ↦₆₄ m27) ∗
       ((sp0 - 144#64) ↦₆₄ m28) ∗ ((sp0 - 136#64) ↦₆₄ m29) ∗
       ((sp0 - 128#64) ↦₆₄ m30) ∗ ((sp0 - 120#64) ↦₆₄ m31) ∗
       ((sp0 - 112#64) ↦₆₄ m32) ∗ ((sp0 - 104#64) ↦₆₄ m33) ∗
       ((sp0 - 96#64) ↦₆₄ m34) ∗ ((sp0 - 88#64) ↦₆₄ m35) ∗
       ((sp0 - 80#64) ↦₆₄ m36) ∗ ((sp0 - 72#64) ↦₆₄ m37) ∗ F)
      (sepPost (Hop2Regs sp0 envp p m fs0 tr0)
        (((sp0 - 368#64) ↦₆₄ 0#64) ∗ ((sp0 - 360#64) ↦₆₄ 0#64) ∗
         ((sp0 - 352#64) ↦₆₄ 0#64) ∗ ((sp0 - 344#64) ↦₆₄ 0#64) ∗
         ((sp0 - 336#64) ↦₆₄ 0#64) ∗ ((sp0 - 328#64) ↦₆₄ 0#64) ∗
         ((sp0 - 320#64) ↦₆₄ 0#64) ∗ ((sp0 - 312#64) ↦₆₄ 0#64) ∗
         ((sp0 - 304#64) ↦₆₄ 0#64) ∗ ((sp0 - 296#64) ↦₆₄ 0#64) ∗
         ((sp0 - 288#64) ↦₆₄ 0#64) ∗ ((sp0 - 280#64) ↦₆₄ 0#64) ∗
         ((sp0 - 272#64) ↦₆₄ 0#64) ∗ ((sp0 - 264#64) ↦₆₄ 0#64) ∗
         ((sp0 - 256#64) ↦₆₄ 0#64) ∗ ((sp0 - 248#64) ↦₆₄ 0#64) ∗
         ((sp0 - 240#64) ↦₆₄ 0#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64) ∗
         ((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 0#64) ∗
         ((sp0 - 208#64) ↦₆₄ 0#64) ∗ ((sp0 - 200#64) ↦₆₄ 0#64) ∗
         ((sp0 - 192#64) ↦₆₄ 0#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64) ∗
         ((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 0#64) ∗
         ((sp0 - 160#64) ↦₆₄ 0#64) ∗ ((sp0 - 152#64) ↦₆₄ 0#64) ∗
         ((sp0 - 144#64) ↦₆₄ 0#64) ∗ ((sp0 - 136#64) ↦₆₄ 0#64) ∗
         ((sp0 - 128#64) ↦₆₄ 0#64) ∗ ((sp0 - 120#64) ↦₆₄ 0#64) ∗
         ((sp0 - 112#64) ↦₆₄ 0#64) ∗ ((sp0 - 104#64) ↦₆₄ 0#64) ∗
         ((sp0 - 96#64) ↦₆₄ 0#64) ∗ ((sp0 - 88#64) ↦₆₄ 0#64) ∗
         ((sp0 - 80#64) ↦₆₄ 0#64) ∗ ((sp0 - 72#64) ↦₆₄ 0#64) ∗ F)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, _⟩ := hf
  delta Hop2Regs
  iterate 18 wp_step
  wp_done

set_option maxHeartbeats 1200000 in
private theorem memset304_tail_r16 (Q : Program) (B : BitVec 64) (hf : MuslMemsetFetch Q B)
    (s1 : State) {fs0 : FsState} {tr0 : List TraceEvent} (sp0 envp p m : BitVec 64) (F : SepProp)
    (hpc : s1.pc = B + 0x294#64) (hrun : s1.status = .Running)
    (hfs : s1.fs = fs0) (htr : s1.trace = tr0) (hsp : s1.sp = sp0 - 416#64)
    (hq0 : s1.readVReg128 0#5 = 0#128) (hx4 : s1.readReg64 .x4 = sp0 - 64#64)
    (hx3 : s1.readReg64 .x3 = sp0 - 400#64) (h64 : (sp0 - 400#64) &&& 63#64 = 0#64)
    (hlr : s1.readReg64 .lr = B + 0x618#64)
    (h19 : s1.readReg64 .x19 = p) (h20 : s1.readReg64 .x20 = envp) (h21 : s1.readReg64 .x21 = m)
    (m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37 : BitVec 64) :
    SepWP Q (B + 0x618#64) s1
      (((sp0 - 368#64) ↦₆₄ 0#64) ∗ ((sp0 - 360#64) ↦₆₄ 0#64) ∗
       ((sp0 - 352#64) ↦₆₄ 0#64) ∗ ((sp0 - 344#64) ↦₆₄ 0#64) ∗
       ((sp0 - 336#64) ↦₆₄ 0#64) ∗ ((sp0 - 328#64) ↦₆₄ 0#64) ∗
       ((sp0 - 320#64) ↦₆₄ 0#64) ∗ ((sp0 - 312#64) ↦₆₄ 0#64) ∗
       ((sp0 - 304#64) ↦₆₄ m8) ∗ ((sp0 - 296#64) ↦₆₄ m9) ∗
       ((sp0 - 288#64) ↦₆₄ m10) ∗ ((sp0 - 280#64) ↦₆₄ m11) ∗
       ((sp0 - 272#64) ↦₆₄ m12) ∗ ((sp0 - 264#64) ↦₆₄ m13) ∗
       ((sp0 - 256#64) ↦₆₄ m14) ∗ ((sp0 - 248#64) ↦₆₄ m15) ∗
       ((sp0 - 240#64) ↦₆₄ m16) ∗ ((sp0 - 232#64) ↦₆₄ m17) ∗
       ((sp0 - 224#64) ↦₆₄ m18) ∗ ((sp0 - 216#64) ↦₆₄ m19) ∗
       ((sp0 - 208#64) ↦₆₄ m20) ∗ ((sp0 - 200#64) ↦₆₄ m21) ∗
       ((sp0 - 192#64) ↦₆₄ m22) ∗ ((sp0 - 184#64) ↦₆₄ m23) ∗
       ((sp0 - 176#64) ↦₆₄ m24) ∗ ((sp0 - 168#64) ↦₆₄ m25) ∗
       ((sp0 - 160#64) ↦₆₄ m26) ∗ ((sp0 - 152#64) ↦₆₄ m27) ∗
       ((sp0 - 144#64) ↦₆₄ m28) ∗ ((sp0 - 136#64) ↦₆₄ m29) ∗
       ((sp0 - 128#64) ↦₆₄ m30) ∗ ((sp0 - 120#64) ↦₆₄ m31) ∗
       ((sp0 - 112#64) ↦₆₄ m32) ∗ ((sp0 - 104#64) ↦₆₄ m33) ∗
       ((sp0 - 96#64) ↦₆₄ m34) ∗ ((sp0 - 88#64) ↦₆₄ m35) ∗
       ((sp0 - 80#64) ↦₆₄ m36) ∗ ((sp0 - 72#64) ↦₆₄ m37) ∗ F)
      (sepPost (Hop2Regs sp0 envp p m fs0 tr0)
        (((sp0 - 368#64) ↦₆₄ 0#64) ∗ ((sp0 - 360#64) ↦₆₄ 0#64) ∗
         ((sp0 - 352#64) ↦₆₄ 0#64) ∗ ((sp0 - 344#64) ↦₆₄ 0#64) ∗
         ((sp0 - 336#64) ↦₆₄ 0#64) ∗ ((sp0 - 328#64) ↦₆₄ 0#64) ∗
         ((sp0 - 320#64) ↦₆₄ 0#64) ∗ ((sp0 - 312#64) ↦₆₄ 0#64) ∗
         ((sp0 - 304#64) ↦₆₄ 0#64) ∗ ((sp0 - 296#64) ↦₆₄ 0#64) ∗
         ((sp0 - 288#64) ↦₆₄ 0#64) ∗ ((sp0 - 280#64) ↦₆₄ 0#64) ∗
         ((sp0 - 272#64) ↦₆₄ 0#64) ∗ ((sp0 - 264#64) ↦₆₄ 0#64) ∗
         ((sp0 - 256#64) ↦₆₄ 0#64) ∗ ((sp0 - 248#64) ↦₆₄ 0#64) ∗
         ((sp0 - 240#64) ↦₆₄ 0#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64) ∗
         ((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 0#64) ∗
         ((sp0 - 208#64) ↦₆₄ 0#64) ∗ ((sp0 - 200#64) ↦₆₄ 0#64) ∗
         ((sp0 - 192#64) ↦₆₄ 0#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64) ∗
         ((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 0#64) ∗
         ((sp0 - 160#64) ↦₆₄ 0#64) ∗ ((sp0 - 152#64) ↦₆₄ 0#64) ∗
         ((sp0 - 144#64) ↦₆₄ 0#64) ∗ ((sp0 - 136#64) ↦₆₄ 0#64) ∗
         ((sp0 - 128#64) ↦₆₄ 0#64) ∗ ((sp0 - 120#64) ↦₆₄ 0#64) ∗
         ((sp0 - 112#64) ↦₆₄ 0#64) ∗ ((sp0 - 104#64) ↦₆₄ 0#64) ∗
         ((sp0 - 96#64) ↦₆₄ 0#64) ∗ ((sp0 - 88#64) ↦₆₄ 0#64) ∗
         ((sp0 - 80#64) ↦₆₄ 0#64) ∗ ((sp0 - 72#64) ↦₆₄ 0#64) ∗ F)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, _⟩ := hf
  delta Hop2Regs
  iterate 22 wp_step
  wp_done

set_option maxHeartbeats 1200000 in
private theorem memset304_tail_r32 (Q : Program) (B : BitVec 64) (hf : MuslMemsetFetch Q B)
    (s1 : State) {fs0 : FsState} {tr0 : List TraceEvent} (sp0 envp p m : BitVec 64) (F : SepProp)
    (hpc : s1.pc = B + 0x294#64) (hrun : s1.status = .Running)
    (hfs : s1.fs = fs0) (htr : s1.trace = tr0) (hsp : s1.sp = sp0 - 416#64)
    (hq0 : s1.readVReg128 0#5 = 0#128) (hx4 : s1.readReg64 .x4 = sp0 - 64#64)
    (hx3 : s1.readReg64 .x3 = sp0 - 416#64) (h64 : (sp0 - 416#64) &&& 63#64 = 0#64)
    (hlr : s1.readReg64 .lr = B + 0x618#64)
    (h19 : s1.readReg64 .x19 = p) (h20 : s1.readReg64 .x20 = envp) (h21 : s1.readReg64 .x21 = m)
    (m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37 : BitVec 64) :
    SepWP Q (B + 0x618#64) s1
      (((sp0 - 368#64) ↦₆₄ 0#64) ∗ ((sp0 - 360#64) ↦₆₄ 0#64) ∗
       ((sp0 - 352#64) ↦₆₄ 0#64) ∗ ((sp0 - 344#64) ↦₆₄ 0#64) ∗
       ((sp0 - 336#64) ↦₆₄ 0#64) ∗ ((sp0 - 328#64) ↦₆₄ 0#64) ∗
       ((sp0 - 320#64) ↦₆₄ 0#64) ∗ ((sp0 - 312#64) ↦₆₄ 0#64) ∗
       ((sp0 - 304#64) ↦₆₄ m8) ∗ ((sp0 - 296#64) ↦₆₄ m9) ∗
       ((sp0 - 288#64) ↦₆₄ m10) ∗ ((sp0 - 280#64) ↦₆₄ m11) ∗
       ((sp0 - 272#64) ↦₆₄ m12) ∗ ((sp0 - 264#64) ↦₆₄ m13) ∗
       ((sp0 - 256#64) ↦₆₄ m14) ∗ ((sp0 - 248#64) ↦₆₄ m15) ∗
       ((sp0 - 240#64) ↦₆₄ m16) ∗ ((sp0 - 232#64) ↦₆₄ m17) ∗
       ((sp0 - 224#64) ↦₆₄ m18) ∗ ((sp0 - 216#64) ↦₆₄ m19) ∗
       ((sp0 - 208#64) ↦₆₄ m20) ∗ ((sp0 - 200#64) ↦₆₄ m21) ∗
       ((sp0 - 192#64) ↦₆₄ m22) ∗ ((sp0 - 184#64) ↦₆₄ m23) ∗
       ((sp0 - 176#64) ↦₆₄ m24) ∗ ((sp0 - 168#64) ↦₆₄ m25) ∗
       ((sp0 - 160#64) ↦₆₄ m26) ∗ ((sp0 - 152#64) ↦₆₄ m27) ∗
       ((sp0 - 144#64) ↦₆₄ m28) ∗ ((sp0 - 136#64) ↦₆₄ m29) ∗
       ((sp0 - 128#64) ↦₆₄ m30) ∗ ((sp0 - 120#64) ↦₆₄ m31) ∗
       ((sp0 - 112#64) ↦₆₄ m32) ∗ ((sp0 - 104#64) ↦₆₄ m33) ∗
       ((sp0 - 96#64) ↦₆₄ m34) ∗ ((sp0 - 88#64) ↦₆₄ m35) ∗
       ((sp0 - 80#64) ↦₆₄ m36) ∗ ((sp0 - 72#64) ↦₆₄ m37) ∗ F)
      (sepPost (Hop2Regs sp0 envp p m fs0 tr0)
        (((sp0 - 368#64) ↦₆₄ 0#64) ∗ ((sp0 - 360#64) ↦₆₄ 0#64) ∗
         ((sp0 - 352#64) ↦₆₄ 0#64) ∗ ((sp0 - 344#64) ↦₆₄ 0#64) ∗
         ((sp0 - 336#64) ↦₆₄ 0#64) ∗ ((sp0 - 328#64) ↦₆₄ 0#64) ∗
         ((sp0 - 320#64) ↦₆₄ 0#64) ∗ ((sp0 - 312#64) ↦₆₄ 0#64) ∗
         ((sp0 - 304#64) ↦₆₄ 0#64) ∗ ((sp0 - 296#64) ↦₆₄ 0#64) ∗
         ((sp0 - 288#64) ↦₆₄ 0#64) ∗ ((sp0 - 280#64) ↦₆₄ 0#64) ∗
         ((sp0 - 272#64) ↦₆₄ 0#64) ∗ ((sp0 - 264#64) ↦₆₄ 0#64) ∗
         ((sp0 - 256#64) ↦₆₄ 0#64) ∗ ((sp0 - 248#64) ↦₆₄ 0#64) ∗
         ((sp0 - 240#64) ↦₆₄ 0#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64) ∗
         ((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 0#64) ∗
         ((sp0 - 208#64) ↦₆₄ 0#64) ∗ ((sp0 - 200#64) ↦₆₄ 0#64) ∗
         ((sp0 - 192#64) ↦₆₄ 0#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64) ∗
         ((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 0#64) ∗
         ((sp0 - 160#64) ↦₆₄ 0#64) ∗ ((sp0 - 152#64) ↦₆₄ 0#64) ∗
         ((sp0 - 144#64) ↦₆₄ 0#64) ∗ ((sp0 - 136#64) ↦₆₄ 0#64) ∗
         ((sp0 - 128#64) ↦₆₄ 0#64) ∗ ((sp0 - 120#64) ↦₆₄ 0#64) ∗
         ((sp0 - 112#64) ↦₆₄ 0#64) ∗ ((sp0 - 104#64) ↦₆₄ 0#64) ∗
         ((sp0 - 96#64) ↦₆₄ 0#64) ∗ ((sp0 - 88#64) ↦₆₄ 0#64) ∗
         ((sp0 - 80#64) ↦₆₄ 0#64) ∗ ((sp0 - 72#64) ↦₆₄ 0#64) ∗ F)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, _⟩ := hf
  delta Hop2Regs
  iterate 22 wp_step
  wp_done

set_option maxHeartbeats 1200000 in
private theorem memset304_tail_r48 (Q : Program) (B : BitVec 64) (hf : MuslMemsetFetch Q B)
    (s1 : State) {fs0 : FsState} {tr0 : List TraceEvent} (sp0 envp p m : BitVec 64) (F : SepProp)
    (hpc : s1.pc = B + 0x294#64) (hrun : s1.status = .Running)
    (hfs : s1.fs = fs0) (htr : s1.trace = tr0) (hsp : s1.sp = sp0 - 416#64)
    (hq0 : s1.readVReg128 0#5 = 0#128) (hx4 : s1.readReg64 .x4 = sp0 - 64#64)
    (hx3 : s1.readReg64 .x3 = sp0 - 368#64) (h64 : (sp0 - 368#64) &&& 63#64 = 0#64)
    (hlr : s1.readReg64 .lr = B + 0x618#64)
    (h19 : s1.readReg64 .x19 = p) (h20 : s1.readReg64 .x20 = envp) (h21 : s1.readReg64 .x21 = m)
    (m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37 : BitVec 64) :
    SepWP Q (B + 0x618#64) s1
      (((sp0 - 368#64) ↦₆₄ 0#64) ∗ ((sp0 - 360#64) ↦₆₄ 0#64) ∗
       ((sp0 - 352#64) ↦₆₄ 0#64) ∗ ((sp0 - 344#64) ↦₆₄ 0#64) ∗
       ((sp0 - 336#64) ↦₆₄ 0#64) ∗ ((sp0 - 328#64) ↦₆₄ 0#64) ∗
       ((sp0 - 320#64) ↦₆₄ 0#64) ∗ ((sp0 - 312#64) ↦₆₄ 0#64) ∗
       ((sp0 - 304#64) ↦₆₄ m8) ∗ ((sp0 - 296#64) ↦₆₄ m9) ∗
       ((sp0 - 288#64) ↦₆₄ m10) ∗ ((sp0 - 280#64) ↦₆₄ m11) ∗
       ((sp0 - 272#64) ↦₆₄ m12) ∗ ((sp0 - 264#64) ↦₆₄ m13) ∗
       ((sp0 - 256#64) ↦₆₄ m14) ∗ ((sp0 - 248#64) ↦₆₄ m15) ∗
       ((sp0 - 240#64) ↦₆₄ m16) ∗ ((sp0 - 232#64) ↦₆₄ m17) ∗
       ((sp0 - 224#64) ↦₆₄ m18) ∗ ((sp0 - 216#64) ↦₆₄ m19) ∗
       ((sp0 - 208#64) ↦₆₄ m20) ∗ ((sp0 - 200#64) ↦₆₄ m21) ∗
       ((sp0 - 192#64) ↦₆₄ m22) ∗ ((sp0 - 184#64) ↦₆₄ m23) ∗
       ((sp0 - 176#64) ↦₆₄ m24) ∗ ((sp0 - 168#64) ↦₆₄ m25) ∗
       ((sp0 - 160#64) ↦₆₄ m26) ∗ ((sp0 - 152#64) ↦₆₄ m27) ∗
       ((sp0 - 144#64) ↦₆₄ m28) ∗ ((sp0 - 136#64) ↦₆₄ m29) ∗
       ((sp0 - 128#64) ↦₆₄ m30) ∗ ((sp0 - 120#64) ↦₆₄ m31) ∗
       ((sp0 - 112#64) ↦₆₄ m32) ∗ ((sp0 - 104#64) ↦₆₄ m33) ∗
       ((sp0 - 96#64) ↦₆₄ m34) ∗ ((sp0 - 88#64) ↦₆₄ m35) ∗
       ((sp0 - 80#64) ↦₆₄ m36) ∗ ((sp0 - 72#64) ↦₆₄ m37) ∗ F)
      (sepPost (Hop2Regs sp0 envp p m fs0 tr0)
        (((sp0 - 368#64) ↦₆₄ 0#64) ∗ ((sp0 - 360#64) ↦₆₄ 0#64) ∗
         ((sp0 - 352#64) ↦₆₄ 0#64) ∗ ((sp0 - 344#64) ↦₆₄ 0#64) ∗
         ((sp0 - 336#64) ↦₆₄ 0#64) ∗ ((sp0 - 328#64) ↦₆₄ 0#64) ∗
         ((sp0 - 320#64) ↦₆₄ 0#64) ∗ ((sp0 - 312#64) ↦₆₄ 0#64) ∗
         ((sp0 - 304#64) ↦₆₄ 0#64) ∗ ((sp0 - 296#64) ↦₆₄ 0#64) ∗
         ((sp0 - 288#64) ↦₆₄ 0#64) ∗ ((sp0 - 280#64) ↦₆₄ 0#64) ∗
         ((sp0 - 272#64) ↦₆₄ 0#64) ∗ ((sp0 - 264#64) ↦₆₄ 0#64) ∗
         ((sp0 - 256#64) ↦₆₄ 0#64) ∗ ((sp0 - 248#64) ↦₆₄ 0#64) ∗
         ((sp0 - 240#64) ↦₆₄ 0#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64) ∗
         ((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 0#64) ∗
         ((sp0 - 208#64) ↦₆₄ 0#64) ∗ ((sp0 - 200#64) ↦₆₄ 0#64) ∗
         ((sp0 - 192#64) ↦₆₄ 0#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64) ∗
         ((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 0#64) ∗
         ((sp0 - 160#64) ↦₆₄ 0#64) ∗ ((sp0 - 152#64) ↦₆₄ 0#64) ∗
         ((sp0 - 144#64) ↦₆₄ 0#64) ∗ ((sp0 - 136#64) ↦₆₄ 0#64) ∗
         ((sp0 - 128#64) ↦₆₄ 0#64) ∗ ((sp0 - 120#64) ↦₆₄ 0#64) ∗
         ((sp0 - 112#64) ↦₆₄ 0#64) ∗ ((sp0 - 104#64) ↦₆₄ 0#64) ∗
         ((sp0 - 96#64) ↦₆₄ 0#64) ∗ ((sp0 - 88#64) ↦₆₄ 0#64) ∗
         ((sp0 - 80#64) ↦₆₄ 0#64) ∗ ((sp0 - 72#64) ↦₆₄ 0#64) ∗ F)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, _⟩ := hf
  delta Hop2Regs
  iterate 18 wp_step
  wp_done

private theorem memset304_tail (Q : Program) (B : BitVec 64) (hf : MuslMemsetFetch Q B)
    (s1 : State) {fs0 : FsState} {tr0 : List TraceEvent} (sp0 envp p m : BitVec 64) (F : SepProp)
    (hpc : s1.pc = B + 0x294#64) (hrun : s1.status = .Running)
    (hfs : s1.fs = fs0) (htr : s1.trace = tr0) (hsp : s1.sp = sp0 - 416#64)
    (hal : (sp0 &&& 15#64 == 0#64) = true)
    (hq0 : s1.readVReg128 0#5 = 0#128) (hx4 : s1.readReg64 .x4 = sp0 - 64#64)
    (hx3 : s1.readReg64 .x3 = (sp0 - 368#64) &&& 0xffffffffffffffc0#64)
    (hlr : s1.readReg64 .lr = B + 0x618#64)
    (h19 : s1.readReg64 .x19 = p) (h20 : s1.readReg64 .x20 = envp) (h21 : s1.readReg64 .x21 = m)
    (m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37 : BitVec 64) :
    SepWP Q (B + 0x618#64) s1
      (((sp0 - 368#64) ↦₆₄ 0#64) ∗ ((sp0 - 360#64) ↦₆₄ 0#64) ∗
       ((sp0 - 352#64) ↦₆₄ 0#64) ∗ ((sp0 - 344#64) ↦₆₄ 0#64) ∗
       ((sp0 - 336#64) ↦₆₄ 0#64) ∗ ((sp0 - 328#64) ↦₆₄ 0#64) ∗
       ((sp0 - 320#64) ↦₆₄ 0#64) ∗ ((sp0 - 312#64) ↦₆₄ 0#64) ∗
       ((sp0 - 304#64) ↦₆₄ m8) ∗ ((sp0 - 296#64) ↦₆₄ m9) ∗
       ((sp0 - 288#64) ↦₆₄ m10) ∗ ((sp0 - 280#64) ↦₆₄ m11) ∗
       ((sp0 - 272#64) ↦₆₄ m12) ∗ ((sp0 - 264#64) ↦₆₄ m13) ∗
       ((sp0 - 256#64) ↦₆₄ m14) ∗ ((sp0 - 248#64) ↦₆₄ m15) ∗
       ((sp0 - 240#64) ↦₆₄ m16) ∗ ((sp0 - 232#64) ↦₆₄ m17) ∗
       ((sp0 - 224#64) ↦₆₄ m18) ∗ ((sp0 - 216#64) ↦₆₄ m19) ∗
       ((sp0 - 208#64) ↦₆₄ m20) ∗ ((sp0 - 200#64) ↦₆₄ m21) ∗
       ((sp0 - 192#64) ↦₆₄ m22) ∗ ((sp0 - 184#64) ↦₆₄ m23) ∗
       ((sp0 - 176#64) ↦₆₄ m24) ∗ ((sp0 - 168#64) ↦₆₄ m25) ∗
       ((sp0 - 160#64) ↦₆₄ m26) ∗ ((sp0 - 152#64) ↦₆₄ m27) ∗
       ((sp0 - 144#64) ↦₆₄ m28) ∗ ((sp0 - 136#64) ↦₆₄ m29) ∗
       ((sp0 - 128#64) ↦₆₄ m30) ∗ ((sp0 - 120#64) ↦₆₄ m31) ∗
       ((sp0 - 112#64) ↦₆₄ m32) ∗ ((sp0 - 104#64) ↦₆₄ m33) ∗
       ((sp0 - 96#64) ↦₆₄ m34) ∗ ((sp0 - 88#64) ↦₆₄ m35) ∗
       ((sp0 - 80#64) ↦₆₄ m36) ∗ ((sp0 - 72#64) ↦₆₄ m37) ∗ F)
      (sepPost (Hop2Regs sp0 envp p m fs0 tr0)
        (((sp0 - 368#64) ↦₆₄ 0#64) ∗ ((sp0 - 360#64) ↦₆₄ 0#64) ∗
         ((sp0 - 352#64) ↦₆₄ 0#64) ∗ ((sp0 - 344#64) ↦₆₄ 0#64) ∗
         ((sp0 - 336#64) ↦₆₄ 0#64) ∗ ((sp0 - 328#64) ↦₆₄ 0#64) ∗
         ((sp0 - 320#64) ↦₆₄ 0#64) ∗ ((sp0 - 312#64) ↦₆₄ 0#64) ∗
         ((sp0 - 304#64) ↦₆₄ 0#64) ∗ ((sp0 - 296#64) ↦₆₄ 0#64) ∗
         ((sp0 - 288#64) ↦₆₄ 0#64) ∗ ((sp0 - 280#64) ↦₆₄ 0#64) ∗
         ((sp0 - 272#64) ↦₆₄ 0#64) ∗ ((sp0 - 264#64) ↦₆₄ 0#64) ∗
         ((sp0 - 256#64) ↦₆₄ 0#64) ∗ ((sp0 - 248#64) ↦₆₄ 0#64) ∗
         ((sp0 - 240#64) ↦₆₄ 0#64) ∗ ((sp0 - 232#64) ↦₆₄ 0#64) ∗
         ((sp0 - 224#64) ↦₆₄ 0#64) ∗ ((sp0 - 216#64) ↦₆₄ 0#64) ∗
         ((sp0 - 208#64) ↦₆₄ 0#64) ∗ ((sp0 - 200#64) ↦₆₄ 0#64) ∗
         ((sp0 - 192#64) ↦₆₄ 0#64) ∗ ((sp0 - 184#64) ↦₆₄ 0#64) ∗
         ((sp0 - 176#64) ↦₆₄ 0#64) ∗ ((sp0 - 168#64) ↦₆₄ 0#64) ∗
         ((sp0 - 160#64) ↦₆₄ 0#64) ∗ ((sp0 - 152#64) ↦₆₄ 0#64) ∗
         ((sp0 - 144#64) ↦₆₄ 0#64) ∗ ((sp0 - 136#64) ↦₆₄ 0#64) ∗
         ((sp0 - 128#64) ↦₆₄ 0#64) ∗ ((sp0 - 120#64) ↦₆₄ 0#64) ∗
         ((sp0 - 112#64) ↦₆₄ 0#64) ∗ ((sp0 - 104#64) ↦₆₄ 0#64) ∗
         ((sp0 - 96#64) ↦₆₄ 0#64) ∗ ((sp0 - 88#64) ↦₆₄ 0#64) ∗
         ((sp0 - 80#64) ↦₆₄ 0#64) ∗ ((sp0 - 72#64) ↦₆₄ 0#64) ∗ F)) := by
  rcases align16_mod64 hal with h | h | h | h
  · exact memset304_tail_r0 Q B hf s1 sp0 envp p m F
      hpc hrun hfs htr hsp hq0 hx4 (hx3.trans (align64_r0 h).1) (align64_r0 h).2 hlr h19 h20 h21
      m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37
  · exact memset304_tail_r16 Q B hf s1 sp0 envp p m F
      hpc hrun hfs htr hsp hq0 hx4 (hx3.trans (align64_r16 h).1) (align64_r16 h).2 hlr h19 h20 h21
      m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37
  · exact memset304_tail_r32 Q B hf s1 sp0 envp p m F
      hpc hrun hfs htr hsp hq0 hx4 (hx3.trans (align64_r32 h).1) (align64_r32 h).2 hlr h19 h20 h21
      m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37
  · exact memset304_tail_r48 Q B hf s1 sp0 envp p m F
      hpc hrun hfs htr hsp hq0 hx4 (hx3.trans (align64_r48 h).1) (align64_r48 h).2 hlr h19 h20 h21
      m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37

set_option maxHeartbeats 1200000 in
theorem musl_memset304 (Q : Program) (B : BitVec 64) (hf : MuslMemsetFetch Q B)
    (s : State) {fs0 : FsState} {tr0 : List TraceEvent} (sp0 envp p m : BitVec 64) (F : SepProp)
    (hpc : s.pc = B + 0x1e0#64) (hrun : s.status = .Running)
    (hfs : s.fs = fs0) (htr : s.trace = tr0) (hsp : s.sp = sp0 - 416#64)
    (hal : (sp0 &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = sp0 - 368#64) (hx1 : s.readReg64 .x1 = 0#64)
    (hx2 : s.readReg64 .x2 = 304#64) (hlr : s.readReg64 .lr = B + 0x618#64)
    (h19 : s.readReg64 .x19 = p) (h20 : s.readReg64 .x20 = envp) (h21 : s.readReg64 .x21 = m)
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37 : BitVec 64) :
    SepWP Q (B + 0x618#64) s
      (((sp0 - 368#64) ↦₆₄ m0) ∗
       ((sp0 - 360#64) ↦₆₄ m1) ∗
       ((sp0 - 352#64) ↦₆₄ m2) ∗
       ((sp0 - 344#64) ↦₆₄ m3) ∗
       ((sp0 - 336#64) ↦₆₄ m4) ∗
       ((sp0 - 328#64) ↦₆₄ m5) ∗
       ((sp0 - 320#64) ↦₆₄ m6) ∗
       ((sp0 - 312#64) ↦₆₄ m7) ∗
       ((sp0 - 304#64) ↦₆₄ m8) ∗
       ((sp0 - 296#64) ↦₆₄ m9) ∗
       ((sp0 - 288#64) ↦₆₄ m10) ∗
       ((sp0 - 280#64) ↦₆₄ m11) ∗
       ((sp0 - 272#64) ↦₆₄ m12) ∗
       ((sp0 - 264#64) ↦₆₄ m13) ∗
       ((sp0 - 256#64) ↦₆₄ m14) ∗
       ((sp0 - 248#64) ↦₆₄ m15) ∗
       ((sp0 - 240#64) ↦₆₄ m16) ∗
       ((sp0 - 232#64) ↦₆₄ m17) ∗
       ((sp0 - 224#64) ↦₆₄ m18) ∗
       ((sp0 - 216#64) ↦₆₄ m19) ∗
       ((sp0 - 208#64) ↦₆₄ m20) ∗
       ((sp0 - 200#64) ↦₆₄ m21) ∗
       ((sp0 - 192#64) ↦₆₄ m22) ∗
       ((sp0 - 184#64) ↦₆₄ m23) ∗
       ((sp0 - 176#64) ↦₆₄ m24) ∗
       ((sp0 - 168#64) ↦₆₄ m25) ∗
       ((sp0 - 160#64) ↦₆₄ m26) ∗
       ((sp0 - 152#64) ↦₆₄ m27) ∗
       ((sp0 - 144#64) ↦₆₄ m28) ∗
       ((sp0 - 136#64) ↦₆₄ m29) ∗
       ((sp0 - 128#64) ↦₆₄ m30) ∗
       ((sp0 - 120#64) ↦₆₄ m31) ∗
       ((sp0 - 112#64) ↦₆₄ m32) ∗
       ((sp0 - 104#64) ↦₆₄ m33) ∗
       ((sp0 - 96#64) ↦₆₄ m34) ∗
       ((sp0 - 88#64) ↦₆₄ m35) ∗
       ((sp0 - 80#64) ↦₆₄ m36) ∗
       ((sp0 - 72#64) ↦₆₄ m37) ∗ F)
      (sepPost (Hop2Regs sp0 envp p m fs0 tr0)
        (((sp0 - 368#64) ↦₆₄ 0#64) ∗
         ((sp0 - 360#64) ↦₆₄ 0#64) ∗
         ((sp0 - 352#64) ↦₆₄ 0#64) ∗
         ((sp0 - 344#64) ↦₆₄ 0#64) ∗
         ((sp0 - 336#64) ↦₆₄ 0#64) ∗
         ((sp0 - 328#64) ↦₆₄ 0#64) ∗
         ((sp0 - 320#64) ↦₆₄ 0#64) ∗
         ((sp0 - 312#64) ↦₆₄ 0#64) ∗
         ((sp0 - 304#64) ↦₆₄ 0#64) ∗
         ((sp0 - 296#64) ↦₆₄ 0#64) ∗
         ((sp0 - 288#64) ↦₆₄ 0#64) ∗
         ((sp0 - 280#64) ↦₆₄ 0#64) ∗
         ((sp0 - 272#64) ↦₆₄ 0#64) ∗
         ((sp0 - 264#64) ↦₆₄ 0#64) ∗
         ((sp0 - 256#64) ↦₆₄ 0#64) ∗
         ((sp0 - 248#64) ↦₆₄ 0#64) ∗
         ((sp0 - 240#64) ↦₆₄ 0#64) ∗
         ((sp0 - 232#64) ↦₆₄ 0#64) ∗
         ((sp0 - 224#64) ↦₆₄ 0#64) ∗
         ((sp0 - 216#64) ↦₆₄ 0#64) ∗
         ((sp0 - 208#64) ↦₆₄ 0#64) ∗
         ((sp0 - 200#64) ↦₆₄ 0#64) ∗
         ((sp0 - 192#64) ↦₆₄ 0#64) ∗
         ((sp0 - 184#64) ↦₆₄ 0#64) ∗
         ((sp0 - 176#64) ↦₆₄ 0#64) ∗
         ((sp0 - 168#64) ↦₆₄ 0#64) ∗
         ((sp0 - 160#64) ↦₆₄ 0#64) ∗
         ((sp0 - 152#64) ↦₆₄ 0#64) ∗
         ((sp0 - 144#64) ↦₆₄ 0#64) ∗
         ((sp0 - 136#64) ↦₆₄ 0#64) ∗
         ((sp0 - 128#64) ↦₆₄ 0#64) ∗
         ((sp0 - 120#64) ↦₆₄ 0#64) ∗
         ((sp0 - 112#64) ↦₆₄ 0#64) ∗
         ((sp0 - 104#64) ↦₆₄ 0#64) ∗
         ((sp0 - 96#64) ↦₆₄ 0#64) ∗
         ((sp0 - 88#64) ↦₆₄ 0#64) ∗
         ((sp0 - 80#64) ↦₆₄ 0#64) ∗
         ((sp0 - 72#64) ↦₆₄ 0#64) ∗ F)) := by
  have ⟨f0, f1, f2, f3, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, _⟩ := hf
  iterate 14 wp_step
  rw [sub368_and_neg16 hal]
  iterate 3 wp_step
  refine memset304_tail Q B hf _ sp0 envp p m F
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37
  · rfl
  · exact hrun
  · exact hfs
  · exact htr
  · exact hsp
  · exact hal
  · rfl
  · simp only [wp_norm]
  · simp only [wp_norm]
  · simp only [wp_norm, hlr]
  · simp only [wp_norm, h19]
  · simp only [wp_norm, h20]
  · simp only [wp_norm, h21]

set_option maxHeartbeats 1200000 in
theorem musl_start_hop2 (Q : Program) (B : BitVec 64) (hf : MuslHop2Fetch Q B)
    (s : State) {fs0 : FsState} {tr0 : List TraceEvent} (sp0 envp p m x19v x20v x29v lr0 : BitVec 64)
    (hpc : s.pc = B + 0x5f4#64) (hrun : s.status = .Running)
    (hfs : s.fs = fs0) (htr : s.trace = tr0) (hsp : s.sp = sp0 - 32#64)
    (hal : (sp0 &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = envp) (hx1 : s.readReg64 .x1 = p) (h19 : s.readReg64 .x19 = x19v)
    (h20 : s.readReg64 .x20 = x20v) (h29 : s.readReg64 .x29 = x29v) (hlr : s.readReg64 .lr = lr0)
    (h21 : s.readReg64 .x21 = m)
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37 c0 c1 c2 c3 : BitVec 64) :
    SepWP Q (B + 0x618#64) s
      (((sp0 - 368#64) ↦₆₄ m0) ∗
       ((sp0 - 360#64) ↦₆₄ m1) ∗
       ((sp0 - 352#64) ↦₆₄ m2) ∗
       ((sp0 - 344#64) ↦₆₄ m3) ∗
       ((sp0 - 336#64) ↦₆₄ m4) ∗
       ((sp0 - 328#64) ↦₆₄ m5) ∗
       ((sp0 - 320#64) ↦₆₄ m6) ∗
       ((sp0 - 312#64) ↦₆₄ m7) ∗
       ((sp0 - 304#64) ↦₆₄ m8) ∗
       ((sp0 - 296#64) ↦₆₄ m9) ∗
       ((sp0 - 288#64) ↦₆₄ m10) ∗
       ((sp0 - 280#64) ↦₆₄ m11) ∗
       ((sp0 - 272#64) ↦₆₄ m12) ∗
       ((sp0 - 264#64) ↦₆₄ m13) ∗
       ((sp0 - 256#64) ↦₆₄ m14) ∗
       ((sp0 - 248#64) ↦₆₄ m15) ∗
       ((sp0 - 240#64) ↦₆₄ m16) ∗
       ((sp0 - 232#64) ↦₆₄ m17) ∗
       ((sp0 - 224#64) ↦₆₄ m18) ∗
       ((sp0 - 216#64) ↦₆₄ m19) ∗
       ((sp0 - 208#64) ↦₆₄ m20) ∗
       ((sp0 - 200#64) ↦₆₄ m21) ∗
       ((sp0 - 192#64) ↦₆₄ m22) ∗
       ((sp0 - 184#64) ↦₆₄ m23) ∗
       ((sp0 - 176#64) ↦₆₄ m24) ∗
       ((sp0 - 168#64) ↦₆₄ m25) ∗
       ((sp0 - 160#64) ↦₆₄ m26) ∗
       ((sp0 - 152#64) ↦₆₄ m27) ∗
       ((sp0 - 144#64) ↦₆₄ m28) ∗
       ((sp0 - 136#64) ↦₆₄ m29) ∗
       ((sp0 - 128#64) ↦₆₄ m30) ∗
       ((sp0 - 120#64) ↦₆₄ m31) ∗
       ((sp0 - 112#64) ↦₆₄ m32) ∗
       ((sp0 - 104#64) ↦₆₄ m33) ∗
       ((sp0 - 96#64) ↦₆₄ m34) ∗
       ((sp0 - 88#64) ↦₆₄ m35) ∗
       ((sp0 - 80#64) ↦₆₄ m36) ∗
       ((sp0 - 72#64) ↦₆₄ m37) ∗
       ((sp0 - 64#64) ↦₆₄ c0) ∗ ((sp0 - 56#64) ↦₆₄ c1) ∗ ((sp0 - 48#64) ↦₆₄ c2) ∗
       ((sp0 - 40#64) ↦₆₄ c3))
      (sepPost (Hop2Regs sp0 envp p m fs0 tr0)
        (((sp0 - 368#64) ↦₆₄ 0#64) ∗
         ((sp0 - 360#64) ↦₆₄ 0#64) ∗
         ((sp0 - 352#64) ↦₆₄ 0#64) ∗
         ((sp0 - 344#64) ↦₆₄ 0#64) ∗
         ((sp0 - 336#64) ↦₆₄ 0#64) ∗
         ((sp0 - 328#64) ↦₆₄ 0#64) ∗
         ((sp0 - 320#64) ↦₆₄ 0#64) ∗
         ((sp0 - 312#64) ↦₆₄ 0#64) ∗
         ((sp0 - 304#64) ↦₆₄ 0#64) ∗
         ((sp0 - 296#64) ↦₆₄ 0#64) ∗
         ((sp0 - 288#64) ↦₆₄ 0#64) ∗
         ((sp0 - 280#64) ↦₆₄ 0#64) ∗
         ((sp0 - 272#64) ↦₆₄ 0#64) ∗
         ((sp0 - 264#64) ↦₆₄ 0#64) ∗
         ((sp0 - 256#64) ↦₆₄ 0#64) ∗
         ((sp0 - 248#64) ↦₆₄ 0#64) ∗
         ((sp0 - 240#64) ↦₆₄ 0#64) ∗
         ((sp0 - 232#64) ↦₆₄ 0#64) ∗
         ((sp0 - 224#64) ↦₆₄ 0#64) ∗
         ((sp0 - 216#64) ↦₆₄ 0#64) ∗
         ((sp0 - 208#64) ↦₆₄ 0#64) ∗
         ((sp0 - 200#64) ↦₆₄ 0#64) ∗
         ((sp0 - 192#64) ↦₆₄ 0#64) ∗
         ((sp0 - 184#64) ↦₆₄ 0#64) ∗
         ((sp0 - 176#64) ↦₆₄ 0#64) ∗
         ((sp0 - 168#64) ↦₆₄ 0#64) ∗
         ((sp0 - 160#64) ↦₆₄ 0#64) ∗
         ((sp0 - 152#64) ↦₆₄ 0#64) ∗
         ((sp0 - 144#64) ↦₆₄ 0#64) ∗
         ((sp0 - 136#64) ↦₆₄ 0#64) ∗
         ((sp0 - 128#64) ↦₆₄ 0#64) ∗
         ((sp0 - 120#64) ↦₆₄ 0#64) ∗
         ((sp0 - 112#64) ↦₆₄ 0#64) ∗
         ((sp0 - 104#64) ↦₆₄ 0#64) ∗
         ((sp0 - 96#64) ↦₆₄ 0#64) ∗
         ((sp0 - 88#64) ↦₆₄ 0#64) ∗
         ((sp0 - 80#64) ↦₆₄ 0#64) ∗
         ((sp0 - 72#64) ↦₆₄ 0#64) ∗
         ((sp0 - 64#64) ↦₆₄ x29v) ∗ ((sp0 - 56#64) ↦₆₄ lr0) ∗ ((sp0 - 48#64) ↦₆₄ x20v) ∗
         ((sp0 - 40#64) ↦₆₄ x19v))) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, hmem⟩ := hf
  have hal' : (s.sp &&& 15#64 == 0#64) = true := hsp ▸ sub32_align16 hal
  iterate 9 wp_step
  refine musl_memset304 Q B hmem _ sp0 envp p m
    (((sp0 - 64#64) ↦₆₄ x29v) ∗ ((sp0 - 56#64) ↦₆₄ lr0) ∗
     ((sp0 - 48#64) ↦₆₄ x20v) ∗ ((sp0 - 40#64) ↦₆₄ x19v))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37
  · rfl
  · exact hrun
  · exact hfs
  · exact htr
  · simp only [wp_norm]
  · exact hal
  · simp only [wp_norm]
  · simp only [wp_norm]
  · simp only [wp_norm]
  · simp only [wp_norm]
  · simp only [wp_norm]
  · simp only [wp_norm]
  · simp only [wp_norm, h21]

end CryptoVerification.SignalSession.MuslStart
