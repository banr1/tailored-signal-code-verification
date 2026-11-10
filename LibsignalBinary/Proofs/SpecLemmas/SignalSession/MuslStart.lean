/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.MuslExit
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.MuslHop2

@[expose] public section

set_option autoImplicit false

/-!
# musl Startup Path from `_start` to `main`

Verifies hops 1–7 of musl's AArch64 startup sequence symbolically in page-aligned base
`B`, from `_start` (`B`) through `_start_c`, `__libc_start_main`, `__init_libc`,
`static_init_tls`, `__copy_tls`, `__init_tp` (`msr TPIDR_EL0` and `set_tid_address`),
and `libc_start_init` to `blr x21` entering `main`:

- `musl_start`: composed `SepWP` triple over hops 1–7 yielding `x0 = argc`,
  `x1 = sp0 + 8`, `sp = sp0 - 48`, and unchanged filesystem and trace.
- `musl_start_ofImage`: lifts the `SepWP` triple to a `Steps` execution of
  `Program.ofImage img E` when musl's text is loaded at `B` above `img.code`.
-/

namespace CryptoVerification.SignalSession.MuslStart

open Arm64 ProofLib CryptoVerification.SignalSession.MuslExit

/-- The code length of an image that `Obj.Loads li` produces is `4 * n` when `li.code` is the
bytes of a `WordTree` of checked size `n`. -/
theorem code_length_of_tree {li : Obj.LinkedImage} {img : Obj.Image} (himg : Obj.Loads li img)
    {t : ProgramReflection.WordTree} {n : Nat} (hcode : li.code = t.toBytes)
    (hsize : t.checkSize? = some n) : img.code.length = 4 * n := by
  obtain ⟨hc, -, -⟩ := ObjectLoad.Loads.canonical himg
  rw [hc, hcode]
  exact ProgramReflection.WordTree.length_toBytes_of_checkSize? hsize

/-- Hop 1 (26 instructions): `_start`, `_start_c`, and `__libc_start_main` up to `bl __init_libc`. -/
def MuslHop1Fetch (Q : Program) (B : BitVec 64) : Prop :=
  Q.fetch B = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x1d#5) 0x0000#16 0) ∧
  Q.fetch (B + 0x4#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x1e#5) 0x0000#16 0) ∧
  Q.fetch (B + 0x8#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x000#12 false) ∧
  Q.fetch (B + 0xc#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x01#5) 0xffffffffffb64000#64) ∧
  Q.fetch (B + 0x10#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x01#5) 0x000#12 false) ∧
  Q.fetch (B + 0x14#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.sp) (Arm64.Reg.gpr 0x00#5) 0xfffffffffffffff0#64) ∧
  Q.fetch (B + 0x18#64) = some (Arm64.Instr.b 0x0000000000000004#64) ∧
  Q.fetch (B + 0x1c#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x20#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x03#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x24#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x04#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x28#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.W32) false (Arm64.Reg.gpr 0x01#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.gpr 0x02#5) 0x0000000000000008#64)) ∧
  Q.fetch (B + 0x2c#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x03#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x03#5) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0x30#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x04#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x04#5) 0x0000000000000018#64)) ∧
  Q.fetch (B + 0x34#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x00#5) 0xfffffffffffeb000#64) ∧
  Q.fetch (B + 0x38#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x00#5) 0x200#12 false) ∧
  Q.fetch (B + 0x3c#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x40#64) = some (Arm64.Instr.b 0x00000000000007a0#64) ∧
  Q.fetch (B + 0x7e0#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1e#5) (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.PreIndex (Arm64.Reg.sp) 0xffffffffffffffe0#64)) ∧
  Q.fetch (B + 0x7e4#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0x7e8#64) = some (Arm64.Instr.addSubExt (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x01#5) (Arm64.ExtendType.SXTW) 3) ∧
  Q.fetch (B + 0x7ec#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W32) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x7f0#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x01#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x02#5) 0x0000000000000000#64)) ∧
  Q.fetch (B + 0x7f4#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x15#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x7f8#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x7fc#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x08#5) 0x008#12 false) ∧
  Q.fetch (B + 0x800#64) = some (Arm64.Instr.bl 0xfffffffffffffdf4#64)

def Hop1Regs (B sp0 envp p : BitVec 64) (a32 : BitVec 32)
    (fs0 : FsState) (tr0 : List TraceEvent) (s : State) : Prop :=
  s.sp = sp0 - 32#64 ∧ s.readReg64 .x0 = envp ∧ s.readReg64 .x1 = p ∧
  s.readReg64 .x19 = sp0 + 8#64 ∧ s.readReg64 .x20 = a32.zeroExtend 64 ∧
  s.readReg64 .x21 = B - 85504#64 ∧ s.readReg64 .lr = B + 2052#64 ∧ s.readReg64 .x29 = 0#64 ∧
  s.fs = fs0 ∧ s.trace = tr0

set_option maxHeartbeats 1600000 in
theorem musl_start_hop1 (Q : Program) (B : BitVec 64) (hf : MuslHop1Fetch Q B)
    (hB : B &&& 0xfff#64 = 0#64) (s : State) (hpc : s.pc = B) (hrun : s.status = .Running)
    (hal : (s.sp &&& 15#64 == 0#64) = true) (hsp16 : s.sp &&& -16#64 = s.sp)
    (p g3 g4 v0 v1 v2 v3 r19 r20 r21 envp : BitVec 64) (a32 ah32 : BitVec 32)
    (h19 : s.readReg64 .x19 = r19) (h20 : s.readReg64 .x20 = r20) (h21 : s.readReg64 .x21 = r21)
    (henvp : envp = s.sp + 8#64 + BitVec.signExtend 64 a32 <<< 3 + 8#64) :
    SepWP Q (B + 0x5f4#64) s
      ((s.sp ↦₃₂ a32) ∗ ((s.sp + 4#64) ↦₃₂ ah32) ∗ ((s.sp + 8#64) ↦₆₄ p) ∗
       ((B + 0x2010#64) ↦₆₄ g3) ∗ ((B + 0x2018#64) ↦₆₄ g4) ∗
       ((s.sp - 32#64) ↦₆₄ v0) ∗ ((s.sp - 24#64) ↦₆₄ v1) ∗ ((s.sp - 16#64) ↦₆₄ v2) ∗
       ((s.sp - 8#64) ↦₆₄ v3))
      (sepPost (Hop1Regs B s.sp envp p a32 s.fs s.trace)
        ((s.sp ↦₃₂ a32) ∗ ((s.sp + 4#64) ↦₃₂ ah32) ∗ ((s.sp + 8#64) ↦₆₄ p) ∗
         ((B + 0x2010#64) ↦₆₄ g3) ∗ ((B + 0x2018#64) ↦₆₄ g4) ∗
         ((s.sp - 32#64) ↦₆₄ 0#64) ∗ ((s.sp - 24#64) ↦₆₄ r21) ∗ ((s.sp - 16#64) ↦₆₄ r20) ∗
         ((s.sp - 8#64) ↦₆₄ r19))) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18,
    f19, f20, f21, f22, f23, f24, f25⟩ := hf
  change s.sp &&& 18446744073709551600#64 = s.sp at hsp16
  delta Hop1Regs
  iterate 26 wp_step
  wp_done

/-- Hop 3a (117 instructions): `__environ`, environment scan, `libc.auxv`, and `aux[tag]` population loop. -/
def MuslHop3aFetch (Q : Program) (B : BitVec 64) : Prop :=
  Q.fetch (B + 0x618#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x08#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x61c#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x14#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x08#5) 0x0000000000000040#64)) ∧
  Q.fetch (B + 0x620#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.gpr 0x14#5) 0x0000000000000008#64)) ∧
  Q.fetch (B + 0x624#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) true (Arm64.Reg.gpr 0x08#5) 0xfffffffffffffffc#64) ∧
  Q.fetch (B + 0x628#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x08#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x62c#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x14#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x08#5) 0x00000000000001f0#64)) ∧
  Q.fetch (B + 0x630#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.gpr 0x14#5) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0x634#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x08#5) 0x0000000000000040#64) ∧
  Q.fetch (B + 0x638#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.sp) 0x030#12 false) ∧
  Q.fetch (B + 0x63c#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x08#5) 0x025#12 false) ∧
  Q.fetch (B + 0x640#64) = some (Arm64.Instr.bCond (Arm64.CondCode.HI) 0x000000000000000c#64) ∧
  Q.fetch (B + 0x644#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x14#5) 0xfffffffffffffff8#64)) ∧
  Q.fetch (B + 0x648#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.RegOffset (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ExtendType.UXTX) 3)) ∧
  Q.fetch (B + 0x64c#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.gpr 0x14#5) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0x650#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) true (Arm64.Reg.gpr 0x08#5) 0xffffffffffffffec#64)

def Hop3aRegs (sp0 p m : BitVec 64)
    (fs0 : FsState) (tr0 : List TraceEvent) (s : State) : Prop :=
  s.sp = sp0 - 416#64 ∧ s.readReg64 .x19 = p ∧ s.readReg64 .x21 = m ∧
  s.fs = fs0 ∧ s.trace = tr0

set_option maxHeartbeats 3200000 in
theorem musl_start_hop3a (Q : Program) (B : BitVec 64) (hf : MuslHop3aFetch Q B)
    (hB : B &&& 0xfff#64 = 0#64) (s : State) {fs0 : FsState} {tr0 : List TraceEvent} (sp0 envp p m : BitVec 64)
    (hpc : s.pc = B + 0x618#64) (hrun : s.status = .Running)
    (hfs : s.fs = fs0) (htr : s.trace = tr0) (hsp : s.sp = sp0 - 416#64)
    (hx19 : s.readReg64 .x19 = p) (hx20 : s.readReg64 .x20 = envp) (h21 : s.readReg64 .x21 = m)
    (e0 e1 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : BitVec 64) :
    SepWP Q (B + 0x654#64) s
      (((B + 0x2040#64) ↦₆₄ e0) ∗
       (envp ↦₆₄ 0#64) ∗
       ((B + 0x21f0#64) ↦₆₄ e1) ∗
       ((envp + 8#64) ↦₆₄ 3#64) ∗
       ((envp + 16#64) ↦₆₄ a0) ∗
       ((envp + 24#64) ↦₆₄ 4#64) ∗
       ((envp + 32#64) ↦₆₄ a1) ∗
       ((envp + 40#64) ↦₆₄ 5#64) ∗
       ((envp + 48#64) ↦₆₄ a2) ∗
       ((envp + 56#64) ↦₆₄ 6#64) ∗
       ((envp + 64#64) ↦₆₄ a3) ∗
       ((envp + 72#64) ↦₆₄ 7#64) ∗
       ((envp + 80#64) ↦₆₄ a4) ∗
       ((envp + 88#64) ↦₆₄ 8#64) ∗
       ((envp + 96#64) ↦₆₄ a5) ∗
       ((envp + 104#64) ↦₆₄ 9#64) ∗
       ((envp + 112#64) ↦₆₄ a6) ∗
       ((envp + 120#64) ↦₆₄ 11#64) ∗
       ((envp + 128#64) ↦₆₄ a7) ∗
       ((envp + 136#64) ↦₆₄ 12#64) ∗
       ((envp + 144#64) ↦₆₄ a8) ∗
       ((envp + 152#64) ↦₆₄ 13#64) ∗
       ((envp + 160#64) ↦₆₄ a9) ∗
       ((envp + 168#64) ↦₆₄ 14#64) ∗
       ((envp + 176#64) ↦₆₄ a10) ∗
       ((envp + 184#64) ↦₆₄ 15#64) ∗
       ((envp + 192#64) ↦₆₄ a11) ∗
       ((envp + 200#64) ↦₆₄ 16#64) ∗
       ((envp + 208#64) ↦₆₄ a12) ∗
       ((envp + 216#64) ↦₆₄ 17#64) ∗
       ((envp + 224#64) ↦₆₄ a13) ∗
       ((envp + 232#64) ↦₆₄ 23#64) ∗
       ((envp + 240#64) ↦₆₄ a14) ∗
       ((envp + 248#64) ↦₆₄ 25#64) ∗
       ((envp + 256#64) ↦₆₄ a15) ∗
       ((envp + 264#64) ↦₆₄ 26#64) ∗
       ((envp + 272#64) ↦₆₄ a16) ∗
       ((envp + 280#64) ↦₆₄ 31#64) ∗
       ((envp + 288#64) ↦₆₄ a17) ∗
       ((envp + 296#64) ↦₆₄ 0#64) ∗
       ((sp0 - 344#64) ↦₆₄ w0) ∗
       ((sp0 - 336#64) ↦₆₄ w1) ∗
       ((sp0 - 328#64) ↦₆₄ w2) ∗
       ((sp0 - 320#64) ↦₆₄ w3) ∗
       ((sp0 - 312#64) ↦₆₄ w4) ∗
       ((sp0 - 304#64) ↦₆₄ w5) ∗
       ((sp0 - 296#64) ↦₆₄ w6) ∗
       ((sp0 - 280#64) ↦₆₄ w7) ∗
       ((sp0 - 272#64) ↦₆₄ w8) ∗
       ((sp0 - 264#64) ↦₆₄ w9) ∗
       ((sp0 - 256#64) ↦₆₄ w10) ∗
       ((sp0 - 248#64) ↦₆₄ w11) ∗
       ((sp0 - 240#64) ↦₆₄ w12) ∗
       ((sp0 - 232#64) ↦₆₄ w13) ∗
       ((sp0 - 184#64) ↦₆₄ w14) ∗
       ((sp0 - 168#64) ↦₆₄ w15) ∗
       ((sp0 - 160#64) ↦₆₄ w16) ∗
       ((sp0 - 120#64) ↦₆₄ w17))
      (sepPost (Hop3aRegs sp0 p m fs0 tr0)
        (((B + 0x2040#64) ↦₆₄ envp) ∗
       (envp ↦₆₄ 0#64) ∗
       ((B + 0x21f0#64) ↦₆₄ (envp + 8#64)) ∗
       ((envp + 8#64) ↦₆₄ 3#64) ∗
       ((envp + 16#64) ↦₆₄ a0) ∗
       ((envp + 24#64) ↦₆₄ 4#64) ∗
       ((envp + 32#64) ↦₆₄ a1) ∗
       ((envp + 40#64) ↦₆₄ 5#64) ∗
       ((envp + 48#64) ↦₆₄ a2) ∗
       ((envp + 56#64) ↦₆₄ 6#64) ∗
       ((envp + 64#64) ↦₆₄ a3) ∗
       ((envp + 72#64) ↦₆₄ 7#64) ∗
       ((envp + 80#64) ↦₆₄ a4) ∗
       ((envp + 88#64) ↦₆₄ 8#64) ∗
       ((envp + 96#64) ↦₆₄ a5) ∗
       ((envp + 104#64) ↦₆₄ 9#64) ∗
       ((envp + 112#64) ↦₆₄ a6) ∗
       ((envp + 120#64) ↦₆₄ 11#64) ∗
       ((envp + 128#64) ↦₆₄ a7) ∗
       ((envp + 136#64) ↦₆₄ 12#64) ∗
       ((envp + 144#64) ↦₆₄ a8) ∗
       ((envp + 152#64) ↦₆₄ 13#64) ∗
       ((envp + 160#64) ↦₆₄ a9) ∗
       ((envp + 168#64) ↦₆₄ 14#64) ∗
       ((envp + 176#64) ↦₆₄ a10) ∗
       ((envp + 184#64) ↦₆₄ 15#64) ∗
       ((envp + 192#64) ↦₆₄ a11) ∗
       ((envp + 200#64) ↦₆₄ 16#64) ∗
       ((envp + 208#64) ↦₆₄ a12) ∗
       ((envp + 216#64) ↦₆₄ 17#64) ∗
       ((envp + 224#64) ↦₆₄ a13) ∗
       ((envp + 232#64) ↦₆₄ 23#64) ∗
       ((envp + 240#64) ↦₆₄ a14) ∗
       ((envp + 248#64) ↦₆₄ 25#64) ∗
       ((envp + 256#64) ↦₆₄ a15) ∗
       ((envp + 264#64) ↦₆₄ 26#64) ∗
       ((envp + 272#64) ↦₆₄ a16) ∗
       ((envp + 280#64) ↦₆₄ 31#64) ∗
       ((envp + 288#64) ↦₆₄ a17) ∗
       ((envp + 296#64) ↦₆₄ 0#64) ∗
       ((sp0 - 344#64) ↦₆₄ a0) ∗
       ((sp0 - 336#64) ↦₆₄ a1) ∗
       ((sp0 - 328#64) ↦₆₄ a2) ∗
       ((sp0 - 320#64) ↦₆₄ a3) ∗
       ((sp0 - 312#64) ↦₆₄ a4) ∗
       ((sp0 - 304#64) ↦₆₄ a5) ∗
       ((sp0 - 296#64) ↦₆₄ a6) ∗
       ((sp0 - 280#64) ↦₆₄ a7) ∗
       ((sp0 - 272#64) ↦₆₄ a8) ∗
       ((sp0 - 264#64) ↦₆₄ a9) ∗
       ((sp0 - 256#64) ↦₆₄ a10) ∗
       ((sp0 - 248#64) ↦₆₄ a11) ∗
       ((sp0 - 240#64) ↦₆₄ a12) ∗
       ((sp0 - 232#64) ↦₆₄ a13) ∗
       ((sp0 - 184#64) ↦₆₄ a14) ∗
       ((sp0 - 168#64) ↦₆₄ a15) ∗
       ((sp0 - 160#64) ↦₆₄ a16) ∗
       ((sp0 - 120#64) ↦₆₄ a17))) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14⟩ := hf
  delta Hop3aRegs
  iterate 117 wp_step
  wp_done

/-- Hop 3b (91 instructions): `__hwcap`, `libc.page_size`, and `__progname` setup from `argv[0]` (`"libsignal-cli"`) up to `bl static_init_tls`. -/
def MuslHop3bFetch (Q : Program) (B : BitVec 64) : Prop :=
  Q.fetch (B + 0x654#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000b0#64)) ∧
  Q.fetch (B + 0x658#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000130#64)) ∧
  Q.fetch (B + 0x65c#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x0a#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x660#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x0a#5) 0x0000000000000250#64)) ∧
  Q.fetch (B + 0x664#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x08#5) 0x0000000000000018#64) ∧
  Q.fetch (B + 0x67c#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000128#64)) ∧
  Q.fetch (B + 0x680#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x13#5) 0x000#12 false) ∧
  Q.fetch (B + 0x684#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000060#64)) ∧
  Q.fetch (B + 0x688#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x0a#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x68c#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x0b#5) 0x0000000000001000#64) ∧
  Q.fetch (B + 0x690#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) 0x000#12 false) ∧
  Q.fetch (B + 0x694#64) = some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSEL) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x13#5) (Arm64.CondCode.EQ)) ∧
  Q.fetch (B + 0x698#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x0c#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x69c#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x0a#5) 0x0000000000000218#64)) ∧
  Q.fetch (B + 0x6a0#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x08#5) 0x000#12 false) ∧
  Q.fetch (B + 0x6a4#64) = some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSEL) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x08#5) (Arm64.CondCode.EQ)) ∧
  Q.fetch (B + 0x6a8#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x08#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x6ac#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x0c#5) 0x00000000000001e0#64)) ∧
  Q.fetch (B + 0x6b0#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x08#5) 0x00000000000001d8#64)) ∧
  Q.fetch (B + 0x6b4#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x09#5) 0x001#12 false) ∧
  Q.fetch (B + 0x6b8#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.B8) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.UnscaledOffset (Arm64.Reg.gpr 0x09#5) 0xffffffffffffffff#64)) ∧
  Q.fetch (B + 0x6bc#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W32) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x0a#5) 0x02f#12 false) ∧
  Q.fetch (B + 0x6c0#64) = some (Arm64.Instr.bCond (Arm64.CondCode.EQ) 0xfffffffffffffff0#64) ∧
  Q.fetch (B + 0x6c4#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W32) true (Arm64.Reg.gpr 0x0a#5) 0xfffffffffffffff0#64) ∧
  Q.fetch (B + 0x6c8#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.sp) 0x030#12 false) ∧
  Q.fetch (B + 0x6cc#64) = some (Arm64.Instr.bl 0x00000000000002a0#64)

def Hop3bRegs (B sp0 p m : BitVec 64)
    (fs0 : FsState) (tr0 : List TraceEvent) (s : State) : Prop :=
  s.sp = sp0 - 416#64 ∧ s.readReg64 .x19 = p ∧ s.readReg64 .x0 = sp0 - 368#64 ∧
  s.readReg64 .lr = B + 0x6d0#64 ∧ s.readReg64 .x21 = m ∧
  s.fs = fs0 ∧ s.trace = tr0

set_option maxHeartbeats 3200000 in
theorem musl_start_hop3b (Q : Program) (B : BitVec 64) (hf : MuslHop3bFetch Q B)
    (hB : B &&& 0xfff#64 = 0#64) (s : State) {fs0 : FsState} {tr0 : List TraceEvent} (sp0 p m : BitVec 64)
    (hpc : s.pc = B + 0x654#64) (hrun : s.status = .Running)
    (hfs : s.fs = fs0) (htr : s.trace = tr0) (hsp : s.sp = sp0 - 416#64)
    (hx19 : s.readReg64 .x19 = p) (hp : p ≠ 0#64) (h21 : s.readReg64 .x21 = m)
    (hal : (sp0 &&& 15#64 == 0#64) = true)
    (hw ex pg d0 d1 d2 d3 : BitVec 64) :
    SepWP Q (B + 0x96c#64) s
      (((sp0 - 240#64) ↦₆₄ hw) ∗
       ((sp0 - 112#64) ↦₆₄ 0#64) ∗
       ((B + 0x2250#64) ↦₆₄ d0) ∗
       ((sp0 - 120#64) ↦₆₄ ex) ∗
       ((sp0 - 320#64) ↦₆₄ pg) ∗
       ((B + 0x2218#64) ↦₆₄ d1) ∗
       ((B + 0x21e0#64) ↦₆₄ d2) ∗
       ((B + 0x21d8#64) ↦₆₄ d3) ∗
       (p ↦₈ 0x6c#8) ∗
       ((p + 1#64) ↦₈ 0x69#8) ∗
       ((p + 2#64) ↦₈ 0x62#8) ∗
       ((p + 3#64) ↦₈ 0x73#8) ∗
       ((p + 4#64) ↦₈ 0x69#8) ∗
       ((p + 5#64) ↦₈ 0x67#8) ∗
       ((p + 6#64) ↦₈ 0x6e#8) ∗
       ((p + 7#64) ↦₈ 0x61#8) ∗
       ((p + 8#64) ↦₈ 0x6c#8) ∗
       ((p + 9#64) ↦₈ 0x2d#8) ∗
       ((p + 10#64) ↦₈ 0x63#8) ∗
       ((p + 11#64) ↦₈ 0x6c#8) ∗
       ((p + 12#64) ↦₈ 0x69#8) ∗
       ((p + 13#64) ↦₈ 0x00#8))
      (sepPost (Hop3bRegs B sp0 p m fs0 tr0)
        (((sp0 - 240#64) ↦₆₄ hw) ∗
       ((sp0 - 112#64) ↦₆₄ 0#64) ∗
       ((B + 0x2250#64) ↦₆₄ hw) ∗
       ((sp0 - 120#64) ↦₆₄ ex) ∗
       ((sp0 - 320#64) ↦₆₄ pg) ∗
       ((B + 0x2218#64) ↦₆₄ pg) ∗
       ((B + 0x21e0#64) ↦₆₄ p) ∗
       ((B + 0x21d8#64) ↦₆₄ p) ∗
       (p ↦₈ 0x6c#8) ∗
       ((p + 1#64) ↦₈ 0x69#8) ∗
       ((p + 2#64) ↦₈ 0x62#8) ∗
       ((p + 3#64) ↦₈ 0x73#8) ∗
       ((p + 4#64) ↦₈ 0x69#8) ∗
       ((p + 5#64) ↦₈ 0x67#8) ∗
       ((p + 6#64) ↦₈ 0x6e#8) ∗
       ((p + 7#64) ↦₈ 0x61#8) ∗
       ((p + 8#64) ↦₈ 0x6c#8) ∗
       ((p + 9#64) ↦₈ 0x2d#8) ∗
       ((p + 10#64) ↦₈ 0x63#8) ∗
       ((p + 11#64) ↦₈ 0x6c#8) ∗
       ((p + 12#64) ↦₈ 0x69#8) ∗
       ((p + 13#64) ↦₈ 0x00#8))) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25⟩ := hf
  have hal' : (s.sp &&& 15#64 == 0#64) = true := by
    rw [hsp]
    have h0 : sp0 &&& 15#64 = 0#64 := eq_of_beq hal
    have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
      simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
    have h' := congrArg BitVec.toNat h0
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [e] at h' ⊢
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
    have hlt := sp0.isLt; omega
  delta Hop3bRegs
  have hpb : (p == 0#64) = false := by simpa using hp
  iterate 91 wp_step
  wp_done

/-- Hop 4: `static_init_tls` program-header scan (`AT_PHDR`) up to `bl __copy_tls`. -/
def MuslHop4Fetch (Q : Program) (B : BitVec 64) : Prop :=
  Q.fetch (B + 0x96c#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PreIndex (Arm64.Reg.sp) 0xfffffffffffffff0#64)) ∧
  Q.fetch (B + 0x970#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000028#64)) ∧
  Q.fetch (B + 0x974#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0a#5) 0x00000000000000d0#64) ∧
  Q.fetch (B + 0x978#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x00#5) 0x0000000000000018#64)) ∧
  Q.fetch (B + 0x97c#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x0b#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x980#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x0f#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x984#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.W32) false (Arm64.Reg.gpr 0x0d#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x0b#5) 0x0000000000000000#64)) ∧
  Q.fetch (B + 0x988#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x10#5) 0xe551#16 0) ∧
  Q.fetch (B + 0x98c#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x0f#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x0f#5) 0x0000000000000008#64)) ∧
  Q.fetch (B + 0x990#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x994#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x998#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVK) (Arm64.Reg.gpr 0x10#5) 0x6474#16 16) ∧
  Q.fetch (B + 0x99c#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x11#5) 0x0080#16 16) ∧
  Q.fetch (B + 0x9a0#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x0c#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x9a4#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W32) (Arm64.MemWidth.W32) false (Arm64.Reg.gpr 0x00#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x12#5) 0x0000000000000000#64)) ∧
  Q.fetch (B + 0x9a8#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W32) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x00#5) 0x006#12 false) ∧
  Q.fetch (B + 0x9ac#64) = some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0x0000000000000010#64) ∧
  Q.fetch (B + 0x9b0#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x12#5) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0x9b4#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x9b8#64) = some (Arm64.Instr.b 0x0000000000000044#64) ∧
  Q.fetch (B + 0x9bc#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x0f#5) 0x0000000000000018#64) ∧
  Q.fetch (B + 0x9d4#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W32) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x00#5) 0x007#12 false) ∧
  Q.fetch (B + 0x9d8#64) = some (Arm64.Instr.condSelect (Arm64.RegWidth.W64) (Arm64.CondSelectOp.CSEL) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x08#5) (Arm64.CondCode.EQ)) ∧
  Q.fetch (B + 0x9dc#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W32) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x10#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x9e0#64) = some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0x000000000000001c#64) ∧
  Q.fetch (B + 0x9e4#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x00#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x12#5) 0x0000000000000028#64)) ∧
  Q.fetch (B + 0x9e8#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x9ec#64) = some (Arm64.Instr.bCond (Arm64.CondCode.LS) 0x0000000000000010#64) ∧
  Q.fetch (B + 0x9fc#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 0x001#12 false) ∧
  Q.fetch (B + 0xa00#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x12#5) (Arm64.Reg.gpr 0x0e#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0xa04#64) = some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0xffffffffffffffa0#64) ∧
  Q.fetch (B + 0xa08#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x08#5) 0x000000000000003c#64) ∧
  Q.fetch (B + 0xa0c#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x08#5) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0xa10#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x0d#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x08#5) 0x0000000000000020#64)) ∧
  Q.fetch (B + 0xa14#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x0c#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0xa18#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0c#5) 0x050#12 false) ∧
  Q.fetch (B + 0xa1c#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x08#5) 0x0000000000000028#64)) ∧
  Q.fetch (B + 0xa20#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0xa24#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x0b#5) 0x0001#16 0) ∧
  Q.fetch (B + 0xa28#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x0c#5) 0x0000000000000008#64)) ∧
  Q.fetch (B + 0xa2c#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x0d#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0xa30#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) 0x1f8#12 false) ∧
  Q.fetch (B + 0xa34#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x0c#5) 0x0000000000000020#64)) ∧
  Q.fetch (B + 0xa38#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x0d#5) 0x0000000000000018#64)) ∧
  Q.fetch (B + 0xa3c#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x0c#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x0d#5) 0x0000000000000000#64)) ∧
  Q.fetch (B + 0xa40#64) = some (Arm64.Instr.b 0x0000000000000014#64) ∧
  Q.fetch (B + 0xa54#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0xa58#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0a#5) 0x001#12 false) ∧
  Q.fetch (B + 0xa5c#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x09#5) 0x010#12 false) ∧
  Q.fetch (B + 0xa60#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0xa64#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0xa68#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x0d#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0xa6c#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.gpr 0x0d#5) 0x068#12 false) ∧
  Q.fetch (B + 0xa70#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0xa74#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x0a#5) 0x007#12 false) ∧
  Q.fetch (B + 0xa78#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0xa7c#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x09#5) 0x010#12 false) ∧
  Q.fetch (B + 0xa80#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x0d#5) 0x0000000000000000#64)) ∧
  Q.fetch (B + 0xa84#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x0d#5) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0xa88#64) = some (Arm64.Instr.bCond (Arm64.CondCode.HI) 0x0000000000000010#64) ∧
  Q.fetch (B + 0xa8c#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x0b#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0xa90#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x0a#5) 0x0008#16 0) ∧
  Q.fetch (B + 0xa94#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x0b#5) 0x0000000000000070#64)) ∧
  Q.fetch (B + 0xa98#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0xa9c#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x09#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0xaa0#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x09#5) 0x200#12 false) ∧
  Q.fetch (B + 0xaa4#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0xaa8#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) 0x0ef#12 false) ∧
  Q.fetch (B + 0xaac#64) = some (Arm64.Instr.logicalImm (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x08#5) 0xfffffffffffffff8#64) ∧
  Q.fetch (B + 0xab0#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x01#5) 0x151#12 false) ∧
  Q.fetch (B + 0xab4#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x09#5) 0x0000000000000000#64)) ∧
  Q.fetch (B + 0xab8#64) = some (Arm64.Instr.bCond (Arm64.CondCode.CC) 0x0000000000000024#64) ∧
  Q.fetch (B + 0xadc#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x00#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0xae0#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x00#5) 0x080#12 false) ∧
  Q.fetch (B + 0xae4#64) = some (Arm64.Instr.bl 0xfffffffffffffdf0#64)

def Hop4Regs (B sp0 m : BitVec 64)
    (fs0 : FsState) (tr0 : List TraceEvent) (s : State) : Prop :=
  s.sp = sp0 - 432#64 ∧ s.readReg64 .x0 = B + 0x2080#64 ∧ s.readReg64 .lr = B + 0xae8#64 ∧
  s.readReg64 .x21 = m ∧
  s.fs = fs0 ∧ s.trace = tr0

set_option maxHeartbeats 3200000 in
theorem musl_start_hop4 (Q : Program) (B : BitVec 64) (hf : MuslHop4Fetch Q B)
    (hB : B &&& 0xfff#64 = 0#64) (s : State) {fs0 : FsState} {tr0 : List TraceEvent} (sp0 ph m : BitVec 64)
    (hpc : s.pc = B + 0x96c#64) (hrun : s.status = .Running)
    (hfs : s.fs = fs0) (htr : s.trace = tr0) (hsp : s.sp = sp0 - 416#64)
    (hx0 : s.readReg64 .x0 = sp0 - 368#64) (hlr : s.readReg64 .lr = B + 0x6d0#64)
    (h21 : s.readReg64 .x21 = m)
    (hal : (sp0 &&& 15#64 == 0#64) = true) (hph : ph + 504#64 ≠ 0#64)
    (v0 t0 t1 t2 t3 t4 t5 t6 t7 t8 : BitVec 64) :
    SepWP Q (B + 0x8d4#64) s
      (((sp0 - 432#64) ↦₆₄ v0) ∗
       ((sp0 - 344#64) ↦₆₄ ph) ∗
       ((sp0 - 336#64) ↦₆₄ 56#64) ∗
       ((sp0 - 328#64) ↦₆₄ 11#64) ∗
       ((B + 0x2000#64) ↦₃₂ 0x20000#32) ∗
       ((B + 0x2008#64) ↦₆₄ 0#64) ∗
       ((B + 0x2058#64) ↦₆₄ t0) ∗
       ((B + 0x2060#64) ↦₆₄ t1) ∗
       ((B + 0x2068#64) ↦₆₄ t2) ∗
       ((B + 0x2070#64) ↦₆₄ t3) ∗
       ((B + 0x2078#64) ↦₆₄ t4) ∗
       ((B + 0x21f8#64) ↦₆₄ t5) ∗
       ((B + 0x2200#64) ↦₆₄ t6) ∗
       ((B + 0x2208#64) ↦₆₄ t7) ∗
       ((B + 0x2210#64) ↦₆₄ t8) ∗
       (ph ↦₃₂ᵣ 6#32) ∗
       ((ph + 16#64) ↦₆₄ᵣ ph) ∗
       ((ph + 56#64) ↦₃₂ᵣ 1#32) ∗
       ((ph + 112#64) ↦₃₂ᵣ 1#32) ∗
       ((ph + 168#64) ↦₃₂ᵣ 1#32) ∗
       ((ph + 224#64) ↦₃₂ᵣ 1#32) ∗
       ((ph + 280#64) ↦₃₂ᵣ 1#32) ∗
       ((ph + 336#64) ↦₃₂ᵣ 1#32) ∗
       ((ph + 392#64) ↦₃₂ᵣ 1#32) ∗
       ((ph + 448#64) ↦₃₂ᵣ 1#32) ∗
       ((ph + 504#64) ↦₃₂ᵣ 7#32) ∗
       ((ph + 520#64) ↦₆₄ᵣ 0#64) ∗
       ((ph + 536#64) ↦₆₄ᵣ 0#64) ∗
       ((ph + 544#64) ↦₆₄ᵣ 0#64) ∗
       ((ph + 552#64) ↦₆₄ᵣ 0#64) ∗
       ((ph + 560#64) ↦₃₂ᵣ 0x6474e551#32) ∗
       ((ph + 600#64) ↦₆₄ᵣ 0#64))
      (sepPost (Hop4Regs B sp0 m fs0 tr0)
        (((sp0 - 432#64) ↦₆₄ (B + 0x6d0#64)) ∗
         ((sp0 - 344#64) ↦₆₄ ph) ∗
         ((sp0 - 336#64) ↦₆₄ 56#64) ∗
         ((sp0 - 328#64) ↦₆₄ 11#64) ∗
         ((B + 0x2000#64) ↦₃₂ 0x20000#32) ∗
         ((B + 0x2008#64) ↦₆₄ 0#64) ∗
         ((B + 0x2058#64) ↦₆₄ 0#64) ∗
         ((B + 0x2060#64) ↦₆₄ 0#64) ∗
         ((B + 0x2068#64) ↦₆₄ 0#64) ∗
         ((B + 0x2070#64) ↦₆₄ 8#64) ∗
         ((B + 0x2078#64) ↦₆₄ 0#64) ∗
         ((B + 0x21f8#64) ↦₆₄ (B + 0x2050#64)) ∗
         ((B + 0x2200#64) ↦₆₄ 0xe0#64) ∗
         ((B + 0x2208#64) ↦₆₄ 8#64) ∗
         ((B + 0x2210#64) ↦₆₄ 1#64) ∗
         (ph ↦₃₂ᵣ 6#32) ∗
         ((ph + 16#64) ↦₆₄ᵣ ph) ∗
         ((ph + 56#64) ↦₃₂ᵣ 1#32) ∗
         ((ph + 112#64) ↦₃₂ᵣ 1#32) ∗
         ((ph + 168#64) ↦₃₂ᵣ 1#32) ∗
         ((ph + 224#64) ↦₃₂ᵣ 1#32) ∗
         ((ph + 280#64) ↦₃₂ᵣ 1#32) ∗
         ((ph + 336#64) ↦₃₂ᵣ 1#32) ∗
         ((ph + 392#64) ↦₃₂ᵣ 1#32) ∗
         ((ph + 448#64) ↦₃₂ᵣ 1#32) ∗
         ((ph + 504#64) ↦₃₂ᵣ 7#32) ∗
         ((ph + 520#64) ↦₆₄ᵣ 0#64) ∗
         ((ph + 536#64) ↦₆₄ᵣ 0#64) ∗
         ((ph + 544#64) ↦₆₄ᵣ 0#64) ∗
         ((ph + 552#64) ↦₆₄ᵣ 0#64) ∗
         ((ph + 560#64) ↦₃₂ᵣ 0x6474e551#32) ∗
         ((ph + 600#64) ↦₆₄ᵣ 0#64))) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55, f56, f57, f58, f59, f60, f61, f62, f63, f64, f65, f66, f67, f68, f69, f70, f71, f72, f73, f74⟩ := hf
  have hal' : (s.sp &&& 15#64 == 0#64) = true := by
    rw [hsp]
    have h0 : sp0 &&& 15#64 = 0#64 := eq_of_beq hal
    have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
      simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
    have h' := congrArg BitVec.toNat h0
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [e] at h' ⊢
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
    have hlt := sp0.isLt; omega
  have hphb : (ph + 504#64 == 0#64) = false := by simpa using hph
  delta Hop4Regs
  iterate 180 wp_step
  simp only [BitVec.sub_self, BitVec.reduceNeg, BitVec.reduceAnd, BitVec.reduceAdd, BitVec.reduceSub]
  wp_done

/-- Hop 5: `__copy_tls` into `builtin_tls` (`B + 0x2080`) with empty TLS image up to `bl __init_tp`. -/
def MuslHop5Fetch (Q : Program) (B : BitVec 64) : Prop :=
  Q.fetch (B + 0x50#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x04#5) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x54#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x05#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x58#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x02#5) 0x080#12 false) ∧
  Q.fetch (B + 0x5c#64) = some (Arm64.Instr.bCond (Arm64.CondCode.HI) 0x00000000000000f4#64) ∧
  Q.fetch (B + 0x60#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x02#5) 0x020#12 false) ∧
  Q.fetch (B + 0x64#64) = some (Arm64.Instr.bCond (Arm64.CondCode.HI) 0x000000000000007c#64) ∧
  Q.fetch (B + 0x68#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x02#5) 0x010#12 false) ∧
  Q.fetch (B + 0x6c#64) = some (Arm64.Instr.bCond (Arm64.CondCode.CC) 0x0000000000000018#64) ∧
  Q.fetch (B + 0x84#64) = some (Arm64.Instr.tbz (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x02#5) 3 0x000000000000001c#64) ∧
  Q.fetch (B + 0xa0#64) = some (Arm64.Instr.tbz (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x02#5) 2 0x0000000000000018#64) ∧
  Q.fetch (B + 0xb8#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x02#5) 0x0000000000000020#64) ∧
  Q.fetch (B + 0xd8#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) ∧
  Q.fetch (B + 0x8d4#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1e#5) (Arm64.Reg.gpr 0x17#5) (Arm64.AddrMode.PreIndex (Arm64.Reg.sp) 0xffffffffffffffd0#64)) ∧
  Q.fetch (B + 0x8d8#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0x8dc#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000020#64)) ∧
  Q.fetch (B + 0x8e0#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x0a#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x8e4#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0a#5) 0x1f8#12 false) ∧
  Q.fetch (B + 0x8e8#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W64) (Arm64.MoveWideOp.MOVN) (Arm64.Reg.gpr 0x0c#5) 0x00c7#16 0) ∧
  Q.fetch (B + 0x8ec#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x0a#5) 0x0000000000000008#64)) ∧
  Q.fetch (B + 0x8f0#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x0a#5) 0x0000000000000018#64)) ∧
  Q.fetch (B + 0x8f4#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x0a#5) 0x0000000000000000#64)) ∧
  Q.fetch (B + 0x8f8#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x8fc#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORN) (Arm64.Reg.gpr 0x0d#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x900#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x904#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0b#5) 0x001#12 false) ∧
  Q.fetch (B + 0x908#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0d#5) (Arm64.ShiftType.LSL) 3) ∧
  Q.fetch (B + 0x90c#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.AND) (Arm64.Reg.gpr 0x0a#5) (Arm64.Reg.gpr 0x0b#5) (Arm64.Reg.gpr 0x0c#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x910#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x0a#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x914#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x15#5) 0x000000000000003c#64) ∧
  Q.fetch (B + 0x918#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUB) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 3) ∧
  Q.fetch (B + 0x91c#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x13#5) 0x0c8#12 false) ∧
  Q.fetch (B + 0x920#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x17#5) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x924#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x15#5) 0x0000000000000028#64)) ∧
  Q.fetch (B + 0x928#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x92c#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.gpr 0x17#5) 0x0000000000000008#64)) ∧
  Q.fetch (B + 0x930#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x15#5) 0x0000000000000028#64)) ∧
  Q.fetch (B + 0x934#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.gpr 0x02#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x15#5) 0x0000000000000008#64)) ∧
  Q.fetch (B + 0x938#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x08#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x93c#64) = some (Arm64.Instr.bl 0xfffffffffffff714#64) ∧
  Q.fetch (B + 0x940#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x15#5) 0x0000000000000000#64)) ∧
  Q.fetch (B + 0x944#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) true (Arm64.Reg.gpr 0x15#5) 0xffffffffffffffe0#64) ∧
  Q.fetch (B + 0x948#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x08#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x94c#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x08#5) 0x0000000000000210#64)) ∧
  Q.fetch (B + 0x950#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x14#5) 0x0000000000000000#64)) ∧
  Q.fetch (B + 0x954#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x13#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x958#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x14#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x00000000000000c0#64)) ∧
  Q.fetch (B + 0x95c#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000020#64)) ∧
  Q.fetch (B + 0x960#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0x964#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1e#5) (Arm64.Reg.gpr 0x17#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.sp) 0x0000000000000030#64)) ∧
  Q.fetch (B + 0x968#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) ∧
  Q.fetch (B + 0xae8#64) = some (Arm64.Instr.bl 0xfffffffffffffd70#64)

theorem add_2050_ne_zero (B : BitVec 64) (hB : B &&& 0xfff#64 = 0#64) :
    (B + 0x2050#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro h
  have h2 : B = 18446744073709543344#64 := by
    have := congrArg (· - 0x2050#64) h
    simpa using this
  rw [h2] at hB
  exact absurd hB (by decide)

/-- `c - (B + k)` is 8-byte aligned when `B` is page-aligned and `c`, `k` are 8-byte aligned. -/
theorem and7_sub_add (B c k : BitVec 64) (hB : B &&& 0xfff#64 = 0#64)
    (hc : 7#64 &&& c = 0#64) (hk : 7#64 &&& k = 0#64) :
    (7#64 &&& (c - (B + k))) = 0#64 := by
  have e : ∀ x : BitVec 64, (7#64 &&& x).toNat = x.toNat % 8 := fun x => by
    simp only [BitVec.toNat_and]; rw [Nat.and_comm]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 3
  have ee : ∀ x : BitVec 64, (x &&& 0xfff#64).toNat = x.toNat % 4096 := fun x => by
    simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 12
  have h1 := congrArg BitVec.toNat hB
  have h2 := congrArg BitVec.toNat hc
  have h3 := congrArg BitVec.toNat hk
  rw [ee] at h1; rw [e] at h2 h3
  simp only [BitVec.toNat_ofNat] at h1 h2 h3
  apply BitVec.eq_of_toNat_eq; rw [e]
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := B.isLt; have := c.isLt; have := k.isLt
  omega

def Hop5Regs (B sp0 r21 : BitVec 64)
    (fs0 : FsState) (tr0 : List TraceEvent) (s : State) : Prop :=
  s.sp = sp0 - 432#64 ∧ s.readReg64 .x0 = B + 0x2080#64 ∧ s.readReg64 .lr = B + 0xaec#64 ∧
  s.readReg64 .x21 = r21 ∧
  s.fs = fs0 ∧ s.trace = tr0

set_option maxHeartbeats 3200000 in
theorem musl_start_hop5 (Q : Program) (B : BitVec 64) (hf : MuslHop5Fetch Q B)
    (hB : B &&& 0xfff#64 = 0#64) (s : State) {fs0 : FsState} {tr0 : List TraceEvent} (sp0 r19 r20 r21 r22 r23 : BitVec 64)
    (hpc : s.pc = B + 0x8d4#64) (hrun : s.status = .Running)
    (hfs : s.fs = fs0) (htr : s.trace = tr0) (hsp : s.sp = sp0 - 432#64)
    (hx0 : s.readReg64 .x0 = B + 0x2080#64) (hlr : s.readReg64 .lr = B + 0xae8#64)
    (h19 : s.readReg64 .x19 = r19) (h20 : s.readReg64 .x20 = r20) (h21 : s.readReg64 .x21 = r21)
    (h22 : s.readReg64 .x22 = r22) (h23 : s.readReg64 .x23 = r23)
    (hal : (sp0 &&& 15#64 == 0#64) = true)
    (c0 c1 c2 c3 c4 c5 u0 u1 u2 : BitVec 64) :
    SepWP Q (B + 0x858#64) s
      (((sp0 - 480#64) ↦₆₄ c0) ∗
       ((sp0 - 472#64) ↦₆₄ c1) ∗
       ((sp0 - 464#64) ↦₆₄ c2) ∗
       ((sp0 - 456#64) ↦₆₄ c3) ∗
       ((sp0 - 448#64) ↦₆₄ c4) ∗
       ((sp0 - 440#64) ↦₆₄ c5) ∗
       ((B + 0x2200#64) ↦₆₄ 0xe0#64) ∗
       ((B + 0x2208#64) ↦₆₄ 8#64) ∗
       ((B + 0x2210#64) ↦₆₄ 1#64) ∗
       ((B + 0x21f8#64) ↦₆₄ (B + 0x2050#64)) ∗
       ((B + 0x2050#64) ↦₆₄ 0#64) ∗
       ((B + 0x2058#64) ↦₆₄ 0#64) ∗
       ((B + 0x2060#64) ↦₆₄ 0#64) ∗
       ((B + 0x2078#64) ↦₆₄ 0#64) ∗
       ((B + 0x2140#64) ↦₆₄ u0) ∗
       ((B + 0x2150#64) ↦₆₄ u1) ∗
       ((B + 0x2158#64) ↦₆₄ u2))
      (sepPost (Hop5Regs B sp0 r21 fs0 tr0)
        (((sp0 - 480#64) ↦₆₄ (B + 0xae8#64)) ∗
         ((sp0 - 472#64) ↦₆₄ r23) ∗
         ((sp0 - 464#64) ↦₆₄ r22) ∗
         ((sp0 - 456#64) ↦₆₄ r21) ∗
         ((sp0 - 448#64) ↦₆₄ r20) ∗
         ((sp0 - 440#64) ↦₆₄ r19) ∗
         ((B + 0x2200#64) ↦₆₄ 0xe0#64) ∗
         ((B + 0x2208#64) ↦₆₄ 8#64) ∗
         ((B + 0x2210#64) ↦₆₄ 1#64) ∗
         ((B + 0x21f8#64) ↦₆₄ (B + 0x2050#64)) ∗
         ((B + 0x2050#64) ↦₆₄ 0#64) ∗
         ((B + 0x2058#64) ↦₆₄ 0#64) ∗
         ((B + 0x2060#64) ↦₆₄ 0#64) ∗
         ((B + 0x2078#64) ↦₆₄ 0#64) ∗
         ((B + 0x2140#64) ↦₆₄ (B + 0x2150#64)) ∗
         ((B + 0x2150#64) ↦₆₄ 1#64) ∗
         ((B + 0x2158#64) ↦₆₄ (B + 0x2148#64)))) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50⟩ := hf
  have hal' : (s.sp &&& 15#64 == 0#64) = true := by
    rw [hsp]
    have h0 : sp0 &&& 15#64 = 0#64 := eq_of_beq hal
    have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
      simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
    have h' := congrArg BitVec.toNat h0
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [e] at h' ⊢
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
    have hlt := sp0.isLt; omega
  have hBn : (B + 0x2050#64 == 0#64) = false := add_2050_ne_zero B hB
  have hmask : (7#64 &&& (18446744073709551416#64 - (B + 8320#64))) = 0#64 :=
    and7_sub_add B _ _ hB (by decide) (by decide)
  delta Hop5Regs
  iterate 51 wp_step
  wp_done

/-- Hop 6 (33 instructions): `__init_tp` (`msr TPIDR_EL0` and `set_tid_address` syscall) returning to `B + 0xaec`. -/
def MuslHop6Fetch (Q : Program) (B : BitVec 64) : Prop :=
  Q.fetch (B + 0x858#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x1e#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.PreIndex (Arm64.Reg.sp) 0xfffffffffffffff0#64)) ∧
  Q.fetch (B + 0x85c#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x860#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.gpr 0x00#5) 0x00000000000000c8#64)) ∧
  Q.fetch (B + 0x864#64) = some (Arm64.Instr.bl 0x0000000000000320#64) ∧
  Q.fetch (B + 0x868#64) = some (Arm64.Instr.tbz (Arm64.RegWidth.W32) true (Arm64.Reg.gpr 0x00#5) 31 0x000000000000005c#64) ∧
  Q.fetch (B + 0x86c#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W32) true (Arm64.Reg.gpr 0x00#5) 0x0000000000000010#64) ∧
  Q.fetch (B + 0x870#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x08#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x874#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x09#5) 0x0001#16 0) ∧
  Q.fetch (B + 0x878#64) = some (Arm64.Instr.str (Arm64.MemWidth.B8) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x08#5) 0x00000000000001e8#64)) ∧
  Q.fetch (B + 0x87c#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x08#5) 0x0002#16 0) ∧
  Q.fetch (B + 0x880#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x00#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x884#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.gpr 0x00#5) 0x048#12 false) ∧
  Q.fetch (B + 0x888#64) = some (Arm64.Instr.str (Arm64.MemWidth.W32) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000028#64)) ∧
  Q.fetch (B + 0x88c#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x08#5) 0x0060#16 0) ∧
  Q.fetch (B + 0x890#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W32) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x09#5) (Arm64.Reg.xzr) (Arm64.Reg.xzr) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x894#64) = some (Arm64.Instr.system false 0x0000#16) ∧
  Q.fetch (B + 0x898#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x08#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x89c#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x08#5) 0x220#12 false) ∧
  Q.fetch (B + 0x8a0#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000098#64)) ∧
  Q.fetch (B + 0x8a4#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x13#5) 0x078#12 false) ∧
  Q.fetch (B + 0x8a8#64) = some (Arm64.Instr.str (Arm64.MemWidth.W32) (Arm64.Reg.gpr 0x00#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000020#64)) ∧
  Q.fetch (B + 0x8ac#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000078#64)) ∧
  Q.fetch (B + 0x8b0#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x08#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x8b4#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x08#5) 0x00000000000001d0#64)) ∧
  Q.fetch (B + 0x8b8#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000008#64)) ∧
  Q.fetch (B + 0x8bc#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0x8c0#64) = some (Arm64.Instr.b 0x0000000000000008#64) ∧
  Q.fetch (B + 0x8c8#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W32) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x8cc#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1e#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.sp) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0x8d0#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) ∧
  Q.fetch (B + 0xb84#64) = some (Arm64.Instr.sysReg false 0x5e82#15 (Arm64.Reg.gpr 0x00#5)) ∧
  Q.fetch (B + 0xb88#64) = some (Arm64.Instr.moveWide (Arm64.RegWidth.W32) (Arm64.MoveWideOp.MOVZ) (Arm64.Reg.gpr 0x00#5) 0x0000#16 0) ∧
  Q.fetch (B + 0xb8c#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5))

/-- `svc #0` with `x8 = 96` (`set_tid_address`) sets `x0 := 1` and advances `pc`. -/
theorem execSyscall_setTid (s : State) (h : s.readReg64 Reg.x8 = 96#64) :
    execSyscall s = (s.writeReg64 Reg.x0 1#64).advancePC := by
  unfold execSyscall Syscall.standard Syscall.dispatch
  rw [h]
  rfl

theorem hop6_gen_state {prog : Program} {tgt : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {pc sp x0 x19 x21 x30 : BitVec 64}
    {fs : FsState} {tr : List TraceEvent}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (h0 : s.readReg64 .x0 = x0) (h19 : s.readReg64 .x19 = x19) (h21 : s.readReg64 .x21 = x21)
    (h30 : s.readReg64 .lr = x30) (hfs : s.fs = fs) (htr : s.trace = tr)
    (h : ∀ s' : State, s'.pc = pc → s'.status = .Running → s'.sp = sp →
      s'.readReg64 .x0 = x0 → s'.readReg64 .x19 = x19 → s'.readReg64 .x21 = x21 →
      s'.readReg64 .lr = x30 → s'.fs = fs → s'.trace = tr → SepWP prog tgt s' P post oom) :
    SepWP prog tgt s P post oom :=
  h s hpc hrun hsp h0 h19 h21 h30 hfs htr

theorem hop6_gen_state9 {prog : Program} {tgt : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc sp x0 x9 x19 x21 x30 : BitVec 64} {fs : FsState} {tr : List TraceEvent}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (h0 : s.readReg64 .x0 = x0) (h9 : s.readReg64 .x9 = x9) (h19 : s.readReg64 .x19 = x19)
    (h21 : s.readReg64 .x21 = x21) (h30 : s.readReg64 .lr = x30) (hfs : s.fs = fs)
    (htr : s.trace = tr)
    (h : ∀ s' : State, s'.pc = pc → s'.status = .Running → s'.sp = sp →
      s'.readReg64 .x0 = x0 → s'.readReg64 .x9 = x9 → s'.readReg64 .x19 = x19 →
      s'.readReg64 .x21 = x21 → s'.readReg64 .lr = x30 → s'.fs = fs → s'.trace = tr →
      SepWP prog tgt s' P post oom) :
    SepWP prog tgt s P post oom :=
  h s hpc hrun hsp h0 h9 h19 h21 h30 hfs htr

def Hop6Regs (B sp0 r19 m : BitVec 64)
    (fs0 : FsState) (tr0 : List TraceEvent) (s : State) : Prop :=
  s.sp = sp0 - 432#64 ∧ s.readReg64 .x0 = 0#64 ∧ s.readReg64 .x19 = r19 ∧
  s.readReg64 .lr = B + 0xaec#64 ∧ s.readReg64 .x21 = m ∧
  s.fs = fs0 ∧ s.trace = tr0

set_option maxHeartbeats 3200000 in
theorem musl_start_hop6 (Q : Program) (B : BitVec 64) (hf : MuslHop6Fetch Q B)
    (hsvc : Q.svc = Syscall.standard)
    (hB : B &&& 0xfff#64 = 0#64) (s : State) {fs0 : FsState} {tr0 : List TraceEvent} (sp0 r19 m : BitVec 64)
    (hpc : s.pc = B + 0x858#64) (hrun : s.status = .Running)
    (hfs : s.fs = fs0) (htr : s.trace = tr0) (hsp : s.sp = sp0 - 432#64)
    (hx0 : s.readReg64 .x0 = B + 0x2080#64) (hlr : s.readReg64 .lr = B + 0xaec#64)
    (h19 : s.readReg64 .x19 = r19) (h21 : s.readReg64 .x21 = m)
    (hal : (sp0 &&& 15#64 == 0#64) = true)
    (d0 d1 e0 e3 e5 e6 e7 e8 sy : BitVec 64) (e1 : BitVec 8) (e2 e4 : BitVec 32) :
    SepWP Q (B + 0xaec#64) s
      (((sp0 - 448#64) ↦₆₄ d0) ∗
       ((sp0 - 440#64) ↦₆₄ d1) ∗
       ((B + 0x2080#64) ↦₆₄ e0) ∗
       ((B + 0x21e8#64) ↦₈ e1) ∗
       ((B + 0x20a8#64) ↦₃₂ e2) ∗
       ((B + 0x2118#64) ↦₆₄ e3) ∗
       ((B + 0x20a0#64) ↦₃₂ e4) ∗
       ((B + 0x20f8#64) ↦₆₄ e5) ∗
       ((B + 0x21d0#64) ↦₆₄ sy) ∗
       ((B + 0x2088#64) ↦₆₄ e6) ∗
       ((B + 0x2090#64) ↦₆₄ e7) ∗
       ((B + 0x2098#64) ↦₆₄ e8))
      (sepPost (Hop6Regs B sp0 r19 m fs0 tr0)
        (((sp0 - 448#64) ↦₆₄ (B + 0xaec#64)) ∗
         ((sp0 - 440#64) ↦₆₄ r19) ∗
         ((B + 0x2080#64) ↦₆₄ (B + 0x2080#64)) ∗
         ((B + 0x21e8#64) ↦₈ 1#8) ∗
         ((B + 0x20a8#64) ↦₃₂ 2#32) ∗
         ((B + 0x2118#64) ↦₆₄ (B + 0x2220#64)) ∗
         ((B + 0x20a0#64) ↦₃₂ 1#32) ∗
         ((B + 0x20f8#64) ↦₆₄ (B + 0x20f8#64)) ∗
         ((B + 0x21d0#64) ↦₆₄ sy) ∗
         ((B + 0x2088#64) ↦₆₄ (B + 0x2080#64)) ∗
         ((B + 0x2090#64) ↦₆₄ (B + 0x2080#64)) ∗
         ((B + 0x2098#64) ↦₆₄ sy))) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32⟩ := hf
  have hal' : (s.sp &&& 15#64 == 0#64) = true := by
    rw [hsp]
    have h0 : sp0 &&& 15#64 = 0#64 := eq_of_beq hal
    have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
      simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
    have h' := congrArg BitVec.toNat h0
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [e] at h' ⊢
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
    have hlt := sp0.isLt; omega
  delta Hop6Regs
  iterate 4 wp_step
  have hmsr : ∀ st : State, Q.evalInst (.sysReg false 0x5e82#15 (.gpr 0x00#5)) st =
      (setTpidrEl0 st (st.readReg64 (.gpr 0x00#5))).advancePC := by
    intro st; cases st; rfl
  refine SepWP.step_pure (by simp) (by simp [hrun]) f30 rfl (by rw [hmsr]; simp) ?_
  rw [hmsr]
  refine hop6_gen_state (pc := B + 0xb88#64) (sp := sp0 - 448#64) (x0 := B + 0x2148#64)
    (x19 := B + 0x2080#64) (x21 := m) (x30 := B + 0x868#64) (fs := fs0) (tr := tr0)
    (by simp [BitVec.add_assoc]) (by simp [hrun]) (by simp) (by simp) (by simp) (by simp [h21])
    (by simp) (by simp [setTpidrEl0, hfs]) (by simp [setTpidrEl0, htr]) ?_
  intro s hpc hrun hsp hx0 h19 h21 hlr hfs htr
  have hal' : (s.sp &&& 15#64 == 0#64) = true := by
    rw [hsp]
    have h0 : sp0 &&& 15#64 = 0#64 := eq_of_beq hal
    have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
      simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
    have h' := congrArg BitVec.toNat h0
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [e] at h' ⊢
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
    have hlt := sp0.isLt; omega
  iterate 13 wp_step
  have hsvc0 : ∀ st : State, st.readReg64 Reg.x8 = 96#64 →
      Q.evalInst (.system false 0#16) st = (st.writeReg64 Reg.x0 1#64).advancePC := by
    intro st h8
    unfold Program.evalInst execInstWithSvc
    rw [hsvc]
    change evalSvc execSyscall st = _
    unfold evalSvc
    dsimp only
    rw [execSyscall_setTid _ h8]
    rcases st with ⟨_, _, _, _, _, ⟨_⟩, _, _, _, _, _, _, _, _, _, _, _, _⟩
    simp [State.writeReg64, State.advancePC]
  refine SepWP.step_pure (by simp) (by simp [hrun]) f15 rfl
    (by rw [hsvc0 _ (by simp)]; simp) ?_
  rw [hsvc0 _ (by simp)]
  clear hal'
  refine hop6_gen_state9 (pc := B + 0x898#64) (sp := sp0 - 448#64) (x0 := 1#64) (x9 := 0#64)
    (x19 := B + 0x2080#64) (x21 := m) (x30 := B + 0x868#64) (fs := fs0) (tr := tr0)
    (by simp [BitVec.add_assoc]) (by simp [hrun]) (by simp [hsp]) (by simp) (by simp)
    (by simp [h19]) (by simp [h21]) (by simp [hlr]) (by simp [hfs]) (by simp [htr]) ?_
  clear hpc hrun hsp hx0 h19 h21 hlr hfs htr
  intro s hpc hrun hsp hx0 hx9 h19 h21 hlr hfs htr
  have hal' : (s.sp &&& 15#64 == 0#64) = true := by
    rw [hsp]
    have h0 : sp0 &&& 15#64 = 0#64 := eq_of_beq hal
    have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
      simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
    have h' := congrArg BitVec.toNat h0
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [e] at h' ⊢
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
    have hlt := sp0.isLt; omega
  iterate 14 wp_step
  wp_done

/-- Hop 7: tail of `static_init_tls`, `__init_libc`, `libc_start_main_stage2`, and `libc_start_init` up to `blr x21`. -/
def MuslHop7Fetch (Q : Program) (B : BitVec 64) : Prop :=
  Q.fetch (B + 0x5ec#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) ∧
  Q.fetch (B + 0x5f0#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) ∧
  Q.fetch (B + 0x6d0#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x00#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000f8#64)) ∧
  Q.fetch (B + 0x6d4#64) = some (Arm64.Instr.bl 0xffffffffffffff1c#64) ∧
  Q.fetch (B + 0x6d8#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000088#64)) ∧
  Q.fetch (B + 0x6dc#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x6e0#64) = some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0x0000000000000018#64) ∧
  Q.fetch (B + 0x6e4#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000098#64)) ∧
  Q.fetch (B + 0x6e8#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x09#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x6ec#64) = some (Arm64.Instr.bCond (Arm64.CondCode.NE) 0x000000000000000c#64) ∧
  Q.fetch (B + 0x6f0#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x00000000000000e8#64)) ∧
  Q.fetch (B + 0x6f4#64) = some (Arm64.Instr.cbz (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x08#5) 0x0000000000000094#64) ∧
  Q.fetch (B + 0x788#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000170#64)) ∧
  Q.fetch (B + 0x78c#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1d#5) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000160#64)) ∧
  Q.fetch (B + 0x790#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.sp) (Arm64.Reg.sp) 0x180#12 false) ∧
  Q.fetch (B + 0x794#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) ∧
  Q.fetch (B + 0x798#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PreIndex (Arm64.Reg.sp) 0xffffffffffffffe0#64)) ∧
  Q.fetch (B + 0x79c#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0x7a0#64) = some (Arm64.Instr.bl 0xfffffffffffffe4c#64) ∧
  Q.fetch (B + 0x7a4#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x13#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x7a8#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x08#5) 0x0000000000002000#64) ∧
  Q.fetch (B + 0x7ac#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x13#5) 0x0000000000000020#64)) ∧
  Q.fetch (B + 0x7b0#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x08#5) (Arm64.AddrMode.Offset (Arm64.Reg.gpr 0x08#5) 0x0000000000000028#64)) ∧
  Q.fetch (B + 0x7b4#64) = some (Arm64.Instr.addSubShift (Arm64.RegWidth.W64) (Arm64.AddSubOp.SUBS) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x08#5) (Arm64.Reg.gpr 0x13#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x7b8#64) = some (Arm64.Instr.bCond (Arm64.CondCode.CS) 0x000000000000001c#64) ∧
  Q.fetch (B + 0x7d4#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0x7d8#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.sp) 0x0000000000000020#64)) ∧
  Q.fetch (B + 0x7dc#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5)) ∧
  Q.fetch (B + 0x804#64) = some (Arm64.Instr.adr true (Arm64.Reg.gpr 0x03#5) 0x0000000000000000#64) ∧
  Q.fetch (B + 0x808#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x03#5) (Arm64.Reg.gpr 0x03#5) 0x824#12 false) ∧
  Q.fetch (B + 0x80c#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W32) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x14#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x810#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x13#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x814#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x15#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x818#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0x81c#64) = some (Arm64.Instr.ldp (Arm64.RegWidth.W64) false (Arm64.Reg.gpr 0x1e#5) (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.sp) 0x0000000000000020#64)) ∧
  Q.fetch (B + 0x820#64) = some (Arm64.Instr.br (Arm64.Reg.gpr 0x03#5)) ∧
  Q.fetch (B + 0x824#64) = some (Arm64.Instr.str (Arm64.MemWidth.X64) (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PreIndex (Arm64.Reg.sp) 0xffffffffffffffd0#64)) ∧
  Q.fetch (B + 0x828#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x15#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0x82c#64) = some (Arm64.Instr.stp (Arm64.RegWidth.W64) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.gpr 0x13#5) (Arm64.AddrMode.Offset (Arm64.Reg.sp) 0x0000000000000020#64)) ∧
  Q.fetch (B + 0x830#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x13#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x02#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x834#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W32) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x14#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x01#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x838#64) = some (Arm64.Instr.addSubExt (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x16#5) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x01#5) (Arm64.ExtendType.SXTW) 3) ∧
  Q.fetch (B + 0x83c#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x15#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x00#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x840#64) = some (Arm64.Instr.bl 0xffffffffffffff58#64) ∧
  Q.fetch (B + 0x844#64) = some (Arm64.Instr.addSubImm (Arm64.RegWidth.W64) (Arm64.AddSubOp.ADD) (Arm64.Reg.gpr 0x02#5) (Arm64.Reg.gpr 0x16#5) 0x008#12 false) ∧
  Q.fetch (B + 0x848#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W32) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x00#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x14#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x84c#64) = some (Arm64.Instr.logicalShift (Arm64.RegWidth.W64) (Arm64.LogicalOp.ORR) (Arm64.Reg.gpr 0x01#5) (Arm64.Reg.xzr) (Arm64.Reg.gpr 0x13#5) (Arm64.ShiftType.LSL) 0) ∧
  Q.fetch (B + 0x850#64) = some (Arm64.Instr.blr (Arm64.Reg.gpr 0x15#5)) ∧
  Q.fetch (B + 0xaec#64) = some (Arm64.Instr.tbz (Arm64.RegWidth.W32) false (Arm64.Reg.gpr 0x00#5) 31 0x000000000000000c#64) ∧
  Q.fetch (B + 0xaf8#64) = some (Arm64.Instr.ldr (Arm64.RegWidth.W64) (Arm64.MemWidth.X64) false (Arm64.Reg.gpr 0x1e#5) (Arm64.AddrMode.PostIndex (Arm64.Reg.sp) 0x0000000000000010#64)) ∧
  Q.fetch (B + 0xafc#64) = some (Arm64.Instr.ret (Arm64.Reg.gpr 0x1e#5))

def Hop7Regs (B sp0 x19v x20v : BitVec 64)
    (fs0 : FsState) (tr0 : List TraceEvent) (s : State) : Prop :=
  s.sp = sp0 - 48#64 ∧ s.readReg64 .x0 = (x20v.truncate 32).zeroExtend 64 ∧
  s.readReg64 .x1 = x19v ∧
  s.readReg64 .x2 = x19v + BitVec.signExtend 64 (x20v.truncate 32) <<< 3 + 8#64 ∧
  s.readReg64 .lr = B + 0x854#64 ∧
  s.fs = fs0 ∧ s.trace = tr0

set_option maxHeartbeats 3200000 in
theorem musl_start_hop7 (Q : Program) (B : BitVec 64) (hf : MuslHop7Fetch Q B)
    (hB : B &&& 0xfff#64 = 0#64) (s : State) {fs0 : FsState} {tr0 : List TraceEvent} (sp0 r22 : BitVec 64)
    (hpc : s.pc = B + 0xaec#64) (hrun : s.status = .Running)
    (hfs : s.fs = fs0) (htr : s.trace = tr0) (hsp : s.sp = sp0 - 432#64)
    (hx0 : s.readReg64 .x0 = 0#64) (h21 : s.readReg64 .x21 = B - 85504#64)
    (h22 : s.readReg64 .x22 = r22)
    (hal : (sp0 &&& 15#64 == 0#64) = true)
    (rnd uid gid ia k0 k1 x29v x20v x19v o21 o20 o19 : BitVec 64) :
    SepWP Q (B - 85504#64) s
      (((sp0 - 432#64) ↦₆₄ (B + 0x6d0#64)) ∗
       ((sp0 - 168#64) ↦₆₄ rnd) ∗
       ((sp0 - 280#64) ↦₆₄ uid) ∗
       ((sp0 - 272#64) ↦₆₄ uid) ∗
       ((sp0 - 264#64) ↦₆₄ gid) ∗
       ((sp0 - 256#64) ↦₆₄ gid) ∗
       ((sp0 - 184#64) ↦₆₄ 0#64) ∗
       ((B + 0x2020#64) ↦₆₄ ia) ∗
       ((B + 0x2028#64) ↦₆₄ ia) ∗
       ((sp0 - 80#64) ↦₆₄ k0) ∗
       ((sp0 - 72#64) ↦₆₄ k1) ∗
       ((sp0 - 64#64) ↦₆₄ x29v) ∗
       ((sp0 - 56#64) ↦₆₄ (B + 2052#64)) ∗
       ((sp0 - 48#64) ↦₆₄ x20v) ∗
       ((sp0 - 40#64) ↦₆₄ x19v) ∗
       ((sp0 - 32#64) ↦₆₄ 0#64) ∗
       ((sp0 - 24#64) ↦₆₄ o21) ∗
       ((sp0 - 16#64) ↦₆₄ o20) ∗
       ((sp0 - 8#64) ↦₆₄ o19))
      (sepPost (Hop7Regs B sp0 x19v x20v fs0 tr0)
        (((sp0 - 432#64) ↦₆₄ (B + 0x6d0#64)) ∗
         ((sp0 - 168#64) ↦₆₄ rnd) ∗
         ((sp0 - 280#64) ↦₆₄ uid) ∗
         ((sp0 - 272#64) ↦₆₄ uid) ∗
         ((sp0 - 264#64) ↦₆₄ gid) ∗
         ((sp0 - 256#64) ↦₆₄ gid) ∗
         ((sp0 - 184#64) ↦₆₄ 0#64) ∗
         ((B + 0x2020#64) ↦₆₄ ia) ∗
         ((B + 0x2028#64) ↦₆₄ ia) ∗
         ((sp0 - 80#64) ↦₆₄ (B + 0x844#64)) ∗
         ((sp0 - 72#64) ↦₆₄ k1) ∗
         ((sp0 - 64#64) ↦₆₄ (x20v.truncate 32).zeroExtend 64) ∗
         ((sp0 - 56#64) ↦₆₄ x19v) ∗
         ((sp0 - 48#64) ↦₆₄ 0#64) ∗
         ((sp0 - 40#64) ↦₆₄ x19v) ∗
         ((sp0 - 32#64) ↦₆₄ r22) ∗
         ((sp0 - 24#64) ↦₆₄ o21) ∗
         ((sp0 - 16#64) ↦₆₄ o20) ∗
         ((sp0 - 8#64) ↦₆₄ o19))) := by
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50⟩ := hf
  have hal' : (s.sp &&& 15#64 == 0#64) = true := by
    rw [hsp]
    have h0 : sp0 &&& 15#64 = 0#64 := eq_of_beq hal
    have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
      simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
    have h' := congrArg BitVec.toNat h0
    rw [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [e] at h' ⊢
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
    have hlt := sp0.isLt; omega
  delta Hop7Regs
  iterate 51 wp_step
  wp_done

/-- Conjunction of instruction-fetch predicates for hops 1–7 (`_start` to `main`). -/
def MuslStartFetch (Q : Program) (B : BitVec 64) : Prop :=
  MuslHop1Fetch Q B ∧ MuslHop2Fetch Q B ∧ MuslHop3aFetch Q B ∧ MuslHop3bFetch Q B ∧
  MuslHop4Fetch Q B ∧ MuslHop5Fetch Q B ∧ MuslHop6Fetch Q B ∧ MuslHop7Fetch Q B

/-- Initial-stack footprint read and preserved by musl startup (`argc`, `argv[0]`, `envp` `NULL`, and 18 `auxv` pairs plus `AT_NULL`). -/
abbrev StartProc (sp0 envp p ph pg ab af ae uid gid plat hw clk rnd hw2 ex : BitVec 64)
    (a32 ah32 : BitVec 32) : SepProp :=
  (sp0 ↦₃₂ a32) ∗
  ((sp0 + 4#64) ↦₃₂ ah32) ∗
  ((sp0 + 8#64) ↦₆₄ p) ∗
  (envp ↦₆₄ 0#64) ∗
  ((envp + 8#64) ↦₆₄ 3#64) ∗
  ((envp + 16#64) ↦₆₄ ph) ∗
  ((envp + 24#64) ↦₆₄ 4#64) ∗
  ((envp + 32#64) ↦₆₄ 56#64) ∗
  ((envp + 40#64) ↦₆₄ 5#64) ∗
  ((envp + 48#64) ↦₆₄ 11#64) ∗
  ((envp + 56#64) ↦₆₄ 6#64) ∗
  ((envp + 64#64) ↦₆₄ pg) ∗
  ((envp + 72#64) ↦₆₄ 7#64) ∗
  ((envp + 80#64) ↦₆₄ ab) ∗
  ((envp + 88#64) ↦₆₄ 8#64) ∗
  ((envp + 96#64) ↦₆₄ af) ∗
  ((envp + 104#64) ↦₆₄ 9#64) ∗
  ((envp + 112#64) ↦₆₄ ae) ∗
  ((envp + 120#64) ↦₆₄ 11#64) ∗
  ((envp + 128#64) ↦₆₄ uid) ∗
  ((envp + 136#64) ↦₆₄ 12#64) ∗
  ((envp + 144#64) ↦₆₄ uid) ∗
  ((envp + 152#64) ↦₆₄ 13#64) ∗
  ((envp + 160#64) ↦₆₄ gid) ∗
  ((envp + 168#64) ↦₆₄ 14#64) ∗
  ((envp + 176#64) ↦₆₄ gid) ∗
  ((envp + 184#64) ↦₆₄ 15#64) ∗
  ((envp + 192#64) ↦₆₄ plat) ∗
  ((envp + 200#64) ↦₆₄ 16#64) ∗
  ((envp + 208#64) ↦₆₄ hw) ∗
  ((envp + 216#64) ↦₆₄ 17#64) ∗
  ((envp + 224#64) ↦₆₄ clk) ∗
  ((envp + 232#64) ↦₆₄ 23#64) ∗
  ((envp + 240#64) ↦₆₄ 0#64) ∗
  ((envp + 248#64) ↦₆₄ 25#64) ∗
  ((envp + 256#64) ↦₆₄ rnd) ∗
  ((envp + 264#64) ↦₆₄ 26#64) ∗
  ((envp + 272#64) ↦₆₄ hw2) ∗
  ((envp + 280#64) ↦₆₄ 31#64) ∗
  ((envp + 288#64) ↦₆₄ ex) ∗
  ((envp + 296#64) ↦₆₄ 0#64)

/-- Footprint for `argv[0] = "libsignal-cli\0"` at `p`. -/
abbrev StartArgv0 (p : BitVec 64) : SepProp :=
  (p ↦₈ 0x6c#8) ∗
  ((p + 1#64) ↦₈ 0x69#8) ∗
  ((p + 2#64) ↦₈ 0x62#8) ∗
  ((p + 3#64) ↦₈ 0x73#8) ∗
  ((p + 4#64) ↦₈ 0x69#8) ∗
  ((p + 5#64) ↦₈ 0x67#8) ∗
  ((p + 6#64) ↦₈ 0x6e#8) ∗
  ((p + 7#64) ↦₈ 0x61#8) ∗
  ((p + 8#64) ↦₈ 0x6c#8) ∗
  ((p + 9#64) ↦₈ 0x2d#8) ∗
  ((p + 10#64) ↦₈ 0x63#8) ∗
  ((p + 11#64) ↦₈ 0x6c#8) ∗
  ((p + 12#64) ↦₈ 0x69#8) ∗
  ((p + 13#64) ↦₈ 0x00#8)

/-- Read-only program-header words at `AT_PHDR = ph` read by `static_init_tls`. -/
abbrev StartPhdrs (ph : BitVec 64) : SepProp :=
  (ph ↦₃₂ᵣ 6#32) ∗
  ((ph + 16#64) ↦₆₄ᵣ ph) ∗
  ((ph + 56#64) ↦₃₂ᵣ 1#32) ∗
  ((ph + 112#64) ↦₃₂ᵣ 1#32) ∗
  ((ph + 168#64) ↦₃₂ᵣ 1#32) ∗
  ((ph + 224#64) ↦₃₂ᵣ 1#32) ∗
  ((ph + 280#64) ↦₃₂ᵣ 1#32) ∗
  ((ph + 336#64) ↦₃₂ᵣ 1#32) ∗
  ((ph + 392#64) ↦₃₂ᵣ 1#32) ∗
  ((ph + 448#64) ↦₃₂ᵣ 1#32) ∗
  ((ph + 504#64) ↦₃₂ᵣ 7#32) ∗
  ((ph + 520#64) ↦₆₄ᵣ 0#64) ∗
  ((ph + 536#64) ↦₆₄ᵣ 0#64) ∗
  ((ph + 544#64) ↦₆₄ᵣ 0#64) ∗
  ((ph + 552#64) ↦₆₄ᵣ 0#64) ∗
  ((ph + 560#64) ↦₃₂ᵣ 0x6474e551#32) ∗
  ((ph + 600#64) ↦₆₄ᵣ 0#64)

set_option maxHeartbeats 3200000 in
/-- Composed `SepWP` startup contract from `_start` (`B`) to `main` (`B - 85504`), reaching
`x0 = argc`, `x1 = sp0 + 8`, `x2 = envp`, `sp = sp0 - 48`, and unchanged filesystem and trace. -/
theorem musl_start (Q : Program) (B : BitVec 64) (hf : MuslStartFetch Q B)
    (hsvc : Q.svc = Syscall.standard)
    (hB : B &&& 0xfff#64 = 0#64) (s : State) (hpc : s.pc = B) (hrun : s.status = .Running)
    (hal : (s.sp &&& 15#64 == 0#64) = true) (hsp16 : s.sp &&& -16#64 = s.sp)
    (envp p ph pg ab af ae uid gid plat hw clk rnd hw2 ex : BitVec 64) (a32 ah32 : BitVec 32)
    (henvp : envp = s.sp + 8#64 + BitVec.signExtend 64 a32 <<< 3 + 8#64)
    (hp : p ≠ 0#64) (hph : ph + 504#64 ≠ 0#64)
    (g3 g4 ia e0 e1 t0 t1 t2 t3 t4 t5 t6 t7 t8 f0 f3 f5 f6 f7 f8 sy u0 u1 u2 : BitVec 64)
    (d0 d1 d2 d3 : BitVec 64) (f1 : BitVec 8) (f2 f4 : BitVec 32)
    (w480 w472 w464 w456 w448 w440 w432 : BitVec 64)
    (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 : BitVec 64)
    (m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37 : BitVec 64)
    (n64 n56 n48 n40 v0 v1 v2 v3 : BitVec 64) :
    SepWP Q (B - 85504#64) s
      (StartProc s.sp envp p ph pg ab af ae uid gid plat hw clk rnd hw2 ex a32 ah32 ∗ StartArgv0 p ∗
        StartPhdrs ph ∗
       ((B + 0x2000#64) ↦₃₂ 0x20000#32) ∗
       ((B + 0x2008#64) ↦₆₄ 0#64) ∗
       ((B + 0x2010#64) ↦₆₄ g3) ∗
       ((B + 0x2018#64) ↦₆₄ g4) ∗
       ((B + 0x2020#64) ↦₆₄ ia) ∗
       ((B + 0x2028#64) ↦₆₄ ia) ∗
       ((B + 0x2040#64) ↦₆₄ e0) ∗
       ((B + 0x2050#64) ↦₆₄ 0#64) ∗
       ((B + 0x2058#64) ↦₆₄ t0) ∗
       ((B + 0x2060#64) ↦₆₄ t1) ∗
       ((B + 0x2068#64) ↦₆₄ t2) ∗
       ((B + 0x2070#64) ↦₆₄ t3) ∗
       ((B + 0x2078#64) ↦₆₄ t4) ∗
       ((B + 0x2080#64) ↦₆₄ f0) ∗
       ((B + 0x2088#64) ↦₆₄ f6) ∗
       ((B + 0x2090#64) ↦₆₄ f7) ∗
       ((B + 0x2098#64) ↦₆₄ f8) ∗
       ((B + 0x20a0#64) ↦₃₂ f4) ∗
       ((B + 0x20a8#64) ↦₃₂ f2) ∗
       ((B + 0x20f8#64) ↦₆₄ f5) ∗
       ((B + 0x2118#64) ↦₆₄ f3) ∗
       ((B + 0x2140#64) ↦₆₄ u0) ∗
       ((B + 0x2150#64) ↦₆₄ u1) ∗
       ((B + 0x2158#64) ↦₆₄ u2) ∗
       ((B + 0x21d0#64) ↦₆₄ sy) ∗
       ((B + 0x21d8#64) ↦₆₄ d3) ∗
       ((B + 0x21e0#64) ↦₆₄ d2) ∗
       ((B + 0x21e8#64) ↦₈ f1) ∗
       ((B + 0x21f0#64) ↦₆₄ e1) ∗
       ((B + 0x21f8#64) ↦₆₄ t5) ∗
       ((B + 0x2200#64) ↦₆₄ t6) ∗
       ((B + 0x2208#64) ↦₆₄ t7) ∗
       ((B + 0x2210#64) ↦₆₄ t8) ∗
       ((B + 0x2218#64) ↦₆₄ d1) ∗
       ((B + 0x2250#64) ↦₆₄ d0) ∗
       ((s.sp - 480#64) ↦₆₄ w480) ∗
       ((s.sp - 472#64) ↦₆₄ w472) ∗
       ((s.sp - 464#64) ↦₆₄ w464) ∗
       ((s.sp - 456#64) ↦₆₄ w456) ∗
       ((s.sp - 448#64) ↦₆₄ w448) ∗
       ((s.sp - 440#64) ↦₆₄ w440) ∗
       ((s.sp - 432#64) ↦₆₄ w432) ∗
       ((s.sp - 368#64) ↦₆₄ m0) ∗
       ((s.sp - 360#64) ↦₆₄ m1) ∗
       ((s.sp - 352#64) ↦₆₄ m2) ∗
       ((s.sp - 344#64) ↦₆₄ m3) ∗
       ((s.sp - 336#64) ↦₆₄ m4) ∗
       ((s.sp - 328#64) ↦₆₄ m5) ∗
       ((s.sp - 320#64) ↦₆₄ m6) ∗
       ((s.sp - 312#64) ↦₆₄ m7) ∗
       ((s.sp - 304#64) ↦₆₄ m8) ∗
       ((s.sp - 296#64) ↦₆₄ m9) ∗
       ((s.sp - 288#64) ↦₆₄ m10) ∗
       ((s.sp - 280#64) ↦₆₄ m11) ∗
       ((s.sp - 272#64) ↦₆₄ m12) ∗
       ((s.sp - 264#64) ↦₆₄ m13) ∗
       ((s.sp - 256#64) ↦₆₄ m14) ∗
       ((s.sp - 248#64) ↦₆₄ m15) ∗
       ((s.sp - 240#64) ↦₆₄ m16) ∗
       ((s.sp - 232#64) ↦₆₄ m17) ∗
       ((s.sp - 224#64) ↦₆₄ m18) ∗
       ((s.sp - 216#64) ↦₆₄ m19) ∗
       ((s.sp - 208#64) ↦₆₄ m20) ∗
       ((s.sp - 200#64) ↦₆₄ m21) ∗
       ((s.sp - 192#64) ↦₆₄ m22) ∗
       ((s.sp - 184#64) ↦₆₄ m23) ∗
       ((s.sp - 176#64) ↦₆₄ m24) ∗
       ((s.sp - 168#64) ↦₆₄ m25) ∗
       ((s.sp - 160#64) ↦₆₄ m26) ∗
       ((s.sp - 152#64) ↦₆₄ m27) ∗
       ((s.sp - 144#64) ↦₆₄ m28) ∗
       ((s.sp - 136#64) ↦₆₄ m29) ∗
       ((s.sp - 128#64) ↦₆₄ m30) ∗
       ((s.sp - 120#64) ↦₆₄ m31) ∗
       ((s.sp - 112#64) ↦₆₄ m32) ∗
       ((s.sp - 104#64) ↦₆₄ m33) ∗
       ((s.sp - 96#64) ↦₆₄ m34) ∗
       ((s.sp - 88#64) ↦₆₄ m35) ∗
       ((s.sp - 80#64) ↦₆₄ m36) ∗
       ((s.sp - 72#64) ↦₆₄ m37) ∗
       ((s.sp - 64#64) ↦₆₄ n64) ∗
       ((s.sp - 56#64) ↦₆₄ n56) ∗
       ((s.sp - 48#64) ↦₆₄ n48) ∗
       ((s.sp - 40#64) ↦₆₄ n40) ∗
       ((s.sp - 32#64) ↦₆₄ v0) ∗
       ((s.sp - 24#64) ↦₆₄ v1) ∗
       ((s.sp - 16#64) ↦₆₄ v2) ∗
       ((s.sp - 8#64) ↦₆₄ v3))
      (sepPost (Hop7Regs B s.sp (s.sp + 8#64) (a32.zeroExtend 64) s.fs s.trace)
        (StartProc s.sp envp p ph pg ab af ae uid gid plat hw clk rnd hw2 ex a32 ah32 ∗ StartArgv0 p
          ∗ StartPhdrs ph ∗
         ((B + 0x2000#64) ↦₃₂ 0x20000#32) ∗
         ((B + 0x2008#64) ↦₆₄ 0#64) ∗
         ((B + 0x2010#64) ↦₆₄ g3) ∗
         ((B + 0x2018#64) ↦₆₄ g4) ∗
         ((B + 0x2020#64) ↦₆₄ ia) ∗
         ((B + 0x2028#64) ↦₆₄ ia) ∗
         ((B + 0x2040#64) ↦₆₄ envp) ∗
         ((B + 0x2050#64) ↦₆₄ 0#64) ∗
         ((B + 0x2058#64) ↦₆₄ 0#64) ∗
         ((B + 0x2060#64) ↦₆₄ 0#64) ∗
         ((B + 0x2068#64) ↦₆₄ 0#64) ∗
         ((B + 0x2070#64) ↦₆₄ 8#64) ∗
         ((B + 0x2078#64) ↦₆₄ 0#64) ∗
         ((B + 0x2080#64) ↦₆₄ (B + 0x2080#64)) ∗
         ((B + 0x2088#64) ↦₆₄ (B + 0x2080#64)) ∗
         ((B + 0x2090#64) ↦₆₄ (B + 0x2080#64)) ∗
         ((B + 0x2098#64) ↦₆₄ sy) ∗
         ((B + 0x20a0#64) ↦₃₂ 1#32) ∗
         ((B + 0x20a8#64) ↦₃₂ 2#32) ∗
         ((B + 0x20f8#64) ↦₆₄ (B + 0x20f8#64)) ∗
         ((B + 0x2118#64) ↦₆₄ (B + 0x2220#64)) ∗
         ((B + 0x2140#64) ↦₆₄ (B + 0x2150#64)) ∗
         ((B + 0x2150#64) ↦₆₄ 1#64) ∗
         ((B + 0x2158#64) ↦₆₄ (B + 0x2148#64)) ∗
         ((B + 0x21d0#64) ↦₆₄ sy) ∗
         ((B + 0x21d8#64) ↦₆₄ p) ∗
         ((B + 0x21e0#64) ↦₆₄ p) ∗
         ((B + 0x21e8#64) ↦₈ 1#8) ∗
         ((B + 0x21f0#64) ↦₆₄ (envp + 8#64)) ∗
         ((B + 0x21f8#64) ↦₆₄ (B + 0x2050#64)) ∗
         ((B + 0x2200#64) ↦₆₄ 0xe0#64) ∗
         ((B + 0x2208#64) ↦₆₄ 8#64) ∗
         ((B + 0x2210#64) ↦₆₄ 1#64) ∗
         ((B + 0x2218#64) ↦₆₄ pg) ∗
         ((B + 0x2250#64) ↦₆₄ hw) ∗
         ((s.sp - 480#64) ↦₆₄ (B + 0xae8#64)) ∗
         (∃∗ v : BitVec 64, (s.sp - 472#64) ↦₆₄ v) ∗
         (∃∗ v : BitVec 64, (s.sp - 464#64) ↦₆₄ v) ∗
         ((s.sp - 456#64) ↦₆₄ (B - 85504#64)) ∗
         ((s.sp - 448#64) ↦₆₄ (B + 0xaec#64)) ∗
         (∃∗ v : BitVec 64, (s.sp - 440#64) ↦₆₄ v) ∗
         ((s.sp - 432#64) ↦₆₄ (B + 0x6d0#64)) ∗
         ((s.sp - 368#64) ↦₆₄ 0#64) ∗
         ((s.sp - 360#64) ↦₆₄ 0#64) ∗
         ((s.sp - 352#64) ↦₆₄ 0#64) ∗
         ((s.sp - 344#64) ↦₆₄ ph) ∗
         ((s.sp - 336#64) ↦₆₄ 56#64) ∗
         ((s.sp - 328#64) ↦₆₄ 11#64) ∗
         ((s.sp - 320#64) ↦₆₄ pg) ∗
         ((s.sp - 312#64) ↦₆₄ ab) ∗
         ((s.sp - 304#64) ↦₆₄ af) ∗
         ((s.sp - 296#64) ↦₆₄ ae) ∗
         ((s.sp - 288#64) ↦₆₄ 0#64) ∗
         ((s.sp - 280#64) ↦₆₄ uid) ∗
         ((s.sp - 272#64) ↦₆₄ uid) ∗
         ((s.sp - 264#64) ↦₆₄ gid) ∗
         ((s.sp - 256#64) ↦₆₄ gid) ∗
         ((s.sp - 248#64) ↦₆₄ plat) ∗
         ((s.sp - 240#64) ↦₆₄ hw) ∗
         ((s.sp - 232#64) ↦₆₄ clk) ∗
         ((s.sp - 224#64) ↦₆₄ 0#64) ∗
         ((s.sp - 216#64) ↦₆₄ 0#64) ∗
         ((s.sp - 208#64) ↦₆₄ 0#64) ∗
         ((s.sp - 200#64) ↦₆₄ 0#64) ∗
         ((s.sp - 192#64) ↦₆₄ 0#64) ∗
         ((s.sp - 184#64) ↦₆₄ 0#64) ∗
         ((s.sp - 176#64) ↦₆₄ 0#64) ∗
         ((s.sp - 168#64) ↦₆₄ rnd) ∗
         ((s.sp - 160#64) ↦₆₄ hw2) ∗
         ((s.sp - 152#64) ↦₆₄ 0#64) ∗
         ((s.sp - 144#64) ↦₆₄ 0#64) ∗
         ((s.sp - 136#64) ↦₆₄ 0#64) ∗
         ((s.sp - 128#64) ↦₆₄ 0#64) ∗
         ((s.sp - 120#64) ↦₆₄ ex) ∗
         ((s.sp - 112#64) ↦₆₄ 0#64) ∗
         ((s.sp - 104#64) ↦₆₄ 0#64) ∗
         ((s.sp - 96#64) ↦₆₄ 0#64) ∗
         ((s.sp - 88#64) ↦₆₄ 0#64) ∗
         ((s.sp - 80#64) ↦₆₄ (B + 0x844#64)) ∗
         ((s.sp - 72#64) ↦₆₄ 0#64) ∗
         ((s.sp - 64#64) ↦₆₄ ((a32.zeroExtend 64).truncate 32).zeroExtend 64) ∗
         ((s.sp - 56#64) ↦₆₄ (s.sp + 8#64)) ∗
         ((s.sp - 48#64) ↦₆₄ 0#64) ∗
         ((s.sp - 40#64) ↦₆₄ (s.sp + 8#64)) ∗
         (∃∗ v : BitVec 64, (s.sp - 32#64) ↦₆₄ v) ∗
         ((s.sp - 24#64) ↦₆₄ (s.readReg64 .x21)) ∗
         ((s.sp - 16#64) ↦₆₄ (s.readReg64 .x20)) ∗
         ((s.sp - 8#64) ↦₆₄ (s.readReg64 .x19)))) := by
  obtain ⟨hf1, hf2, hf3a, hf3b, hf4, hf5, hf6, hf7⟩ := hf
  refine SepWP.bind_sepPost
    (musl_start_hop1 Q B hf1 hB s hpc hrun hal hsp16 p g3 g4 v0 v1 v2 v3 _ _ _ envp a32 ah32
      rfl rfl rfl henvp) (by sep_frame) ?_
  rintro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hlr1, hx29_1, hfs1, htr1⟩
  refine SepWP.bind_sepPost
    (musl_start_hop2 Q B hf2 s1 s.sp envp p (B - 85504#64) (s.sp + 8#64) (a32.zeroExtend 64)
      0#64 (B + 2052#64) hpc1 hrun1 hfs1 htr1 hsp1 hal hx0_1 hx1_1 hx19_1 hx20_1 hx29_1 hlr1 hx21_1
      m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25
        m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37
      n64 n56 n48 n40) (by sep_frame) ?_
  rintro s2 hpc2 hrun2 ⟨hsp2, hx19_2, hx20_2, hx21_2, hfs2, htr2⟩
  refine SepWP.bind_sepPost
    (musl_start_hop3a Q B hf3a hB s2 s.sp envp p (B - 85504#64) hpc2 hrun2 hfs2 htr2 hsp2
      hx19_2 hx20_2 hx21_2 e0 e1 ph 56#64 11#64 pg ab af ae uid uid gid gid plat hw clk 0#64 rnd hw2
      ex 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64)
    (by sep_frame) ?_
  rintro s3 hpc3 hrun3 ⟨hsp3, hx19_3, hx21_3, hfs3, htr3⟩
  refine SepWP.bind_sepPost
    (musl_start_hop3b Q B hf3b hB s3 s.sp p (B - 85504#64) hpc3 hrun3 hfs3 htr3 hsp3 hx19_3 hp
      hx21_3 hal hw ex pg d0 d1 d2 d3) (by sep_frame) ?_
  rintro s4 hpc4 hrun4 ⟨hsp4, hx19_4, hx0_4, hlr4, hx21_4, hfs4, htr4⟩
  refine SepWP.bind_sepPost
    (musl_start_hop4 Q B hf4 hB s4 s.sp ph (B - 85504#64) hpc4 hrun4 hfs4 htr4 hsp4 hx0_4 hlr4
      hx21_4 hal hph w432 t0 t1 t2 t3 t4 t5 t6 t7 t8) (by sep_frame) ?_
  rintro s5 hpc5 hrun5 ⟨hsp5, hx0_5, hlr5, hx21_5, hfs5, htr5⟩
  refine SepWP.bind_sepPost
    (musl_start_hop5 Q B hf5 hB s5 s.sp (s5.readReg64 .x19) (s5.readReg64 .x20) (B - 85504#64)
      (s5.readReg64 .x22) (s5.readReg64 .x23) hpc5 hrun5 hfs5 htr5 hsp5 hx0_5 hlr5 rfl rfl hx21_5
      rfl rfl hal w480 w472 w464 w456 w448 w440 u0 u1 u2) (by sep_frame) ?_
  rintro s6 hpc6 hrun6 ⟨hsp6, hx0_6, hlr6, hx21_6, hfs6, htr6⟩
  refine SepWP.bind_sepPost
    (musl_start_hop6 Q B hf6 hsvc hB s6 s.sp (s6.readReg64 .x19) (B - 85504#64) hpc6 hrun6 hfs6 htr6
      hsp6 hx0_6 hlr6 rfl hx21_6 hal (s5.readReg64 .x20) (s5.readReg64 .x19) f0 f3 f5 f6 f7 f8 sy
      f1 f2 f4) (by sep_frame) ?_
  rintro s7 hpc7 hrun7 ⟨hsp7, hx0_7, hx19_7, hlr7, hx21_7, hfs7, htr7⟩
  exact SepWP.done_sepPost
    (musl_start_hop7 Q B hf7 hB s7 s.sp (s7.readReg64 .x22) hpc7 hrun7 hfs7 htr7 hsp7 hx0_7
      hx21_7 rfl hal rnd uid gid ia 0#64 0#64 0#64 (a32.zeroExtend 64) (s.sp + 8#64)
      (s.readReg64 .x21) (s.readReg64 .x20) (s.readReg64 .x19))
    (by sep_frame) (fun _ _ _ h => h) (by sep_frame)

/-! ## Lifting `SepWP` to `Steps` on `Program.ofImage` -/

/-- Lifts a `SepWP` `sepPost` triple on `Q` to a `Steps` run of `P` when `Q` and `P` share extern hooks and `svc`. -/
theorem steps_of_sepWP {P Q : Program} (hPQ : ∀ pc, Q.externAt? pc = P.externAt? pc)
    (hsvc : Q.svc = P.svc := by rfl)
    {tgt : BitVec 64} {s : State} {Pre Post R : SepProp} {Inv : State → Prop}
    (h : SepWP Q tgt s Pre (sepPost Inv Post)) (hL : Q.CodeLoaded s.mem)
    (hm : s.mem ⊨ Pre ∗ R) :
    ∃ sm, Steps P s sm ∧ sm.pc = tgt ∧ sm.status = .Running ∧ Inv sm ∧ (sm.mem ⊨ Post ∗ R) := by
  unfold SepWP at h
  rcases h R hm hL with ⟨sm, hsteps, ⟨hpc, hrun, P_f, hmf, hInv, hent⟩ | ⟨-, hoom⟩⟩
  · exact ⟨sm, steps_of_externAt_eq hPQ hsvc hsteps, hpc, hrun, hInv,
      Satisfies.mono (sepConj_mono_left hent) hmf⟩
  · simp at hoom

/-- `MuslStartFetch` moves from the hookless `{ code }` (base 0) to `muslProg P B code`, when no
PC `B + k` with `k < 0xb90` (musl's text) is a hook PC. -/
theorem muslStartFetch_muslProg (P : Program) (B : BitVec 64) (code : List (BitVec 8))
    (hx : ∀ k : BitVec 64, k.toNat < 0xb90 → (muslProg P B code).externAt? (B + k) = none)
    (hf : MuslStartFetch ({ code } : Program) 0#64) : MuslStartFetch (muslProg P B code) B := by
  have e : ∀ k : BitVec 64, k.toNat < 0xb90 →
      (muslProg P B code).fetch (B + k) = ({ code } : Program).fetch (0#64 + k) := by
    intro k hk
    rw [BitVec.zero_add]
    exact muslProg_fetch_add P B code k (hx k hk)
  have e0 : (muslProg P B code).fetch B = ({ code } : Program).fetch 0#64 := by
    have := e 0#64 (by decide)
    rwa [BitVec.add_zero] at this
  unfold MuslStartFetch MuslHop1Fetch MuslHop2Fetch MuslMemsetFetch MuslHop3aFetch MuslHop3bFetch
    MuslHop4Fetch MuslHop5Fetch MuslHop6Fetch MuslHop7Fetch at hf ⊢
  simp (disch := decide) only [e, e0]
  exact hf

/-- `sp0 - 48` is 16-byte aligned when `sp0` is. -/
theorem spAligned_sub48 (sp0 : BitVec 64) (hal : (sp0 &&& 15#64 == 0#64) = true) :
    ((sp0 - 48#64) &&& 0b1111#64 == 0#64) = true := by
  have h0 : sp0 &&& 15#64 = 0#64 := eq_of_beq hal
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h0
  rw [e] at h'
  rw [show (0b1111#64) = 15#64 from rfl, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [e]
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have hlt := sp0.isLt
  omega

/-- Lifts a `MuslStartFetch`-parametric `SepWP` triple to a `Steps` run of `Program.ofImage img E`. -/
theorem musl_start_ofImage {li : Obj.LinkedImage} {img : Obj.Image} (himg : Obj.Loads li img)
    (E : String → Option (State → State)) {B : BitVec 64} {code : List (BitVec 8)}
    (hend : img.base.toNat + img.code.length ≤ B.toNat) (hnw : B.toNat + 0xb90 ≤ 2 ^ 64)
    (hf : MuslStartFetch ({ code } : Program) 0#64)
    {s : State} (hL : ({ base := B, code } : Program).CodeLoaded s.mem)
    {tgt : BitVec 64} {Pre Post R : SepProp} {Inv : State → Prop}
    (hwp : ∀ Q, MuslStartFetch Q B → Q.svc = Syscall.standard → SepWP Q tgt s Pre (sepPost Inv Post))
    (hm : s.mem ⊨ Pre ∗ R) :
    ∃ sm, Steps (Program.ofImage img E) s sm ∧ sm.pc = tgt ∧ sm.status = .Running ∧ Inv sm ∧
      (sm.mem ⊨ Post ∗ R) := by
  have hst : ∀ x ∈ (Program.ofImage img E).stubs, x.2 < 2 ^ 64 := by
    rintro ⟨n, o⟩ hmem
    have h1 := stub_lt_code himg hmem
    have h2 := B.isLt
    simp only at h1 ⊢
    omega
  have hPQ : ∀ pc, (muslProg (Program.ofImage img E) B code).externAt? pc =
      (Program.ofImage img E).externAt? pc :=
    muslProg_externAt? _ B code hst (fun _ => rfl)
  have hfQ : MuslStartFetch (muslProg (Program.ofImage img E) B code) B := by
    refine muslStartFetch_muslProg _ B code (fun k hk => ?_) hf
    rw [hPQ]
    apply externAt?_ofImage_eq_none_of_ge himg E
    have : (B + k).toNat = B.toNat + k.toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    omega
  exact steps_of_sepWP hPQ rfl (hwp _ hfQ rfl) (hL.of_base_code rfl rfl) hm

end CryptoVerification.SignalSession.MuslStart
