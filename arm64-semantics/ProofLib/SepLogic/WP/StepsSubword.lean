/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Std.Tactic.BVDecide
public import Arm64
public import ProofLib.SimpAttrs
public import ProofLib.CoreLemmas
public import ProofLib.Lemmas
public import ProofLib.SepLogic.Frame
public import ProofLib.Abi.Aapcs
public import ProofLib.SepLogic
public import ProofLib.SepLogic.Bytes
public import ProofLib.ObjectLoad
public import ProofLib.Hoare.Safety
public import ProofLib.VCGen
public import ProofLib.LitNorm
public import ProofLib.BV.WidthNorm
public import ProofLib.SepLogic.WP.Defs
public import ProofLib.SepLogic.CondClassify
public import ProofLib.BV.Arith
public import ProofLib.SepLogic.WP.StateNorm
public import ProofLib.SepLogic.WP.Access
public import ProofLib.SepLogic.WP.StepsCore

/-!
# Subword and Exclusive `SepWP` Load/Store Step Lemmas

`SepWP` step rules for 32-bit, 16-bit, and byte-decomposed loads, stores, and pairs,
load-acquire/store-release instructions, and load/store-exclusive instructions and retry loops.
-/

@[expose] public section

namespace ProofLib

open Arm64

/-- 32-bit load (`LDR Wt, [addr]`) step rule for `SepWP`: looks up `(ea ↦₃₂ v)` in `P` via `SepLoad32`. -/
theorem SepWP.step_ldr32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .W32 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad32 ea P v)
    (hexec : ((applyWriteback s wb).writeReg .W32 rt (v.zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W32 .W32 false rt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read32 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 4 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr .W32 .W32 false rt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- 32-bit unscaled load (`LDUR Wt, [addr]`) step rule for `SepWP`: looks up `(ea ↦₃₂ v)` in `P`
    via `SepLoad32`. -/
theorem SepWP.step_ldur32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .W32 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad32 ea P v)
    (hexec : ((applyWriteback s wb).writeReg .W32 rt (v.zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_ldr32 hpc hrun hfetch hsp haddr hload hexec hnext

/-- 32-bit signed load (`LDRSW Xt, [addr]`) step rule for `SepWP`: looks up `(ea ↦₃₂ v)` in `P`
    via `SepLoad32`. -/
theorem SepWP.step_ldrsw32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W64 .W32 true rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad32 ea P v)
    (hexec : ((applyWriteback s wb).writeReg .W64 rt (v.signExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W64 .W32 true rt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read32 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 4 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr .W64 .W32 true rt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- Unscaled 32-bit signed load (`LDURSW Xt, [addr]`) step rule for `SepWP`: looks up
    `(ea ↦₃₂ v)` in `P` via `SepLoad32`. -/
theorem SepWP.step_ldursw32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W64 .W32 true rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad32 ea P v)
    (hexec : ((applyWriteback s wb).writeReg .W64 rt (v.signExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_ldrsw32 hpc hrun hfetch hsp haddr hload hexec hnext

/-- 32-bit load pair (`LDP Wt1, Wt2, [addr]`) step rule for `SepWP`: looks up `(ea ↦₃₂ v1)` and
    `(ea + 4 ↦₃₂ v2)` in `P` via `SepLoad32`. -/
theorem SepWP.step_ldp32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldp .W32 false rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 4#64 = ea2)
    (hload1 : SepLoad32 ea P v1)
    (hload2 : SepLoad32 ea2 P v2)
    (hexec : (((applyWriteback s wb).writeReg .W32 rt1 (v1.zeroExtend 64)).writeReg .W32 rt2 (v2.zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldp .W32 false rt1 rt2 addr) := hpc.symm ▸ hfetch
  have hread1 : s.mem.read32 ea = v1 := hload1.load hm
  have hread2 : s.mem.read32 ea2 = v2 := hload2.load hm
  have hcan1 : s.mem.canRead ea 4 = true := hload1.readable hm
  have hcan2 : s.mem.canRead ea2 4 = true := hload2.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldp .W32 false rt1 rt2 addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdp, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hea2, hread1, hread2, hcan1, hcan2,
      MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- 32-bit store (`STR Wt, [addr]`) step rule for `SepWP`: updates `(ea ↦₃₂ _)` to `(ea ↦₃₂ val)`
    in `P` via `SepStore32` and abstracts the post-store memory to a fresh variable `m'`. -/
theorem SepWP.step_str32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .W32 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg32 rt = val)
    (hstore : SepStore32 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .W32 rt addr) := hpc.symm ▸ hfetch
  have htrunc : (s.readReg64 rt).truncate 32 = val := hval
  let m' := s.mem.write32 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea _ = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .W32 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact hnext m' R hm'

/-- 32-bit unscaled store (`STUR Wt, [addr]`) step rule for `SepWP`: updates `(ea ↦₃₂ _)` to
    `(ea ↦₃₂ val)` in `P` via `SepStore32` and abstracts the post-store memory to a fresh `m'`. -/
theorem SepWP.step_stur32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .W32 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg32 rt = val)
    (hstore : SepStore32 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_str32 hpc hrun hfetch hsp haddr hval hstore hexec hnext

/-- 32-bit store pair (`STP Wt1, Wt2, [addr]`) step rule for `SepWP`: updates `ea` and `ea + 4`
    in `P` via `SepStore32` and abstracts the post-store memory to a fresh variable `m'`. -/
theorem SepWP.step_stp32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stp .W32 rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 4#64 = ea2)
    (hv1 : s.readReg32 rt1 = v1)
    (hv2 : s.readReg32 rt2 = v2)
    (hstore1 : SepStore32 ea v1 P P1)
    (hstore2 : SepStore32 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.stp .W32 rt1 rt2 addr) := hpc.symm ▸ hfetch
  have htrunc1 : (s.readReg64 rt1).truncate 32 = v1 := hv1
  have htrunc2 : (s.readReg64 rt2).truncate 32 = v2 := hv2
  let m1 := s.mem.write32 ea v1
  let m2 := m1.write32 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 4 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 4 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write32 _ _ _)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stp .W32 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, htrunc1, htrunc2, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact hnext m2 R hm2

/-- 32-bit load (`LDR Wt, [addr]`) from the low 32 bits of a 64-bit word `(ea ↦₆₄ v)`. -/
theorem SepWP.step_ldr32_64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .W32 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad64 ea P v)
    (hexec : ((applyWriteback s wb).writeReg .W32 rt ((v.truncate 32).zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W32 .W32 false rt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read32 ea = v.truncate 32 := by
    rw [Memory.read32_eq_truncate_read64, hload.load hm]
  have hcan : s.mem.canRead ea 4 = true := Memory.canRead_4_of_8 (hload.readable hm)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr .W32 .W32 false rt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- 32-bit load (`LDR Wt, [addr]`) from the high 32 bits (`base + 4`) of a 64-bit word `(base ↦₆₄ v)`. -/
theorem SepWP.step_ldr32_hi64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea base : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .W32 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hbase : ea - 4#64 = base)
    (hload : SepLoad64 base P v)
    (hexec : ((applyWriteback s wb).writeReg .W32 rt ((v.extractLsb' 32 32).zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W32 .W32 false rt addr) := hpc.symm ▸ hfetch
  have hea : ea = base + 4#64 := by rw [← hbase]; bv_decide
  have hread : s.mem.read32 ea = v.extractLsb' 32 32 := by
    rw [hea, Memory.read32_add4_eq_extract_read64, hload.load hm]
  have hcan : s.mem.canRead ea 4 = true := by
    rw [hea]
    exact Memory.canRead_hi4_of_8 (hload.readable hm)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr .W32 .W32 false rt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- 32-bit signed load (`LDRSW Xt, [addr]`) from the low 32 bits of a 64-bit word `(ea ↦₆₄ v)`. -/
theorem SepWP.step_ldrsw32_64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W64 .W32 true rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad64 ea P v)
    (hexec : ((applyWriteback s wb).writeReg .W64 rt ((v.truncate 32).signExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W64 .W32 true rt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read32 ea = v.truncate 32 := by
    rw [Memory.read32_eq_truncate_read64, hload.load hm]
  have hcan : s.mem.canRead ea 4 = true := Memory.canRead_4_of_8 (hload.readable hm)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr .W64 .W32 true rt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- 32-bit signed load (`LDRSW Xt, [addr]`) from the high 32 bits (`base + 4`) of a 64-bit word `(base ↦₆₄ v)`. -/
theorem SepWP.step_ldrsw32_hi64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea base : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W64 .W32 true rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hbase : ea - 4#64 = base)
    (hload : SepLoad64 base P v)
    (hexec : ((applyWriteback s wb).writeReg .W64 rt ((v.extractLsb' 32 32).signExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W64 .W32 true rt addr) := hpc.symm ▸ hfetch
  have hea : ea = base + 4#64 := by rw [← hbase]; bv_decide
  have hread : s.mem.read32 ea = v.extractLsb' 32 32 := by
    rw [hea, Memory.read32_add4_eq_extract_read64, hload.load hm]
  have hcan : s.mem.canRead ea 4 = true := by
    rw [hea]
    exact Memory.canRead_hi4_of_8 (hload.readable hm)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr .W64 .W32 true rt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- 32-bit load pair (`LDP Wt1, Wt2, [addr]`) from a single 64-bit word `(ea ↦₆₄ v)`. -/
theorem SepWP.step_ldp32_64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldp .W32 false rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad64 ea P v)
    (hexec : (((applyWriteback s wb).writeReg .W32 rt1 ((v.truncate 32).zeroExtend 64)).writeReg .W32 rt2 ((v.extractLsb' 32 32).zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldp .W32 false rt1 rt2 addr) := hpc.symm ▸ hfetch
  have hread1 : s.mem.read32 ea = v.truncate 32 := by
    rw [Memory.read32_eq_truncate_read64, hload.load hm]
  have hread2 : s.mem.read32 (ea + 4#64) = v.extractLsb' 32 32 := by
    rw [Memory.read32_add4_eq_extract_read64, hload.load hm]
  have hcan1 : s.mem.canRead ea 4 = true := Memory.canRead_4_of_8 (hload.readable hm)
  have hcan2 : s.mem.canRead (ea + 4#64) 4 = true := Memory.canRead_hi4_of_8 (hload.readable hm)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldp .W32 false rt1 rt2 addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdp, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread1, hread2, hcan1, hcan2,
      MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

private theorem isLazyFree_write8_eq_of_false {m : Memory} {addr : BitVec 64}
    (h : m.isLazyFree addr = false) (v : BitVec 8) :
    (m.write8 addr v).isLazyFree = m.isLazyFree := by
  funext a
  by_cases ha : a = addr
  · subst ha; simp [h]
  · simp [ha]

private theorem noLazyFree8_of_canRead8 {m : Memory} {base : BitVec 64}
    (h : m.canRead base 8 = true) :
    m.isLazyFree (base + 0#64) = false ∧ m.isLazyFree (base + 1#64) = false ∧
    m.isLazyFree (base + 2#64) = false ∧ m.isLazyFree (base + 3#64) = false ∧
    m.isLazyFree (base + 4#64) = false ∧ m.isLazyFree (base + 5#64) = false ∧
    m.isLazyFree (base + 6#64) = false ∧ m.isLazyFree (base + 7#64) = false := by
  have hnlf : m.allNoLazyFree base 8 = true := (Bool.and_eq_true _ _).mp h |>.2
  simpa [Memory.allNoLazyFree, BitVec.add_assoc, Bool.and_eq_true] using hnlf

private theorem isLazyFree_write64_eq_of_canRead8 {m : Memory} {base : BitVec 64}
    (h : m.canRead base 8 = true) (v : BitVec 64) :
    (m.write64 base v).isLazyFree = m.isLazyFree := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := noLazyFree8_of_canRead8 h
  funext a
  simp only [Memory.write64, Memory.isLazyFree_write8]
  repeat' split
  all_goals simp_all

private theorem isLazyFree_write32_lo_eq_of_canRead8 {m : Memory} {base : BitVec 64}
    (h : m.canRead base 8 = true) (v : BitVec 32) :
    (m.write32 base v).isLazyFree = m.isLazyFree := by
  obtain ⟨h0, h1, h2, h3, _, _, _, _⟩ := noLazyFree8_of_canRead8 h
  funext a
  simp only [Memory.write32, Memory.isLazyFree_write8]
  repeat' split
  all_goals simp_all

private theorem isLazyFree_write32_hi_eq_of_canRead8 {m : Memory} {base ea : BitVec 64}
    (hbase : ea - 4#64 = base) (h : m.canRead base 8 = true) (v : BitVec 32) :
    (m.write32 ea v).isLazyFree = m.isLazyFree := by
  have hea : ea = base + 4#64 := by rw [← hbase]; bv_decide
  subst hea
  obtain ⟨_, _, _, _, h4, h5, h6, h7⟩ := noLazyFree8_of_canRead8 h
  have ha0 : base + 4#64 + 0#64 = base + 4#64 := by bv_bits
  have ha1 : base + 4#64 + 1#64 = base + 5#64 := by bv_bits
  have ha2 : base + 4#64 + 2#64 = base + 6#64 := by bv_bits
  have ha3 : base + 4#64 + 3#64 = base + 7#64 := by bv_bits
  funext a
  simp only [Memory.write32, Memory.isLazyFree_write8, ha0, ha1, ha2, ha3]
  repeat' split
  all_goals simp_all

/-- 32-bit store (`STR Wt, [addr]`) into the low 32 bits of a 64-bit word `(ea ↦₆₄ old64)`. -/
theorem SepWP.step_str32_64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {old64 new64 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .W32 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad64 ea P old64)
    (hval : (old64 &&& 0xffffffff00000000#64) ||| ((s.readReg32 rt).zeroExtend 64) = new64)
    (hstore : SepStore64 ea new64 P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .W32 rt addr) := hpc.symm ▸ hfetch
  let val32 := (s.readReg64 rt).truncate 32
  let m' := s.mem.write32 ea val32
  have hm64 : s.mem.write64 ea new64 ⊨ P' ∗ R := hstore.store hm
  have hm' : m' ⊨ P' ∗ R := by
    refine Satisfies.congr_mem (fun a => ?_) ?_ ?_ (by simp [m']) hm64
    · exact Memory.read8_write32_eq_read8_write64_lo s.mem ea a val32 old64 new64
        (hload.load hm) hval
    · rw [Memory.perm_write32, Memory.perm_write64]
    · rw [isLazyFree_write32_lo_eq_of_canRead8 (hload.readable hm),
        isLazyFree_write64_eq_of_canRead8 (hload.readable hm)]
  have hcan : s.mem.canWrite ea 4 = true := Memory.canWrite_4_of_8 (hstore.writable hm)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .W32 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hcan,
      MemWidth.bytes, hpc, m', val32]
  rw [hstep]
  exact hnext m' R hm'

/-- 32-bit store (`STR Wt, [addr]`) into the high 32 bits (`base + 4`) of a 64-bit word `(base ↦₆₄ old64)`. -/
theorem SepWP.step_str32_hi64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea base : BitVec 64} {wb : Option (Reg × BitVec 64)} {old64 new64 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .W32 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hbase : ea - 4#64 = base)
    (hload : SepLoad64 base P old64)
    (hval : (old64 &&& 0x00000000ffffffff#64) ||| (((s.readReg32 rt).zeroExtend 64) <<< 32) = new64)
    (hstore : SepStore64 base new64 P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .W32 rt addr) := hpc.symm ▸ hfetch
  let val32 := (s.readReg64 rt).truncate 32
  let m' := s.mem.write32 ea val32
  have hm64 : s.mem.write64 base new64 ⊨ P' ∗ R := hstore.store hm
  have hm' : m' ⊨ P' ∗ R := by
    refine Satisfies.congr_mem (fun a => ?_) ?_ ?_ (by simp [m']) hm64
    · exact Memory.read8_write32_eq_read8_write64_hi s.mem base ea a val32 old64 new64
        hbase (hload.load hm) hval
    · rw [Memory.perm_write32, Memory.perm_write64]
    · rw [isLazyFree_write32_hi_eq_of_canRead8 hbase (hload.readable hm),
        isLazyFree_write64_eq_of_canRead8 (hload.readable hm)]
  have hea : ea = base + 4#64 := by rw [← hbase]; bv_decide
  have hcan : s.mem.canWrite ea 4 = true := by
    rw [hea]
    exact Memory.canWrite_hi4_of_8 (hstore.writable hm)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .W32 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hcan,
      MemWidth.bytes, hpc, m', val32]
  rw [hstep]
  exact hnext m' R hm'

/-- 32-bit load-acquire (`LDAR Wt, [Xn]`) from the low 32 bits of a 64-bit word `(ea ↦₆₄ v)`. -/
theorem SepWP.step_ldar32_64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rn rt : Reg} {ea v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldarStlr .W32 true rn rt))
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .W32 ea = true)
    (hload : SepLoad64 ea P v)
    (hexec : (s.writeReg .W32 rt ((v.truncate 32).zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldarStlr .W32 true rn rt) := hpc.symm ▸ hfetch
  have hread : s.mem.read32 ea = v.truncate 32 := by
    rw [Memory.read32_eq_truncate_read64, hload.load hm]
  have hcan : s.mem.canRead ea 4 = true := Memory.canRead_4_of_8 (hload.readable hm)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldarStlr .W32 true rn rt) s = s' := by
    rw [← hexec]
    simp [Program.evalInst, execInstWithSvc, Memory.readSized, State.writeReg,
      State.advancePC, State.setPC, hsp, haddr, halign, hread, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    rfl
  apply hnext R
  rwa [hmem]

/-- 64-bit store-release (`STLR Xt, [Xn]`) step rule for `SepWP`: updates `(ea ↦₆₄ _)` in `P` to
    `(ea ↦₆₄ val)` via `SepStore64`. -/
theorem SepWP.step_stlr64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rn rt : Reg} {ea val : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldarStlr .X64 false rn rt))
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .X64 ea = true)
    (hval : s.readReg64 rt = val)
    (hstore : SepStore64 ea val P P')
    (hexec : (s.setMem (s.mem.write64 ea val)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.ldarStlr .X64 false rn rt) s = s' := by
    rw [← hexec]
    simp [Program.evalInst, execInstWithSvc, Memory.writeSized, State.advancePC, State.setPC,
      State.setMem, hsp, haddr, halign, hval, hstore.writable hm, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem.write64 ea val := by rw [← hexec]; rfl
  exact hnext R (hmem ▸ hstore.store hm)

/-- 32-bit store-release (`STLR Wt, [Xn]`) step rule for `SepWP`: updates `(ea ↦₃₂ _)` in `P` to
    `(ea ↦₃₂ v)` via `SepStore32` and abstracts the post-store memory to a fresh variable `m'`. -/
theorem SepWP.step_stlr32 {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc pc' : BitVec 64} {rn rt : Reg} {ea : BitVec 64} {v : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldarStlr .W32 false rn rt))
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .W32 ea = true)
    (hval : (s.readReg64 rt).truncate 32 = v)
    (hstore : SepStore32 ea v P P')
    (hpc' : pc + 4#64 = pc' := by bv_lin)
    (hnext : ∀ m' : Memory, SepWP prog target_pc ((s.setMem m').setPC pc') P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  let m' := s.mem.write32 ea v
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 4 = true := hstore.writable hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.ldarStlr .W32 false rn rt) s = (s.setMem m').setPC pc' := by
    subst hpc'
    simp [Program.evalInst, execInstWithSvc, Memory.writeSized, State.advancePC, State.setPC,
      State.setMem, hsp, haddr, halign, hval, hcan, MemWidth.bytes, hpc, m']
  rw [hstep]
  exact hnext m' R hm'

/-- 64-bit load-acquire (`LDAR Xt, [Xn]`) step rule for `SepWP`: looks up `(ea ↦₆₄ v)` in `P`
    via `SepLoad64`. -/
theorem SepWP.step_ldar64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rn rt : Reg} {ea v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldarStlr .X64 true rn rt))
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .X64 ea = true)
    (hload : SepLoad64 ea P v)
    (hexec : (s.writeReg .W64 rt v).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.ldarStlr .X64 true rn rt) s = s' := by
    rw [← hexec]
    simp [Program.evalInst, execInstWithSvc, Memory.readSized, State.advancePC, State.setPC,
      hsp, haddr, halign, hload.load hm, hload.readable hm, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by rw [← hexec]; rfl
  exact hnext R (hmem ▸ hm)

/-! ## Load/Store-Exclusive Step Lemmas -/

/-- 64-bit load-exclusive (`LDXR Xt, [Xn]` / `LDAXR Xt, [Xn]`) step rule: looks up
    `(ea ↦₆₄ v)` in `P` via `SepLoad64`. -/
theorem SepWP.step_ldxr64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {acq : Bool} {rn rt : Reg} {ea v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldxr .X64 acq rn rt))
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .X64 ea = true)
    (hload : SepLoad64 ea P v)
    (hexec : (s.writeReg .W64 rt v).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldxr .X64 acq rn rt) := hpc.symm ▸ hfetch
  have hread : s.mem.read64 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 8 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldxr .X64 acq rn rt) s = s' := by
    rw [← hexec]
    simp [Program.evalInst, execInstWithSvc, Memory.readSized, State.advancePC, State.setPC, hsp, haddr, halign, hread,
      hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    rfl
  apply hnext R
  rwa [hmem]

/-- 32-bit load-exclusive (`LDXR Wt, [Xn]` / `LDAXR Wt, [Xn]`) step rule: looks up
    `(ea ↦₃₂ v)` in `P` via `SepLoad32`. -/
theorem SepWP.step_ldxr32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {acq : Bool} {rn rt : Reg} {ea : BitVec 64} {v : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldxr .W32 acq rn rt))
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .W32 ea = true)
    (hload : SepLoad32 ea P v)
    (hexec : (s.writeReg .W32 rt (v.zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldxr .W32 acq rn rt) := hpc.symm ▸ hfetch
  have hread : s.mem.read32 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 4 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldxr .W32 acq rn rt) s = s' := by
    rw [← hexec]
    simp [Program.evalInst, execInstWithSvc, Memory.readSized, State.advancePC, State.setPC, hsp, haddr, halign, hread,
      hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    rfl
  apply hnext R
  rwa [hmem]

/-- 64-bit store-exclusive (`STXR Ws, Xt, [Xn]` / `STLXR Ws, Xt, [Xn]`) single-step rule when the
    store-exclusive oracle does not fail (`s.exclWillFail = false`): consumes one oracle entry via
    `s.stepExclOracle`, updates `(ea ↦₆₄ _)` to `(ea ↦₆₄ val)` in `P` via `SepStore64`, writes
    status `ws := 0`, and abstracts the post-store memory to a fresh variable `m'`. -/
theorem SepWP.step_stxr64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rel : Bool} {rs rn rt : Reg} {ea val : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stxr .X64 rel rs rn rt))
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .X64 ea = true)
    (hno_fail : s.exclWillFail = false)
    (hval : s.readReg64 rt = val)
    (hstore : SepStore64 ea val P P')
    (hexec : (s.stepExclOracle.writeReg .W32 rs 0#64).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.stxr .X64 rel rs rn rt) := hpc.symm ▸ hfetch
  let m' := s.mem.write64 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 8 = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stxr .X64 rel rs rn rt) s = s'.setMem m' := by
    rw [← hexec]
    simp only [Program.evalInst, execInstWithSvc, hsp, haddr, halign, hno_fail, hval, MemWidth.bytes, hcan, Memory.writeSized,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc, m']
  rw [hstep]
  exact hnext m' R hm'

/-- 32-bit store-exclusive (`STXR Ws, Wt, [Xn]` / `STLXR Ws, Wt, [Xn]`) single-step rule when the
    store-exclusive oracle does not fail (`s.exclWillFail = false`): consumes one oracle entry via
    `s.stepExclOracle`, updates `(ea ↦₃₂ _)` to `(ea ↦₃₂ val)` in `P` via `SepStore32`, writes
    status `ws := 0`, and abstracts the post-store memory to a fresh variable `m'`. -/
theorem SepWP.step_stxr32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rel : Bool} {rs rn rt : Reg} {ea : BitVec 64} {val : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stxr .W32 rel rs rn rt))
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .W32 ea = true)
    (hno_fail : s.exclWillFail = false)
    (hval : s.readReg32 rt = val)
    (hstore : SepStore32 ea val P P')
    (hexec : (s.stepExclOracle.writeReg .W32 rs 0#64).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.stxr .W32 rel rs rn rt) := hpc.symm ▸ hfetch
  have htrunc : (s.readReg64 rt).truncate 32 = val := hval
  let m' := s.mem.write32 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 4 = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stxr .W32 rel rs rn rt) s = s'.setMem m' := by
    rw [← hexec]
    simp only [Program.evalInst, execInstWithSvc, hsp, haddr, halign, hno_fail, MemWidth.bytes, hcan, Memory.writeSized, htrunc,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc, m']
  rw [hstep]
  exact hnext m' R hm'

/-! ## Store-Exclusive Retry-Loop Step Lemmas -/

@[simp, arm64_norm, wp_norm]
theorem State.exclWillFail_eq_headD (s : State) :
    s.exclWillFail = s.exclFails.headD false := by cases s; rfl

attribute [arm64_norm, wp_norm] _root_.List.headD_nil _root_.List.headD_cons
  _root_.List.tail_nil _root_.List.tail_cons

/-- Update `s.exclFails` to `ef`. -/
def _root_.Arm64.State.withExclFails (s : State) (ef : List Bool) : State :=
  { s with exclFails := ef }

/-- State at the `STXR`/`STLXR` instruction after a retry iteration with remaining oracle `ef`
    and status register `rs := w_rs`. -/
def _root_.Arm64.State.stxrIter (s : State) (ef : List Bool) (rs : Reg) (w_rs : BitVec 64) : State :=
  (s.withExclFails ef).writeReg64 rs w_rs

/-- True when `r` is a non-zero general-purpose register (`.gpr idx` with `idx != 31#5`). -/
def _root_.Arm64.Reg.isNonZeroGpr (r : Reg) : Bool :=
  match r with
  | .gpr idx => idx != 31#5
  | _ => false

private theorem reg_ne_of_bne {r1 r2 : Reg} (h : (r1 != r2) = true) : r1 ≠ r2 := by
  intro heq; subst heq; revert h; cases r1 <;> decide +revert

private theorem State.writeReg64_readReg64_self (s : State) (r : Reg) :
    s.writeReg64 r (s.readReg64 r) = s := by
  cases s with
  | mk regs vregs sp pc pstate mem tpidrEl0 fpsr brkStart brk fs oracle oracleIdx exclFails trace status symtab =>
    cases r with
    | gpr idx =>
      dsimp [State.writeReg64, State.readReg64]
      by_cases h31 : idx == 31#5
      · simp [h31]
      · simp [h31, RegFile.write, RegFile.read]
        cases regs
        congr 1
        funext i
        by_cases hi : i = idx <;> simp [hi]
    | sp => rfl
    | xzr => rfl

private theorem State.stxrIter_self (s : State) (rs : Reg) :
    s.stxrIter s.exclFails rs (s.readReg64 rs) = s := by
  simp [State.stxrIter, State.withExclFails, State.writeReg64_readReg64_self]

private theorem State.stxrIter_setPState (s : State) (ef : List Bool) (rs : Reg)
    (w_rs : BitVec 64) (ps : PState) :
    (s.stxrIter ef rs w_rs).setPState ps = (s.setPState ps).stxrIter ef rs w_rs := by
  cases s; cases rs <;> rfl

private theorem State.stxrIter_advancePC (s : State) (ef : List Bool) (rs : Reg)
    (w_rs : BitVec 64) :
    (s.stxrIter ef rs w_rs).advancePC = s.advancePC.stxrIter ef rs w_rs := by
  cases s; cases rs <;> rfl

private theorem State.readReg64_stxrIter_of_bne (s : State) (ef : List Bool) (rs r : Reg)
    (w_rs : BitVec 64) (hne : (r != rs) = true) :
    (s.stxrIter ef rs w_rs).readReg64 r = s.readReg64 r := by
  dsimp [State.stxrIter, State.writeReg]
  exact State.readReg64_writeReg64_ne (s.withExclFails ef) rs r _ (reg_ne_of_bne hne)

private theorem State.readReg_stxrIter_of_bne (s : State) (ef : List Bool) (rs r : Reg)
    (w : Width) (w_rs : BitVec 64) (hne : (r != rs) = true) :
    (s.stxrIter ef rs w_rs).readReg w r = s.readReg w r := by
  cases w <;> simp [State.readReg, State.readReg32, State.readReg64_stxrIter_of_bne s ef rs r w_rs hne]

private theorem checkRegSPAligned_stxrIter_of_bne (s : State) (ef : List Bool) (rs r : Reg)
    (w_rs : BitVec 64) (_hne : (r != rs) = true) (hrs : rs.isNonZeroGpr = true) :
    checkRegSPAligned (s.stxrIter ef rs w_rs) r = checkRegSPAligned s r := by
  cases r with
  | gpr _ => rfl
  | xzr => rfl
  | sp =>
    cases rs with
    | gpr idx =>
      simp [checkRegSPAligned, State.spAligned, State.stxrIter, State.withExclFails, State.writeReg64]
    | sp => simp [Reg.isNonZeroGpr] at hrs
    | xzr => simp [Reg.isNonZeroGpr] at hrs

private theorem State.writeReg_stxrIter_of_bne (s : State) (ef : List Bool) (rs r : Reg)
    (w : Width) (w_rs v : BitVec 64) (hne : (r != rs) = true) :
    (s.stxrIter ef rs w_rs).writeReg w r v = (s.writeReg w r v).stxrIter ef rs w_rs := by
  have hne' : rs ≠ r := (reg_ne_of_bne hne).symm
  dsimp [State.stxrIter, State.writeReg]
  rw [State.writeReg64_comm_or_same]
  simp only [hne', ↓reduceIte]
  cases s; cases r <;> rfl

private theorem execAddSubImm_stxrIter_of_bne (s : State) (ef : List Bool) (rs rd r_src : Reg)
    (w_op : Width) (op : AddSubOp) (imm12 : BitVec 12) (sh : Bool) (w_rs : BitVec 64)
    (hrd : (rd != rs) = true) (hsrc : (r_src != rs) = true) :
    execAddSubImm w_op op rd r_src imm12 sh (s.stxrIter ef rs w_rs) =
      (execAddSubImm w_op op rd r_src imm12 sh s).stxrIter ef rs w_rs := by
  dsimp [execAddSubImm]
  rw [State.readReg_stxrIter_of_bne s ef rs r_src w_op w_rs hsrc]
  rw [State.writeReg_stxrIter_of_bne s ef rs rd w_op w_rs _ hrd]
  rcases h : evalAddSub w_op op (s.readReg w_op r_src)
    (if sh = true then imm12.zeroExtend 64 <<< 12 else imm12.zeroExtend 64) none with ⟨res, optPs⟩
  cases optPs with
  | none =>
    dsimp only []
    exact State.stxrIter_advancePC _ ef rs w_rs
  | some ps =>
    dsimp only []
    rw [State.stxrIter_setPState, State.stxrIter_advancePC]

private theorem execInst_cbnz_stxrIter_one {prog : Program} (s : State) (ef : List Bool) (rs : Reg)
    (pc_cbnz offset : BitVec 64) (hrs : rs.isNonZeroGpr = true) :
    prog.evalInst (.cbz .W32 true rs offset) ((s.stxrIter ef rs 1#64).setPC pc_cbnz) =
      (s.setPC (pc_cbnz + offset)).stxrIter ef rs 1#64 := by
  cases rs with
  | gpr idx =>
    have h31 : (idx == 31#5) = false := by
      simpa [Reg.isNonZeroGpr, bne_iff_ne, beq_eq_false_iff_ne] using hrs
    have hread : (((s.stxrIter ef (.gpr idx) 1#64).setPC pc_cbnz).readReg .W32 (.gpr idx)) = 1#64 := by
      simp [State.readReg, State.readReg32, State.setPC, State.stxrIter, State.withExclFails,
        State.writeReg64, State.readReg64, RegFile.read, RegFile.write, h31]
    simp only [Program.evalInst, execInstWithSvc, hread]
    rfl
  | sp => simp [Reg.isNonZeroGpr] at hrs
  | xzr => simp [Reg.isNonZeroGpr] at hrs

private theorem execInst_ldxr_stxrIter {prog : Program} (s : State) (ef : List Bool) (sz : MemWidth) (acq : Bool)
    (rs rn rt_ld : Reg) (pc_ld ea : BitVec 64) (hrs : rs.isNonZeroGpr = true)
    (hrn : (rn != rs) = true) (hrt_ld : (rt_ld != rs) = true)
    (hsp : checkRegSPAligned s rn = true) (haddr : s.readReg64 rn = ea)
    (halign : sz.isAligned ea = true) (hcan : s.mem.canRead ea sz.bytes = true) :
    prog.evalInst (.ldxr sz acq rn rt_ld) ((s.setPC pc_ld).stxrIter ef rs 1#64) =
      (((s.writeReg (match sz with | .X64 => .W64 | _ => .W32) rt_ld (s.mem.readSized sz false ea)).setPC
        (pc_ld + 4#64)).stxrIter ef rs 1#64) := by
  have hsp' : checkRegSPAligned ((s.setPC pc_ld).stxrIter ef rs 1#64) rn = true := by
    rw [checkRegSPAligned_stxrIter_of_bne _ ef rs rn 1#64 hrn hrs]
    exact hsp
  have haddr' : ((s.setPC pc_ld).stxrIter ef rs 1#64).readReg64 rn = ea := by
    rw [State.readReg64_stxrIter_of_bne _ ef rs rn 1#64 hrn]
    exact haddr
  have hmem' : ((s.setPC pc_ld).stxrIter ef rs 1#64).mem = s.mem := rfl
  simp only [Program.evalInst, execInstWithSvc, hsp', haddr', halign, hmem', hcan,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases sz <;> {
    dsimp only []
    rw [State.writeReg_stxrIter_of_bne _ ef rs rt_ld _ 1#64 _ hrt_ld]
    rw [State.stxrIter_advancePC]
    cases s; cases rt_ld <;> rfl
  }

private theorem reaches_pc_stxr_retry_aux {prog : Program} {target_pc : BitVec 64}
    {s : State} {Q : State → Prop} {Qoom : State → Prop}
    {pc pc_cbnz offset ea : BitVec 64} {sz : MemWidth} {rel : Bool} {rs rn rt : Reg}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stxr sz rel rs rn rt))
    (hpc_cbnz : pc + 4#64 = pc_cbnz)
    (hfetch_cbnz : prog.fetch pc_cbnz = some (.cbz .W32 true rs offset))
    (hrs : rs.isNonZeroGpr = true)
    (hrn : (rn != rs) = true)
    (hrt : (rt != rs) = true)
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : sz.isAligned ea = true)
    (hcan : s.mem.canWrite ea sz.bytes = true)
    (hbody : ∀ (bs : List Bool),
      reaches_pc prog target_pc (s.stxrIter bs rs 1#64) Q Qoom →
      reaches_pc prog target_pc ((s.setPC (pc_cbnz + offset)).stxrIter bs rs 1#64) Q Qoom)
    (ef : List Bool) (w_rs : BitVec 64)
    (hsucc : reaches_pc prog target_pc
      (((s.withExclFails (ef.dropWhile (· == true)).tail).writeReg .W32 rs 0#64).setPC (pc + 4#64)
        |>.setMem (s.mem.writeSized sz ea (s.readReg64 rt))) Q Qoom) :
    reaches_pc prog target_pc (s.stxrIter ef rs w_rs) Q Qoom := by
  induction ef generalizing w_rs with
  | nil =>
    have hrun' : (s.stxrIter [] rs w_rs).status = .Running := hrun
    have hpc' : (s.stxrIter [] rs w_rs).pc = pc := hpc
    have hfetch' : prog.fetch (s.stxrIter [] rs w_rs).pc = some (.stxr sz rel rs rn rt) :=
      hpc'.symm ▸ hfetch
    have hsp' : checkRegSPAligned (s.stxrIter [] rs w_rs) rn = true := by
      rw [checkRegSPAligned_stxrIter_of_bne s [] rs rn w_rs hrn hrs]; exact hsp
    have haddr' : (s.stxrIter [] rs w_rs).readReg64 rn = ea := by
      rw [State.readReg64_stxrIter_of_bne s [] rs rn w_rs hrn]; exact haddr
    have hrt' : (s.stxrIter [] rs w_rs).readReg64 rt = s.readReg64 rt :=
      State.readReg64_stxrIter_of_bne s [] rs rt w_rs hrt
    have hcan' : (s.stxrIter [] rs w_rs).mem.canWrite ea sz.bytes = true := hcan
    have hfail' : (s.stxrIter [] rs w_rs).exclWillFail = false := rfl
    apply reaches_pc_step hrun' hfetch'
    have hstep : prog.evalInst (.stxr sz rel rs rn rt) (s.stxrIter [] rs w_rs) =
        (((s.withExclFails []).writeReg .W32 rs 0#64).setPC (pc + 4#64)
          |>.setMem (s.mem.writeSized sz ea (s.readReg64 rt))) := by
      simp only [Program.evalInst, execInstWithSvc, hsp', haddr', halign, hcan', hfail', hrt',
        Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hmem : (s.stxrIter [] rs w_rs).mem = s.mem := rfl
      have hstep_o : (s.stxrIter [] rs w_rs).stepExclOracle = s.stxrIter [] rs w_rs := by
        cases s; cases rs <;> rfl
      rw [hmem, hstep_o]
      dsimp [State.stxrIter, State.writeReg]
      rw [State.writeReg64_setMem, State.writeReg64_writeReg64_same]
      cases s; cases rs <;> simp [State.withExclFails, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
    rw [hstep]
    exact hsucc
  | cons b bs ih =>
    cases b with
    | false =>
      have hrun' : (s.stxrIter (false :: bs) rs w_rs).status = .Running := hrun
      have hpc' : (s.stxrIter (false :: bs) rs w_rs).pc = pc := hpc
      have hfetch' : prog.fetch (s.stxrIter (false :: bs) rs w_rs).pc = some (.stxr sz rel rs rn rt) :=
        hpc'.symm ▸ hfetch
      have hsp' : checkRegSPAligned (s.stxrIter (false :: bs) rs w_rs) rn = true := by
        rw [checkRegSPAligned_stxrIter_of_bne s (false :: bs) rs rn w_rs hrn hrs]; exact hsp
      have haddr' : (s.stxrIter (false :: bs) rs w_rs).readReg64 rn = ea := by
        rw [State.readReg64_stxrIter_of_bne s (false :: bs) rs rn w_rs hrn]; exact haddr
      have hrt' : (s.stxrIter (false :: bs) rs w_rs).readReg64 rt = s.readReg64 rt :=
        State.readReg64_stxrIter_of_bne s (false :: bs) rs rt w_rs hrt
      have hcan' : (s.stxrIter (false :: bs) rs w_rs).mem.canWrite ea sz.bytes = true := hcan
      have hfail' : (s.stxrIter (false :: bs) rs w_rs).exclWillFail = false := rfl
      apply reaches_pc_step hrun' hfetch'
      have hstep : prog.evalInst (.stxr sz rel rs rn rt) (s.stxrIter (false :: bs) rs w_rs) =
          (((s.withExclFails bs).writeReg .W32 rs 0#64).setPC (pc + 4#64)
            |>.setMem (s.mem.writeSized sz ea (s.readReg64 rt))) := by
        simp only [Program.evalInst, execInstWithSvc, hsp', haddr', halign, hcan', hfail', hrt',
          Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        have hmem : (s.stxrIter (false :: bs) rs w_rs).mem = s.mem := rfl
        have hstep_o : (s.stxrIter (false :: bs) rs w_rs).stepExclOracle = s.stxrIter bs rs w_rs := by
          cases s; cases rs <;> rfl
        rw [hmem, hstep_o]
        dsimp [State.stxrIter, State.writeReg]
        rw [State.writeReg64_setMem, State.writeReg64_writeReg64_same]
        cases s; cases rs <;> simp [State.withExclFails, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
      rw [hstep]
      simpa [List.dropWhile] using hsucc
    | true =>
      have hrun' : (s.stxrIter (true :: bs) rs w_rs).status = .Running := hrun
      have hpc' : (s.stxrIter (true :: bs) rs w_rs).pc = pc := hpc
      have hfetch' : prog.fetch (s.stxrIter (true :: bs) rs w_rs).pc = some (.stxr sz rel rs rn rt) :=
        hpc'.symm ▸ hfetch
      have hsp' : checkRegSPAligned (s.stxrIter (true :: bs) rs w_rs) rn = true := by
        rw [checkRegSPAligned_stxrIter_of_bne s (true :: bs) rs rn w_rs hrn hrs]; exact hsp
      have haddr' : (s.stxrIter (true :: bs) rs w_rs).readReg64 rn = ea := by
        rw [State.readReg64_stxrIter_of_bne s (true :: bs) rs rn w_rs hrn]; exact haddr
      have hcan' : (s.stxrIter (true :: bs) rs w_rs).mem.canWrite ea sz.bytes = true := hcan
      have hfail' : (s.stxrIter (true :: bs) rs w_rs).exclWillFail = true := rfl
      apply reaches_pc_step hrun' hfetch'
      have hstep : prog.evalInst (.stxr sz rel rs rn rt) (s.stxrIter (true :: bs) rs w_rs) =
          (s.stxrIter bs rs 1#64).setPC pc_cbnz := by
        simp only [Program.evalInst, execInstWithSvc, hsp', haddr', halign, hcan', hfail',
          Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        have hstep_o : (s.stxrIter (true :: bs) rs w_rs).stepExclOracle = s.stxrIter bs rs w_rs := by
          cases s; cases rs <;> rfl
        rw [hstep_o]
        dsimp [State.stxrIter, State.writeReg]
        rw [State.writeReg64_writeReg64_same]
        subst hpc_cbnz
        cases s; cases rs <;> simp [State.withExclFails, State.writeReg64, State.advancePC, State.setPC, hpc]
      rw [hstep]
      have hrun_cbnz : ((s.stxrIter bs rs 1#64).setPC pc_cbnz).status = .Running := hrun
      have hfetch_cbnz' : prog.fetch ((s.stxrIter bs rs 1#64).setPC pc_cbnz).pc =
          some (.cbz .W32 true rs offset) := hfetch_cbnz
      apply reaches_pc_step hrun_cbnz hfetch_cbnz'
      rw [execInst_cbnz_stxrIter_one s bs rs pc_cbnz offset hrs]
      apply hbody bs
      exact ih 1#64 (by simpa [List.dropWhile] using hsucc)

/-- 64-bit store-exclusive (`STXR Ws, Xt, [Xn]` / `STLXR Ws, Xt, [Xn]`) in a 3-instruction
    LL/SC retry loop (`pc_ld: ldxr/ldaxr Xt_ld, [Xn]; pc: stxr/stlxr Ws, Xt, [Xn]; pc_cbnz: cbnz Ws, pc_ld`):
    consumes any finite prefix of spurious failures via `s.stepExclLoop`, updates `(ea ↦₆₄ _)` to
    `(ea ↦₆₄ val)` in `P` via `SepStore64`, writes `ws := 0`, and stops at `pc + 4` (`pc_cbnz`)
    so the following `wp_step` steps through `cbnz` (not taken). -/
theorem SepWP.step_stxr64_retry1 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc pc_cbnz offset pc_ld : BitVec 64} {rel acq : Bool} {rs rn rt rt_ld : Reg}
    {ea v_ld val : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stxr .X64 rel rs rn rt))
    (hpc_cbnz : pc + 4#64 = pc_cbnz)
    (hfetch_cbnz : prog.fetch pc_cbnz = some (.cbz .W32 true rs offset))
    (hpc_ld : pc_cbnz + offset = pc_ld)
    (hfetch_ld : prog.fetch pc_ld = some (.ldxr .X64 acq rn rt_ld))
    (hregs : (rs.isNonZeroGpr && (rn != rs) && (rt != rs) && (rt_ld != rs)) = true)
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .X64 ea = true)
    (hload : SepLoad64 ea P v_ld)
    (hrestore : (s.writeReg .W64 rt_ld v_ld).setPC (pc_ld + 4#64) = s)
    (hval : s.readReg64 rt = val)
    (hstore : SepStore64 ea val P P')
    (hexec : (s.stepExclLoop.writeReg .W32 rs 0#64).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have h1 : (rs.isNonZeroGpr && (rn != rs) && (rt != rs)) = true ∧ (rt_ld != rs) = true :=
    Bool.and_eq_true_iff.mp hregs
  have h2 : (rs.isNonZeroGpr && (rn != rs)) = true ∧ (rt != rs) = true :=
    Bool.and_eq_true_iff.mp h1.1
  have h3 : rs.isNonZeroGpr = true ∧ (rn != rs) = true :=
    Bool.and_eq_true_iff.mp h2.1
  have hrs := h3.1
  have hrn := h3.2
  have hrt := h2.2
  have hrt_ld := h1.2
  have hread : s.mem.readSized .X64 false ea = v_ld := by
    simpa [Memory.readSized] using hload.load hm
  have hcan_r : s.mem.canRead ea (MemWidth.bytes .X64) = true := hload.readable hm
  have hcan_w : s.mem.canWrite ea (MemWidth.bytes .X64) = true := hstore.writable hm
  let m' := s.mem.write64 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  rw [← State.stxrIter_self s rs]
  apply reaches_pc_stxr_retry_aux hpc hrun hfetch hpc_cbnz hfetch_cbnz hrs hrn hrt hsp haddr halign hcan_w
  · intro bs hcont
    rw [hpc_ld]
    have hrun_ld : ((s.setPC pc_ld).stxrIter bs rs 1#64).status = .Running := hrun
    have hfetch_ld' : prog.fetch ((s.setPC pc_ld).stxrIter bs rs 1#64).pc =
        some (.ldxr .X64 acq rn rt_ld) := hfetch_ld
    apply reaches_pc_step hrun_ld hfetch_ld'
    rw [execInst_ldxr_stxrIter s bs .X64 acq rs rn rt_ld pc_ld ea hrs hrn hrt_ld hsp haddr halign hcan_r]
    rw [hread]
    dsimp only []
    rw [hrestore]
    exact hcont
  · have hsucc_eq :
        (((s.withExclFails (s.exclFails.dropWhile (· == true)).tail).writeReg .W32 rs 0#64).setPC
          (pc + 4#64) |>.setMem (s.mem.writeSized .X64 ea (s.readReg64 rt))) = s'.setMem m' := by
      rw [← hexec, hval]
      rfl
    rw [hsucc_eq]
    exact hnext m' R hm'

/-- 32-bit store-exclusive (`STXR Ws, Wt, [Xn]` / `STLXR Ws, Wt, [Xn]`) in a 3-instruction
    LL/SC retry loop (`pc_ld: ldxr/ldaxr Wt_ld, [Xn]; pc: stxr/stlxr Ws, Wt, [Xn]; pc_cbnz: cbnz Ws, pc_ld`). -/
theorem SepWP.step_stxr32_retry1 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc pc_cbnz offset pc_ld : BitVec 64} {rel acq : Bool} {rs rn rt rt_ld : Reg}
    {ea : BitVec 64} {v_ld val : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stxr .W32 rel rs rn rt))
    (hpc_cbnz : pc + 4#64 = pc_cbnz)
    (hfetch_cbnz : prog.fetch pc_cbnz = some (.cbz .W32 true rs offset))
    (hpc_ld : pc_cbnz + offset = pc_ld)
    (hfetch_ld : prog.fetch pc_ld = some (.ldxr .W32 acq rn rt_ld))
    (hregs : (rs.isNonZeroGpr && (rn != rs) && (rt != rs) && (rt_ld != rs)) = true)
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .W32 ea = true)
    (hload : SepLoad32 ea P v_ld)
    (hrestore : (s.writeReg .W32 rt_ld (v_ld.zeroExtend 64)).setPC (pc_ld + 4#64) = s)
    (hval : s.readReg32 rt = val)
    (hstore : SepStore32 ea val P P')
    (hexec : (s.stepExclLoop.writeReg .W32 rs 0#64).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have h1 : (rs.isNonZeroGpr && (rn != rs) && (rt != rs)) = true ∧ (rt_ld != rs) = true :=
    Bool.and_eq_true_iff.mp hregs
  have h2 : (rs.isNonZeroGpr && (rn != rs)) = true ∧ (rt != rs) = true :=
    Bool.and_eq_true_iff.mp h1.1
  have h3 : rs.isNonZeroGpr = true ∧ (rn != rs) = true :=
    Bool.and_eq_true_iff.mp h2.1
  have hrs := h3.1
  have hrn := h3.2
  have hrt := h2.2
  have hrt_ld := h1.2
  have hread : s.mem.readSized .W32 false ea = v_ld.zeroExtend 64 := by
    dsimp [Memory.readSized]
    rw [hload.load hm]
  have hcan_r : s.mem.canRead ea (MemWidth.bytes .W32) = true := hload.readable hm
  have hcan_w : s.mem.canWrite ea (MemWidth.bytes .W32) = true := hstore.writable hm
  have htrunc : BitVec.setWidth 32 (s.readReg64 rt) = val := hval
  let m' := s.mem.write32 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  rw [← State.stxrIter_self s rs]
  apply reaches_pc_stxr_retry_aux hpc hrun hfetch hpc_cbnz hfetch_cbnz hrs hrn hrt hsp haddr halign hcan_w
  · intro bs hcont
    rw [hpc_ld]
    have hrun_ld : ((s.setPC pc_ld).stxrIter bs rs 1#64).status = .Running := hrun
    have hfetch_ld' : prog.fetch ((s.setPC pc_ld).stxrIter bs rs 1#64).pc =
        some (.ldxr .W32 acq rn rt_ld) := hfetch_ld
    apply reaches_pc_step hrun_ld hfetch_ld'
    rw [execInst_ldxr_stxrIter s bs .W32 acq rs rn rt_ld pc_ld ea hrs hrn hrt_ld hsp haddr halign hcan_r]
    rw [hread]
    dsimp only []
    rw [hrestore]
    exact hcont
  · have hsucc_eq :
        (((s.withExclFails (s.exclFails.dropWhile (· == true)).tail).writeReg .W32 rs 0#64).setPC
          (pc + 4#64) |>.setMem (s.mem.writeSized .W32 ea (s.readReg64 rt))) = s'.setMem m' := by
      rw [← hexec]
      dsimp [Memory.writeSized]
      rw [htrunc]
      rfl
    rw [hsucc_eq]
    exact hnext m' R hm'

/-- 64-bit store-exclusive (`STXR Ws, Xt, [Xn]` / `STLXR Ws, Xt, [Xn]`) in a 4-instruction
    LL/SC retry loop (`pc_ld: ldxr/ldaxr Xt_ld, [Xn]; pc_op: addSubImm ...; pc: stxr/stlxr Ws, Xt, [Xn]; pc_cbnz: cbnz Ws, pc_ld`). -/
theorem SepWP.step_stxr64_retry2 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc pc_cbnz offset pc_ld pc_op : BitVec 64} {rel acq sh : Bool}
    {rs rn rt rt_ld rd r_src : Reg} {w_op : Width} {op : AddSubOp} {imm12 : BitVec 12}
    {ea v_ld val : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stxr .X64 rel rs rn rt))
    (hpc_cbnz : pc + 4#64 = pc_cbnz)
    (hfetch_cbnz : prog.fetch pc_cbnz = some (.cbz .W32 true rs offset))
    (hpc_ld : pc_cbnz + offset = pc_ld)
    (hfetch_ld : prog.fetch pc_ld = some (.ldxr .X64 acq rn rt_ld))
    (hpc_op : pc_ld + 4#64 = pc_op)
    (hfetch_op : prog.fetch pc_op = some (.addSubImm w_op op rd r_src imm12 sh))
    (hregs : (rs.isNonZeroGpr && (rn != rs) && (rt != rs) && (rt_ld != rs) && (rd != rs) && (r_src != rs)) = true)
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .X64 ea = true)
    (hload : SepLoad64 ea P v_ld)
    (hrestore : execAddSubImm w_op op rd r_src imm12 sh ((s.writeReg .W64 rt_ld v_ld).setPC pc_op) = s)
    (hval : s.readReg64 rt = val)
    (hstore : SepStore64 ea val P P')
    (hexec : (s.stepExclLoop.writeReg .W32 rs 0#64).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have h1 : (rs.isNonZeroGpr && (rn != rs) && (rt != rs) && (rt_ld != rs) && (rd != rs)) = true ∧ (r_src != rs) = true :=
    Bool.and_eq_true_iff.mp hregs
  have h2 : (rs.isNonZeroGpr && (rn != rs) && (rt != rs) && (rt_ld != rs)) = true ∧ (rd != rs) = true :=
    Bool.and_eq_true_iff.mp h1.1
  have h3 : (rs.isNonZeroGpr && (rn != rs) && (rt != rs)) = true ∧ (rt_ld != rs) = true :=
    Bool.and_eq_true_iff.mp h2.1
  have h4 : (rs.isNonZeroGpr && (rn != rs)) = true ∧ (rt != rs) = true :=
    Bool.and_eq_true_iff.mp h3.1
  have h5 : rs.isNonZeroGpr = true ∧ (rn != rs) = true :=
    Bool.and_eq_true_iff.mp h4.1
  have hrs := h5.1
  have hrn := h5.2
  have hrt := h4.2
  have hrt_ld := h3.2
  have hrd := h2.2
  have hsrc := h1.2
  have hread : s.mem.readSized .X64 false ea = v_ld := by
    simpa [Memory.readSized] using hload.load hm
  have hcan_r : s.mem.canRead ea (MemWidth.bytes .X64) = true := hload.readable hm
  have hcan_w : s.mem.canWrite ea (MemWidth.bytes .X64) = true := hstore.writable hm
  let m' := s.mem.write64 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  rw [← State.stxrIter_self s rs]
  apply reaches_pc_stxr_retry_aux hpc hrun hfetch hpc_cbnz hfetch_cbnz hrs hrn hrt hsp haddr halign hcan_w
  · intro bs hcont
    rw [hpc_ld]
    have hrun_ld : ((s.setPC pc_ld).stxrIter bs rs 1#64).status = .Running := hrun
    have hfetch_ld' : prog.fetch ((s.setPC pc_ld).stxrIter bs rs 1#64).pc =
        some (.ldxr .X64 acq rn rt_ld) := hfetch_ld
    apply reaches_pc_step hrun_ld hfetch_ld'
    rw [execInst_ldxr_stxrIter s bs .X64 acq rs rn rt_ld pc_ld ea hrs hrn hrt_ld hsp haddr halign hcan_r]
    rw [hread, hpc_op]
    dsimp only []
    have hrun_op : (((s.writeReg .W64 rt_ld v_ld).setPC pc_op).stxrIter bs rs 1#64).status = .Running := hrun
    have hfetch_op' : prog.fetch (((s.writeReg .W64 rt_ld v_ld).setPC pc_op).stxrIter bs rs 1#64).pc =
        some (.addSubImm w_op op rd r_src imm12 sh) := hfetch_op
    apply reaches_pc_step hrun_op hfetch_op'
    dsimp only [Program.evalInst, execInstWithSvc]
    rw [execAddSubImm_stxrIter_of_bne _ bs rs rd r_src w_op op imm12 sh 1#64 hrd hsrc]
    rw [hrestore]
    exact hcont
  · have hsucc_eq :
        (((s.withExclFails (s.exclFails.dropWhile (· == true)).tail).writeReg .W32 rs 0#64).setPC
          (pc + 4#64) |>.setMem (s.mem.writeSized .X64 ea (s.readReg64 rt))) = s'.setMem m' := by
      rw [← hexec, hval]
      rfl
    rw [hsucc_eq]
    exact hnext m' R hm'

/-- 32-bit store-exclusive (`STXR Ws, Wt, [Xn]` / `STLXR Ws, Wt, [Xn]`) in a 4-instruction
    LL/SC retry loop (`pc_ld: ldxr/ldaxr Wt_ld, [Xn]; pc_op: addSubImm ...; pc: stxr/stlxr Ws, Wt, [Xn]; pc_cbnz: cbnz Ws, pc_ld`). -/
theorem SepWP.step_stxr32_retry2 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc pc_cbnz offset pc_ld pc_op : BitVec 64} {rel acq sh : Bool}
    {rs rn rt rt_ld rd r_src : Reg} {w_op : Width} {op : AddSubOp} {imm12 : BitVec 12}
    {ea : BitVec 64} {v_ld val : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stxr .W32 rel rs rn rt))
    (hpc_cbnz : pc + 4#64 = pc_cbnz)
    (hfetch_cbnz : prog.fetch pc_cbnz = some (.cbz .W32 true rs offset))
    (hpc_ld : pc_cbnz + offset = pc_ld)
    (hfetch_ld : prog.fetch pc_ld = some (.ldxr .W32 acq rn rt_ld))
    (hpc_op : pc_ld + 4#64 = pc_op)
    (hfetch_op : prog.fetch pc_op = some (.addSubImm w_op op rd r_src imm12 sh))
    (hregs : (rs.isNonZeroGpr && (rn != rs) && (rt != rs) && (rt_ld != rs) && (rd != rs) && (r_src != rs)) = true)
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .W32 ea = true)
    (hload : SepLoad32 ea P v_ld)
    (hrestore : execAddSubImm w_op op rd r_src imm12 sh ((s.writeReg .W32 rt_ld (v_ld.zeroExtend 64)).setPC pc_op) = s)
    (hval : s.readReg32 rt = val)
    (hstore : SepStore32 ea val P P')
    (hexec : (s.stepExclLoop.writeReg .W32 rs 0#64).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have h1 : (rs.isNonZeroGpr && (rn != rs) && (rt != rs) && (rt_ld != rs) && (rd != rs)) = true ∧ (r_src != rs) = true :=
    Bool.and_eq_true_iff.mp hregs
  have h2 : (rs.isNonZeroGpr && (rn != rs) && (rt != rs) && (rt_ld != rs)) = true ∧ (rd != rs) = true :=
    Bool.and_eq_true_iff.mp h1.1
  have h3 : (rs.isNonZeroGpr && (rn != rs) && (rt != rs)) = true ∧ (rt_ld != rs) = true :=
    Bool.and_eq_true_iff.mp h2.1
  have h4 : (rs.isNonZeroGpr && (rn != rs)) = true ∧ (rt != rs) = true :=
    Bool.and_eq_true_iff.mp h3.1
  have h5 : rs.isNonZeroGpr = true ∧ (rn != rs) = true :=
    Bool.and_eq_true_iff.mp h4.1
  have hrs := h5.1
  have hrn := h5.2
  have hrt := h4.2
  have hrt_ld := h3.2
  have hrd := h2.2
  have hsrc := h1.2
  have hread : s.mem.readSized .W32 false ea = v_ld.zeroExtend 64 := by
    dsimp [Memory.readSized]
    rw [hload.load hm]
  have hcan_r : s.mem.canRead ea (MemWidth.bytes .W32) = true := hload.readable hm
  have hcan_w : s.mem.canWrite ea (MemWidth.bytes .W32) = true := hstore.writable hm
  have htrunc : BitVec.setWidth 32 (s.readReg64 rt) = val := hval
  let m' := s.mem.write32 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  rw [← State.stxrIter_self s rs]
  apply reaches_pc_stxr_retry_aux hpc hrun hfetch hpc_cbnz hfetch_cbnz hrs hrn hrt hsp haddr halign hcan_w
  · intro bs hcont
    rw [hpc_ld]
    have hrun_ld : ((s.setPC pc_ld).stxrIter bs rs 1#64).status = .Running := hrun
    have hfetch_ld' : prog.fetch ((s.setPC pc_ld).stxrIter bs rs 1#64).pc =
        some (.ldxr .W32 acq rn rt_ld) := hfetch_ld
    apply reaches_pc_step hrun_ld hfetch_ld'
    rw [execInst_ldxr_stxrIter s bs .W32 acq rs rn rt_ld pc_ld ea hrs hrn hrt_ld hsp haddr halign hcan_r]
    rw [hread, hpc_op]
    dsimp only []
    have hrun_op : (((s.writeReg .W32 rt_ld (v_ld.zeroExtend 64)).setPC pc_op).stxrIter bs rs 1#64).status = .Running := hrun
    have hfetch_op' : prog.fetch (((s.writeReg .W32 rt_ld (v_ld.zeroExtend 64)).setPC pc_op).stxrIter bs rs 1#64).pc =
        some (.addSubImm w_op op rd r_src imm12 sh) := hfetch_op
    apply reaches_pc_step hrun_op hfetch_op'
    dsimp only [Program.evalInst, execInstWithSvc]
    rw [execAddSubImm_stxrIter_of_bne _ bs rs rd r_src w_op op imm12 sh 1#64 hrd hsrc]
    rw [hrestore]
    exact hcont
  · have hsucc_eq :
        (((s.withExclFails (s.exclFails.dropWhile (· == true)).tail).writeReg .W32 rs 0#64).setPC
          (pc + 4#64) |>.setMem (s.mem.writeSized .W32 ea (s.readReg64 rt))) = s'.setMem m' := by
      rw [← hexec]
      dsimp [Memory.writeSized]
      rw [htrunc]
      rfl
    rw [hsucc_eq]
    exact hnext m' R hm'

theorem Memory.canRead_1_of_8 {m : Memory} {ea : BitVec 64} (h : m.canRead ea 8 = true) :
    m.canRead ea 1 = true := by
  simp only [Memory.canRead, Bool.and_eq_true] at h ⊢
  have h8p : m.allPerm (·.r) ea (1 + 7) = true := h.1
  have h8l : m.allNoLazyFree ea (1 + 7) = true := h.2
  rw [Memory.allPerm_add, Bool.and_eq_true] at h8p
  rw [Memory.allNoLazyFree_add, Bool.and_eq_true] at h8l
  exact ⟨h8p.1, h8l.1⟩

theorem Memory.canWrite_1_of_8 {m : Memory} {ea : BitVec 64} (h : m.canWrite ea 8 = true) :
    m.canWrite ea 1 = true := by
  have h8 : m.allPerm (fun p => p.w && !p.x) ea (1 + 7) = true := h
  rw [Memory.allPerm_add, Bool.and_eq_true] at h8
  exact h8.1

theorem Memory.read8_eq_truncate_read64 (m : Memory) (ea : BitVec 64) :
    m.read8 ea = (m.read64 ea).truncate 8 := by
  have h0 : ea + 0#64 = ea := by bv_decide
  unfold Memory.read64
  rw [h0]
  bv_decide

theorem Memory.read8_write8_eq_read8_write64_lo (m : Memory) (ea a : BitVec 64)
    (val8 : BitVec 8) (old64 new64 : BitVec 64)
    (hold : m.read64 ea = old64)
    (hnew : (old64 &&& 0xffffffffffffff00#64) ||| val8.zeroExtend 64 = new64) :
    (m.write8 ea val8).read8 a = (m.write64 ea new64).read8 a := by
  subst hold hnew
  rw [Memory.read8_write8, Memory.read8_write64]
  have hb0 : (((m.read64 ea &&& 0xffffffffffffff00#64) ||| val8.zeroExtend 64).extractLsb' 0 8) =
      val8 := by bv_bits
  have hb1 : (((m.read64 ea &&& 0xffffffffffffff00#64) ||| val8.zeroExtend 64).extractLsb' 8 8) =
      m.read8 (ea + 1#64) := by unfold Memory.read64; bv_bits
  have hb2 : (((m.read64 ea &&& 0xffffffffffffff00#64) ||| val8.zeroExtend 64).extractLsb' 16 8) =
      m.read8 (ea + 2#64) := by unfold Memory.read64; bv_bits
  have hb3 : (((m.read64 ea &&& 0xffffffffffffff00#64) ||| val8.zeroExtend 64).extractLsb' 24 8) =
      m.read8 (ea + 3#64) := by unfold Memory.read64; bv_bits
  have hb4 : (((m.read64 ea &&& 0xffffffffffffff00#64) ||| val8.zeroExtend 64).extractLsb' 32 8) =
      m.read8 (ea + 4#64) := by unfold Memory.read64; bv_bits
  have hb5 : (((m.read64 ea &&& 0xffffffffffffff00#64) ||| val8.zeroExtend 64).extractLsb' 40 8) =
      m.read8 (ea + 5#64) := by unfold Memory.read64; bv_bits
  have hb6 : (((m.read64 ea &&& 0xffffffffffffff00#64) ||| val8.zeroExtend 64).extractLsb' 48 8) =
      m.read8 (ea + 6#64) := by unfold Memory.read64; bv_bits
  have hb7 : (((m.read64 ea &&& 0xffffffffffffff00#64) ||| val8.zeroExtend 64).extractLsb' 56 8) =
      m.read8 (ea + 7#64) := by unfold Memory.read64; bv_bits
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
  by_cases h7 : a = ea + 7#64
  · subst h7; simp
  · by_cases h6 : a = ea + 6#64
    · subst h6; simp
    · by_cases h5 : a = ea + 5#64
      · subst h5; simp
      · by_cases h4 : a = ea + 4#64
        · subst h4; simp
        · by_cases h3 : a = ea + 3#64
          · subst h3; simp
          · by_cases h2 : a = ea + 2#64
            · subst h2; simp
            · by_cases h1 : a = ea + 1#64
              · subst h1; simp
              · simp [h7, h6, h5, h4, h3, h2, h1]

/-- 8-bit load (`LDRB Wt, [addr]`) from the low byte of a 64-bit word `(ea ↦₆₄ v)`. -/
theorem SepWP.step_ldr8_64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .B8 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad64 ea P v)
    (hexec : ((applyWriteback s wb).writeReg .W32 rt ((v.truncate 8).zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W32 .B8 false rt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read8 ea = v.truncate 8 := by
    rw [Memory.read8_eq_truncate_read64, hload.load hm]
  have hcan : s.mem.canRead ea 1 = true := Memory.canRead_1_of_8 (hload.readable hm)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr .W32 .B8 false rt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- 8-bit store (`STRB Wt, [addr]`) into the low byte of a 64-bit word `(ea ↦₆₄ old64)`. -/
theorem SepWP.step_str8_64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {old64 new64 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad64 ea P old64)
    (hval : (old64 &&& 0xffffffffffffff00#64) ||| (((s.readReg32 rt).truncate 8).zeroExtend 64) = new64)
    (hstore : SepStore64 ea new64 P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .B8 rt addr) := hpc.symm ▸ hfetch
  let val8 := (s.readReg64 rt).truncate 8
  let m' := s.mem.write8 ea val8
  have hm64 : s.mem.write64 ea new64 ⊨ P' ∗ R := hstore.store hm
  have hval' : (old64 &&& 0xffffffffffffff00#64) ||| val8.zeroExtend 64 = new64 := by
    simpa [val8, State.readReg32] using hval
  have hm' : m' ⊨ P' ∗ R := by
    refine Satisfies.congr_mem (fun a => ?_) ?_ ?_ (by simp [m']) hm64
    · exact Memory.read8_write8_eq_read8_write64_lo s.mem ea a val8 old64 new64
        (hload.load hm) hval'
    · rw [Memory.perm_write8, Memory.perm_write64]
    · have h0 : s.mem.isLazyFree ea = false := by
        have h := (noLazyFree8_of_canRead8 (hload.readable hm)).1
        simpa using h
      rw [isLazyFree_write8_eq_of_false h0, isLazyFree_write64_eq_of_canRead8 (hload.readable hm)]
  have hcan : s.mem.canWrite ea 1 = true := Memory.canWrite_1_of_8 (hstore.writable hm)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .B8 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, hcan,
      MemWidth.bytes, hpc, m', val8]
  rw [hstep]
  exact hnext m' R hm'

/-- 32-bit unscaled load (`LDUR Wt, [addr]`) from the low 32 bits of a 64-bit word `(ea ↦₆₄ v)`. -/
theorem SepWP.step_ldur32_64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .W32 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad64 ea P v)
    (hexec : ((applyWriteback s wb).writeReg .W32 rt ((v.truncate 32).zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_ldr32_64 hpc hrun hfetch hsp haddr hload hexec hnext

/-- 32-bit unscaled store (`STUR Wt, [addr]`) into the low 32 bits of a 64-bit word `(ea ↦₆₄ old64)`. -/
theorem SepWP.step_stur32_64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {old64 new64 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .W32 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad64 ea P old64)
    (hval : (old64 &&& 0xffffffff00000000#64) ||| ((s.readReg32 rt).zeroExtend 64) = new64)
    (hstore : SepStore64 ea new64 P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_str32_64 hpc hrun hfetch hsp haddr hload hval hstore hexec hnext

theorem Memory.read8_write32_pair_eq_read8_write64 (m : Memory) (ea a : BitVec 64)
    (v1 v2 : BitVec 32) (new64 : BitVec 64)
    (hnew : (((v2.zeroExtend 64) <<< 32) ||| v1.zeroExtend 64) = new64) :
    ((m.write32 ea v1).write32 (ea + 4#64) v2).read8 a = (m.write64 ea new64).read8 a := by
  subst hnew
  rw [Memory.read8_write32, Memory.read8_write32, Memory.read8_write64]
  have ha3 : ea + 4#64 + 3#64 = ea + 7#64 := by bv_bits
  have ha2 : ea + 4#64 + 2#64 = ea + 6#64 := by bv_bits
  have ha1 : ea + 4#64 + 1#64 = ea + 5#64 := by bv_bits
  rw [ha3, ha2, ha1]
  have hb0 : ((((v2.zeroExtend 64) <<< 32) ||| v1.zeroExtend 64).extractLsb' 0 8) =
      v1.extractLsb' 0 8 := by bv_bits
  have hb1 : ((((v2.zeroExtend 64) <<< 32) ||| v1.zeroExtend 64).extractLsb' 8 8) =
      v1.extractLsb' 8 8 := by bv_bits
  have hb2 : ((((v2.zeroExtend 64) <<< 32) ||| v1.zeroExtend 64).extractLsb' 16 8) =
      v1.extractLsb' 16 8 := by bv_bits
  have hb3 : ((((v2.zeroExtend 64) <<< 32) ||| v1.zeroExtend 64).extractLsb' 24 8) =
      v1.extractLsb' 24 8 := by bv_bits
  have hb4 : ((((v2.zeroExtend 64) <<< 32) ||| v1.zeroExtend 64).extractLsb' 32 8) =
      v2.extractLsb' 0 8 := by bv_bits
  have hb5 : ((((v2.zeroExtend 64) <<< 32) ||| v1.zeroExtend 64).extractLsb' 40 8) =
      v2.extractLsb' 8 8 := by bv_bits
  have hb6 : ((((v2.zeroExtend 64) <<< 32) ||| v1.zeroExtend 64).extractLsb' 48 8) =
      v2.extractLsb' 16 8 := by bv_bits
  have hb7 : ((((v2.zeroExtend 64) <<< 32) ||| v1.zeroExtend 64).extractLsb' 56 8) =
      v2.extractLsb' 24 8 := by bv_bits
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]

/-- 32-bit store pair (`STP Wt1, Wt2, [addr]`) into a single 64-bit word `(ea ↦₆₄ _)`. -/
theorem SepWP.step_stp32_64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {new64 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stp .W32 rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (((s.readReg32 rt2).zeroExtend 64) <<< 32) ||| ((s.readReg32 rt1).zeroExtend 64) = new64)
    (hstore : SepStore64 ea new64 P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.stp .W32 rt1 rt2 addr) := hpc.symm ▸ hfetch
  let v1 := (s.readReg64 rt1).truncate 32
  let v2 := (s.readReg64 rt2).truncate 32
  let m' := (s.mem.write32 ea v1).write32 (ea + 4#64) v2
  have hm64 : s.mem.write64 ea new64 ⊨ P' ∗ R := hstore.store hm
  have hm' : m' ⊨ P' ∗ R := by
    refine Satisfies.congr_mem (fun a => ?_) ?_ ?_ (by simp [m']) hm64
    · exact Memory.read8_write32_pair_eq_read8_write64 s.mem ea a v1 v2 new64 hval
    · rw [Memory.perm_write32, Memory.perm_write32, Memory.perm_write64]
    · funext a
      have ha0 : ea + 4#64 + 0#64 = ea + 4#64 := by bv_bits
      have ha1 : ea + 4#64 + 1#64 = ea + 5#64 := by bv_bits
      have ha2 : ea + 4#64 + 2#64 = ea + 6#64 := by bv_bits
      have ha3 : ea + 4#64 + 3#64 = ea + 7#64 := by bv_bits
      simp only [m', Memory.write32, Memory.write64, Memory.isLazyFree_write8, ha0, ha1, ha2, ha3]
  have hcan1 : s.mem.canWrite ea 4 = true := Memory.canWrite_4_of_8 (hstore.writable hm)
  have hcan2 : s.mem.canWrite (ea + 4#64) 4 = true := Memory.canWrite_hi4_of_8 (hstore.writable hm)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stp .W32 rt1 rt2 addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hcan1, hcan2, MemWidth.bytes, hpc, m', v1, v2]
  rw [hstep]
  exact hnext m' R hm'

/-- 32-bit store pair (`STP Wt1, Wt2, [addr]`) straddling the high 32 bits of `base1 = ea - 4`
    and the low 32 bits of `base2 = ea + 4`. -/
theorem SepWP.step_stp32_hi_lo64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt1 rt2 : Reg} {addr : AddrMode}
    {ea base1 base2 : BitVec 64} {wb : Option (Reg × BitVec 64)}
    {old1 new1 old2 new2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stp .W32 rt1 rt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hbase1 : ea - 4#64 = base1)
    (hbase2 : ea + 4#64 = base2)
    (hload1 : SepLoad64 base1 P old1)
    (hval1 : (old1 &&& 0x00000000ffffffff#64) ||| (((s.readReg32 rt1).zeroExtend 64) <<< 32) = new1)
    (hstore1 : SepStore64 base1 new1 P P1)
    (hload2 : SepLoad64 base2 P1 old2)
    (hval2 : (old2 &&& 0xffffffff00000000#64) ||| ((s.readReg32 rt2).zeroExtend 64) = new2)
    (hstore2 : SepStore64 base2 new2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.stp .W32 rt1 rt2 addr) := hpc.symm ▸ hfetch
  let v1 := (s.readReg64 rt1).truncate 32
  let v2 := (s.readReg64 rt2).truncate 32
  let m1 := s.mem.write32 ea v1
  let m2 := m1.write32 (ea + 4#64) v2
  have hm1_64 : s.mem.write64 base1 new1 ⊨ P1 ∗ R := hstore1.store hm
  have hm1 : m1 ⊨ P1 ∗ R := by
    refine Satisfies.congr_mem (fun a => ?_) ?_ ?_ (by simp [m1]) hm1_64
    · exact Memory.read8_write32_eq_read8_write64_hi s.mem base1 ea a v1 old1 new1
        hbase1 (hload1.load hm) hval1
    · rw [Memory.perm_write32, Memory.perm_write64]
    · rw [isLazyFree_write32_hi_eq_of_canRead8 hbase1 (hload1.readable hm),
        isLazyFree_write64_eq_of_canRead8 (hload1.readable hm)]
  have hm2_64 : m1.write64 base2 new2 ⊨ P2 ∗ R := hstore2.store hm1
  have hm2 : m2 ⊨ P2 ∗ R := by
    have hm2_eq : m2 = m1.write32 base2 v2 := by simp [m2, hbase2]
    rw [hm2_eq]
    refine Satisfies.congr_mem (fun a => ?_) ?_ ?_ (by simp) hm2_64
    · exact Memory.read8_write32_eq_read8_write64_lo m1 base2 a v2 old2 new2
        (hload2.load hm1) hval2
    · rw [Memory.perm_write32, Memory.perm_write64]
    · rw [isLazyFree_write32_lo_eq_of_canRead8 (hload2.readable hm1),
        isLazyFree_write64_eq_of_canRead8 (hload2.readable hm1)]
  have hea1 : ea = base1 + 4#64 := by rw [← hbase1]; bv_decide
  have hcan1 : s.mem.canWrite ea 4 = true := by
    rw [hea1]
    exact Memory.canWrite_hi4_of_8 (hstore1.writable hm)
  have hcan2 : m1.canWrite (ea + 4#64) 4 = true := by
    rw [hbase2]
    exact Memory.canWrite_4_of_8 (hstore2.writable hm1)
  rw [Memory.canWrite_congr (Memory.perm_write32 _ _ _)] at hcan2
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stp .W32 rt1 rt2 addr) s = s'.setMem m2 := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStp, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hcan1, hcan2, MemWidth.bytes, hpc, m1, m2, v1, v2]
  rw [hstep]
  exact hnext m2 R hm2

/-- 16-bit load (`LDRH Wt, [addr]`) step rule for `SepWP`: looks up `(ea ↦₁₆ v)` in `P` via `SepLoad16`. -/
theorem SepWP.step_ldr16 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 16}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .H16 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad16 ea P v)
    (hexec : ((applyWriteback s wb).writeReg .W32 rt (v.zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W32 .H16 false rt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read16 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 2 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr .W32 .H16 false rt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

abbrev SepWP.step_ldr16' := @SepWP.step_ldr16
abbrev SepWP.step_ldur16 := @SepWP.step_ldr16

/-- 16-bit signed load (`LDRSH Wt/Xt, [addr]`) step rule for `SepWP`: looks up `(ea ↦₁₆ v)` in `P` via `SepLoad16`. -/
theorem SepWP.step_ldrsh16 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {w : RegWidth} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 16}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr w .H16 true rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad16 ea P v)
    (hexec : ((applyWriteback s wb).writeReg w rt (v.signExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr w .H16 true rt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read16 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 2 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr w .H16 true rt addr) s = s' := by
    rw [← hexec]
    cases w <;> cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases w <;> cases wb <;> rfl
  apply hnext R
  rwa [hmem]

abbrev SepWP.step_ldursh16 := @SepWP.step_ldrsh16

/-- 16-bit store (`STRH Wt, [addr]`) step rule for `SepWP`: updates `(ea ↦₁₆ _)` to `(ea ↦₁₆ val)`
    in `P` via `SepStore16` and abstracts the post-store memory to a fresh variable `m'`. -/
theorem SepWP.step_str16 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 16}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .H16 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : (s.readReg32 rt).truncate 16 = val)
    (hstore : SepStore16 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .H16 rt addr) := hpc.symm ▸ hfetch
  have htrunc : (s.readReg64 rt).truncate 16 = val := by
    rw [← bitvec_truncate16_truncate32]
    exact hval
  let m' := s.mem.write16 ea val
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea _ = true := hstore.writable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .H16 rt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact hnext m' R hm'

abbrev SepWP.step_stur16 := @SepWP.step_str16

/-- 32-bit load (`LDR Wt, [addr]`) step rule for `SepWP` with explicit `P = (ea ↦₃₂ v) ∗ F`. -/
theorem SepWP.step_ldr32_eq {prog : Program} {target_pc : BitVec 64}
    {s : State} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc pc' : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 32}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .W32 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hP : P = (ea ↦₃₂ v) ∗ F)
    (hpc' : pc + 4#64 = pc')
    (hnext : SepWP prog target_pc
      (((applyWriteback s wb).writeReg .W32 rt (v.zeroExtend 64)).setPC pc') P post oom) :
    SepWP prog target_pc s P post oom := by
  subst hpc'
  intro R hm
  have hm' : s.mem ⊨ (ea ↦₃₂ v) ∗ (F ∗ R) := by rwa [hP, sepConj_assoc] at hm
  have hread : s.mem.read32 ea = v := (IsBlock.pointsTo32 ea v).read hm'
  have hcan : s.mem.canRead ea 4 = true := (IsBlock.pointsTo32 ea v).canRead (by decide) hm'
  have hfetch' : prog.fetch s.pc = some (.ldr .W32 .W32 false rt addr) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr .W32 .W32 false rt addr) s =
      (((applyWriteback s wb).writeReg .W32 rt (v.zeroExtend 64)).setPC (pc + 4#64)) := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  apply hnext R
  have hmem : (((applyWriteback s wb).writeReg .W32 rt (v.zeroExtend 64)).setPC (pc + 4#64)).mem = s.mem := by
    cases wb <;> rfl
  rwa [hmem]

/-- 32-bit store (`STR Wt, [addr]`) step rule for `SepWP` with explicit `P = (ea ↦₃₂ v) ∗ F`. -/
theorem SepWP.step_str32_eq {prog : Program} {target_pc : BitVec 64}
    {s : State} {P P' F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc pc' : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v val : BitVec 32}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .W32 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg32 rt = val)
    (hP : P = (ea ↦₃₂ v) ∗ F)
    (hP' : P' = (ea ↦₃₂ val) ∗ F)
    (hpc' : pc + 4#64 = pc')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (((applyWriteback s wb).setPC pc').setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  subst hpc'
  intro R hm
  have hm' : s.mem ⊨ (ea ↦₃₂ v) ∗ (F ∗ R) := by rwa [hP, sepConj_assoc] at hm
  have hcan : s.mem.canWrite ea 4 = true := (IsBlock.pointsTo32 ea v).canWrite (by decide) hm'
  let m' := s.mem.write32 ea val
  have hm'' : m' ⊨ P' ∗ R := by
    rw [hP', sepConj_assoc]
    exact (IsBlock.pointsTo32 ea v).write32 hm' val
  have hfetch' : prog.fetch s.pc = some (.str .W32 rt addr) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .W32 rt addr) s = (((applyWriteback s wb).setPC (pc + 4#64)).setMem m') := by
    have htrunc : (s.readReg64 rt).truncate 32 = val := hval
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hcan,
      MemWidth.bytes, hpc, m']
  rw [hstep]
  exact hnext m' R hm''

/-- 16-bit load (`LDRH Wt, [addr]`) step rule for `SepWP` with explicit `P = (ea ↦₁₆ v) ∗ F`. -/
theorem SepWP.step_ldr16_eq {prog : Program} {target_pc : BitVec 64}
    {s : State} {P F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc pc' : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 16}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .H16 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hP : P = (ea ↦₁₆ v) ∗ F)
    (hpc' : pc + 4#64 = pc')
    (hnext : SepWP prog target_pc
      (((applyWriteback s wb).writeReg .W32 rt (v.zeroExtend 64)).setPC pc') P post oom) :
    SepWP prog target_pc s P post oom := by
  subst hpc'
  intro R hm
  have hm' : s.mem ⊨ (ea ↦₁₆ v) ∗ (F ∗ R) := by rwa [hP, sepConj_assoc] at hm
  have hread : s.mem.read16 ea = v := (IsBlock.pointsTo16 ea v).read hm'
  have hcan : s.mem.canRead ea 2 = true := (IsBlock.pointsTo16 ea v).canRead (by decide) hm'
  have hfetch' : prog.fetch s.pc = some (.ldr .W32 .H16 false rt addr) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr .W32 .H16 false rt addr) s =
      (((applyWriteback s wb).writeReg .W32 rt (v.zeroExtend 64)).setPC (pc + 4#64)) := by
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  apply hnext R
  have hmem : (((applyWriteback s wb).writeReg .W32 rt (v.zeroExtend 64)).setPC (pc + 4#64)).mem = s.mem := by
    cases wb <;> rfl
  rwa [hmem]

/-- 32-bit load (`LDR Wt, [X0, #off]`) step rule using `SepFrame`. -/
theorem SepWP.step_ldr32_x0 {prog : Program} {target_pc : BitVec 64}
    {s : State} {P Frame : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc pc' : BitVec 64} {i : BitVec 5} {rt : Reg} {tif off : BitVec 64} {v : BitVec 32}
    (hrt : rt = .gpr i)
    (hpc : s.pc = pc) (hpc' : pc + 4#64 = pc') (hrun : s.status = .Running)
    (hfetch : prog.fetch pc =
      some (.ldr .W32 .W32 false rt (.Offset (.gpr 0#5) off)))
    (hx0 : s.readReg64 (.gpr 0#5) = tif)
    (hframe : SepFrame ((tif + off) ↦₃₂ v) P Frame)
    (hnext : SepWP prog target_pc
      ((s.writeReg64 (.gpr i) (v.zeroExtend 64)).setPC pc') P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_ldr32_eq (wb := none) hpc hrun hfetch (by rfl)
    (by simp [evalAddrMode, hx0])
    hframe.eq hpc' (by simpa [State.writeReg, hrt] using hnext)

/-- 16-bit load (`LDRH Wt, [X0, #off]`) step rule using `SepFrame`. -/
theorem SepWP.step_ldr16_x0 {prog : Program} {target_pc : BitVec 64}
    {s : State} {P Frame : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc pc' : BitVec 64} {i : BitVec 5} {rt : Reg} {tif off : BitVec 64} {v : BitVec 16}
    (hrt : rt = .gpr i)
    (hpc : s.pc = pc) (hpc' : pc + 4#64 = pc') (hrun : s.status = .Running)
    (hfetch : prog.fetch pc =
      some (.ldr .W32 .H16 false rt (.Offset (.gpr 0#5) off)))
    (hx0 : s.readReg64 (.gpr 0#5) = tif)
    (hframe : SepFrame ((tif + off) ↦₁₆ v) P Frame)
    (hnext : SepWP prog target_pc
      ((s.writeReg64 (.gpr i) (v.zeroExtend 64)).setPC pc') P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_ldr16_eq (wb := none) hpc hrun hfetch (by rfl)
    (by simp [evalAddrMode, hx0])
    hframe.eq hpc' (by simpa [State.writeReg, hrt] using hnext)

theorem Memory.canRead_2_of_1_1 {m : Memory} {ea : BitVec 64}
    (h0 : m.canRead ea 1 = true) (h1 : m.canRead (ea + 1#64) 1 = true) :
    m.canRead ea 2 = true := by
  simp only [Memory.canRead, Bool.and_eq_true] at h0 h1 ⊢
  constructor
  · change m.allPerm (·.r) ea (1 + 1) = true
    rw [Memory.allPerm_add, Bool.and_eq_true]
    exact ⟨h0.1, h1.1⟩
  · change m.allNoLazyFree ea (1 + 1) = true
    rw [Memory.allNoLazyFree_add, Bool.and_eq_true]
    exact ⟨h0.2, h1.2⟩


theorem Memory.canWrite_2_of_1_1 {m : Memory} {ea : BitVec 64}
    (h0 : m.canWrite ea 1 = true) (h1 : m.canWrite (ea + 1#64) 1 = true) :
    m.canWrite ea 2 = true := by
  change m.allPerm (fun p => p.w && !p.x) ea (1 + 1) = true
  rw [Memory.allPerm_add, Bool.and_eq_true]
  exact ⟨h0, h1⟩


/-- 16-bit unsigned halfword load (`LDRH Wt, [addr]`) step rule for `SepWP` over two adjacent
    byte atoms `(ea ↦₈ b0)` and `(ea + 1 ↦₈ b1)`. -/
theorem SepWP.step_ldrh_bytes {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea ea1 : BitVec 64} {wb : Option (Reg × BitVec 64)} {b0 b1 : BitVec 8}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .H16 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea1 : ea + 1#64 = ea1)
    (hload0 : SepLoad8 ea P b0)
    (hload1 : SepLoad8 ea1 P b1)
    (hexec : ((applyWriteback s wb).writeReg .W32 rt ((b1 ++ b0).zeroExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W32 .H16 false rt addr) := hpc.symm ▸ hfetch
  have hread0 : s.mem.read8 (ea + 0#64) = b0 := by
    rw [BitVec.add_zero]
    exact hload0.load hm
  have hread1 : s.mem.read8 (ea + 1#64) = b1 := by
    rw [hea1]
    exact hload1.load hm
  have hread16 : s.mem.read16 ea = b1 ++ b0 := by
    simp only [Memory.read16, hread0, hread1]
  have hcan0 : s.mem.canRead ea 1 = true := hload0.readable hm
  have hcan1 : s.mem.canRead (ea + 1#64) 1 = true := hea1 ▸ hload1.readable hm
  have hcan : s.mem.canRead ea 2 = true := Memory.canRead_2_of_1_1 hcan0 hcan1
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr .W32 .H16 false rt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread16, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]


/-- 16-bit halfword store (`STRH Wt, [addr]`) step rule for `SepWP` over two adjacent
    byte atoms `(ea ↦₈ _)` and `(ea + 1 ↦₈ _)`. -/
theorem SepWP.step_strh_bytes {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea ea1 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v0 v1 : BitVec 8}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .H16 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea1 : ea + 1#64 = ea1)
    (hv0 : (s.readReg32 rt).truncate 8 = v0)
    (hv1 : (s.readReg32 rt).extractLsb' 8 8 = v1)
    (hstore0 : SepStore8 ea v0 P P1)
    (hstore1 : SepStore8 ea1 v1 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.str .H16 rt addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write8 ea v0
  let m2 := m1.write8 ea1 v1
  have hm1 : m1 ⊨ P1 ∗ R := hstore0.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore1.store hm1
  have hcan0 : s.mem.canWrite ea 1 = true := hstore0.writable hm
  have hcan1 : m1.canWrite ea1 1 = true := hstore1.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write8 _ _ _)] at hcan1
  have hcan : s.mem.canWrite ea 2 = true := Memory.canWrite_2_of_1_1 hcan0 (hea1.symm ▸ hcan1)
  have htrunc0 : ((s.readReg64 rt).truncate 16).extractLsb' 0 8 = v0 := by
    rw [← hv0, State.readReg32]
    bv_bits
  have htrunc1 : ((s.readReg64 rt).truncate 16).extractLsb' 8 8 = v1 := by
    rw [← hv1, State.readReg32]
    bv_bits
  have hea0 : ea + 0#64 = ea := BitVec.add_zero ea
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.str .H16 rt addr) s = s'.setMem m2 := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, Memory.write16, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea0, hea1, htrunc0, htrunc1, hcan, MemWidth.bytes, hpc, m1, m2]
  rw [hstep]
  exact hnext m2 R hm2

abbrev SepWP.step_ldurh_bytes := @SepWP.step_ldrh_bytes

/-- Unscaled 16-bit signed halfword load (`LDURSH Wt|Xt, [addr]`) step rule for `SepWP` over two
    adjacent byte atoms `(ea ↦₈ b0)` and `(ea + 1 ↦₈ b1)`. -/
theorem SepWP.step_ldursh_bytes {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {w : RegWidth} {rt : Reg} {addr : AddrMode}
    {ea ea1 : BitVec 64} {wb : Option (Reg × BitVec 64)} {b0 b1 : BitVec 8}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr w .H16 true rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea1 : ea + 1#64 = ea1)
    (hload0 : SepLoad8 ea P b0)
    (hload1 : SepLoad8 ea1 P b1)
    (hexec : ((applyWriteback s wb).writeReg w rt ((b1 ++ b0).signExtend 64)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr w .H16 true rt addr) := hpc.symm ▸ hfetch
  have hread0 : s.mem.read8 (ea + 0#64) = b0 := by
    rw [BitVec.add_zero]
    exact hload0.load hm
  have hread1 : s.mem.read8 (ea + 1#64) = b1 := by
    rw [hea1]
    exact hload1.load hm
  have hread16 : s.mem.read16 ea = b1 ++ b0 := by
    simp only [Memory.read16, hread0, hread1]
  have hcan0 : s.mem.canRead ea 1 = true := hload0.readable hm
  have hcan1 : s.mem.canRead (ea + 1#64) 1 = true := hea1 ▸ hload1.readable hm
  have hcan : s.mem.canRead ea 2 = true := Memory.canRead_2_of_1_1 hcan0 hcan1
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldr w .H16 true rt addr) s = s' := by
    rw [← hexec]
    cases w <;> cases wb <;> simp [Program.evalInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread16, hcan, MemWidth.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases w <;> cases wb <;> rfl
  apply hnext R
  rwa [hmem]

abbrev SepWP.step_sturh_bytes := @SepWP.step_strh_bytes


/-- Every byte in a read-only region `memRO m base n` (`n ≤ 2^64`) is readable (`m.canRead base n = true`). -/
theorem canRead_of_memRO {m : Memory} {base : BitVec 64} {n : Nat}
    (hro : memRO m base n) (hn : n ≤ 2 ^ 64) :
    m.canRead base n = true := by
  simp only [Memory.canRead, Bool.and_eq_true, Memory.allPerm_iff, Memory.allNoLazyFree_iff]
  have hin : ∀ j, j < n → InRegion base n (base + BitVec.ofNat 64 j) := by
    intro j hj
    unfold InRegion
    have heq : (base + BitVec.ofNat 64 j) - base = BitVec.ofNat 64 j := by bv_omega
    rw [heq, BitVec.toNat_ofNat]
    omega
  refine ⟨fun j hj => ?_, fun j hj => (hro _ (hin j hj)).2⟩
  rw [(hro _ (hin j hj)).1]
  rfl

theorem _root_.Arm64.Memory.canRead_of_memRO {m : Memory} {base : BitVec 64} {n : Nat}
    (hro : memRO m base n) (hn : n ≤ 2 ^ 64) :
    m.canRead base n = true :=
  ProofLib.canRead_of_memRO hro hn




end ProofLib
