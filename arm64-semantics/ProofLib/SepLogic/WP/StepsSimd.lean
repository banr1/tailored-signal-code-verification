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
public import ProofLib.SepLogic.ByteRegion
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
# Unscaled 64-Bit, SIMD, and `DC ZVA` `SepWP` Load/Store Steps

`SepWP` step lemmas for unscaled 64-bit loads/stores (`SepWP.step_ldur64`, `SepWP.step_stur64`),
32/64/128-bit SIMD scalar and pair loads/stores, and 64-byte cache-line zeroing (`SepWP.step_dcZva`,
`SepWP.step_dcZva_bytes`).
-/

@[expose] public section

namespace ProofLib

open Arm64

/-- 64-bit unscaled load (`LDUR Xd, [addr]`) step rule for `SepWP` via `SepLoad64`. -/
theorem SepWP.step_ldur64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W64 .X64 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad64 ea P v)
    (hexec : ((applyWriteback s wb).writeReg64 rt v).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_ldr64 hpc hrun hfetch hsp haddr hload hexec hnext

/-- 64-bit unscaled store (`STUR Xt, [addr]`) step rule for `SepWP` via `SepStore64`, abstracting
    the post-store memory to a fresh variable `m'`. -/
theorem SepWP.step_stur64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {val : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.str .X64 rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hval : s.readReg64 rt = val)
    (hstore : SepStore64 ea val P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom :=
  SepWP.step_str64 hpc hrun hfetch hsp haddr hval hstore hexec hnext

/-- 128-bit SIMD load (`LDR Qt, [addr]`) step rule for `SepWP`: looks up `ea` and `ea + 8`
    in `P` via `SepLoad64`. -/
theorem SepWP.step_ldrSimd128 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt : BitVec 5} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .Q128 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hload1 : SepLoad64 ea P v1)
    (hload2 : SepLoad64 ea2 P v2)
    (hexec : ((applyWriteback s wb).writeVReg128 vt (v2 ++ v1)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldrSimd .Q128 vt addr) := hpc.symm ▸ hfetch
  have hread1 : s.mem.read64 ea = v1 := hload1.load hm
  have hread2 : s.mem.read64 ea2 = v2 := hload2.load hm
  have hcan1 : s.mem.canRead ea 8 = true := hload1.readable hm
  have hcan2 : s.mem.canRead ea2 8 = true := hload2.readable hm
  have hcan16 : s.mem.canRead ea 16 = true :=
    Memory.canRead_16_of_8_8 hcan1 (hea2.symm ▸ hcan2)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldrSimd .Q128 vt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.readSimdSized, Memory.read128, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hea2, hread1, hread2, hcan16,
      SimdMemSize.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- 128-bit SIMD store (`STR Qt, [addr]`) step rule for `SepWP`: updates `ea` and `ea + 8`
    in `P` via `SepStore64`. -/
theorem SepWP.step_strSimd128 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt : BitVec 5} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .Q128 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hv1 : (s.readVReg128 vt).extractLsb' 0 64 = v1)
    (hv2 : (s.readVReg128 vt).extractLsb' 64 64 = v2)
    (hstore1 : SepStore64 ea v1 P P1)
    (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.strSimd .Q128 vt addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  have hcan16 : s.mem.canWrite ea 16 = true :=
    Memory.canWrite_16_of_8_8 hcan1 (hea2.symm ▸ hcan2)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.strSimd .Q128 vt addr) s = s'.setMem m2 := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized, Memory.write128, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, hv1, hv2, hcan16, SimdMemSize.bytes, hpc, m1, m2]
  rw [hstep]
  exact hnext m2 R hm2

/-- 128-bit SIMD load pair (`LDP Qt1, Qt2, [addr]`) step rule for `SepWP`: looks up
    `ea`, `ea + 8`, `ea + 16`, `ea + 24` in `P` via `SepLoad64`. -/
theorem SepWP.step_ldpSimd128 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    {ea ea2 ea3 ea4 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 v3 v4 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldpSimd .Q128 vt1 vt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hea3 : ea + 16#64 = ea3)
    (hea4 : ea3 + 8#64 = ea4)
    (hload1 : SepLoad64 ea P v1)
    (hload2 : SepLoad64 ea2 P v2)
    (hload3 : SepLoad64 ea3 P v3)
    (hload4 : SepLoad64 ea4 P v4)
    (hexec : (((applyWriteback s wb).writeVReg128 vt1 (v2 ++ v1)).writeVReg128 vt2 (v4 ++ v3)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldpSimd .Q128 vt1 vt2 addr) := hpc.symm ▸ hfetch
  have hread1 : s.mem.read64 ea = v1 := hload1.load hm
  have hread2 : s.mem.read64 ea2 = v2 := hload2.load hm
  have hread3 : s.mem.read64 ea3 = v3 := hload3.load hm
  have hread4 : s.mem.read64 ea4 = v4 := hload4.load hm
  have hcan1 : s.mem.canRead ea 8 = true := hload1.readable hm
  have hcan2 : s.mem.canRead ea2 8 = true := hload2.readable hm
  have hcan3 : s.mem.canRead ea3 8 = true := hload3.readable hm
  have hcan4 : s.mem.canRead ea4 8 = true := hload4.readable hm
  have hcan_lo : s.mem.canRead ea 16 = true :=
    Memory.canRead_16_of_8_8 hcan1 (hea2.symm ▸ hcan2)
  have hcan_hi : s.mem.canRead ea3 16 = true :=
    Memory.canRead_16_of_8_8 hcan3 (hea4.symm ▸ hcan4)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldpSimd .Q128 vt1 vt2 addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.readSimdSized, Memory.read128, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hea2, hea3, hea4,
      hread1, hread2, hread3, hread4, hcan_lo, hcan_hi, SimdMemSize.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- 128-bit SIMD store pair (`STP Qt1, Qt2, [addr]`) step rule for `SepWP`: updates
    `ea`, `ea + 8`, `ea + 16`, `ea + 24` in `P` via `SepStore64`. -/
theorem SepWP.step_stpSimd128 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P1 P2 P3 P4 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    {ea ea2 ea3 ea4 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 v3 v4 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stpSimd .Q128 vt1 vt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hea3 : ea + 16#64 = ea3)
    (hea4 : ea3 + 8#64 = ea4)
    (hv1 : (s.readVReg128 vt1).extractLsb' 0 64 = v1)
    (hv2 : (s.readVReg128 vt1).extractLsb' 64 64 = v2)
    (hv3 : (s.readVReg128 vt2).extractLsb' 0 64 = v3)
    (hv4 : (s.readVReg128 vt2).extractLsb' 64 64 = v4)
    (hstore1 : SepStore64 ea v1 P P1)
    (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hstore3 : SepStore64 ea3 v3 P2 P3)
    (hstore4 : SepStore64 ea4 v4 P3 P4)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P4 post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.stpSimd .Q128 vt1 vt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  let m3 := m2.write64 ea3 v3
  let m4 := m3.write64 ea4 v4
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hm3 : m3 ⊨ P3 ∗ R := hstore3.store hm2
  have hm4 : m4 ⊨ P4 ∗ R := hstore4.store hm3
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  have hcan3 : m2.canWrite ea3 8 = true := hstore3.writable hm2
  have hcan4 : m3.canWrite ea4 8 = true := hstore4.writable hm3
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _),
      Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan3
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _),
      Memory.canWrite_congr (Memory.perm_write64 _ _ _),
      Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan4
  have hcan_lo : s.mem.canWrite ea 16 = true :=
    Memory.canWrite_16_of_8_8 hcan1 (hea2.symm ▸ hcan2)
  have hcan_hi : s.mem.canWrite ea3 16 = true :=
    Memory.canWrite_16_of_8_8 hcan3 (hea4.symm ▸ hcan4)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stpSimd .Q128 vt1 vt2 addr) s = s'.setMem m4 := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized, Memory.write128, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, hea3, hea4, hv1, hv2, hv3, hv4, hcan_lo, hcan_hi,
      SimdMemSize.bytes, hpc, m1, m2, m3, m4]
  rw [hstep]
  exact hnext m4 R hm4

/-- 64-bit SIMD load (`LDR Dt, [addr]`, any `AddrMode`) step rule for `SepWP`: loads `v` at `ea`
    via `SepLoad64` and writes `v.zeroExtend 128` into `Vt`. -/
theorem SepWP.step_ldrSimd64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt : BitVec 5} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .D64 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad64 ea P v)
    (hexec : ((applyWriteback s wb).writeVReg128 vt (v.zeroExtend 128)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldrSimd .D64 vt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read64 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 8 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldrSimd .D64 vt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.readSimdSized, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, SimdMemSize.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- 64-bit SIMD store (`STR Dt, [addr]`, any `AddrMode`) step rule for `SepWP`: stores the low
    64 bits of `Vt` at `ea` via `SepStore64`. -/
theorem SepWP.step_strSimd64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt : BitVec 5} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .D64 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hv : (s.readVReg128 vt).extractLsb' 0 64 = v)
    (hstore : SepStore64 ea v P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.strSimd .D64 vt addr) := hpc.symm ▸ hfetch
  let m' := s.mem.write64 ea v
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 8 = true := hstore.writable hm
  have htr : (s.readVReg128 vt).truncate 64 = v := by
    rw [← hv]; ext i hi; simp
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.strSimd .D64 vt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, htr, hcan, SimdMemSize.bytes, hpc, m']
  rw [hstep]
  exact hnext m' R hm'

/-- 32-bit SIMD load (`LDR St, [addr]`, any `AddrMode`) step rule for `SepWP`: loads `v` at `ea`
    via `SepLoad32` and writes `v.zeroExtend 128` into `Vt`. -/
theorem SepWP.step_ldrSimd32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt : BitVec 5} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldrSimd .S32 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hload : SepLoad32 ea P v)
    (hexec : ((applyWriteback s wb).writeVReg128 vt (v.zeroExtend 128)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldrSimd .S32 vt addr) := hpc.symm ▸ hfetch
  have hread : s.mem.read32 ea = v := hload.load hm
  have hcan : s.mem.canRead ea 4 = true := hload.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldrSimd .S32 vt addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.readSimdSized, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hread, hcan, SimdMemSize.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- 32-bit SIMD store (`STR St, [addr]`, any `AddrMode`) step rule for `SepWP`: stores the low
    32 bits of `Vt` at `ea` via `SepStore32`. -/
theorem SepWP.step_strSimd32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt : BitVec 5} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 32}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.strSimd .S32 vt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hv : (s.readVReg128 vt).extractLsb' 0 32 = v)
    (hstore : SepStore32 ea v P P')
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.strSimd .S32 vt addr) := hpc.symm ▸ hfetch
  let m' := s.mem.write32 ea v
  have hm' : m' ⊨ P' ∗ R := hstore.store hm
  have hcan : s.mem.canWrite ea 4 = true := hstore.writable hm
  have htr : (s.readVReg128 vt).truncate 32 = v := by
    rw [← hv]; ext i hi; simp
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.strSimd .S32 vt addr) s = s'.setMem m' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, htr, hcan, SimdMemSize.bytes, hpc, m']
  rw [hstep]
  exact hnext m' R hm'

/-- 64-bit SIMD load pair (`LDP Dt1, Dt2, [addr]`, any `AddrMode`) step rule for `SepWP`: looks up
    `ea` and `ea + 8` via `SepLoad64`, zero-extending each into `Vt1` / `Vt2`. -/
theorem SepWP.step_ldpSimd64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldpSimd .D64 vt1 vt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hload1 : SepLoad64 ea P v1)
    (hload2 : SepLoad64 ea2 P v2)
    (hexec : (((applyWriteback s wb).writeVReg128 vt1 (v1.zeroExtend 128)).writeVReg128 vt2
      (v2.zeroExtend 128)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldpSimd .D64 vt1 vt2 addr) := hpc.symm ▸ hfetch
  have hread1 : s.mem.read64 ea = v1 := hload1.load hm
  have hread2 : s.mem.read64 ea2 = v2 := hload2.load hm
  have hcan1 : s.mem.canRead ea 8 = true := hload1.readable hm
  have hcan2 : s.mem.canRead ea2 8 = true := hload2.readable hm
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.ldpSimd .D64 vt1 vt2 addr) s = s' := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.readSimdSized, applyWriteback,
      State.advancePC, State.setPC, hsp, haddr, hea2, hread1, hread2, hcan1, hcan2,
      SimdMemSize.bytes, hpc]
  rw [hstep]
  have hmem : s'.mem = s.mem := by
    rw [← hexec]
    cases wb <;> rfl
  apply hnext R
  rwa [hmem]

/-- 64-bit SIMD store pair (`STP Dt1, Dt2, [addr]`, any `AddrMode`) step rule for `SepWP`: updates
    `ea` and `ea + 8` to the low 64 bits of `Vt1` / `Vt2` via `SepStore64`. -/
theorem SepWP.step_stpSimd64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P1 P2 : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {vt1 vt2 : BitVec 5} {addr : AddrMode}
    {ea ea2 : BitVec 64} {wb : Option (Reg × BitVec 64)} {v1 v2 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.stpSimd .D64 vt1 vt2 addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hea2 : ea + 8#64 = ea2)
    (hv1 : (s.readVReg128 vt1).extractLsb' 0 64 = v1)
    (hv2 : (s.readVReg128 vt2).extractLsb' 0 64 = v2)
    (hstore1 : SepStore64 ea v1 P P1)
    (hstore2 : SepStore64 ea2 v2 P1 P2)
    (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P2 post oom) :
    SepWP prog target_pc s P post oom := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.stpSimd .D64 vt1 vt2 addr) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea v1
  let m2 := m1.write64 ea2 v2
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : m1.canWrite ea2 8 = true := hstore2.writable hm1
  rw [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at hcan2
  have htr1 : (s.readVReg128 vt1).truncate 64 = v1 := by
    rw [← hv1]; ext i hi; simp
  have htr2 : (s.readVReg128 vt2).truncate 64 = v2 := by
    rw [← hv2]; ext i hi; simp
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.stpSimd .D64 vt1 vt2 addr) s = s'.setMem m2 := by
    rw [← hexec]
    cases wb <;> simp [Program.evalInst, execInstWithSvc, Memory.writeSimdSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64,
      hsp, haddr, hea2, htr1, htr2, hcan1, hcan2, SimdMemSize.bytes, hpc, m1, m2]
  rw [hstep]
  exact hnext m2 R hm2

theorem Memory.canWrite_64_of_16_16_16_16 {m : Memory} {ea : BitVec 64}
    (h1 : m.canWrite ea 16 = true)
    (h2 : m.canWrite (ea + 16#64) 16 = true)
    (h3 : m.canWrite (ea + 16#64 + 16#64) 16 = true)
    (h4 : m.canWrite (ea + 16#64 + 16#64 + 16#64) 16 = true) :
    m.canWrite ea 64 = true := by
  change m.allPerm (fun p => p.w && !p.x) ea (16 + (16 + (16 + 16))) = true
  rw [Memory.allPerm_add, Memory.allPerm_add, Memory.allPerm_add]
  dsimp only [Memory.canWrite] at h1 h2 h3 h4
  simp only [h1, h2, h3, h4, Bool.and_self]

/-- 64-byte cache-line zero (`DC ZVA, Xt`) step rule for `SepWP`: zeroes the eight 64-bit words
    at `ea, ea + 8, ..., ea + 56` (where `ea = s.readReg64 rt &&& ~~~63#64`) in `P` via
    `SepStore64`. -/
theorem SepWP.step_dcZva {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P1 P2 P3 P4 P5 P6 P7 P8 : SepProp} {post : State → SepProp → Prop}
    {pc : BitVec 64} {rt : Reg}
    {v ea ea2 ea3 ea4 ea5 ea6 ea7 ea8 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.dcZva rt))
    (hval : s.readReg64 rt = v)
    (hea : v &&& ~~~63#64 = ea)
    (hea2 : ea + 8#64 = ea2)
    (hea3 : ea + 16#64 = ea3)
    (hea4 : ea3 + 8#64 = ea4)
    (hea5 : ea3 + 16#64 = ea5)
    (hea6 : ea5 + 8#64 = ea6)
    (hea7 : ea5 + 16#64 = ea7)
    (hea8 : ea7 + 8#64 = ea8)
    (hstore1 : SepStore64 ea 0#64 P P1)
    (hstore2 : SepStore64 ea2 0#64 P1 P2)
    (hstore3 : SepStore64 ea3 0#64 P2 P3)
    (hstore4 : SepStore64 ea4 0#64 P3 P4)
    (hstore5 : SepStore64 ea5 0#64 P4 P5)
    (hstore6 : SepStore64 ea6 0#64 P5 P6)
    (hstore7 : SepStore64 ea7 0#64 P6 P7)
    (hstore8 : SepStore64 ea8 0#64 P7 P8)
    (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P8 post) :
    SepWP prog target_pc s P post := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.dcZva rt) := hpc.symm ▸ hfetch
  let m1 := s.mem.write64 ea 0#64
  let m2 := m1.write64 ea2 0#64
  let m3 := m2.write64 ea3 0#64
  let m4 := m3.write64 ea4 0#64
  let m5 := m4.write64 ea5 0#64
  let m6 := m5.write64 ea6 0#64
  let m7 := m6.write64 ea7 0#64
  let m8 := m7.write64 ea8 0#64
  have hm1 : m1 ⊨ P1 ∗ R := hstore1.store hm
  have hm2 : m2 ⊨ P2 ∗ R := hstore2.store hm1
  have hm3 : m3 ⊨ P3 ∗ R := hstore3.store hm2
  have hm4 : m4 ⊨ P4 ∗ R := hstore4.store hm3
  have hm5 : m5 ⊨ P5 ∗ R := hstore5.store hm4
  have hm6 : m6 ⊨ P6 ∗ R := hstore6.store hm5
  have hm7 : m7 ⊨ P7 ∗ R := hstore7.store hm6
  have hm8 : m8 ⊨ P8 ∗ R := hstore8.store hm7
  have hcan1 : s.mem.canWrite ea 8 = true := hstore1.writable hm
  have hcan2 : s.mem.canWrite ea2 8 = true := by
    have h := hstore2.writable hm1
    rwa [Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at h
  have hcan3 : s.mem.canWrite ea3 8 = true := by
    have h := hstore3.writable hm2
    rwa [Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at h
  have hcan4 : s.mem.canWrite ea4 8 = true := by
    have h := hstore4.writable hm3
    rwa [Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at h
  have hcan5 : s.mem.canWrite ea5 8 = true := by
    have h := hstore5.writable hm4
    rwa [Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at h
  have hcan6 : s.mem.canWrite ea6 8 = true := by
    have h := hstore6.writable hm5
    rwa [Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at h
  have hcan7 : s.mem.canWrite ea7 8 = true := by
    have h := hstore7.writable hm6
    rwa [Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at h
  have hcan8 : s.mem.canWrite ea8 8 = true := by
    have h := hstore8.writable hm7
    rwa [Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _),
         Memory.canWrite_congr (Memory.perm_write64 _ _ _)] at h
  have hcan_q0 : s.mem.canWrite ea 16 = true :=
    Memory.canWrite_16_of_8_8 hcan1 (hea2.symm ▸ hcan2)
  have hcan_q1 : s.mem.canWrite ea3 16 = true :=
    Memory.canWrite_16_of_8_8 hcan3 (hea4.symm ▸ hcan4)
  have hcan_q2 : s.mem.canWrite ea5 16 = true :=
    Memory.canWrite_16_of_8_8 hcan5 (hea6.symm ▸ hcan6)
  have hcan_q3 : s.mem.canWrite ea7 16 = true :=
    Memory.canWrite_16_of_8_8 hcan7 (hea8.symm ▸ hcan8)
  have hcan64 : s.mem.canWrite ea 64 = true :=
    Memory.canWrite_64_of_16_16_16_16 hcan_q0 (hea3.symm ▸ hcan_q1)
      (hea3.symm ▸ hea5.symm ▸ hcan_q2) (hea3.symm ▸ hea5.symm ▸ hea7.symm ▸ hcan_q3)
  apply reaches_pc_step hrun hfetch'
  have hstep : prog.evalInst (.dcZva rt) s = s'.setMem m8 := by
    change execInst (.dcZva rt) s = s'.setMem m8
    rw [← hexec, execInst_dcZva, hval, hea]
    dsimp only [Memory.write128, State.advancePC, State.setPC, State.setMem,
      m1, m2, m3, m4, m5, m6, m7, m8]
    rw [hcan64]
    simp only [Bool.not_true, Bool.false_eq_true, reduceIte]
    rw [hea2, hea3, hea4, hea5, hea6, hea7, hea8, hpc]
    rfl
  rw [hstep]
  exact hnext m8 R hm8

/-- Bridge an alignment or masking equality written with the decoded literal mask
    `0xffffffffffffffc0#64` to the `~~~63#64` premise of `step_dcZva` / `step_dcZva_bytes`. -/
theorem dcZva_ea_of_mask_eq {v ea : BitVec 64}
    (h : v &&& 0xffffffffffffffc0#64 = ea) :
    v &&& ~~~63#64 = ea := h

theorem dcZva_ea_of_aligned_eq {u v : BitVec 64}
    (hu : u &&& 0xffffffffffffffc0#64 = u) (heq : u = v) :
    v &&& ~~~63#64 = v := by
  subst heq
  exact hu

theorem dcZva_aligned_of_and_mask (x : BitVec 64) :
    (x &&& 0xffffffffffffffc0#64) &&& 0xffffffffffffffc0#64 = x &&& 0xffffffffffffffc0#64 := by
  bv_bits

theorem dcZva_aligned_of_and63_zero {u : BitVec 64} (h : u &&& 63#64 = 0#64) :
    u &&& 0xffffffffffffffc0#64 = u := by
  revert h
  bv_bits

theorem dcZva_aligned_of_toNat_mod64 {u : BitVec 64} (h : u.toNat % 64 = 0) :
    u &&& 0xffffffffffffffc0#64 = u := by
  have h1 : u &&& 63#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_and, Nat.and_two_pow_sub_one_eq_mod _ 6, h]
  exact dcZva_aligned_of_and63_zero h1

theorem dcZva_ea_of_aligned_add_ofNat {u v : BitVec 64} {off : Nat}
    (hu : u &&& 0xffffffffffffffc0#64 = u)
    (hmod : off % 64 = 0)
    (hadd : u + BitVec.ofNat 64 off = v) :
    v &&& ~~~63#64 = v := by
  subst hadd
  have h1 : BitVec.ofNat 64 off &&& 63#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_two_pow_sub_one_eq_mod _ 6, hmod]
  revert hu h1
  bv_bits

/-- Bundled 64-byte zero store witness for `DC ZVA, Xt`: packages the eight adjacent 64-bit zero
    stores at `ea, ea + 8, ..., ea + 56` into a single separation-logic update from `P` to `P'`. -/
structure SepStoreDcZva (ea : BitVec 64) (P P' : SepProp) : Prop where
  exists_chain : ∃ P1 P2 P3 P4 P5 P6 P7 : SepProp,
    SepStore64 ea 0#64 P P1 ∧
    SepStore64 (ea + 8#64) 0#64 P1 P2 ∧
    SepStore64 (ea + 16#64) 0#64 P2 P3 ∧
    SepStore64 ((ea + 16#64) + 8#64) 0#64 P3 P4 ∧
    SepStore64 ((ea + 16#64) + 16#64) 0#64 P4 P5 ∧
    SepStore64 (((ea + 16#64) + 16#64) + 8#64) 0#64 P5 P6 ∧
    SepStore64 (((ea + 16#64) + 16#64) + 16#64) 0#64 P6 P7 ∧
    SepStore64 ((((ea + 16#64) + 16#64) + 16#64) + 8#64) 0#64 P7 P'

theorem SepStoreDcZva.left {ea : BitVec 64} {L L' R : SepProp}
    (h : SepStoreDcZva ea L L') : SepStoreDcZva ea (L ∗ R) (L' ∗ R) := by
  rcases h with ⟨⟨P1, P2, P3, P4, P5, P6, P7, s1, s2, s3, s4, s5, s6, s7, s8⟩⟩
  exact ⟨⟨P1 ∗ R, P2 ∗ R, P3 ∗ R, P4 ∗ R, P5 ∗ R, P6 ∗ R, P7 ∗ R,
    s1.left, s2.left, s3.left, s4.left, s5.left, s6.left, s7.left, s8.left⟩⟩

theorem SepStoreDcZva.right {ea : BitVec 64} {L R R' : SepProp}
    (h : SepStoreDcZva ea R R') : SepStoreDcZva ea (L ∗ R) (L ∗ R') := by
  rcases h with ⟨⟨P1, P2, P3, P4, P5, P6, P7, s1, s2, s3, s4, s5, s6, s7, s8⟩⟩
  exact ⟨⟨L ∗ P1, L ∗ P2, L ∗ P3, L ∗ P4, L ∗ P5, L ∗ P6, L ∗ P7,
    s1.right, s2.right, s3.right, s4.right, s5.right, s6.right, s7.right, s8.right⟩⟩

/-- Leaf witness for `SepStoreDcZva` on a byte-slice atom at byte offset `off`, collapsing the
    eight 64-bit zero writes into `ByteSlice.fillSet bs 0#8` over `[off, off + 64)`. -/
theorem SepStoreDcZva.of_pointsToBytes_here
    (ea base : BitVec 64) (bs : List (BitVec 8)) (off : Nat)
    (hoff : off + 64 ≤ bs.length)
    (ha : base + BitVec.ofNat 64 off = ea) :
    SepStoreDcZva ea (base ↦ₛ bs)
      (base ↦ₛ ByteSlice.fillSet bs 0#8 (fun i => decide (off ≤ i) && decide (i < off + 64))) := by
  subst ha
  let bs1 := ByteSlice.write64 bs off 0#64
  let bs2 := ByteSlice.write64 bs1 (off + 8) 0#64
  let bs3 := ByteSlice.write64 bs2 (off + 16) 0#64
  let bs4 := ByteSlice.write64 bs3 (off + 24) 0#64
  let bs5 := ByteSlice.write64 bs4 (off + 32) 0#64
  let bs6 := ByteSlice.write64 bs5 (off + 40) 0#64
  let bs7 := ByteSlice.write64 bs6 (off + 48) 0#64
  have hlen1 : bs1.length = bs.length := by dsimp [bs1]; byte_region_len
  have hlen2 : bs2.length = bs.length := by dsimp [bs2]; rw [ByteSlice.write64_length _ _ _ (by omega), hlen1]
  have hlen3 : bs3.length = bs.length := by dsimp [bs3]; rw [ByteSlice.write64_length _ _ _ (by omega), hlen2]
  have hlen4 : bs4.length = bs.length := by dsimp [bs4]; rw [ByteSlice.write64_length _ _ _ (by omega), hlen3]
  have hlen5 : bs5.length = bs.length := by dsimp [bs5]; rw [ByteSlice.write64_length _ _ _ (by omega), hlen4]
  have hlen6 : bs6.length = bs.length := by dsimp [bs6]; rw [ByteSlice.write64_length _ _ _ (by omega), hlen5]
  have hlen7 : bs7.length = bs.length := by dsimp [bs7]; rw [ByteSlice.write64_length _ _ _ (by omega), hlen6]
  have s1 := SepStore64.of_pointsToBytes_here (base + BitVec.ofNat 64 off) base bs off 0#64 (by omega) rfl
  have s2 := SepStore64.of_pointsToBytes_here ((base + BitVec.ofNat 64 off) + 8#64) base bs1 (off + 8) 0#64
    (by omega) (by rw [BitVec.ofNat_add]; bv_lin)
  have s3 := SepStore64.of_pointsToBytes_here ((base + BitVec.ofNat 64 off) + 16#64) base bs2 (off + 16) 0#64
    (by omega) (by rw [BitVec.ofNat_add]; bv_lin)
  have s4 := SepStore64.of_pointsToBytes_here (((base + BitVec.ofNat 64 off) + 16#64) + 8#64) base bs3 (off + 24) 0#64
    (by omega) (by rw [BitVec.ofNat_add]; bv_lin)
  have s5 := SepStore64.of_pointsToBytes_here (((base + BitVec.ofNat 64 off) + 16#64) + 16#64) base bs4 (off + 32) 0#64
    (by omega) (by rw [BitVec.ofNat_add]; bv_lin)
  have s6 := SepStore64.of_pointsToBytes_here ((((base + BitVec.ofNat 64 off) + 16#64) + 16#64) + 8#64) base bs5 (off + 40) 0#64
    (by omega) (by rw [BitVec.ofNat_add]; bv_lin)
  have s7 := SepStore64.of_pointsToBytes_here ((((base + BitVec.ofNat 64 off) + 16#64) + 16#64) + 16#64) base bs6 (off + 48) 0#64
    (by omega) (by rw [BitVec.ofNat_add]; bv_lin)
  have s8 := SepStore64.of_pointsToBytes_here (((((base + BitVec.ofNat 64 off) + 16#64) + 16#64) + 16#64) + 8#64) base bs7 (off + 56) 0#64
    (by omega) (by rw [BitVec.ofNat_add]; bv_lin)
  dsimp only [bs1, bs2, bs3, bs4, bs5, bs6, bs7] at s8
  rw [ByteSlice.write64_zero_8_eq_fillSet bs off hoff] at s8
  exact ⟨⟨_, _, _, _, _, _, _, s1, s2, s3, s4, s5, s6, s7, s8⟩⟩

/-- 64-byte cache-line zero (`DC ZVA, Xt`) step rule for `SepWP` over a byte-slice atom via
    `SepStoreDcZva`. -/
theorem SepWP.step_dcZva_bytes {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P P' : SepProp} {post : State → SepProp → Prop}
    {pc : BitVec 64} {rt : Reg}
    {v ea : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.dcZva rt))
    (hval : s.readReg64 rt = v)
    (hea : v &&& ~~~63#64 = ea)
    (hstore : SepStoreDcZva ea P P')
    (hexec : s.setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, SepWP prog target_pc (s'.setMem m') P' post) :
    SepWP prog target_pc s P post := by
  rcases hstore with ⟨⟨P1, P2, P3, P4, P5, P6, P7, s1, s2, s3, s4, s5, s6, s7, s8⟩⟩
  exact SepWP.step_dcZva hpc hrun hfetch hval hea rfl rfl rfl rfl rfl rfl rfl
    s1 s2 s3 s4 s5 s6 s7 s8 hexec hnext


end ProofLib
