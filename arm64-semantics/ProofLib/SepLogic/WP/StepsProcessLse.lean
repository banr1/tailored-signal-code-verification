/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.SepLogic.WP.StepsSubword
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# EL0 System-Register and LSE Atomic Step Lemmas

Proves `SepWP` step rules for `MRS`/`MSR` on `DCZID_EL0` and `TPIDR_EL0`, 32-bit and 64-bit LSE
`CAS`, and 32-bit LSE `SWP`.
-/

set_option autoImplicit false

@[expose] public section

namespace ProofLib

open Arm64

/-! ## EL0 System-Register Step Lemmas -/

/-- `MRS Xt, DCZID_EL0` (`0x5807#15`): writes `4#64` (`DCZID_EL0.BS = 4`, 64-byte cache zeroing
    block size) to `rt` and advances `pc` by `4`. -/
theorem SepWP.step_mrs_dczid_el0 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.sysReg true 0x5807#15 rt))
    (hexec : (s.writeReg64 rt 4#64).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.step_pure hpc hrun hfetch ?_ ?_ hnext
  · rw [← hexec]
    cases s; cases rt <;> rfl
  · rw [← hexec]; cases s; cases rt <;> rfl

/-- `MRS Xt, TPIDR_EL0` (`0x5e82#15`): reads the EL0 thread pointer `s.tpidrEl0` into `rt` and
    advances `pc` by `4`. -/
theorem SepWP.step_mrs_tpidr_el0 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.sysReg true 0x5e82#15 rt))
    (hexec : (s.writeReg64 rt s.tpidrEl0).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.step_pure hpc hrun hfetch ?_ ?_ hnext
  · rw [← hexec]
    cases s; cases rt <;> rfl
  · rw [← hexec]; cases s; cases rt <;> rfl

/-- `MSR TPIDR_EL0, Xt` (`0x5e82#15`): updates `tpidrEl0` to `s.readReg64 rt`
    (`setTpidrEl0`) and advances `pc` by `4`. -/
theorem SepWP.step_msr_tpidr_el0 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc : BitVec 64} {rt : Reg}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.sysReg false 0x5e82#15 rt))
    (hexec : (setTpidrEl0 s (s.readReg64 rt)).setPC (pc + 4#64) = s')
    (hnext : SepWP prog target_pc s' P post oom) :
    SepWP prog target_pc s P post oom := by
  refine SepWP.step_pure hpc hrun hfetch ?_ ?_ hnext
  · rw [← hexec]
    cases s; cases rt <;> rfl
  · rw [← hexec]; cases s; rfl

/-! ## LSE Atomic Step Lemmas -/

theorem zeroExtend64_beq_32 (a b : BitVec 32) :
    (a.zeroExtend 64 == b.zeroExtend 64) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have h64 : a.zeroExtend 64 ≠ b.zeroExtend 64 := by
      intro heq
      apply h
      have := congrArg (fun x : BitVec 64 => x.truncate 32) heq
      simpa using this
    rw [beq_false_of_ne h64, beq_false_of_ne h]

/-- 32-bit LSE compare-and-swap (`CAS`/`CASA`/`CASL`/`CASAL Ws, Wt, [Xn]`) over `((ea ↦₃₂ v0) ∗ F)`:
    compares `v0` with `exp := s.readReg32 rs`, stores `new := s.readReg32 rt` when `v0 == exp`
    (leaving memory at `v0` otherwise), writes `v0` (zero-extended) to `rs`, and advances `pc` by `4`. -/
theorem SepWP.step_cas32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc ea : BitVec 64} {acq rel : Bool} {rs rn rt : Reg} {v0 exp new : BitVec 32}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.cas .W32 acq rel rs rn rt))
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .W32 ea = true)
    (hexp : s.readReg32 rs = exp)
    (hnew : s.readReg32 rt = new)
    (hexec : (s.writeReg32 rs v0).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc (s'.setMem m') ((ea ↦₃₂ (if v0 == exp then new else v0)) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post oom := by
  intro R hm
  have hm' : s.mem ⊨ (ea ↦₃₂ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcr : s.mem.canRead ea 4 = true := (IsBlock.pointsTo32 ea v0).canRead (by decide) hm'
  have hcw : s.mem.canWrite ea 4 = true := (IsBlock.pointsTo32 ea v0).canWrite (by decide) hm'
  have hrd : s.mem.read32 ea = v0 := (IsBlock.pointsTo32 ea v0).read hm'
  have hfetch' : prog.fetch s.pc = some (.cas .W32 acq rel rs rn rt) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  have hexp' : ((s.readReg64 rs).truncate 32).zeroExtend 64 = exp.zeroExtend 64 := by
    rw [← hexp]; rfl
  have hnew' : (s.readReg64 rt).truncate 32 = new := hnew
  dsimp only [Program.evalInst, execInstWithSvc, MemWidth.bytes]
  simp only [hsp, haddr, halign, hcr, hcw, Bool.and_self, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, Memory.readSized, hrd, hexp', zeroExtend64_beq_32, Memory.writeSized, hnew']
  by_cases hcmp : (v0 == exp) = true
  · simp only [hcmp, ↓reduceIte]
    have hst : ((s.setMem (s.mem.write32 ea new)).writeReg .W32 rs (v0.zeroExtend 64)).advancePC =
        s'.setMem (s.mem.write32 ea new) := by
      rw [← hexec]
      cases s; cases rs <;> simp [State.writeReg, State.writeReg32, State.writeReg64,
        State.advancePC, State.setPC, State.setMem, hpc]
    rw [hst]
    apply hnext (s.mem.write32 ea new) R
    simp only [hcmp, ↓reduceIte]
    rw [sepConj_assoc]
    exact (IsBlock.pointsTo32 ea v0).write32 hm' new
  · have hcmp_f : (v0 == exp) = false := Bool.eq_false_iff.mpr hcmp
    simp only [hcmp_f, Bool.false_eq_true, ↓reduceIte]
    have hst : (s.writeReg .W32 rs (v0.zeroExtend 64)).advancePC = s'.setMem s.mem := by
      rw [← hexec]
      cases s; cases rs <;> simp [State.writeReg, State.writeReg32, State.writeReg64,
        State.advancePC, State.setPC, State.setMem, hpc]
    rw [hst]
    apply hnext s.mem R
    simpa [hcmp_f] using hm

/-- 64-bit LSE compare-and-swap (`CAS`/`CASA`/`CASL`/`CASAL Xs, Xt, [Xn]`) over `((ea ↦₆₄ v0) ∗ F)`:
    compares `v0` with `exp := s.readReg64 rs`, stores `new := s.readReg64 rt` when `v0 == exp`
    (leaving memory at `v0` otherwise), writes `v0` to `rs`, and advances `pc` by `4`. -/
theorem SepWP.step_cas64 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc ea v0 exp new : BitVec 64} {acq rel : Bool} {rs rn rt : Reg}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.cas .X64 acq rel rs rn rt))
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .X64 ea = true)
    (hexp : s.readReg64 rs = exp)
    (hnew : s.readReg64 rt = new)
    (hexec : (s.writeReg64 rs v0).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc (s'.setMem m') ((ea ↦₆₄ (if v0 == exp then new else v0)) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₆₄ v0) ∗ F) post oom := by
  intro R hm
  have hm' : s.mem ⊨ (ea ↦₆₄ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcr : s.mem.canRead ea 8 = true := (IsBlock.pointsTo64 ea v0).canRead (by decide) hm'
  have hcw : s.mem.canWrite ea 8 = true := (IsBlock.pointsTo64 ea v0).canWrite (by decide) hm'
  have hrd : s.mem.read64 ea = v0 := (IsBlock.pointsTo64 ea v0).read hm'
  have hfetch' : prog.fetch s.pc = some (.cas .X64 acq rel rs rn rt) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  dsimp only [Program.evalInst, execInstWithSvc, MemWidth.bytes]
  simp only [hsp, haddr, halign, hcr, hcw, Bool.and_self, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, Memory.readSized, hrd, hexp, Memory.writeSized, hnew]
  by_cases hcmp : (v0 == exp) = true
  · simp only [hcmp, ↓reduceIte]
    have hst : ((s.setMem (s.mem.write64 ea new)).writeReg .W64 rs v0).advancePC =
        s'.setMem (s.mem.write64 ea new) := by
      rw [← hexec]
      cases s; cases rs <;> simp [State.writeReg, State.writeReg64, State.advancePC,
        State.setPC, State.setMem, hpc]
    rw [hst]
    apply hnext (s.mem.write64 ea new) R
    simp only [hcmp, ↓reduceIte]
    rw [sepConj_assoc]
    exact (IsBlock.pointsTo64 ea v0).write64 hm' new
  · have hcmp_f : (v0 == exp) = false := Bool.eq_false_iff.mpr hcmp
    simp only [hcmp_f, Bool.false_eq_true, ↓reduceIte]
    have hst : (s.writeReg .W64 rs v0).advancePC = s'.setMem s.mem := by
      rw [← hexec]
      cases s; cases rs <;> simp [State.writeReg, State.writeReg64, State.advancePC,
        State.setPC, State.setMem, hpc]
    rw [hst]
    apply hnext s.mem R
    simpa [hcmp_f] using hm

/-- 32-bit LSE atomic swap (`SWP`/`SWPA`/`SWPL`/`SWPAL Ws, Wt, [Xn]`) over `((ea ↦₃₂ v0) ∗ F)`:
    stores `new := s.readReg32 rs` at `ea`, writes `v0` (zero-extended) to `rt`, and advances `pc`
    by `4`. -/
theorem SepWP.step_atomicRmw_swp32 {prog : Program} {target_pc : BitVec 64}
    {s s' : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    {pc ea : BitVec 64} {acq rel : Bool} {rs rn rt : Reg} {v0 new : BitVec 32}
    (hpc : s.pc = pc) (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.atomicRmw .SWP .W32 acq rel rs rn rt))
    (hsp : checkRegSPAligned s rn = true)
    (haddr : s.readReg64 rn = ea)
    (halign : MemWidth.isAligned .W32 ea = true)
    (hnew : s.readReg32 rs = new)
    (hexec : (s.writeReg32 rt v0).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory,
      SepWP prog target_pc (s'.setMem m') ((ea ↦₃₂ new) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post oom := by
  intro R hm
  have hm' : s.mem ⊨ (ea ↦₃₂ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcr : s.mem.canRead ea 4 = true := (IsBlock.pointsTo32 ea v0).canRead (by decide) hm'
  have hcw : s.mem.canWrite ea 4 = true := (IsBlock.pointsTo32 ea v0).canWrite (by decide) hm'
  have hrd : s.mem.read32 ea = v0 := (IsBlock.pointsTo32 ea v0).read hm'
  have hfetch' : prog.fetch s.pc = some (.atomicRmw .SWP .W32 acq rel rs rn rt) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  have htrunc : (evalAtomicOp .SWP .W32 (v0.zeroExtend 64) (s.readReg64 rs)).truncate 32 = new := by
    rw [← hnew]
    dsimp [evalAtomicOp, State.readReg32]
    bv_bits
  have hst : ((s.setMem (s.mem.write32 ea new)).writeReg .W32 rt (v0.zeroExtend 64)).advancePC =
      s'.setMem (s.mem.write32 ea new) := by
    rw [← hexec]
    cases s; cases rt <;> simp [State.writeReg, State.writeReg32, State.writeReg64,
      State.advancePC, State.setPC, State.setMem, hpc]
  dsimp only [Program.evalInst, execInstWithSvc, MemWidth.bytes]
  simp only [hsp, haddr, halign, hcr, hcw, Bool.and_self, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, Memory.readSized, hrd, Memory.writeSized, htrunc, hst]
  apply hnext (s.mem.write32 ea new) R
  rw [sepConj_assoc]
  exact (IsBlock.pointsTo32 ea v0).write32 hm' new


end ProofLib
