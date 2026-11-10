/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.SepLogic.WP
public import ProofLib.SepLogic.WP.StepsProcess
public import ProofLib.StdStartup.Layout
public import ProofLib.StdStartup.MemOps
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics

/-!
# AArch64 Outline Atomics and LSE Initialization

Instruction templates and `subroutine_ok` contracts for `__rust_enable_lse` and the AArch64
outline atomic helpers (`__aarch64_cas8_relax`, `__aarch64_cas4_acq`, `__aarch64_cas8_acq`,
`__aarch64_swp4_rel`, and `__aarch64_cas1_acq`) under both LSE and LL/SC (`exclFails`) execution.
-/
set_option autoImplicit false
@[expose] public section
namespace ProofLib.StdStartup
open Arm64 ProofLib

/-- Instruction sequence (`4` insns) for `__rust_enable_lse` at `L.rustEnableLseAddr`. -/
def rustEnableLseInstrs (L : StdBinaryLayout) : List Instr :=
  [ .adr true .x8 (adrpOff L.rustEnableLseAddr L.haveLseAtomicsAddr), .moveWide .W32 .MOVZ .x9 1#16 0,
    .str .B8 .x9 (.Offset .x8 (pageLo12 L.haveLseAtomicsAddr)), .ret .x30 ]

/-- Shared instruction template (`12` insns) for 64-bit outline CAS (`acq = false` relax, `true` acq). -/
def cas8GenInstrs (addr haveLseAddr : BitVec 64) (acq : Bool) : List Instr :=
  [ .adr true .x16 (adrpOff addr haveLseAddr), .ldr .W32 .B8 false .x16 (.Offset .x16 (pageLo12 haveLseAddr)),
    .cbz .W32 false .x16 12#64, .cas .X64 acq false .x0 .x2 .x1, .ret .x30,
    .logicalShift .W64 .ORR .x16 .xzr .x0 .LSL 0, .ldxr .X64 acq .x2 .x0,
    .addSubShift .W64 .SUBS .xzr .x0 .x16 .LSL 0, .bCond .NE 12#64,
    .stxr .X64 false .x17 .x2 .x1, .cbz .W32 true .x17 (-16#64), .ret .x30 ]

/-- Instruction sequence (`12` insns) for `__aarch64_cas8_relax` at `L.cas8RelaxAddr`. -/
def cas8RelaxInstrs (L : StdBinaryLayout) : List Instr := cas8GenInstrs L.cas8RelaxAddr L.haveLseAtomicsAddr false

/-- Instruction sequence (`12` insns) for `__aarch64_cas4_acq` at `L.cas4AcqAddr`. -/
def cas4AcqInstrs (L : StdBinaryLayout) : List Instr :=
  [ .adr true .x16 (adrpOff L.cas4AcqAddr L.haveLseAtomicsAddr),
    .ldr .W32 .B8 false .x16 (.Offset .x16 (pageLo12 L.haveLseAtomicsAddr)),
    .cbz .W32 false .x16 12#64, .cas .W32 true false .x0 .x2 .x1, .ret .x30,
    .logicalShift .W32 .ORR .x16 .xzr .x0 .LSL 0, .ldxr .W32 true .x2 .x0,
    .addSubShift .W32 .SUBS .xzr .x0 .x16 .LSL 0, .bCond .NE 12#64,
    .stxr .W32 false .x17 .x2 .x1, .cbz .W32 true .x17 (-16#64), .ret .x30 ]

/-- Instruction sequence (`12` insns) for `__aarch64_cas8_acq` at `L.cas8AcqAddr`. -/
def cas8AcqInstrs (L : StdBinaryLayout) : List Instr := cas8GenInstrs L.cas8AcqAddr L.haveLseAtomicsAddr true

/-- Instruction sequence (`10` insns) for `__aarch64_swp4_rel` at `L.swp4RelAddr`. -/
def swp4RelInstrs (L : StdBinaryLayout) : List Instr :=
  [ .adr true .x16 (adrpOff L.swp4RelAddr L.haveLseAtomicsAddr),
    .ldr .W32 .B8 false .x16 (.Offset .x16 (pageLo12 L.haveLseAtomicsAddr)),
    .cbz .W32 false .x16 12#64, .atomicRmw .SWP .W32 false true .x0 .x1 .x0, .ret .x30,
    .logicalShift .W32 .ORR .x16 .xzr .x0 .LSL 0, .ldxr .W32 false .x1 .x0,
    .stxr .W32 true .x17 .x1 .x16, .cbz .W32 true .x17 (-8#64), .ret .x30 ]

/-- Instruction sequence (`12` insns) for `__aarch64_cas1_acq` at `addr` (byte-width acquire CAS:
    `casab` when `HAVE_LSE_ATOMICS ≠ 0`, otherwise a `uxtb` + `ldaxrb`/`stxrb` retry loop). -/
def cas1AcqInstrs (addr haveLseAddr : BitVec 64) : List Instr :=
  [ .adr true .x16 (adrpOff addr haveLseAddr), .ldr .W32 .B8 false .x16 (.Offset .x16 (pageLo12 haveLseAddr)),
    .cbz .W32 false .x16 12#64, .cas .B8 true false .x0 .x2 .x1, .ret .x30,
    .bitfield .W32 .UBFM .x16 .x0 0 7, .ldxr .B8 true .x2 .x0,
    .addSubShift .W32 .SUBS .xzr .x0 .x16 .LSL 0, .bCond .NE 12#64,
    .stxr .B8 false .x17 .x2 .x1, .cbz .W32 true .x17 (-16#64), .ret .x30 ]

/-- Contract for byte-width outline compare-and-swap (`__aarch64_cas1_acq`) reading
    `haveLseAddr ↦₈ᵣ haveLse` under arbitrary `exclFails` (`w0 = exp`, `w1 = new`, `x2 = ptr`, low
    bytes compared). Returns the old byte zero-extended in `x0`. -/
def stdCas1Spec (haveLseAddr : BitVec 64) : Spec (BitVec 8 × BitVec 64 × BitVec 8 × BitVec 8 × BitVec 8) where
  pre := fun (haveLse, ptr, v0, exp, new) s0 =>
    ⌜(s0.readReg64 .x0).truncate 8 = exp ∧ (s0.readReg64 .x1).truncate 8 = new ∧ s0.readReg64 .x2 = ptr⌝ ∗
    ((haveLseAddr ↦₈ᵣ haveLse) ∗ (ptr ↦₈ v0))
  post := fun (haveLse, ptr, v0, exp, new) s0 sf =>
    ⌜sf.readReg64 .x0 = v0.zeroExtend 64 ∧ StdStatePreserved s0 sf⌝ ∗
    ((haveLseAddr ↦₈ᵣ haveLse) ∗ (ptr ↦₈ (if v0 == exp then new else v0)))
  onPanic := fun _ _ _ => ⌜False⌝
  onExit  := fun _ _ _ _ => ⌜False⌝
  onOom   := fun _ _ _ => ⌜False⌝

private theorem step_str8_perm {prog : Program} {target_pc pc ea : BitVec 64} {s s' : State} {P P' : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {rt : Reg} {addr : AddrMode} {wb : Option (Reg × BitVec 64)} {val : BitVec 8}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.str .B8 rt addr))
    (hsp : checkAddrSPAligned s addr = true) (haddr : evalAddrMode s addr = (ea, wb)) (hval : (s.readReg32 rt).truncate 8 = val)
    (hstore : SepStore8 ea val P P') (hexec : (applyWriteback s wb).setPC (pc + 4#64) = s')
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (s'.setMem m') P' post oom) : SepWP prog target_pc s P post oom := by
  apply SepWP.of_reaches_pc; intro R hm; have htrunc : (s.readReg64 rt).truncate 8 = val := by rw [← bitvec_truncate8_truncate32]; exact hval
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.str .B8 rt addr) s = s'.setMem (s.mem.write8 ea val) := by
    rw [← hexec]; cases wb <;> simp [Program.evalInst, execInstWithSvc, execStr, Memory.writeSized, applyWriteback,
      State.advancePC, State.setPC, State.setMem, State.writeReg64, hsp, haddr, htrunc, hstore.writable hm, MemWidth.bytes, hpc]
  rw [hstep]; exact SepWP.to_reaches_pc (hnext _ (Memory.perm_write8 s.mem ea val)) (hstore.store hm)

private theorem fetch_at {P : Program} {base off : BitVec 64} {ls : List Instr} {inst : Instr}
    (i : Nat) (h : hasInstrs P base ls) (hi : ls[i]? = some inst := by rfl) (hoff : BitVec.ofNat 64 (4 * i) = off := by rfl) :
    P.fetch (base + off) = some inst := by
  have hlt : i < ls.length := (List.getElem?_eq_some_iff.mp hi).1
  have hf := h.fetch_off i off hlt hoff; rw [List.getElem?_eq_getElem hlt] at hi; cases hi; exact hf
private theorem fetch_at0 {P : Program} {base : BitVec 64} {ls : List Instr} {inst : Instr}
    (h : hasInstrs P base ls) (hi : ls[0]? = some inst := by rfl) : P.fetch base = some inst := by simpa using fetch_at 0 h hi rfl

private theorem step_cas64_perm {prog : Program} {target_pc pc ea v0 exp new : BitVec 64} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {acq : Bool}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.cas .X64 acq false .x0 .x2 .x1))
    (haddr : s.readReg64 .x2 = ea) (halign : MemWidth.isAligned .X64 ea = true) (hexp : s.readReg64 .x0 = exp) (hnew : s.readReg64 .x1 = new)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((s.writeReg64 .x0 v0).setPC (pc + 4#64)).setMem m')
        ((ea ↦₆₄ (if v0 == exp then new else v0)) ∗ F) post oom) : SepWP prog target_pc s ((ea ↦₆₄ v0) ∗ F) post oom := by
  apply SepWP.of_reaches_pc; intro R hm; have hm' : s.mem ⊨ (ea ↦₆₄ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcr := (IsBlock.pointsTo64 ea v0).canRead (by decide) hm'; have hcw := (IsBlock.pointsTo64 ea v0).canWrite (by decide) hm'
  have hrd := (IsBlock.pointsTo64 ea v0).read hm'; have hsp : checkRegSPAligned s .x2 = true := rfl
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch); dsimp only [Program.evalInst, execInstWithSvc, MemWidth.bytes]
  simp only [hsp, haddr, halign, hcr, hcw, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Memory.readSized, hrd, hexp, Memory.writeSized, hnew]
  cases hcmp : (v0 == exp)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hst : (s.writeReg .W64 .x0 v0).advancePC = ((s.writeReg64 .x0 v0).setPC (pc + 4#64)).setMem s.mem := by
      cases s; simp [State.writeReg, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
    rw [hst]; exact SepWP.to_reaches_pc (hnext s.mem rfl) (by simpa [hcmp] using hm)
  · simp only [↓reduceIte]
    have hst : ((s.setMem (s.mem.write64 ea new)).writeReg .W64 .x0 v0).advancePC =
        ((s.writeReg64 .x0 v0).setPC (pc + 4#64)).setMem (s.mem.write64 ea new) := by
      cases s; simp [State.writeReg, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
    rw [hst]; refine SepWP.to_reaches_pc (hnext _ (Memory.perm_write64 s.mem ea new)) ?_
    simp only [hcmp, ↓reduceIte]; rw [sepConj_assoc]; exact (IsBlock.pointsTo64 ea v0).write64 hm' new

private theorem step_cas32_perm {prog : Program} {target_pc pc ea : BitVec 64} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {v0 exp new : BitVec 32}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.cas .W32 true false .x0 .x2 .x1))
    (haddr : s.readReg64 .x2 = ea) (halign : MemWidth.isAligned .W32 ea = true) (hexp : s.readReg32 .x0 = exp) (hnew : s.readReg32 .x1 = new)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((s.writeReg32 .x0 v0).setPC (pc + 4#64)).setMem m')
        ((ea ↦₃₂ (if v0 == exp then new else v0)) ∗ F) post oom) : SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post oom := by
  apply SepWP.of_reaches_pc; intro R hm; have hm' : s.mem ⊨ (ea ↦₃₂ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcr := (IsBlock.pointsTo32 ea v0).canRead (by decide) hm'; have hcw := (IsBlock.pointsTo32 ea v0).canWrite (by decide) hm'
  have hrd := (IsBlock.pointsTo32 ea v0).read hm'; have hsp : checkRegSPAligned s .x2 = true := rfl
  have hexp' : ((s.readReg64 .x0).truncate 32).zeroExtend 64 = exp.zeroExtend 64 := by rw [← hexp]; rfl
  have hnew' : (s.readReg64 .x1).truncate 32 = new := hnew
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch); dsimp only [Program.evalInst, execInstWithSvc, MemWidth.bytes]
  simp only [hsp, haddr, halign, hcr, hcw, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Memory.readSized, hrd, hexp', zeroExtend64_beq_32, Memory.writeSized, hnew']
  cases hcmp : (v0 == exp)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hst : (s.writeReg .W32 .x0 (v0.zeroExtend 64)).advancePC = ((s.writeReg32 .x0 v0).setPC (pc + 4#64)).setMem s.mem := by
      cases s; simp [State.writeReg, State.writeReg32, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
    rw [hst]; exact SepWP.to_reaches_pc (hnext s.mem rfl) (by simpa [hcmp] using hm)
  · simp only [↓reduceIte]
    have hst : ((s.setMem (s.mem.write32 ea new)).writeReg .W32 .x0 (v0.zeroExtend 64)).advancePC =
        ((s.writeReg32 .x0 v0).setPC (pc + 4#64)).setMem (s.mem.write32 ea new) := by
      cases s; simp [State.writeReg, State.writeReg32, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
    rw [hst]; refine SepWP.to_reaches_pc (hnext _ (Memory.perm_write32 s.mem ea new)) ?_
    simp only [hcmp, ↓reduceIte]; rw [sepConj_assoc]; exact (IsBlock.pointsTo32 ea v0).write32 hm' new

private theorem step_swp32_perm {prog : Program} {target_pc pc ea : BitVec 64} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {v0 new : BitVec 32}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.atomicRmw .SWP .W32 false true .x0 .x1 .x0))
    (haddr : s.readReg64 .x1 = ea) (halign : MemWidth.isAligned .W32 ea = true) (hnew : s.readReg32 .x0 = new)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((s.writeReg32 .x0 v0).setPC (pc + 4#64)).setMem m') ((ea ↦₃₂ new) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post oom := by
  apply SepWP.of_reaches_pc; intro R hm; have hm' : s.mem ⊨ (ea ↦₃₂ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcr := (IsBlock.pointsTo32 ea v0).canRead (by decide) hm'; have hcw := (IsBlock.pointsTo32 ea v0).canWrite (by decide) hm'
  have hrd := (IsBlock.pointsTo32 ea v0).read hm'; have hsp : checkRegSPAligned s .x1 = true := rfl
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have htrunc : (evalAtomicOp .SWP .W32 (v0.zeroExtend 64) (s.readReg64 .x0)).truncate 32 = new := by rw [← hnew]; dsimp [evalAtomicOp, State.readReg32]; bv_bits
  have hst : ((s.setMem (s.mem.write32 ea new)).writeReg .W32 .x0 (v0.zeroExtend 64)).advancePC =
      ((s.writeReg32 .x0 v0).setPC (pc + 4#64)).setMem (s.mem.write32 ea new) := by
    cases s; simp [State.writeReg, State.writeReg32, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
  dsimp only [Program.evalInst, execInstWithSvc, MemWidth.bytes]
  simp only [hsp, haddr, halign, hcr, hcw, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Memory.readSized, hrd, Memory.writeSized, htrunc, hst]
  refine SepWP.to_reaches_pc (hnext _ (Memory.perm_write32 s.mem ea new)) ?_; rw [sepConj_assoc]; exact (IsBlock.pointsTo32 ea v0).write32 hm' new
private theorem step_stxr64_either {prog : Program} {target_pc pc ea v0 val : BitVec 64} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.stxr .X64 false .x17 .x2 .x1))
    (haddr : s.readReg64 .x2 = ea) (halign : MemWidth.isAligned .X64 ea = true) (hval : s.readReg64 .x1 = val)
    (hok : s.exclWillFail = false → ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((s.stepExclOracle.writeReg .W32 .x17 0#64).setPC (pc + 4#64)).setMem m') ((ea ↦₆₄ val) ∗ F) post oom)
    (hfail : s.exclWillFail = true → SepWP prog target_pc ((s.stepExclOracle.writeReg .W32 .x17 1#64).setPC (pc + 4#64)) ((ea ↦₆₄ v0) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₆₄ v0) ∗ F) post oom := by
  apply SepWP.of_reaches_pc; intro R hm; have hm' : s.mem ⊨ (ea ↦₆₄ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcw := (IsBlock.pointsTo64 ea v0).canWrite (by decide) hm'; have hsp : checkRegSPAligned s .x2 = true := rfl
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch); cases hf : s.exclWillFail
  · have hstep : prog.evalInst (.stxr .X64 false .x17 .x2 .x1) s = ((s.stepExclOracle.writeReg .W32 .x17 0#64).setPC (pc + 4#64)).setMem (s.mem.write64 ea val) := by
      simp only [Program.evalInst, execInstWithSvc, hsp, haddr, halign, hf, hval, MemWidth.bytes, hcw, Memory.writeSized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
    rw [hstep]; refine SepWP.to_reaches_pc (hok hf _ (Memory.perm_write64 s.mem ea val)) ?_; rw [sepConj_assoc]; exact (IsBlock.pointsTo64 ea v0).write64 hm' val
  · have hstep : prog.evalInst (.stxr .X64 false .x17 .x2 .x1) s = (s.stepExclOracle.writeReg .W32 .x17 1#64).setPC (pc + 4#64) := by
      simp only [Program.evalInst, execInstWithSvc, hsp, haddr, halign, hf, MemWidth.bytes, hcw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC, State.setPC, hpc]
    rw [hstep]; exact SepWP.to_reaches_pc (hfail hf) (by simpa [State.stepExclOracle] using hm)
private theorem step_stxr32_either {prog : Program} {target_pc pc ea : BitVec 64} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {v0 val : BitVec 32} {rel : Bool} {rn rt : Reg}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.stxr .W32 rel .x17 rn rt))
    (hsp : checkRegSPAligned s rn = true) (haddr : s.readReg64 rn = ea) (halign : MemWidth.isAligned .W32 ea = true) (hval : s.readReg32 rt = val)
    (hok : s.exclWillFail = false → ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((s.stepExclOracle.writeReg .W32 .x17 0#64).setPC (pc + 4#64)).setMem m') ((ea ↦₃₂ val) ∗ F) post oom)
    (hfail : s.exclWillFail = true → SepWP prog target_pc ((s.stepExclOracle.writeReg .W32 .x17 1#64).setPC (pc + 4#64)) ((ea ↦₃₂ v0) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₃₂ v0) ∗ F) post oom := by
  apply SepWP.of_reaches_pc; intro R hm; have hm' : s.mem ⊨ (ea ↦₃₂ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcw := (IsBlock.pointsTo32 ea v0).canWrite (by decide) hm'; have htrunc : (s.readReg64 rt).truncate 32 = val := hval
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch); cases hf : s.exclWillFail
  · have hstep : prog.evalInst (.stxr .W32 rel .x17 rn rt) s = ((s.stepExclOracle.writeReg .W32 .x17 0#64).setPC (pc + 4#64)).setMem (s.mem.write32 ea val) := by
      simp only [Program.evalInst, execInstWithSvc, hsp, haddr, halign, hf, htrunc, MemWidth.bytes, hcw, Memory.writeSized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
    rw [hstep]; refine SepWP.to_reaches_pc (hok hf _ (Memory.perm_write32 s.mem ea val)) ?_; rw [sepConj_assoc]; exact (IsBlock.pointsTo32 ea v0).write32 hm' val
  · have hstep : prog.evalInst (.stxr .W32 rel .x17 rn rt) s = (s.stepExclOracle.writeReg .W32 .x17 1#64).setPC (pc + 4#64) := by
      simp only [Program.evalInst, execInstWithSvc, hsp, haddr, halign, hf, MemWidth.bytes, hcw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC, State.setPC, hpc]
    rw [hstep]; exact SepWP.to_reaches_pc (hfail hf) (by simpa [State.stepExclOracle] using hm)
private theorem step_ldxr8 {prog : Program} {target_pc pc ea : BitVec 64} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {v0 : BitVec 8}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.ldxr .B8 true .x2 .x0)) (haddr : s.readReg64 .x2 = ea)
    (hnext : SepWP prog target_pc ((s.writeReg .W32 .x0 (v0.zeroExtend 64)).setPC (pc + 4#64)) ((ea ↦₈ v0) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₈ v0) ∗ F) post oom := by
  apply SepWP.of_reaches_pc; intro R hm; have hm' : s.mem ⊨ (ea ↦₈ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcr := (IsBlock.pointsTo8 ea v0).canRead (by decide) hm'; have hrd := (IsBlock.pointsTo8 ea v0).read hm'
  have hsp : checkRegSPAligned s .x2 = true := rfl
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch)
  have hstep : prog.evalInst (.ldxr .B8 true .x2 .x0) s = (s.writeReg .W32 .x0 (v0.zeroExtend 64)).setPC (pc + 4#64) := by
    simp [Program.evalInst, execInstWithSvc, Memory.readSized, State.advancePC, State.setPC, hsp, haddr, MemWidth.isAligned, hrd, hcr, MemWidth.bytes, hpc]
  rw [hstep]; exact SepWP.to_reaches_pc hnext hm
private theorem step_cas8_perm {prog : Program} {target_pc pc ea : BitVec 64} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {v0 exp new : BitVec 8}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.cas .B8 true false .x0 .x2 .x1))
    (haddr : s.readReg64 .x2 = ea) (hexp : (s.readReg64 .x0).truncate 8 = exp) (hnew : (s.readReg64 .x1).truncate 8 = new)
    (hnext : ∀ m' : Memory, m'.perm = s.mem.perm → SepWP prog target_pc (((s.writeReg .W32 .x0 (v0.zeroExtend 64)).setPC (pc + 4#64)).setMem m')
        ((ea ↦₈ (if v0 == exp then new else v0)) ∗ F) post oom) : SepWP prog target_pc s ((ea ↦₈ v0) ∗ F) post oom := by
  apply SepWP.of_reaches_pc; intro R hm; have hm' : s.mem ⊨ (ea ↦₈ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcr := (IsBlock.pointsTo8 ea v0).canRead (by decide) hm'; have hcw := (IsBlock.pointsTo8 ea v0).canWrite (by decide) hm'
  have hrd := (IsBlock.pointsTo8 ea v0).read hm'; have hsp : checkRegSPAligned s .x2 = true := rfl
  have hbeq : (v0.zeroExtend 64 == exp.zeroExtend 64) = (v0 == exp) := by
    by_cases h : v0 = exp
    · subst h; simp
    · have h64 : v0.zeroExtend 64 ≠ exp.zeroExtend 64 := fun heq => h (by simpa using congrArg (fun x : BitVec 64 => x.truncate 8) heq)
      rw [beq_false_of_ne h64, beq_false_of_ne h]
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch); dsimp only [Program.evalInst, execInstWithSvc, MemWidth.bytes]
  simp only [hsp, haddr, MemWidth.isAligned, hcr, hcw, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Memory.readSized, hrd, hexp, hbeq, Memory.writeSized, hnew]
  cases hcmp : (v0 == exp)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hst : (s.writeReg .W32 .x0 (v0.zeroExtend 64)).advancePC = ((s.writeReg .W32 .x0 (v0.zeroExtend 64)).setPC (pc + 4#64)).setMem s.mem := by
      cases s; simp [State.writeReg, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
    rw [hst]; exact SepWP.to_reaches_pc (hnext s.mem rfl) (by simpa [hcmp] using hm)
  · simp only [↓reduceIte]
    have hst : ((s.setMem (s.mem.write8 ea new)).writeReg .W32 .x0 (v0.zeroExtend 64)).advancePC =
        ((s.writeReg .W32 .x0 (v0.zeroExtend 64)).setPC (pc + 4#64)).setMem (s.mem.write8 ea new) := by
      cases s; simp [State.writeReg, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
    rw [hst]; refine SepWP.to_reaches_pc (hnext _ (Memory.perm_write8 s.mem ea new)) ?_
    simp only [hcmp, ↓reduceIte]; rw [sepConj_assoc]; exact (IsBlock.pointsTo8 ea v0).write8 hm' new
private theorem step_stxr8_either {prog : Program} {target_pc pc ea : BitVec 64} {s : State} {F : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp} {v0 val : BitVec 8}
    (hpc : s.pc = pc) (hrun : s.status = .Running) (hfetch : prog.fetch pc = some (.stxr .B8 false .x17 .x2 .x1))
    (haddr : s.readReg64 .x2 = ea) (hval : (s.readReg64 .x1).truncate 8 = val)
    (hok : s.exclWillFail = false → ∀ m' : Memory, m'.perm = s.mem.perm →
      SepWP prog target_pc (((s.stepExclOracle.writeReg .W32 .x17 0#64).setPC (pc + 4#64)).setMem m') ((ea ↦₈ val) ∗ F) post oom)
    (hfail : s.exclWillFail = true → SepWP prog target_pc ((s.stepExclOracle.writeReg .W32 .x17 1#64).setPC (pc + 4#64)) ((ea ↦₈ v0) ∗ F) post oom) :
    SepWP prog target_pc s ((ea ↦₈ v0) ∗ F) post oom := by
  apply SepWP.of_reaches_pc; intro R hm; have hm' : s.mem ⊨ (ea ↦₈ v0) ∗ (F ∗ R) := by rw [← sepConj_assoc]; exact hm
  have hcw := (IsBlock.pointsTo8 ea v0).canWrite (by decide) hm'; have hsp : checkRegSPAligned s .x2 = true := rfl
  apply reaches_pc_step hrun (hpc.symm ▸ hfetch); cases hf : s.exclWillFail
  · have hstep : prog.evalInst (.stxr .B8 false .x17 .x2 .x1) s = ((s.stepExclOracle.writeReg .W32 .x17 0#64).setPC (pc + 4#64)).setMem (s.mem.write8 ea val) := by
      simp only [Program.evalInst, execInstWithSvc, hsp, haddr, MemWidth.isAligned, hf, hval, MemWidth.bytes, hcw, Memory.writeSized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC, State.setPC, State.setMem, hpc]
    rw [hstep]; refine SepWP.to_reaches_pc (hok hf _ (Memory.perm_write8 s.mem ea val)) ?_; rw [sepConj_assoc]; exact (IsBlock.pointsTo8 ea v0).write8 hm' val
  · have hstep : prog.evalInst (.stxr .B8 false .x17 .x2 .x1) s = (s.stepExclOracle.writeReg .W32 .x17 1#64).setPC (pc + 4#64) := by
      simp only [Program.evalInst, execInstWithSvc, hsp, haddr, MemWidth.isAligned, hf, MemWidth.bytes, hcw, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      simp [State.stepExclOracle, State.writeReg, State.writeReg64, State.advancePC, State.setPC, hpc]
    rw [hstep]; exact SepWP.to_reaches_pc (hfail hf) (by simpa [State.stepExclOracle] using hm)
private theorem exclFails_tail_lt {s : State} {k : Nat} (hk : s.exclFails.length < k + 1) (hf : s.exclWillFail = true) : s.exclFails.tail.length < k := by
  cases h : s.exclFails with | nil => simp [State.exclWillFail_eq_headD, h] at hf | cons _ tl => simp [h] at hk ⊢; omega

private def LlscFrame (s0 s : State) : Prop :=
  s.sp = s0.sp ∧ s.readReg64 (.gpr 30#5) = s0.readReg64 (.gpr 30#5) ∧ CalleeSavedPreserved s0 s ∧ StdStatePreserved s0 s
private theorem LlscFrame.refl (s0 : State) : LlscFrame s0 s0 := ⟨rfl, rfl, CalleeSavedPreserved.rfl s0, ProcessFieldsPreserved.refl s0⟩
private theorem LlscFrame.pc {s0 s : State} {p : BitVec 64} (h : LlscFrame s0 s) : LlscFrame s0 (s.setPC p) := by cases s; exact h
private theorem LlscFrame.ps {s0 s : State} {p : PState} (h : LlscFrame s0 s) : LlscFrame s0 (s.setPState p) := by cases s; exact h
private theorem LlscFrame.ex {s0 s : State} (h : LlscFrame s0 s) : LlscFrame s0 s.stepExclOracle := by cases s; exact h
private theorem LlscFrame.mem {s0 s : State} {m' : Memory} (hm : m'.perm = s.mem.perm) (h : LlscFrame s0 s) : LlscFrame s0 (s.setMem m') := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hp⟩; cases s; exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun a => (congrFun hm a).trans (hp a)⟩
private theorem LlscFrame.w64 {s0 s : State} {r : Reg} {v : BitVec 64}
    (hr : r = .gpr 0#5 ∨ r = .gpr 8#5 ∨ r = .gpr 9#5 ∨ r = .gpr 16#5 ∨ r = .gpr 17#5) (h : LlscFrame s0 s) : LlscFrame s0 (s.writeReg64 r v) := by
  rcases h with ⟨h1, h2, hcs, hst⟩
  have hlr : (s.writeReg64 r v).readReg64 (.gpr 30#5) = s.readReg64 (.gpr 30#5) := by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact State.readReg64_writeReg64_ne s _ _ v (by decide)
  have hcs' : CalleeSavedPreserved s (s.writeReg64 r v) := by
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;> exact State.readReg64_writeReg64_ne s _ _ v (by decide)
  have hsp : (s.writeReg64 r v).sp = s.sp := by rcases hr with rfl | rfl | rfl | rfl | rfl <;> cases s <;> rfl
  have hpf : StdStatePreserved s (s.writeReg64 r v) := by rcases hr with rfl | rfl | rfl | rfl | rfl <;> cases s <;> exact ProcessFieldsPreserved.refl _
  exact ⟨hsp.trans h1, hlr.trans h2, CalleeSavedPreserved.trans hcs hcs', ProcessFieldsPreserved.trans hst hpf⟩
private theorem LlscFrame.w32 {s0 s : State} {r : Reg} {v : BitVec 32}
    (hr : r = .gpr 0#5 ∨ r = .gpr 8#5 ∨ r = .gpr 9#5 ∨ r = .gpr 16#5 ∨ r = .gpr 17#5) (h : LlscFrame s0 s) : LlscFrame s0 (s.writeReg32 r v) := LlscFrame.w64 hr h
private theorem LlscFrame.w {s0 s : State} {w : RegWidth} {r : Reg} {v : BitVec 64}
    (hr : r = .gpr 0#5 ∨ r = .gpr 8#5 ∨ r = .gpr 9#5 ∨ r = .gpr 16#5 ∨ r = .gpr 17#5) (h : LlscFrame s0 s) : LlscFrame s0 (s.writeReg w r v) := by cases w <;> exact LlscFrame.w64 hr h

local macro "llsc_inv" : tactic => `(tactic|
  repeat (
    first
    | assumption | exact LlscFrame.refl _ | apply LlscFrame.pc | apply LlscFrame.ps | apply LlscFrame.ex
    | refine LlscFrame.w64 (by decide) ?_ | refine LlscFrame.w32 (by decide) ?_ | refine LlscFrame.w (by decide) ?_
    | refine LlscFrame.mem (by simp [State.stepExclOracle, wp_norm, arm64_norm, *]) ?_))

private theorem done_subroutine {P : Program} {s0 sf : State} {P_f R : SepProp} {Q : State → SepProp}
    (hpc : sf.pc = s0.readReg64 .lr) (hrun : sf.status = .Running) (hinv : LlscFrame s0 sf)
    (hq : StdStatePreserved s0 sf → sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf ∗ R) :
    SepWP P (s0.readReg64 .lr) sf P_f (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf ∗ R) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) :=
  SepWP.done hpc hrun ⟨hq hinv.2.2.2, hinv.1, hinv.2.2.1⟩

private theorem done_atomic {P : Program} {s0 sf : State} {A A' B R : SepProp} {P_ret : State → Prop}
    (hpc : sf.pc = s0.readReg64 .lr) (hrun : sf.status = .Running) (hinv : LlscFrame s0 sf) (hret : P_ret sf) (hA : A = A' := by rfl) :
    SepWP P (s0.readReg64 .lr) sf (A ∗ B)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (⌜P_ret sf ∧ StdStatePreserved s0 sf⌝ ∗ B ∗ A') ∗ R) ∧ sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) :=
  done_subroutine hpc hrun hinv fun hstd hm => by rw [hA, sepConj_comm A'] at hm; rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨⟨hret, hstd⟩, hm⟩

section
arm64_proof_prelude

theorem rustEnableLse_ok (P : Program) (L : StdBinaryLayout) (h : hasInstrs P L.rustEnableLseAddr (rustEnableLseInstrs L)) :
    subroutine_ok P L.rustEnableLseAddr (stdRustEnableLseSpec L.haveLseAtomicsAddr) := by
  apply subroutine_ok_of_sepWP_init; intro oldVal R s0 hpc hrun hpre _hsp
  dsimp only [stdRustEnableLseSpec] at hpre ⊢; refine ⟨L.haveLseAtomicsAddr ↦₈ oldVal, hpre, ?_⟩
  have hf0 := fetch_at0 h; have hf1 := fetch_at 1 (off := 4#64) h; have hf2 := fetch_at 2 (off := 8#64) h; have hf3 := fetch_at 3 (off := 12#64) h
  wp_steps 2; refine step_str8_perm (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun]) hf2 rfl
    (ea := L.haveLseAtomicsAddr) (wb := none) (val := 1#8) (by simp [evalAddrMode, wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm]) (by wp_sep_access) rfl fun m' hm_perm => ?_
  wp_step; refine done_subroutine (s0 := s0) (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm, hrun]) (by llsc_inv) fun hstd hm => ?_
  rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hstd, hm⟩

local macro "wp_simp" : tactic => `(tactic|
  simp (config := { decide := true }) [State.stepExclOracle, State.readReg32, wp_norm, arm64_norm, bv_lin_norm, *])

private theorem cas8_gen_ok (P : Program) (addr haveLseAddr : BitVec 64) (acq : Bool)
    (h : hasInstrs P addr (cas8GenInstrs addr haveLseAddr acq)) : subroutine_ok P addr (stdCas8Spec haveLseAddr) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨haveLse, ptr, v0, exp, new⟩ R s0 hpc hrun hpre _hsp
  dsimp only [stdCas8Spec] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, halign⟩, hmem⟩; simp only [arm64_norm] at hx0 hx1 hx2
  rw [sepConj_comm (haveLseAddr ↦₈ᵣ haveLse)] at hmem; refine ⟨(ptr ↦₆₄ v0) ∗ (haveLseAddr ↦₈ᵣ haveLse), hmem, ?_⟩
  have hf0 := fetch_at0 h; have hf1 := fetch_at 1 (off := 4#64) h; have hf2 := fetch_at 2 (off := 8#64) h; have hf3 := fetch_at 3 (off := 12#64) h
  have hf4 := fetch_at 4 (off := 16#64) h; have hf5 := fetch_at 5 (off := 20#64) h; have hf6 := fetch_at 6 (off := 24#64) h
  have hf7 := fetch_at 7 (off := 28#64) h; have hf8 := fetch_at 8 (off := 32#64) h; have hf9 := fetch_at 9 (off := 36#64) h
  have hf10 := fetch_at 10 (off := 40#64) h; have hf11 := fetch_at 11 (off := 44#64) h
  wp_steps 3; wp_if hcbz
  · wp_step
    suffices hloop : ∀ (k : Nat) (st : State), st.exclFails.length < k → st.pc = addr + 24#64 → st.status = .Running →
        st.readReg64 (.gpr 16#5) = exp → st.readReg64 (.gpr 1#5) = new → st.readReg64 (.gpr 2#5) = ptr → LlscFrame s0 st →
        SepWP P (s0.readReg64 .lr) st ((ptr ↦₆₄ v0) ∗ (haveLseAddr ↦₈ᵣ haveLse)) _ from
      hloop (_ + 1) _ (Nat.lt_succ_self _) (by wp_simp) (by wp_simp) (by wp_simp) (by wp_simp) (by wp_simp) (by llsc_inv)
    intro k; induction k with | zero => intro _ hk; omega | succ k ih =>
      intro st hk hpc_s hrun_s hx16_s hx1_s hx2_s hinv_s
      refine SepWP.step_ldxr64 hpc_s hrun_s hf6 rfl hx2_s halign (SepLoad64.left (SepLoad64.here rfl)) rfl ?_
      wp_steps 2; wp_if hne
      · wp_step; exact done_atomic (by have := hinv_s.2.1; wp_simp) (by wp_simp) (by llsc_inv) (by wp_simp) (by simp [beq_false_of_ne hne])
      · subst hne; refine step_stxr64_either (ea := ptr) (val := new) (by wp_simp) (by wp_simp) hf9 (by wp_simp) halign (by wp_simp) (fun _ m' hm_p => ?_) (fun hfail => ?_)
        · wp_step; wp_step; exact done_atomic (by have := hinv_s.2.1; wp_simp) (by wp_simp) (by llsc_inv) (by wp_simp) (by simp)
        · wp_step; exact ih _ (by simpa [State.stepExclOracle, wp_norm, arm64_norm] using exclFails_tail_lt (by simpa [wp_norm, arm64_norm] using hk) hfail)
            (by wp_simp) (by wp_simp) (by wp_simp) (by wp_simp) (by wp_simp) (by llsc_inv)
  · refine step_cas64_perm (ea := ptr) (exp := exp) (new := new) (by wp_simp) (by wp_simp) hf3 (by wp_simp) halign (by wp_simp) (by wp_simp) fun m' hm_p => ?_
    wp_step; exact done_atomic (by wp_simp) (by wp_simp) (by llsc_inv) (by wp_simp)

theorem cas8Relax_ok (P : Program) (L : StdBinaryLayout) (h : hasInstrs P L.cas8RelaxAddr (cas8RelaxInstrs L)) :
    subroutine_ok P L.cas8RelaxAddr (stdCas8Spec L.haveLseAtomicsAddr) := cas8_gen_ok P L.cas8RelaxAddr L.haveLseAtomicsAddr false h

theorem cas8Acq_ok (P : Program) (L : StdBinaryLayout) (h : hasInstrs P L.cas8AcqAddr (cas8AcqInstrs L)) :
    subroutine_ok P L.cas8AcqAddr (stdCas8Spec L.haveLseAtomicsAddr) := cas8_gen_ok P L.cas8AcqAddr L.haveLseAtomicsAddr true h

theorem cas4Acq_ok (P : Program) (L : StdBinaryLayout) (h : hasInstrs P L.cas4AcqAddr (cas4AcqInstrs L)) :
    subroutine_ok P L.cas4AcqAddr (stdCas4Spec L.haveLseAtomicsAddr) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨haveLse, ptr, v0, exp, new⟩ R s0 hpc hrun hpre _hsp
  dsimp only [stdCas4Spec] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, halign⟩, hmem⟩; simp only [arm64_norm] at hx0 hx1 hx2
  rw [sepConj_comm (L.haveLseAtomicsAddr ↦₈ᵣ haveLse)] at hmem; refine ⟨(ptr ↦₃₂ v0) ∗ (L.haveLseAtomicsAddr ↦₈ᵣ haveLse), hmem, ?_⟩
  have hf0 := fetch_at0 h; have hf1 := fetch_at 1 (off := 4#64) h; have hf2 := fetch_at 2 (off := 8#64) h; have hf3 := fetch_at 3 (off := 12#64) h
  have hf4 := fetch_at 4 (off := 16#64) h; have hf5 := fetch_at 5 (off := 20#64) h; have hf6 := fetch_at 6 (off := 24#64) h
  have hf7 := fetch_at 7 (off := 28#64) h; have hf8 := fetch_at 8 (off := 32#64) h; have hf9 := fetch_at 9 (off := 36#64) h
  have hf10 := fetch_at 10 (off := 40#64) h; have hf11 := fetch_at 11 (off := 44#64) h
  wp_steps 3; wp_if hcbz
  · wp_step
    suffices hloop : ∀ (k : Nat) (st : State), st.exclFails.length < k → st.pc = L.cas4AcqAddr + 24#64 → st.status = .Running →
        (st.readReg64 (.gpr 16#5)).truncate 32 = exp → (st.readReg64 (.gpr 1#5)).truncate 32 = new → st.readReg64 (.gpr 2#5) = ptr →
        LlscFrame s0 st → SepWP P (s0.readReg64 .lr) st ((ptr ↦₃₂ v0) ∗ (L.haveLseAtomicsAddr ↦₈ᵣ haveLse)) _ from
      hloop (_ + 1) _ (Nat.lt_succ_self _) (by wp_simp) (by wp_simp) (by wp_simp; try bv_bits) (by wp_simp) (by wp_simp) (by llsc_inv)
    intro k; induction k with | zero => intro _ hk; omega | succ k ih =>
      intro st hk hpc_s hrun_s hx16_s hx1_s hx2_s hinv_s
      refine SepWP.step_ldxr32 hpc_s hrun_s hf6 rfl hx2_s halign (SepLoad32.left (SepLoad32.here rfl)) rfl ?_
      wp_steps 2; wp_if hne
      · try simp only [hx16_s, wp_norm, arm64_norm] at hne
        wp_step; exact done_atomic (by have := hinv_s.2.1; wp_simp) (by wp_simp) (by llsc_inv) (by wp_simp; try bv_bits) (by simp [beq_false_of_ne hne])
      · try simp only [hx16_s, wp_norm, arm64_norm] at hne
        subst hne; refine step_stxr32_either (ea := ptr) (val := new) (by wp_simp) (by wp_simp) hf9 rfl (by wp_simp) halign (by wp_simp) (fun _ m' hm_p => ?_) (fun hfail => ?_)
        · wp_step; wp_step; exact done_atomic (by have := hinv_s.2.1; wp_simp) (by wp_simp) (by llsc_inv) (by wp_simp; try bv_bits) (by simp)
        · wp_step; exact ih _ (by simpa [State.stepExclOracle, wp_norm, arm64_norm] using exclFails_tail_lt (by simpa [wp_norm, arm64_norm] using hk) hfail)
            (by wp_simp) (by wp_simp) (by wp_simp) (by wp_simp) (by wp_simp) (by llsc_inv)
  · refine step_cas32_perm (ea := ptr) (exp := exp) (new := new) (by wp_simp) (by wp_simp) hf3 (by wp_simp) halign (by wp_simp) (by wp_simp) fun m' hm_p => ?_
    wp_step; exact done_atomic (by wp_simp) (by wp_simp) (by llsc_inv) (by wp_simp; try bv_bits)

theorem swp4Rel_ok (P : Program) (L : StdBinaryLayout) (h : hasInstrs P L.swp4RelAddr (swp4RelInstrs L)) :
    subroutine_ok P L.swp4RelAddr (stdSwp4Spec L.haveLseAtomicsAddr) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨haveLse, ptr, v0, new⟩ R s0 hpc hrun hpre _hsp
  dsimp only [stdSwp4Spec] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, halign⟩, hmem⟩; simp only [arm64_norm] at hx0 hx1
  rw [sepConj_comm (L.haveLseAtomicsAddr ↦₈ᵣ haveLse)] at hmem; refine ⟨(ptr ↦₃₂ v0) ∗ (L.haveLseAtomicsAddr ↦₈ᵣ haveLse), hmem, ?_⟩
  have hf0 := fetch_at0 h; have hf1 := fetch_at 1 (off := 4#64) h; have hf2 := fetch_at 2 (off := 8#64) h; have hf3 := fetch_at 3 (off := 12#64) h
  have hf4 := fetch_at 4 (off := 16#64) h; have hf5 := fetch_at 5 (off := 20#64) h; have hf6 := fetch_at 6 (off := 24#64) h
  have hf7 := fetch_at 7 (off := 28#64) h; have hf8 := fetch_at 8 (off := 32#64) h; have hf9 := fetch_at 9 (off := 36#64) h
  wp_steps 3; wp_if hcbz
  · wp_step
    suffices hloop : ∀ (k : Nat) (st : State), st.exclFails.length < k → st.pc = L.swp4RelAddr + 24#64 → st.status = .Running →
        (st.readReg64 (.gpr 16#5)).truncate 32 = new → st.readReg64 (.gpr 1#5) = ptr → LlscFrame s0 st →
        SepWP P (s0.readReg64 .lr) st ((ptr ↦₃₂ v0) ∗ (L.haveLseAtomicsAddr ↦₈ᵣ haveLse)) _ from
      hloop (_ + 1) _ (Nat.lt_succ_self _) (by wp_simp) (by wp_simp) (by wp_simp; try bv_bits) (by wp_simp) (by llsc_inv)
    intro k; induction k with | zero => intro _ hk; omega | succ k ih =>
      intro st hk hpc_s hrun_s hx16_s hx1_s hinv_s
      refine SepWP.step_ldxr32 hpc_s hrun_s hf6 rfl hx1_s halign (SepLoad32.left (SepLoad32.here rfl)) rfl ?_
      refine step_stxr32_either (ea := ptr) (val := new) (by wp_simp) (by wp_simp) hf7 rfl (by wp_simp) halign (by wp_simp) (fun _ m' hm_p => ?_) (fun hfail => ?_)
      · wp_step; wp_step; exact done_atomic (by have := hinv_s.2.1; wp_simp) (by wp_simp) (by llsc_inv) (by wp_simp; try bv_bits)
      · wp_step; exact ih _ (by simpa [State.stepExclOracle, wp_norm, arm64_norm] using exclFails_tail_lt (by simpa [wp_norm, arm64_norm] using hk) hfail)
          (by wp_simp) (by wp_simp) (by wp_simp) (by wp_simp) (by llsc_inv)
  · refine step_swp32_perm (ea := ptr) (new := new) (by wp_simp) (by wp_simp) hf3 (by wp_simp) halign (by wp_simp) fun m' hm_p => ?_
    wp_step; exact done_atomic (by wp_simp) (by wp_simp) (by llsc_inv) (by wp_simp; try bv_bits)

theorem cas1Acq_ok (P : Program) (addr haveLseAddr : BitVec 64) (h : hasInstrs P addr (cas1AcqInstrs addr haveLseAddr)) :
    subroutine_ok P addr (stdCas1Spec haveLseAddr) := by
  apply subroutine_ok_of_sepWP_init; rintro ⟨haveLse, ptr, v0, exp, new⟩ R s0 hpc hrun hpre _hsp
  dsimp only [stdCas1Spec] at hpre ⊢; rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩; simp only [arm64_norm] at hx0 hx1 hx2
  rw [sepConj_comm (haveLseAddr ↦₈ᵣ haveLse)] at hmem; refine ⟨(ptr ↦₈ v0) ∗ (haveLseAddr ↦₈ᵣ haveLse), hmem, ?_⟩
  have hf0 := fetch_at0 h; have hf1 := fetch_at 1 (off := 4#64) h; have hf2 := fetch_at 2 (off := 8#64) h; have hf3 := fetch_at 3 (off := 12#64) h
  have hf4 := fetch_at 4 (off := 16#64) h; have hf5 := fetch_at 5 (off := 20#64) h; have hf6 := fetch_at 6 (off := 24#64) h
  have hf7 := fetch_at 7 (off := 28#64) h; have hf8 := fetch_at 8 (off := 32#64) h; have hf9 := fetch_at 9 (off := 36#64) h
  have hf10 := fetch_at 10 (off := 40#64) h; have hf11 := fetch_at 11 (off := 44#64) h
  wp_steps 3; wp_if hcbz
  · wp_step
    suffices hloop : ∀ (k : Nat) (st : State), st.exclFails.length < k → st.pc = addr + 24#64 → st.status = .Running →
        st.readReg64 (.gpr 16#5) = exp.zeroExtend 64 → (st.readReg64 (.gpr 1#5)).truncate 8 = new → st.readReg64 (.gpr 2#5) = ptr →
        LlscFrame s0 st → SepWP P (s0.readReg64 .lr) st ((ptr ↦₈ v0) ∗ (haveLseAddr ↦₈ᵣ haveLse)) _ from
      hloop (_ + 1) _ (Nat.lt_succ_self _) (by wp_simp) (by wp_simp) (by wp_simp; bv_bits) (by wp_simp) (by wp_simp) (by llsc_inv)
    intro k; induction k with | zero => intro _ hk; omega | succ k ih =>
      intro st hk hpc_s hrun_s hx16_s hx1_s hx2_s hinv_s
      refine step_ldxr8 hpc_s hrun_s hf6 hx2_s ?_
      wp_steps 2; wp_if hne
      · wp_step; exact done_atomic (by have := hinv_s.2.1; wp_simp) (by wp_simp) (by llsc_inv) (by wp_simp)
          (by have hne' : v0 ≠ exp := fun he => hne (by subst he; wp_simp); simp [beq_false_of_ne hne'])
      · have he : v0 = exp := by revert hne; wp_simp; bv_bits
        subst he; refine step_stxr8_either (ea := ptr) (val := new) (by wp_simp) (by wp_simp) hf9 (by wp_simp) (by wp_simp) (fun _ m' hm_p => ?_) (fun hfail => ?_)
        · wp_step; wp_step; exact done_atomic (by have := hinv_s.2.1; wp_simp) (by wp_simp) (by llsc_inv) (by wp_simp) (by simp)
        · wp_step; exact ih _ (by simpa [State.stepExclOracle, wp_norm, arm64_norm] using exclFails_tail_lt (by simpa [wp_norm, arm64_norm] using hk) hfail)
            (by wp_simp) (by wp_simp) (by wp_simp) (by wp_simp) (by wp_simp) (by llsc_inv)
  · refine step_cas8_perm (ea := ptr) (exp := exp) (new := new) (by wp_simp) (by wp_simp) hf3 (by wp_simp) (by wp_simp) (by wp_simp) fun m' hm_p => ?_
    wp_step; exact done_atomic (by wp_simp) (by wp_simp) (by llsc_inv) (by wp_simp)

theorem stdOutlineAtomics_of_hasInstrs (P : Program) (L : StdBinaryLayout)
    (h1 : hasInstrs P L.cas8RelaxAddr (cas8RelaxInstrs L)) (h2 : hasInstrs P L.cas4AcqAddr (cas4AcqInstrs L))
    (h3 : hasInstrs P L.cas8AcqAddr (cas8AcqInstrs L)) (h4 : hasInstrs P L.swp4RelAddr (swp4RelInstrs L)) :
    StdOutlineAtomics P L.haveLseAtomicsAddr L.cas8RelaxAddr L.cas4AcqAddr L.cas8AcqAddr L.swp4RelAddr :=
  ⟨cas8Relax_ok P L h1, cas4Acq_ok P L h2, cas8Acq_ok P L h3, swp4Rel_ok P L h4⟩
end
end ProofLib.StdStartup
