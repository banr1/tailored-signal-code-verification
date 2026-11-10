/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.OpcodeExclusion
public import ProofLib.FsTrace
public import ProofLib.Process
public import ProofLib.SepLogic.SliceArray
public import ProofLib.SepLogic.WP.StepsProcessLse
public import ProofLib.SepLogic.WP.StepsProcessLlsc
public import ProofLib.SepLogic.WP.StepsProcessSyscalls
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.Hoare.Model
import ProofLib.SepLogic.Model

/-!
# Process, System-Register, and Atomic Step Lemmas

Re-exports LSE atomic, LL/SC exclusive, and syscall `SepWP` step lemmas, and provides
process-field preservation (`ProcessFieldsPreserved`, `NonSyscallPreserved`), pure-code execution
lifting (`SepWP.lift_noSyscalls`, `subroutine_ok_lift_pureWords_process`), and word-array focusing
lemmas (`pointsToWords64_focus*`).
-/

set_option autoImplicit false

@[expose] public section

namespace ProofLib

open Arm64

/-! ## Pure-Code Subroutine Lifting -/

/-- Non-memory-content process state preserved across pure (non-`SVC`, non-`MSR TPIDR_EL0`)
    instructions: `fs`, `trace`, `tpidrEl0`, `sigActions`, `brk`, `brkStart`, `physMemAvail`,
    and `mem.perm`. -/
abbrev ProcessFieldsPreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0 ∧
  sf.sigActions = s0.sigActions ∧ sf.brk = s0.brk ∧ sf.brkStart = s0.brkStart ∧
  sf.physMemAvail = s0.physMemAvail ∧
  (∀ a, sf.mem.perm a = s0.mem.perm a)

theorem ProcessFieldsPreserved.refl (s : State) : ProcessFieldsPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem ProcessFieldsPreserved.trans {s0 s1 s2 : State}
    (h01 : ProcessFieldsPreserved s0 s1) (h12 : ProcessFieldsPreserved s1 s2) :
    ProcessFieldsPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   h12.2.2.2.2.2.1.trans h01.2.2.2.2.2.1,
   h12.2.2.2.2.2.2.1.trans h01.2.2.2.2.2.2.1,
   fun a => (h12.2.2.2.2.2.2.2 a).trans (h01.2.2.2.2.2.2.2 a)⟩

private def projSB (s : State) :=
  (s.sigActions, s.brk, s.brkStart, s.physMemAvail, s.oracleIdx, s.sigAltStack)
private theorem projSB_adv (s : State) : projSB s.advancePC = projSB s := by cases s; rfl
private theorem projSB_pc (s : State) (p : BitVec 64) : projSB (s.setPC p) = projSB s := by cases s; rfl
private theorem projSB_w64 (s : State) (r : Reg) (v : BitVec 64) : projSB (s.writeReg64 r v) = projSB s := by
  cases s; cases r <;> rfl
private theorem projSB_w32 (s : State) (r : Reg) (v : BitVec 32) : projSB (s.writeReg32 r v) = projSB s :=
  projSB_w64 s r _
private theorem projSB_w (s : State) (w : Width) (r : Reg) (v : BitVec 64) : projSB (s.writeReg w r v) = projSB s :=
  projSB_w64 s r _
private theorem projSB_v128 (s : State) (r : BitVec 5) (v : BitVec 128) : projSB (s.writeVReg128 r v) = projSB s := by
  cases s; rfl
private theorem projSB_v64 (s : State) (r : BitVec 5) (v : BitVec 64) : projSB (s.writeVReg64 r v) = projSB s :=
  projSB_v128 s r _
private theorem projSB_v32 (s : State) (r : BitVec 5) (v : BitVec 32) : projSB (s.writeVReg32 r v) = projSB s :=
  projSB_v128 s r _
private theorem projSB_ps (s : State) (p : PState) : projSB (s.setPState p) = projSB s := by cases s; rfl
private theorem projSB_fp (s : State) (f : BitVec 32) : projSB (s.setFpsr f) = projSB s := by cases s; rfl
private theorem projSB_ofp (s : State) (f : BitVec 32) : projSB (s.orFpsr f) = projSB s := by cases s; rfl
private theorem projSB_st (s : State) (st : ExecStatus) : projSB (s.setStatus st) = projSB s := by cases s; rfl
private theorem projSB_wst (s : State) (st : ExecStatus) : projSB { s with status := st } = projSB s := by cases s; rfl
private theorem projSB_mem (s : State) (m : Memory) : projSB (s.setMem m) = projSB s := by cases s; rfl
private theorem projSB_tp (s : State) (v : BitVec 64) : projSB (setTpidrEl0 s v) = projSB s := by cases s; rfl
private theorem projSB_ex (s : State) : projSB s.stepExclOracle = projSB s := by cases s; rfl
private theorem projSB_as (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) :
    projSB (applySimdResult s rd r) = projSB s := by cases s; cases r <;> rfl
private theorem projSB_ass (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) (sat : Option (BitVec 32)) :
    projSB (applySimdSatResult s rd r sat) = projSB s := by cases s; cases r <;> cases sat <;> rfl
private theorem projSB_slr (sz : SimdMemSize) (m : Memory) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State), projSB (simdLoadRegs sz m n vt ea s) = projSB s
  | 0, _, _, _ => rfl
  | n + 1, _, _, s => (projSB_slr sz m n _ _ _).trans (projSB_v128 s _ _)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem execInst_projSB_of_not_isSvc0 {inst : Instr} (h : inst.isSvc0 = false) (s : State) :
    projSB (execInst inst s) = projSB s := by
  cases inst
  case system isHalt imm =>
    cases isHalt
    · by_cases himm : imm == 0#16
      · have heq : imm = 0#16 := of_decide_eq_true himm; subst heq; simp [Instr.isSvc0] at h
      · dsimp only [execInst, execInstWithSvc]; simp [himm, projSB_st]
    · dsimp only [execInst, execInstWithSvc]; by_cases himm : imm == 1#16 <;> simp [himm, projSB_st]
  case simdThreeSame q u size rm opcode rn rd =>
    dsimp only [execInst, execInstWithSvc]
    by_cases hop : opcode == 0b00011#5
    · simp only [hop, ↓reduceIte]
      rcases size with ⟨_ | _ | _ | _ | _, _⟩ <;> try omega
      all_goals (cases u <;> first | exact (projSB_adv _).trans (projSB_v128 _ _ _) | exact projSB_ass _ _ _ _)
    · simp only [hop, Bool.false_eq_true, ↓reduceIte, projSB_adv, projSB_v128, projSB_st, projSB_wst,
        projSB_as, projSB_ass, apply_ite projSB, ite_self]
  case ldpSimd _ _ _ addr | stpSimd _ _ _ addr | ldrSimd _ _ addr | strSimd _ _ addr =>
    dsimp only [execInst, execInstWithSvc]
    rcases evalAddrMode s addr with ⟨_, _ | ⟨_, _⟩⟩ <;>
      simp [projSB_adv, projSB_mem, projSB_v128, projSB_w64, projSB_st, apply_ite projSB]
  case ldr | ldrLit | str | ldp | stp | ldnp | stnp | addSubImm | logicalImm | moveWide | bitfield
     | logicalShift | addSubShift | addSubExt | addSubCarry | condCompareReg | condCompareImm
     | condSelect | dataProc1 | dataProc2 | dataProc3 =>
    cases s; dsimp only [execInst, execInstWithSvc, execLdr, execLdrLit, execStr, execLdp, execStp,
      execAddSubImm, execLogicalImm, execMoveWide, execBitfield, execLogicalShift, execAddSubShift,
      execAddSubExt, execAddSubCarry, execCondCompare, execCondSelect, execDataProc1, execDataProc2,
      execDataProc3]; (repeat' split) <;> rfl
  all_goals
    dsimp only [execInst, execInstWithSvc]
    simp only [projSB_adv, projSB_pc, projSB_w64, projSB_w32, projSB_w, projSB_v128, projSB_v64,
      projSB_v32, projSB_ps, projSB_fp, projSB_ofp, projSB_st, projSB_wst, projSB_mem, projSB_tp,
      projSB_ex, projSB_as, projSB_ass, projSB_slr, apply_ite projSB, ite_self]
    try (cases s; (repeat' split) <;> rfl)

theorem execInst_brk_oracle_of_not_isSvc0 {inst : Instr} (h : inst.isSvc0 = false) (s : State) :
    (execInst inst s).sigActions = s.sigActions ∧
    (execInst inst s).brk = s.brk ∧
    (execInst inst s).brkStart = s.brkStart ∧
    (execInst inst s).physMemAvail = s.physMemAvail ∧
    (execInst inst s).oracleIdx = s.oracleIdx ∧
    (execInst inst s).fs = s.fs := by
  have hne : inst ≠ .system false 0#16 := by rintro rfl; simp [Instr.isSvc0] at h
  have hsb := execInst_projSB_of_not_isSvc0 h s
  exact ⟨congrArg Prod.fst hsb, congrArg (fun p => p.2.1) hsb,
    congrArg (fun p => p.2.2.1) hsb, congrArg (fun p => p.2.2.2.1) hsb,
    congrArg (fun p => p.2.2.2.2.1) hsb, execInst_fs_of_ne_svc0 inst s hne⟩

theorem execInst_sigAltStack_of_not_isSvc0 {inst : Instr} (h : inst.isSvc0 = false) (s : State) :
    (execInst inst s).sigAltStack = s.sigAltStack :=
  congrArg (fun p => p.2.2.2.2.2) (execInst_projSB_of_not_isSvc0 h s)

theorem execInst_preserves_processFields {inst : Instr}
    (hsvc : inst.isSvc = false) (hmsr : inst.isMsrTpidrEl0 = false) (s : State) :
    ProcessFieldsPreserved s (execInst inst s) := by
  have hsvc0 : inst.isSvc0 = false := inst.isSvc0_eq_false_of_isSvc_eq_false hsvc
  obtain ⟨hsig, hbrk, hbrkS, hphys, _, hfs⟩ := execInst_brk_oracle_of_not_isSvc0 hsvc0 s
  exact ⟨hfs, execInst_trace_of_not_isSvc hsvc s,
    execInst_tpidrEl0_of_not_isMsrTpidrEl0 hmsr s, hsig, hbrk, hbrkS, hphys,
    execInst_perm_apply_of_not_isSvc0 hsvc0 s⟩

/-- Architectural kernel/process fields preserved by every non-`SVC #0` instruction:
    `trace`, `mem.perm`, `brk`, `brkStart`, `physMemAvail`, `oracleIdx`, `fs`, and
    no new `lazyFree` bytes (`s0.mem.isLazyFree a = false → sf.mem.isLazyFree a = false`). -/
protected def NonSyscallPreserved (s0 sf : State) : Prop :=
  sf.trace = s0.trace ∧
  sf.mem.perm = s0.mem.perm ∧
  sf.brk = s0.brk ∧
  sf.brkStart = s0.brkStart ∧
  sf.physMemAvail = s0.physMemAvail ∧
  (sf.oracleIdx = s0.oracleIdx ∧ ∀ a, s0.mem.isLazyFree a = false → sf.mem.isLazyFree a = false) ∧
  sf.fs = s0.fs

protected theorem NonSyscallPreserved.refl (s : State) : ProofLib.NonSyscallPreserved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, fun _ h => h⟩, rfl⟩

protected theorem NonSyscallPreserved.trans {s0 s1 s2 : State}
    (h01 : ProofLib.NonSyscallPreserved s0 s1) (h12 : ProofLib.NonSyscallPreserved s1 s2) :
    ProofLib.NonSyscallPreserved s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
   h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
   ⟨h12.2.2.2.2.2.1.1.trans h01.2.2.2.2.2.1.1,
    fun a h => h12.2.2.2.2.2.1.2 a (h01.2.2.2.2.2.1.2 a h)⟩,
   h12.2.2.2.2.2.2.trans h01.2.2.2.2.2.2⟩

protected theorem execInst_nonSyscallPreserved_of_not_isSvc0 {inst : Instr}
    (h : inst.isSvc0 = false) (s : State) :
    ProofLib.NonSyscallPreserved s (execInst inst s) := by
  obtain ⟨_, hbrk, hbrkS, hphys, hoi, hfs⟩ := execInst_brk_oracle_of_not_isSvc0 h s
  exact ⟨execInst_trace_of_not_isSvc0 h s, execInst_perm_of_not_isSvc0 h s,
    hbrk, hbrkS, hphys, ⟨hoi, fun _ => execInst_isLazyFree_false_of_not_isSvc0 h s⟩, hfs⟩

@[simp] theorem NonSyscallPreserved_mk (s0 : State)
    (regs : RegFile) (vregs : VRegFile) (sp pc : BitVec 64) (pstate : PState) (mem : Memory)
    (tpidrEl0 : BitVec 64) (fpsr : BitVec 32) (brkStart brk : BitVec 64) (fs : FsState)
    (oracle : Oracle) (oracleIdx : Nat) (exclFails : List Bool) (trace : List TraceEvent)
    (status : ExecStatus) (symtab : String → String → Option (BitVec 64))
    (sigActions : BitVec 32 → SigAction) (sigAltStack : SigAltStack) (physMemAvail : Nat) :
    ProofLib.NonSyscallPreserved s0
      (State.mk regs vregs sp pc pstate mem tpidrEl0 fpsr brkStart brk fs oracle oracleIdx
        exclFails trace status symtab sigActions sigAltStack physMemAvail) ↔
      (trace = s0.trace ∧ mem.perm = s0.mem.perm ∧ brk = s0.brk ∧
       brkStart = s0.brkStart ∧ physMemAvail = s0.physMemAvail ∧
       (oracleIdx = s0.oracleIdx ∧ ∀ a, s0.mem.isLazyFree a = false → mem.isLazyFree a = false) ∧
       fs = s0.fs) := Iff.rfl

@[simp, arm64_norm]
theorem execInst_mrs_tpidr_el0 (rt : Reg) (s : State) :
    execInst (.sysReg true 0x5e82#15 rt) s = (s.writeReg64 rt s.tpidrEl0).advancePC :=
  execInst_mrs_tpidr rt s

@[simp, arm64_norm]
theorem execSetTidAddress_eq (s : State) :
    execSetTidAddress s = (s.writeReg64 .x0 1#64).advancePC := rfl

@[simp, arm64_norm]
theorem NonSyscallPreserved_setTpidrEl0 (s0 s : State) (v : BitVec 64) :
    ProofLib.NonSyscallPreserved s0 (setTpidrEl0 s v) ↔ ProofLib.NonSyscallPreserved s0 s := by
  cases s; rfl

@[simp, arm64_norm]
theorem setMem_setTpidrEl0_NonSyscallPreserved (s0 s : State) (v : BitVec 64) (m : Memory) :
    ProofLib.NonSyscallPreserved s0 ((setTpidrEl0 s v).setMem m) ↔
      ProofLib.NonSyscallPreserved s0 (s.setMem m) := by
  cases s; rfl

@[simp, arm64_norm]
theorem fetch_withSvc (prog : Program) (svc : State → State) (pc : BitVec 64) :
    (prog.withSvc svc).fetch pc = prog.fetch pc := rfl

@[simp, arm64_norm]
theorem externAt?_withSvc (prog : Program) (svc : State → State) (pc : BitVec 64) :
    (prog.withSvc svc).externAt? pc = prog.externAt? pc := rfl

/-- Lift multi-step execution `Steps (prog.withSvc noSyscalls) sa sf` reaching a `.Running` state
    to `Steps prog sa sf` under `prog.svc = Syscall.standard`, establishing
    `ProofLib.NonSyscallPreserved sa sf`. -/
theorem steps_lift_noSyscalls {prog : Program}
    (hext : ∀ pc, prog.externAt? pc = none) (hsvc : prog.svc = Syscall.standard)
    {sa sf : State} (hsteps : Steps (prog.withSvc noSyscalls) sa sf) (hrun_f : sf.status = .Running) :
    Steps prog sa sf ∧ ProofLib.NonSyscallPreserved sa sf := by
  induction hsteps with
  | refl _ => exact ⟨Steps.refl _, ProofLib.NonSyscallPreserved.refl _⟩
  | @step s1 s2 _ h1 hrest ih =>
    have hrun2 : s2.status = .Running := by
      cases hrest with
      | refl => exact hrun_f
      | step hs2 _ => exact hs2.running_of_step
    cases h1 with
    | halt_unmapped _ _ _ => cases hrun2
    | extern _ hex _ _ => rw [externAt?_withSvc, hext] at hex; cases hex
    | extern_fault _ hex _ => rw [externAt?_withSvc, hext] at hex; cases hex
    | @exec inst hrun1 hfm =>
      have hfm' : prog.fetchMem s1.mem s1.pc = some inst := hfm
      have hnot_svc0 : inst.isSvc0 = false := by
        cases ht : inst.isSvc0 with
        | false => rfl
        | true =>
          cases inst with
          | system isHalt imm =>
            cases isHalt with
            | true => simp [Instr.isSvc0] at ht
            | false =>
              simp only [Instr.isSvc0, Bool.not_false, Bool.true_and, beq_iff_eq] at ht
              subst ht
              simp [Program.evalInst, Program.withSvc, execInstWithSvc_svc0, noSyscalls,
                State.setStatus] at hrun2
          | _ => simp [Instr.isSvc0] at ht
      have heval_no : (prog.withSvc noSyscalls).evalInst inst s1 = execInst inst s1 :=
        evalInst_eq_execInst_of_not_isSvc0 hnot_svc0 s1
      have heval_p : prog.evalInst inst s1 = execInst inst s1 :=
        Program.evalInst_eq_execInst inst s1 hsvc
      have hstep_p : Step prog s1 ((prog.withSvc noSyscalls).evalInst inst s1) := by
        rw [heval_no, ← heval_p]
        exact Step.exec hrun1 hfm'
      have hnsp1 : ProofLib.NonSyscallPreserved s1 ((prog.withSvc noSyscalls).evalInst inst s1) := by
        rw [heval_no]
        exact ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnot_svc0 s1
      obtain ⟨hsteps_rest, hnsp_rest⟩ := ih hrun_f
      exact ⟨Steps.step hstep_p hsteps_rest, hnsp1.trans hnsp_rest⟩

/-- Lift a total-correctness `SepWP` proved under `prog.withSvc noSyscalls` to `prog` (with
    `prog.svc = Syscall.standard`), strengthening the postcondition with
    `ProofLib.NonSyscallPreserved s0 sf` automatically. -/
theorem SepWP.lift_noSyscalls {prog : Program} {target_pc : BitVec 64} {s0 : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (hext : ∀ pc, prog.externAt? pc = none)
    (hwp : SepWP (prog.withSvc noSyscalls) target_pc s0 P post)
    (hsvc : prog.svc = Syscall.standard := by rfl) :
    SepWP prog target_pc s0 P (fun sf Q => ProofLib.NonSyscallPreserved s0 sf ∧ post sf Q) := by
  apply SepWP.of_reaches_pc
  intro R hmem hL
  have hL' : (prog.withSvc noSyscalls).CodeLoaded s0.mem := hL.of_base_code rfl rfl
  obtain ⟨sf, hsteps, hout⟩ := SepWP.to_reaches_pc hwp hmem hL'
  rcases hout with ⟨hpc, hrun, Q, hQ, hpost⟩ | ⟨_, hoom⟩
  · obtain ⟨hsteps_p, hnsp⟩ := steps_lift_noSyscalls hext hsvc hsteps hrun
    exact ⟨sf, hsteps_p, Or.inl ⟨hpc, hrun, Q, hQ, hnsp, hpost⟩⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-- Clear execute permission when `inCode = false`. -/
def stripPerm (inCode : Bool) (p : Perm) : Perm :=
  if inCode || !p.x then p else { p with w := false, x := false }

/-- Strip execute permission outside `keep` across all cells of `m`. -/
def stripExecOutside (keep : BitVec 64 → Bool) (m : Memory) : Memory :=
  ⟨fun a => match m.cells a with
    | some (some p, b) => some (some (stripPerm (keep a) p), b)
    | other => other⟩

/-- Strip execute permission outside `keep` on `s.mem`. -/
def stripS (keep : BitVec 64 → Bool) (s : State) : State := s.setMem (stripExecOutside keep s.mem)

/-- Code-range predicate `(a - prog.base).toNat < prog.code.length` for `prog`. -/
abbrev progKeep (prog : Program) (a : BitVec 64) : Bool :=
  decide ((a - prog.base).toNat < prog.code.length)

theorem strip_read8 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripExecOutside keep m).read8 a = m.read8 a := by
  dsimp only [stripExecOutside, Memory.read8]; cases m.cells a with | none => rfl | some cb => rcases cb with ⟨_ | _, _⟩ <;> rfl

theorem strip_isLazyFree (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripExecOutside keep m).isLazyFree a = m.isLazyFree a := by
  dsimp only [stripExecOutside, Memory.isLazyFree]
  rcases m.cells a with _ | ⟨_ | p, _⟩
  · rfl
  · rfl
  · simp only [stripPerm]; split <;> rfl

theorem strip_isAnon (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripExecOutside keep m).isAnon a = m.isAnon a := by
  dsimp only [stripExecOutside, Memory.isAnon]
  rcases m.cells a with _ | ⟨_ | p, _⟩
  · rfl
  · rfl
  · simp only [stripPerm]; split <;> rfl

theorem strip_readSized (keep : BitVec 64 → Bool) (m : Memory) (sz : MemWidth) (sg : Bool) (a : BitVec 64) :
    (stripExecOutside keep m).readSized sz sg a = m.readSized sz sg a := by
  cases sz <;> simp [Memory.readSized, Memory.read16, Memory.read32, Memory.read64, strip_read8]

theorem strip_readSimdSized (keep : BitVec 64 → Bool) (m : Memory) (sz : SimdMemSize) (a : BitVec 64) :
    (stripExecOutside keep m).readSimdSized sz a = m.readSimdSized sz a := by
  cases sz <;> simp [Memory.readSimdSized, Memory.read16, Memory.read32, Memory.read64, Memory.read128, strip_read8]

theorem strip_perm (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripExecOutside keep m).perm a =
      (m.perm a).map (stripPerm (keep a)) := by
  dsimp only [stripExecOutside, Memory.perm]
  rcases m.cells a with _ | ⟨_ | p, _⟩
  · rfl
  · rfl
  · rcases p with ⟨r, w, x, _, _⟩
    simp only [Option.map, Perm.rwx, stripPerm]; cases keep a <;> cases x <;> rfl

private theorem perm_rwx_of_perm_eq_some {m : Memory} {a : BitVec 64} {p : Perm}
    (hp : m.perm a = some p) : p.lazyFree = false ∧ p.anon = true := by
  unfold Memory.perm at hp
  cases hc : m.cells a with
  | none => simp [hc] at hp
  | some cb =>
    rcases cb with ⟨_ | q, _⟩ <;> simp [hc, Perm.rwx] at hp
    subst hp; exact ⟨rfl, rfl⟩

theorem strip_perm_props (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    ((stripExecOutside keep m).perm a).r = (m.perm a).r ∧
    (((stripExecOutside keep m).perm a).w && !((stripExecOutside keep m).perm a).x) =
      ((m.perm a).w && !(m.perm a).x) ∧
    ((stripExecOutside keep m).perm a).mapped = (m.perm a).mapped ∧
    ((stripExecOutside keep m).perm a = some Perm.rw ↔ m.perm a = some Perm.rw) := by
  rw [strip_perm]; unfold stripPerm Perm.rw
  generalize keep a = ic
  cases hp : m.perm a with
  | none => simp
  | some p =>
    have ⟨hlf_p, han_p⟩ := perm_rwx_of_perm_eq_some hp
    rcases p with ⟨r, w, x, lf, an⟩
    dsimp only at hlf_p han_p; subst hlf_p han_p
    cases ic <;> cases x <;> simp

theorem strip_perm_of_keep {keep : BitVec 64 → Bool} {m : Memory} {a : BitVec 64}
    (ha : keep a = true) :
    (stripExecOutside keep m).perm a = m.perm a := by
  rw [strip_perm]; unfold stripPerm; simp only [ha, Bool.true_or, ↓reduceIte, Option.map_id']

theorem strip_perm_x_imp {keep : BitVec 64 → Bool} {m : Memory} {a : BitVec 64} :
    ((stripExecOutside keep m).perm a).x = true →
    (m.perm a).x = true ∧ keep a = true := by
  rw [strip_perm]; unfold stripPerm
  generalize keep a = ic
  cases m.perm a with
  | none => simp
  | some p => rcases p with ⟨r, w, x, _, _⟩; cases ic <;> cases x <;> simp

private theorem strip_perm_in_code {prog : Program} {m : Memory} {a : BitVec 64}
    (ha : (a - prog.base).toNat < prog.code.length) :
    (stripExecOutside (progKeep prog) m).perm a = m.perm a :=
  strip_perm_of_keep (decide_eq_true ha)

private theorem strip_execOnlyIn (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (stripExecOutside (progKeep prog) m) := by
  intro a hx
  exact of_decide_eq_true (strip_perm_x_imp hx).2

theorem strip_allPerm_eq {keep : BitVec 64 → Bool} {m : Memory} {p : Option Perm → Bool}
    (hp : ∀ a, p ((stripExecOutside keep m).perm a) = p (m.perm a)) :
    ∀ (a : BitVec 64) (n : Nat), (stripExecOutside keep m).allPerm p a n = m.allPerm p a n
  | _, 0 => rfl
  | a, n + 1 => by simp only [Memory.allPerm, hp a, strip_allPerm_eq hp (a + 1#64) n]

theorem strip_allNoLazyFree (keep : BitVec 64 → Bool) (m : Memory) :
    ∀ (a : BitVec 64) (n : Nat), (stripExecOutside keep m).allNoLazyFree a n = m.allNoLazyFree a n
  | _, 0 => rfl
  | a, n + 1 => by simp only [Memory.allNoLazyFree, strip_isLazyFree, strip_allNoLazyFree keep m (a + 1#64) n]

theorem strip_canRead (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) (n : Nat) :
    (stripExecOutside keep m).canRead a n = m.canRead a n := by
  simp only [Memory.canRead, strip_allPerm_eq (fun x => (strip_perm_props keep m x).1), strip_allNoLazyFree]

theorem strip_canWrite (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) (n : Nat) :
    (stripExecOutside keep m).canWrite a n = m.canWrite a n :=
  strip_allPerm_eq (fun x => (strip_perm_props keep m x).2.1) a n

theorem strip_write8 (keep : BitVec 64 → Bool) (m : Memory) (addr : BitVec 64) (val : BitVec 8) :
    (stripExecOutside keep m).write8 addr val = stripExecOutside keep (m.write8 addr val) := by
  ext a; simp only [stripExecOutside, Memory.write8, Memory.rawPerm]
  by_cases ha : a = addr
  · subst ha; simp only [↓reduceIte]
    rcases m.cells a with _ | ⟨_ | p, _⟩
    · rfl
    · rfl
    · simp only [stripPerm]; split <;> rfl
  · simp [ha]

theorem strip_write16 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) (v : BitVec 16) :
    (stripExecOutside keep m).write16 a v = stripExecOutside keep (m.write16 a v) := by
  simp [Memory.write16, strip_write8]
theorem strip_write32 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) (v : BitVec 32) :
    (stripExecOutside keep m).write32 a v = stripExecOutside keep (m.write32 a v) := by
  simp [Memory.write32, strip_write8]
theorem strip_write64 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    (stripExecOutside keep m).write64 a v = stripExecOutside keep (m.write64 a v) := by
  simp [Memory.write64, strip_write8]
theorem strip_writeSized (keep : BitVec 64 → Bool) (m : Memory) (sz : MemWidth) (a v : BitVec 64) :
    (stripExecOutside keep m).writeSized sz a v = stripExecOutside keep (m.writeSized sz a v) := by
  cases sz <;> simp [Memory.writeSized, strip_write8, strip_write16, strip_write32, strip_write64]
theorem strip_writeSimdSized (keep : BitVec 64 → Bool) (m : Memory) (sz : SimdMemSize) (a : BitVec 64) (v : BitVec 128) :
    (stripExecOutside keep m).writeSimdSized sz a v = stripExecOutside keep (m.writeSimdSized sz a v) := by
  cases sz <;> simp [Memory.writeSimdSized, Memory.write128, strip_write8, strip_write16, strip_write32, strip_write64]
theorem strip_simdStoreRegs (keep : BitVec 64 → Bool) (sz : SimdMemSize) (vals : BitVec 5 → BitVec 128) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (m : Memory),
      simdStoreRegs sz vals n vt ea (stripExecOutside keep m) = stripExecOutside keep (simdStoreRegs sz vals n vt ea m)
  | 0, _, _, _ => rfl
  | n + 1, vt, ea, m => by
    simp only [simdStoreRegs, strip_writeSimdSized, strip_simdStoreRegs keep sz vals n]

private def isStrippedXo (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) : Bool :=
  !keep a &&
    match m.perm a with
    | some p => !p.r && p.x
    | none => false

private def xoGuard (keep : BitVec 64 → Bool) (m : Memory) : SepProp :=
  ⟨fun h =>
    (∀ a, if isStrippedXo keep m a then
        (∃ b, h.phys a = some (.protNone b)) ∨ h.phys a = some .protNoneLazy
      else h.phys a = none) ∧
    (∀ γ k, h.auth γ k = none) ∧
    (∀ γ k, h.frag γ k = none) ∧
    (∀ a, h.mapped a = false)⟩

private theorem strip_satisfies_xoGuard (keep : BitVec 64 → Bool) (m : Memory) (P : SepProp)
    (hP : m ⊨ P) : stripExecOutside keep m ⊨ P ∗ xoGuard keep m := by
  rw [SepProp.satisfies_iff] at hP ⊢
  unfold Heap.Matches at hP ⊢
  simp only [SepProp.holds_sepConj_iff]
  rcases hP with ⟨h, hPh, hm⟩
  let hxo : Heap :=
    { phys := fun a =>
        if isStrippedXo keep m a then
          if m.isLazyFree a then some .protNoneLazy else some (.protNone (m.read8 a))
        else none }
  have hnot_xo : ∀ a c, h.phys a = some c → isStrippedXo keep m a = false := by
    intro a c hc
    have hcell := hm.1 a c hc
    unfold isStrippedXo
    cases hp : m.perm a with
    | none => simp
    | some p =>
      rcases p with ⟨r, w, x, lf, an⟩
      cases c <;> simp only [hp, Perm.rw, Perm.protNone, Option.some.injEq, Perm.mk.injEq,
        Option.r] at hcell
      · rcases hcell with ⟨_, ⟨_, _, rfl, _, _⟩, _⟩; simp
      · rcases hcell with ⟨_, rfl, _⟩; simp
      · rcases hcell with ⟨_, ⟨_, _, rfl, _, _⟩, _⟩; simp
      · rcases hcell with ⟨_, _, rfl, _, _⟩; simp
      · rcases hcell with ⟨_, _, rfl, _, _⟩; simp
  have hdisj : h.Disjoint hxo := by
    unfold Heap.Disjoint
    refine ⟨fun a => ?_, fun _ _ => Or.inr rfl, fun _ _ => Or.inr rfl,
      fun _ _ _ _ h' => ?_, fun _ => Or.inr rfl⟩
    · cases hc : h.phys a with
      | none => exact Or.inl rfl
      | some c =>
        have hfx := hnot_xo a c hc
        exact Or.inr (Or.inl (by dsimp [hxo]; simp [hfx]))
    · rcases h' with ⟨_, hf⟩ | ⟨ha, _⟩
      · cases hf
      · cases ha
  have hG : (xoGuard keep m).holds hxo := by
    refine ⟨fun a => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
    by_cases hfx : isStrippedXo keep m a
    · by_cases hlf : m.isLazyFree a <;> simp [hxo, hfx, hlf]
    · simp [hxo, hfx]
  refine ⟨h.union hxo, ⟨h, hxo, hdisj, rfl, hPh, hG⟩, ?_, ?_, ?_⟩
  · intro a c hu
    unfold Heap.union at hu; dsimp only at hu
    cases hc : h.phys a with
    | some c' =>
      rw [hc] at hu; injection hu with hu'; subst hu'
      have hcell := hm.1 a c' hc
      have hp := strip_perm_props keep m a
      cases c' with
      | rw b =>
        simp only [strip_read8, hp.2.2.2, strip_isLazyFree]; exact hcell
      | ro b =>
        simp only [strip_read8, hp.1, strip_isLazyFree]; exact hcell
      | protNone b =>
        refine ⟨(strip_read8 keep m a).trans hcell.1, ?_, (strip_isLazyFree keep m a).trans hcell.2.2⟩
        rw [strip_perm, hcell.2.1]
        unfold stripPerm Perm.protNone
        cases keep a <;> rfl
      | lazy =>
        simp only [hp.2.2.2]; exact hcell
      | protNoneLazy =>
        rw [strip_perm, hcell]
        unfold stripPerm Perm.protNone
        cases keep a <;> rfl
    | none =>
      rw [hc] at hu; dsimp [hxo] at hu
      by_cases hfx : isStrippedXo keep m a
      · simp only [hfx, ↓reduceIte] at hu
        have hsp_pn : (stripExecOutside keep m).perm a = some Perm.protNone := by
          rw [strip_perm]
          unfold isStrippedXo at hfx
          unfold stripPerm Perm.protNone
          generalize keep a = ic at hfx ⊢
          cases hp : m.perm a with
          | none => simp [hp] at hfx
          | some p =>
            have ⟨hlf_p, han_p⟩ := perm_rwx_of_perm_eq_some hp
            rw [hp] at hfx; rcases p with ⟨r, w, x, lf, an⟩
            dsimp only at hlf_p han_p; subst hlf_p han_p
            cases ic <;> cases r <;> cases w <;> cases x <;> simp_all
        by_cases hlf : m.isLazyFree a = true
        · simp only [hlf, ↓reduceIte] at hu; injection hu with hu'; subst hu'; exact hsp_pn
        · simp only [hlf, Bool.false_eq_true, ↓reduceIte] at hu; injection hu with hu'; subst hu'
          exact ⟨strip_read8 keep m a, hsp_pn,
            (strip_isLazyFree keep m a).trans (Bool.eq_false_iff.mpr hlf)⟩
      · simp only [hfx, Bool.false_eq_true, ↓reduceIte] at hu; cases hu
  · obtain ⟨bound, hb⟩ := hm.2.1
    refine ⟨bound, fun γ hγ k => ?_⟩
    obtain ⟨ha, hf⟩ := hb γ hγ k
    exact ⟨by unfold Heap.union; dsimp only [hxo]; rw [ha],
           by unfold Heap.union; dsimp only [hxo]; rw [hf]⟩
  · intro a hma
    unfold Heap.union at hma; dsimp only [hxo] at hma
    rw [Bool.or_false] at hma
    rw [(strip_perm_props keep m a).2.2.1, strip_isAnon]
    exact hm.2.2 a hma

private theorem unstrip_satisfies_xoGuard (keep : BitVec 64 → Bool) (m0 mf : Memory) (Q : SepProp)
    (hperm : ∀ a, mf.perm a = m0.perm a)
    (hQ : stripExecOutside keep mf ⊨ Q ∗ xoGuard keep m0) : mf ⊨ Q := by
  rw [SepProp.satisfies_iff] at hQ ⊢
  unfold Heap.Matches at hQ ⊢
  simp only [SepProp.holds_sepConj_iff] at hQ
  rcases hQ with ⟨_, ⟨hq, hxo, hdisj, rfl, hQh, hG⟩, hmu⟩
  unfold Heap.Disjoint at hdisj
  have hperm_pn_of_not_xo : ∀ a, isStrippedXo keep m0 a = false →
      (stripExecOutside keep mf).perm a = some Perm.protNone → mf.perm a = some Perm.protNone := by
    intro a hfx0 hp_f
    have hfx_f : isStrippedXo keep mf a = false := by
      unfold isStrippedXo at hfx0 ⊢; rw [hperm a]; exact hfx0
    rw [strip_perm] at hp_f
    unfold isStrippedXo at hfx_f
    unfold stripPerm at hp_f
    unfold Perm.protNone at hp_f ⊢
    generalize keep a = ic at hfx_f hp_f
    cases hpm : mf.perm a with
    | none => rw [hpm] at hp_f; cases hp_f
    | some p =>
      have ⟨hlf_p, han_p⟩ := perm_rwx_of_perm_eq_some hpm
      rw [hpm] at hfx_f hp_f; rcases p with ⟨r, w, x, lf, an⟩
      dsimp only at hlf_p han_p; subst hlf_p han_p
      cases ic <;> cases r <;> cases w <;> cases x <;> simp_all
  refine ⟨hq, hQh, ?_, ?_, ?_⟩
  · intro a c hc
    have hu : (hq.union hxo).phys a = some c := by unfold Heap.union; dsimp only; rw [hc]
    have hcell := hmu.1 a c hu
    have hp := strip_perm_props keep mf a
    have hnot_xo0 : ∀ (hro_ne : ∀ b0, c ≠ .ro b0), isStrippedXo keep m0 a = false := by
      intro hro_ne
      by_cases hfx : isStrippedXo keep m0 a
      · have hga := hG.1 a; simp only [hfx, ↓reduceIte] at hga
        rcases hdisj.1 a with h1 | h2 | ⟨b0, h3, _⟩
        · rw [hc] at h1; cases h1
        · rcases hga with ⟨b', hb'⟩ | hb' <;> rw [hb'] at h2 <;> cases h2
        · rw [hc] at h3; injection h3 with h3'; exact False.elim (hro_ne b0 h3')
      · exact Bool.eq_false_iff.mpr hfx
    cases c with
    | rw b =>
      rw [strip_read8, hp.2.2.2, strip_isLazyFree] at hcell; exact hcell
    | ro b =>
      rw [strip_read8, hp.1, strip_isLazyFree] at hcell; exact hcell
    | protNone b =>
      rw [strip_read8, strip_isLazyFree] at hcell
      exact ⟨hcell.1, hperm_pn_of_not_xo a (hnot_xo0 (fun _ h => by cases h)) hcell.2.1, hcell.2.2⟩
    | lazy =>
      rw [hp.2.2.2] at hcell; exact hcell
    | protNoneLazy =>
      exact hperm_pn_of_not_xo a (hnot_xo0 (fun _ h => by cases h)) hcell
  · obtain ⟨bound, hb⟩ := hmu.2.1
    refine ⟨bound, fun γ hγ k => ?_⟩
    obtain ⟨ha, hf⟩ := hb γ hγ k
    unfold Heap.union at ha hf; dsimp only at ha hf
    refine ⟨?_, ?_⟩
    · cases hqa : hq.auth γ k with
      | none => rfl
      | some oa => rw [hqa] at ha; cases ha
    · cases hqf : hq.frag γ k with
      | none => rfl
      | some v => rw [hqf] at hf; cases hf
  · intro a hma
    have hu : (hq.union hxo).mapped a = true := by
      unfold Heap.union; dsimp only; rw [hma, Bool.true_or]
    have hm' := hmu.2.2 a hu
    rwa [(strip_perm_props keep mf a).2.2.1, strip_isAnon] at hm'

/-- Transport a framed separation-logic satisfaction `m0 ⊨ P ∗ R` across `stripExecOutside keep`
    and restore `mf ⊨ Q ∗ R` once `mf.perm` agrees with `m0.perm`. -/
theorem strip_frame (keep : BitVec 64 → Bool) {m0 : Memory} {P R : SepProp}
    (hpre : m0 ⊨ P ∗ R) :
    ∃ R_view : SepProp,
      (stripExecOutside keep m0 ⊨ P ∗ R_view) ∧
      ∀ {Q : SepProp} {mf : Memory},
        (∀ a, mf.perm a = m0.perm a) →
        (stripExecOutside keep mf ⊨ Q ∗ R_view) →
        (mf ⊨ Q ∗ R) := by
  refine ⟨R ∗ xoGuard keep m0, ?_, ?_⟩
  · rw [← sepConj_assoc]
    exact strip_satisfies_xoGuard keep m0 (P ∗ R) hpre
  · intro Q mf hperm hpost'
    rw [← sepConj_assoc] at hpost'
    exact unstrip_satisfies_xoGuard keep m0 mf (Q ∗ R) hperm hpost'

private theorem ss_mem (p : BitVec 64 → Bool) (s : State) : (stripS p s).mem = stripExecOutside p s.mem := by cases s; rfl
private theorem ss_r64 (p : BitVec 64 → Bool) (s : State) (r : Reg) : (stripS p s).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem ss_r32 (p : BitVec 64 → Bool) (s : State) (r : Reg) : (stripS p s).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem ss_rr (p : BitVec 64 → Bool) (s : State) (w : Width) (r : Reg) : (stripS p s).readReg w r = s.readReg w r := by cases s; rfl
private theorem ss_rv128 (p : BitVec 64 → Bool) (s : State) (r : BitVec 5) : (stripS p s).readVReg128 r = s.readVReg128 r := by cases s; rfl
private theorem ss_rv128_eta (p : BitVec 64 → Bool) (s : State) : (stripS p s).readVReg128 = s.readVReg128 := by funext r; cases s; rfl
private theorem ss_rv64 (p : BitVec 64 → Bool) (s : State) (r : BitVec 5) : (stripS p s).readVReg64 r = s.readVReg64 r := by cases s; rfl
private theorem ss_rv32 (p : BitVec 64 → Bool) (s : State) (r : BitVec 5) : (stripS p s).readVReg32 r = s.readVReg32 r := by cases s; rfl
private theorem ss_pc (p : BitVec 64 → Bool) (s : State) : (stripS p s).pc = s.pc := by cases s; rfl
private theorem ss_sp (p : BitVec 64 → Bool) (s : State) : (stripS p s).sp = s.sp := by cases s; rfl
private theorem ss_ps (p : BitVec 64 → Bool) (s : State) : (stripS p s).pstate = s.pstate := by cases s; rfl
private theorem ss_fp (p : BitVec 64 → Bool) (s : State) : (stripS p s).fpsr = s.fpsr := by cases s; rfl
private theorem ss_tp (p : BitVec 64 → Bool) (s : State) : (stripS p s).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
private theorem ss_ewf (p : BitVec 64 → Bool) (s : State) : (stripS p s).exclWillFail = s.exclWillFail := by cases s; rfl
private theorem ss_csp (p : BitVec 64 → Bool) (s : State) (r : Reg) : checkRegSPAligned (stripS p s) r = checkRegSPAligned s r := by
  cases s; cases r <;> rfl
private theorem ss_casp (p : BitVec 64 → Bool) (s : State) (a : AddrMode) : checkAddrSPAligned (stripS p s) a = checkAddrSPAligned s a := by
  cases s; cases a <;> rfl
private theorem ss_eam (p : BitVec 64 → Bool) (s : State) (a : AddrMode) : evalAddrMode (stripS p s) a = evalAddrMode s a := by
  cases s; cases a <;> rfl
private theorem ss_adv (p : BitVec 64 → Bool) (s : State) : (stripS p s).advancePC = stripS p s.advancePC := by cases s; rfl
private theorem ss_spc (p : BitVec 64 → Bool) (s : State) (q : BitVec 64) : (stripS p s).setPC q = stripS p (s.setPC q) := by cases s; rfl
private theorem ss_w64 (p : BitVec 64 → Bool) (s : State) (r : Reg) (v : BitVec 64) :
    (stripS p s).writeReg64 r v = stripS p (s.writeReg64 r v) := by cases s; cases r <;> rfl
private theorem ss_w32 (p : BitVec 64 → Bool) (s : State) (r : Reg) (v : BitVec 32) :
    (stripS p s).writeReg32 r v = stripS p (s.writeReg32 r v) := ss_w64 p s r _
private theorem ss_w (p : BitVec 64 → Bool) (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (stripS p s).writeReg w r v = stripS p (s.writeReg w r v) := ss_w64 p s r _
private theorem ss_wv128 (p : BitVec 64 → Bool) (s : State) (r : BitVec 5) (v : BitVec 128) :
    (stripS p s).writeVReg128 r v = stripS p (s.writeVReg128 r v) := by cases s; rfl
private theorem ss_wv64 (p : BitVec 64 → Bool) (s : State) (r : BitVec 5) (v : BitVec 64) :
    (stripS p s).writeVReg64 r v = stripS p (s.writeVReg64 r v) := ss_wv128 p s r _
private theorem ss_wv32 (p : BitVec 64 → Bool) (s : State) (r : BitVec 5) (v : BitVec 32) :
    (stripS p s).writeVReg32 r v = stripS p (s.writeVReg32 r v) := ss_wv128 p s r _
private theorem ss_sps (p : BitVec 64 → Bool) (s : State) (q : PState) : (stripS p s).setPState q = stripS p (s.setPState q) := by cases s; rfl
private theorem ss_sfp (p : BitVec 64 → Bool) (s : State) (f : BitVec 32) : (stripS p s).setFpsr f = stripS p (s.setFpsr f) := by cases s; rfl
private theorem ss_sofp (p : BitVec 64 → Bool) (s : State) (f : BitVec 32) : (stripS p s).orFpsr f = stripS p (s.orFpsr f) := by cases s; rfl
private theorem ss_sst (p : BitVec 64 → Bool) (s : State) (st : ExecStatus) : (stripS p s).setStatus st = stripS p (s.setStatus st) := by cases s; rfl
private theorem ss_wst (p : BitVec 64 → Bool) (s : State) (st : ExecStatus) :
    { stripS p s with status := st } = stripS p { s with status := st } := by cases s; rfl
private theorem ss_stp (p : BitVec 64 → Bool) (s : State) (v : BitVec 64) : setTpidrEl0 (stripS p s) v = stripS p (setTpidrEl0 s v) := by cases s; rfl
private theorem ss_sex (p : BitVec 64 → Bool) (s : State) : (stripS p s).stepExclOracle = stripS p s.stepExclOracle := by cases s; rfl
private theorem ss_smem (p : BitVec 64 → Bool) (s : State) (m : Memory) :
    (stripS p s).setMem (stripExecOutside p m) = stripS p (s.setMem m) := by cases s; rfl
private theorem ss_as (p : BitVec 64 → Bool) (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) :
    applySimdResult (stripS p s) rd r = stripS p (applySimdResult s rd r) := by cases s; cases r <;> rfl
private theorem ss_ass (p : BitVec 64 → Bool) (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) (sat : Option (BitVec 32)) :
    applySimdSatResult (stripS p s) rd r sat = stripS p (applySimdSatResult s rd r sat) := by cases s; cases r <;> cases sat <;> rfl
private theorem ss_slr (p : BitVec 64 → Bool) (sz : SimdMemSize) (m : Memory) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State),
      simdLoadRegs sz (stripExecOutside p m) n vt ea (stripS p s) = stripS p (simdLoadRegs sz m n vt ea s)
  | 0, _, _, _ => rfl
  | n + 1, _, _, s => by simp only [simdLoadRegs, strip_readSimdSized, ss_slr p sz m n, ss_wv128]
private theorem ss_ite (p : BitVec 64 → Bool) (c : Prop) [Decidable c] (a b : State) :
    (if c then stripS p a else stripS p b) = stripS p (if c then a else b) := by split <;> rfl
private theorem ss_regs (p : BitVec 64 → Bool) (s : State) : (stripS p s).regs = s.regs := by cases s; rfl
private theorem ss_vregs (p : BitVec 64 → Bool) (s : State) : (stripS p s).vregs = s.vregs := by cases s; rfl
private theorem ss_bs (p : BitVec 64 → Bool) (s : State) : (stripS p s).brkStart = s.brkStart := by cases s; rfl
private theorem ss_brk (p : BitVec 64 → Bool) (s : State) : (stripS p s).brk = s.brk := by cases s; rfl
private theorem ss_fs (p : BitVec 64 → Bool) (s : State) : (stripS p s).fs = s.fs := by cases s; rfl
private theorem ss_orc (p : BitVec 64 → Bool) (s : State) : (stripS p s).oracle = s.oracle := by cases s; rfl
private theorem ss_oi (p : BitVec 64 → Bool) (s : State) : (stripS p s).oracleIdx = s.oracleIdx := by cases s; rfl
private theorem ss_ef (p : BitVec 64 → Bool) (s : State) : (stripS p s).exclFails = s.exclFails := by cases s; rfl
private theorem ss_tr (p : BitVec 64 → Bool) (s : State) : (stripS p s).trace = s.trace := by cases s; rfl
private theorem ss_st (p : BitVec 64 → Bool) (s : State) : (stripS p s).status = s.status := by cases s; rfl
private theorem ss_sym (p : BitVec 64 → Bool) (s : State) : (stripS p s).symtab = s.symtab := by cases s; rfl
private theorem ss_sig (p : BitVec 64 → Bool) (s : State) : (stripS p s).sigActions = s.sigActions := by cases s; rfl
private theorem ss_sas (p : BitVec 64 → Bool) (s : State) : (stripS p s).sigAltStack = s.sigAltStack := by cases s; rfl
private theorem ss_pma (p : BitVec 64 → Bool) (s : State) : (stripS p s).physMemAvail = s.physMemAvail := by cases s; rfl
private theorem ss_mk (p : BitVec 64 → Bool) {rg vr sp pc ps m tp fp bs b fs o oi ef tr st sym sig sas pma} :
    State.mk rg vr sp pc ps (stripExecOutside p m) tp fp bs b fs o oi ef tr st sym sig sas pma =
      stripS p (State.mk rg vr sp pc ps m tp fp bs b fs o oi ef tr st sym sig sas pma) := rfl

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
theorem execInst_stripS {inst : Instr} (h : inst.isSvc0 = false) (keep : BitVec 64 → Bool) (s : State) :
    execInst inst (stripS keep s) = stripS keep (execInst inst s) := by
  cases inst
  case system isHalt imm =>
    cases isHalt
    · by_cases himm : imm == 0#16
      · have heq : imm = 0#16 := of_decide_eq_true himm; subst heq; simp [Instr.isSvc0] at h
      · dsimp only [execInst, execInstWithSvc]; simp [himm, ss_sst]
    · dsimp only [execInst, execInstWithSvc]; by_cases himm : imm == 1#16 <;> simp [himm, ss_sst]
  case simdThreeSame q u size rm opcode rn rd =>
    by_cases hop : opcode == 0b00011#5
    · have hsz : size = 0#2 ∨ size = 1#2 ∨ size = 2#2 ∨ size = 3#2 := by clear h; revert size; decide
      rcases hsz with rfl | rfl | rfl | rfl <;> cases u <;>
        (dsimp only [execInst, execInstWithSvc]; simp only [hop, ↓reduceIte, ss_rv128];
         split <;> simp only [ss_wv128, ss_adv, ss_ass])
    · dsimp only [execInst, execInstWithSvc]
      simp only [hop, Bool.false_eq_true, ↓reduceIte, ss_rv128, ss_regs, ss_vregs, ss_sp, ss_pc, ss_ps,
        ss_mem, ss_tp, ss_fp, ss_bs, ss_brk, ss_fs, ss_orc, ss_oi, ss_ef, ss_tr, ss_st, ss_sym, ss_sig, ss_sas, ss_pma,
        ss_mk, ss_adv, ss_wv128, ss_sst, ss_wst, ss_as, ss_ass, ss_ite]
  case st1SinglePost q rm opcode sBit size rn vt =>
    dsimp only [execInst, execInstWithSvc]
    by_cases h0 : opcode.extractLsb' 1 2 == 0#2 <;> by_cases h1 : opcode.extractLsb' 1 2 == 1#2 <;>
      by_cases hs0 : size.extractLsb' 0 1 == 0#1 <;>
      simp only [h0, h1, hs0, Bool.false_eq_true, ↓reduceIte, ss_mem, ss_regs, ss_vregs, ss_sp, ss_pc,
        ss_ps, ss_tp, ss_fp, ss_bs, ss_brk, ss_fs, ss_orc, ss_oi, ss_ef, ss_tr, ss_st, ss_sym, ss_sig, ss_sas, ss_pma,
        ss_mk, ss_r64, ss_rv128, ss_csp, strip_canWrite, strip_write8, strip_write16, strip_write32,
        strip_write64, ss_smem, ss_w64, ss_adv, ss_sst, ss_ite]
  case simdLdStMulti isLoad q size selem rn postIdx rm vt =>
    dsimp only [execInst, execInstWithSvc]
    by_cases hbad : (size == 3#2 && !q || !(selem == 2 || selem == 3 || selem == 4)) = true
    · simp only [hbad, ↓reduceIte, ss_regs, ss_vregs, ss_sp, ss_pc, ss_ps, ss_mem, ss_tp, ss_fp,
        ss_bs, ss_brk, ss_fs, ss_orc, ss_oi, ss_ef, ss_tr, ss_st, ss_sym, ss_sig, ss_sas, ss_pma, ss_mk, ss_wst]
    · by_cases h3 : selem ≥ 3 <;> by_cases h4 : selem ≥ 4 <;>
        simp only [hbad, h3, h4, Bool.false_eq_true, ↓reduceIte, ss_r64, ss_rv128_eta, ss_mem, ss_csp,
          strip_canRead, strip_canWrite, strip_readSimdSized, strip_simdStoreRegs,
          ss_w64, ss_wv128, ss_adv, ss_smem, ss_sst, ss_ite]
  case ldr _ _ _ _ addr | str _ _ addr | ldp _ _ _ _ addr | stp _ _ _ addr
     | ldpSimd _ _ _ addr | stpSimd _ _ _ addr | ldrSimd _ _ addr | strSimd _ _ addr =>
    dsimp only [execInst, execInstWithSvc, execLdr, execStr, execLdp, execStp]
    rw [ss_casp, ss_eam]
    rcases evalAddrMode s addr with ⟨_, _ | ⟨_, _⟩⟩ <;>
      simp only [ss_mem, ss_r64, ss_rv128, strip_canRead, strip_canWrite, strip_readSized,
        strip_readSimdSized, strip_writeSized, strip_writeSimdSized,
        ss_w64, ss_w, ss_wv128, ss_smem, ss_adv, ss_sst, ss_ite]
  case addSubImm | logicalImm | moveWide | bitfield | extr | logicalShift | addSubShift
     | addSubExt | addSubCarry | condCompareReg | condCompareImm | condSelect
     | dataProc1 | dataProc2 | dataProc3 =>
    dsimp only [execInst, execInstWithSvc, execAddSubImm, execLogicalImm, execMoveWide, execBitfield,
      execLogicalShift, execAddSubShift, execAddSubExt, execAddSubCarry, execCondCompare,
      execCondSelect, execDataProc1, execDataProc2, execDataProc3]
    simp only [ss_r64, ss_r32, ss_rr, ss_pc, ss_sp, ss_ps, ss_w64, ss_w32, ss_w, ss_sps, ss_adv, ss_ite]
    try ((repeat' split) <;> simp only [ss_w64, ss_w32, ss_w, ss_sps, ss_adv, ss_ite])
  all_goals
    dsimp only [execInst, execInstWithSvc, execLdrLit, execLdp, execStp, evalAddrMode]
    simp only [ss_mem, ss_regs, ss_vregs, ss_bs, ss_brk, ss_fs, ss_orc, ss_oi, ss_ef, ss_tr, ss_st,
      ss_sym, ss_sig, ss_sas, ss_pma, ss_mk, ss_r64, ss_r32, ss_rr, ss_rv128, ss_rv128_eta, ss_rv64, ss_rv32,
      ss_pc, ss_sp, ss_ps, ss_fp, ss_tp, ss_ewf, ss_csp, ss_casp, ss_eam,
      strip_canRead, strip_canWrite, strip_readSized, strip_readSimdSized,
      strip_write8, strip_write16, strip_write32, strip_write64, strip_writeSized, strip_writeSimdSized,
      strip_simdStoreRegs, ss_slr,
      ss_adv, ss_spc, ss_w64, ss_w32, ss_w, ss_wv128, ss_wv64, ss_wv32,
      ss_sps, ss_sfp, ss_sofp, ss_sst, ss_wst, ss_stp, ss_sex, ss_smem, ss_as, ss_ass, ss_ite]

open Process (pureWordsProg)

private theorem readWordOff_bounds {P : Program} {off : Nat} {w : BitVec 32}
    (h : P.readWordOff off = some w) : off % 4 = 0 ∧ off + 3 < P.code.length := by
  unfold Program.readWordOff at h
  by_cases hmod : off % 4 = 0
  · simp only [hmod, ne_eq, not_true_eq_false, ↓reduceIte] at h
    rcases hd : P.code.drop off with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;>
      rw [hd] at h <;> try contradiction
    have hdl : (P.code.drop off).length = P.code.length - off := List.length_drop
    rw [hd] at hdl; simp only [List.length_cons] at hdl; exact ⟨hmod, by omega⟩
  · simp only [hmod, ne_eq, not_false_eq_true, ↓reduceIte] at h; contradiction

private theorem codeLoaded_pureWordsProg {P : Program} {m : Memory} {addr : BitVec 64} {words : List (BitVec 32)}
    (hP : P.CodeLoaded m) (hw : P.hasWords addr words) (hne : words ≠ []) :
    (pureWordsProg addr words).CodeLoaded m := by
  let off := (addr - P.base).toNat
  have hpos : 0 < words.length := List.length_pos_iff.mpr hne
  have hoff_al : off % 4 = 0 := (readWordOff_bounds (hw.2.1 0 hpos)).1
  have hlt_end : off + 4 * (words.length - 1) + 3 < P.code.length :=
    (readWordOff_bounds (hw.2.1 (words.length - 1) (by omega))).2
  have hoff_end : off + 4 * words.length ≤ P.code.length := by omega
  have hbase_al := hP.aligned; have hno_wrap := hP.no_wrap
  have haddr_nat : addr.toNat = P.base.toNat + off := by
    have : off < P.code.length := by omega
    dsimp [off] at this ⊢; bv_omega
  have hclen : (pureWordsProg addr words).code.length = 4 * words.length :=
    Program.length_flatMap_wordToBytesLE words
  refine Program.CodeLoaded.intro (by change addr.toNat % 4 = 0; omega)
    (by change addr.toNat + (pureWordsProg addr words).code.length ≤ 2 ^ 64; omega) fun k hk => ?_
  rw [hclen] at hk
  have hkP : off + k < P.code.length := by omega
  have haddr_k : (pureWordsProg addr words).base + BitVec.ofNat 64 k = P.base + BitVec.ofNat 64 (off + k) := by
    change addr + BitVec.ofNat 64 k = P.base + BitVec.ofNat 64 (off + k)
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hc_eq : P.code[off + k] = (pureWordsProg addr words).code[k]'(hclen ▸ hk) := by
    have hq := Program.code_getElem?_of_hasWordsOff hw k hk
    rw [List.getElem?_eq_getElem hkP] at hq
    change some P.code[off + k] = (pureWordsProg addr words).code[k]? at hq
    rw [List.getElem?_eq_getElem (hclen ▸ hk)] at hq; exact Option.some.inj hq
  rw [haddr_k, ← hc_eq]
  exact ⟨hP.byte_eq (off + k) hkP, hP.perm_eq (off + k) hkP, hP.isLazyFree_eq (off + k) hkP⟩

private theorem strip_codeLoaded {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (stripExecOutside (progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hin : (prog.base + BitVec.ofNat 64 i - prog.base).toNat < prog.code.length := by
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hi
  rw [strip_read8, strip_perm_in_code hin, strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem steps_lift_pureWords {P : Program} {addr : BitVec 64} {words : List (BitVec 32)}
    (hall : (pureWordsProg addr words).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true)
    (hext : ∀ pc, P.externAt? pc = none)
    {s1' sf' : State} (hsteps : Steps (pureWordsProg addr words) s1' sf') (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = stripS (progKeep (pureWordsProg addr words)) s1 →
      (pureWordsProg addr words).CodeLoaded s1.mem →
      ∃ sf, Steps P s1 sf ∧ sf' = stripS (progKeep (pureWordsProg addr words)) sf ∧ ProcessFieldsPreserved s1 sf := by
  let prog₀ := pureWordsProg addr words
  induction hsteps with
  | refl _ => intro s1 hs1 _; exact ⟨s1, Steps.refl s1, hs1, ProcessFieldsPreserved.refl s1⟩
  | @step sa' sb' _ hstep hrest ih =>
    intro s1 hsa hL1
    have hL1' : prog₀.CodeLoaded sa'.mem := by rw [hsa, ss_mem]; exact strip_codeLoaded hL1
    cases hstep with
    | halt_unmapped _ _ _ =>
      cases hrest with
      | refl => cases hrun_f
      | step hs1 _ => exact absurd hs1.running_of_step (fun h => by cases h)
    | extern _ hext0 _ _ | extern_fault _ hext0 _ =>
      simp [pureWordsProg, Program.ofWords, Program.externAt?, Program.hookAtOff?] at hext0
    | @exec inst hrun' hfm' =>
      have hp_i := Program.fetchMem_of_allInstrs hall hL1' (by rw [hsa, ss_mem]; exact strip_execOnlyIn _ _) sa'.pc inst hfm'
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp_i; rcases hp_i with ⟨hsvc, hmsr⟩
      have hsvc0 : inst.isSvc0 = false := inst.isSvc0_eq_false_of_isSvc_eq_false hsvc
      have hrun1 : s1.status = .Running := by rw [hsa] at hrun'; cases s1; exact hrun'
      have hfmP : P.fetchMem s1.mem s1.pc = some inst := by
        rw [hsa, ss_pc, ss_mem] at hfm'; unfold Program.fetchMem at hfm' ⊢
        have he0 : prog₀.externAt? s1.pc = none := rfl
        rw [he0] at hfm'; rw [hext s1.pc]
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfm' ⊢
        by_cases hal_pc : s1.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfm' ⊢
          split at hfm'; · contradiction
          rename_i hce'
          have hce : s1.mem.canExec s1.pc 4 = true := by
            simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
            unfold Memory.canExec at hce' ⊢; rw [Memory.allPerm_iff] at hce' ⊢
            intro k hk; have hxk := hce' k hk
            rwa [strip_perm_in_code (strip_execOnlyIn prog₀ s1.mem _ hxk)] at hxk
          have hr32 : (stripExecOutside (progKeep prog₀) s1.mem).read32 s1.pc = s1.mem.read32 s1.pc := by
            simp [Memory.read32, strip_read8]
          rw [hr32] at hfm'; simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hfm'
        · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfm'; contradiction
      let s2 := P.evalInst inst s1
      have hstepP : Step P s1 s2 := Step.exec hrun1 hfmP
      have hs2_eq : s2 = execInst inst s1 := evalInst_eq_execInst_of_not_isSvc0 hsvc0 s1
      have hsb_eq : prog₀.evalInst inst sa' = stripS (progKeep prog₀) s2 := by
        rw [evalInst_eq_execInst_of_not_isSvc0 hsvc0, hsa, execInst_stripS hsvc0, ← hs2_eq]
      have hpf12 : ProcessFieldsPreserved s1 s2 := hs2_eq ▸ execInst_preserves_processFields hsvc hmsr s1
      obtain ⟨sf, hstepsP, hsf_eq, hpf2f⟩ := ih hrun_f s2 hsb_eq (hstepP.codeLoaded hL1)
      exact ⟨sf, Steps.step hstepP hstepsP, hsf_eq, hpf12.trans hpf2f⟩

/-- Lift `subroutine_ok (pureWordsProg addr words) addr spec` to any hook-free program `P`
    containing `words` at `addr` when `words` excludes `SVC` and `MSR TPIDR_EL0`, strengthening the
    postcondition with `ProcessFieldsPreserved s0 sf`. -/
theorem subroutine_ok_lift_pureWords_process {α : Type}
    {P : Program} {addr : BitVec 64} {words : List (BitVec 32)} {spec : Spec α}
    (h_sub : subroutine_ok (pureWordsProg addr words) addr spec)
    (h_all : (pureWordsProg addr words).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true)
    (h_words : P.hasWords addr words) (h_no_ext : ∀ pc, P.externAt? pc = none)
    (h_panic : spec.onPanic = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_exit : spec.onExit = fun _ _ _ _ => ⌜False⌝ := by rfl)
    (h_oom : spec.onOom = fun _ _ _ => ⌜False⌝ := by rfl)
    (h_ne : words ≠ [] := by decide)
    (h_pre_mem : ∀ x (s : State) (m : Memory),
      spec.pre x (s.setMem m) = spec.pre x s := by intro _ s _; cases s; simp [State.setMem])
    (h_post_mem : ∀ x (s0 sf : State) (m0 mf : Memory),
      spec.post x (s0.setMem m0) (sf.setMem mf) = spec.post x s0 sf := by
        intro _ s0 sf _ _; cases s0; cases sf; simp [State.setMem]) :
    subroutine_ok P addr
      { spec with post := fun x s0 sf => ⌜ProcessFieldsPreserved s0 sf⌝ ∗ spec.post x s0 sf } := by
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro x R s0 hpc hrun hpre hsp hLP
  let prog₀ := pureWordsProg addr words
  let kp₀ := progKeep prog₀
  have hL0 : prog₀.CodeLoaded s0.mem := codeLoaded_pureWordsProg hLP h_words h_ne
  let s0' := stripS kp₀ s0
  have hpre' : s0'.mem ⊨ spec.pre x s0' ∗ (R ∗ xoGuard kp₀ s0.mem) := by
    dsimp [s0', stripS]
    rw [h_pre_mem, State.mem_setMem, ← sepConj_assoc]
    exact strip_satisfies_xoGuard kp₀ s0.mem _ hpre
  obtain ⟨sf', hsteps', hout'⟩ := reaches_outcome_iff.1
    (subroutine_ok_iff.1 h_sub x (R ∗ xoGuard kp₀ s0.mem) s0' ((ss_pc kp₀ s0).trans hpc)
      (by cases s0; exact hrun) hpre' (by cases s0; exact hsp))
    (by rw [ss_mem]; exact strip_codeLoaded hL0)
  rcases hout' with ⟨hret', hcc', hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · obtain ⟨sf, hstepsP, hsf_eq, hpf⟩ := steps_lift_pureWords h_all h_no_ext hsteps' hret'.2.2 s0 rfl hL0
    refine ⟨sf, hstepsP, Or.inl ⟨?_, ?_, ?_⟩⟩
    · rcases hret' with ⟨hr_pc, hr_sp, hr_st⟩
      rw [hsf_eq, ss_pc] at hr_pc; rw [hsf_eq, ss_sp] at hr_sp
      have hrun_sf : sf.status = .Running := by rw [hsf_eq] at hr_st; cases sf; exact hr_st
      exact ⟨hr_pc.trans (ss_r64 kp₀ s0 Reg.lr), hr_sp.trans (ss_sp kp₀ s0), hrun_sf⟩
    · rw [hsf_eq] at hcc'; rcases hcc' with ⟨hsp_cc, hcs⟩
      rw [ss_sp] at hsp_cc
      exact ⟨hsp_cc.trans (ss_sp kp₀ s0), by cases s0; cases sf; exact hcs⟩
    · rw [hsf_eq] at hpost'; dsimp [s0', stripS] at hpost'
      rw [h_post_mem, State.mem_setMem, ← sepConj_assoc] at hpost'
      have hpost'' : sf.mem ⊨ spec.post x s0 sf ∗ R :=
        unstrip_satisfies_xoGuard kp₀ s0.mem sf.mem _ hpf.2.2.2.2.2.2.2 hpost'
      rw [sepConj_assoc, satisfies_pure_sepConj]; exact ⟨hpf, hpost''⟩
  · rw [h_panic] at hp; exact False.elim (not_satisfies_false_sepConj hp)
  · rw [h_exit] at he; exact False.elim (not_satisfies_false_sepConj he)
  · rw [h_oom] at ho; exact False.elim (not_satisfies_false_sepConj ho)

/-- Lift any running `Steps Program.pureMem` trace starting from `stripS keep s0` back to a
    running `Steps Program.pureMem` trace from `s0`, establishing `ProofLib.NonSyscallPreserved s0 sf`
    whenever every word at an address with `keep pc = true` in a frozen-preserving memory `m`
    decodes to a non-`SVC #0` instruction. -/
theorem steps_pureMem_lift_stripS (keep : BitVec 64 → Bool) {m₀ : Memory}
    (h_no_svc : ∀ (m : Memory) (pc : BitVec 64) (inst : Instr),
      m₀.KeepsFrozen m →
      keep pc = true → keep (pc + 1#64) = true →
      keep (pc + 2#64) = true → keep (pc + 3#64) = true →
      Program.pureMem.fetchMem m pc = some inst → inst.isSvc0 = false) :
    ∀ {s0 s' sf' : State},
      s' = stripS keep s0 →
      m₀.KeepsFrozen s0.mem →
      Steps Program.pureMem s' sf' →
      sf'.status = .Running →
      ∃ sf : State,
        sf' = stripS keep sf ∧
        Steps Program.pureMem s0 sf ∧
        ProofLib.NonSyscallPreserved s0 sf := by
  intro s0 s' sf' hs' hkf hsteps hrun_f
  induction hsteps generalizing s0 with
  | refl _ =>
    subst hs'
    exact ⟨s0, rfl, Steps.refl s0, ProofLib.NonSyscallPreserved.refl s0⟩
  | @step s1' s2' sf' hstep hrest ih =>
    subst hs'
    have hrun2' : s2'.status = .Running := by
      cases hrest with
      | refl _ => exact hrun_f
      | step hs _ => exact hs.status_running
    cases hstep with
    | halt_unmapped _ _ _ => simp at hrun2'
    | extern _ h_ext _ _ => nomatch h_ext
    | extern_fault _ h_ext _ => nomatch h_ext
    | exec hrun1' hfetch' =>
      rename_i inst
      have hrun1 : s0.status = .Running := by cases s0; exact hrun1'
      rw [ss_pc, ss_mem] at hfetch'
      unfold Program.fetchMem at hfetch'
      by_cases hce' : (stripExecOutside keep s0.mem).canExec s0.pc 4 = true
      · have hr32 : (stripExecOutside keep s0.mem).read32 s0.pc = s0.mem.read32 s0.pc := by
          simp [Memory.read32, strip_read8]
        simp only [hce', Bool.not_true, Bool.false_eq_true, ↓reduceIte, hr32] at hfetch'
        have hx4 :
            ((stripExecOutside keep s0.mem).perm s0.pc).x = true ∧
            ((stripExecOutside keep s0.mem).perm (s0.pc + 1#64)).x = true ∧
            ((stripExecOutside keep s0.mem).perm (s0.pc + 2#64)).x = true ∧
            ((stripExecOutside keep s0.mem).perm (s0.pc + 3#64)).x = true := by
          simpa [Memory.canExec, Memory.allPerm, Bool.and_eq_true, BitVec.add_assoc] using hce'
        obtain ⟨hx0, hk0⟩ := strip_perm_x_imp hx4.1
        obtain ⟨hx1, hk1⟩ := strip_perm_x_imp hx4.2.1
        obtain ⟨hx2, hk2⟩ := strip_perm_x_imp hx4.2.2.1
        obtain ⟨hx3, hk3⟩ := strip_perm_x_imp hx4.2.2.2
        have hce : s0.mem.canExec s0.pc 4 = true := by
          simp [Memory.canExec, Memory.allPerm, BitVec.add_assoc, hx0, hx1, hx2, hx3]
        have hfetch : Program.pureMem.fetchMem s0.mem s0.pc = some inst := by
          unfold Program.fetchMem
          simpa [hce] using hfetch'
        have hns : inst.isSvc0 = false := h_no_svc s0.mem s0.pc inst hkf hk0 hk1 hk2 hk3 hfetch
        rw [evalInst_pureMem] at hrest hrun2' ih
        have hstep_s0 : Step Program.pureMem s0 (execInst inst s0) :=
          evalInst_pureMem inst s0 ▸ Step.exec hrun1 hfetch
        have hcomm : execInst inst (stripS keep s0) = stripS keep (execInst inst s0) :=
          execInst_stripS hns keep s0
        have hnsp1 : ProofLib.NonSyscallPreserved s0 (execInst inst s0) :=
          ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hns s0
        have hkf2 : m₀.KeepsFrozen (execInst inst s0).mem := hkf.trans hstep_s0.keepsFrozen
        obtain ⟨sf, hsf_eq, hsteps_rest, hnsp_rest⟩ := ih hcomm hkf2 hrun_f
        exact ⟨sf, hsf_eq, Steps.step hstep_s0 hsteps_rest, hnsp1.trans hnsp_rest⟩
      · simp [hce'] at hfetch'

/-- Linear-time scan checking that no contiguous 4-byte window in `bs` encodes `SVC #0`
    (`0xd4000001`). -/
protected def noSvc0Window : List (BitVec 8) → Bool
  | b0 :: b1 :: b2 :: b3 :: tl =>
    !isSvc0Word (b3 ++ b2 ++ b1 ++ b0) && ProofLib.noSvc0Window (b1 :: b2 :: b3 :: tl)
  | _ => true

protected theorem noSvc0Window_getElem :
    ∀ (bs : List (BitVec 8)) (i : Nat),
      ProofLib.noSvc0Window bs = true →
      (hi : i + 3 < bs.length) →
      isSvc0Word (bs[i + 3] ++ bs[i + 2] ++ bs[i + 1] ++ bs[i]) = false
  | [], _, _, hi => absurd hi (by simp)
  | [_], _, _, hi => absurd hi (by simp)
  | [_, _], _, _, hi => absurd hi (by simp)
  | [_, _, _], _, _, hi => absurd hi (by simp)
  | b0 :: b1 :: b2 :: b3 :: tl, 0, h, _ => by
    unfold ProofLib.noSvc0Window at h
    rcases Bool.and_eq_true_iff.mp h with ⟨h0, _⟩
    cases isSvc0Word (b3 ++ b2 ++ b1 ++ b0) <;> simp_all
  | _ :: b1 :: b2 :: b3 :: tl, i + 1, h, hi => by
    unfold ProofLib.noSvc0Window at h
    rcases Bool.and_eq_true_iff.mp h with ⟨_, htl⟩
    exact ProofLib.noSvc0Window_getElem (b1 :: b2 :: b3 :: tl) i htl (by simp at hi ⊢; omega)

protected theorem holdsBytes_rx_not_isSvc0 {m₀ m : Memory} {base pc : BitVec 64} {bs : List (BitVec 8)}
    {inst : Instr}
    (hb : Obj.HoldsBytes m₀ base bs (fun _ => Perm.rx))
    (hkf : m₀.KeepsFrozen m)
    (hwrap : base.toNat + bs.length + 4 ≤ 2 ^ 64)
    (hwin : ProofLib.noSvc0Window bs = true)
    (hr0 : InRegion base bs.length pc)
    (hr3 : InRegion base bs.length (pc + 3#64))
    (hfetch : Program.pureMem.fetchMem m pc = some inst) :
    inst.isSvc0 = false := by
  have hb' : Obj.HoldsBytes m base bs (fun _ => Perm.rx) := by
    intro i hi
    obtain ⟨hr, hp, hnlf⟩ := hb i hi
    have hf : m₀.Frozen (base + BitVec.ofNat 64 i) := by
      unfold Memory.Frozen; rw [hp]; rfl
    obtain ⟨mr, mp, mlf, _⟩ := hkf _ hf
    exact ⟨mr.trans hr, mp.trans hp, mlf.trans hnlf⟩
  let i := (pc - base).toNat
  have hi3 : i + 3 < bs.length := by
    unfold InRegion at hr0 hr3
    dsimp [i]
    bv_omega
  have ha0 : pc + 0#64 = base + BitVec.ofNat 64 i := by
    unfold InRegion at hr0; dsimp [i]; bv_omega
  have ha1 : pc + 1#64 = base + BitVec.ofNat 64 (i + 1) := by
    unfold InRegion at hr0 hr3; dsimp [i]; bv_omega
  have ha2 : pc + 2#64 = base + BitVec.ofNat 64 (i + 2) := by
    unfold InRegion at hr0 hr3; dsimp [i]; bv_omega
  have ha3 : pc + 3#64 = base + BitVec.ofNat 64 (i + 3) := by
    unfold InRegion at hr0 hr3; dsimp [i]; bv_omega
  have hr32 : m.read32 pc = bs[i + 3] ++ bs[i + 2] ++ bs[i + 1] ++ bs[i] := by
    dsimp (config := { zetaHave := true }) only [Memory.read32]
    rw [ha0, (hb' i (by omega)).1, ha1, (hb' (i + 1) (by omega)).1,
        ha2, (hb' (i + 2) (by omega)).1, ha3, (hb' (i + 3) (by omega)).1]
    rfl
  unfold Program.fetchMem at hfetch
  split at hfetch
  · simp at hfetch
  · split at hfetch
    · simp at hfetch
    · split at hfetch
      · simp at hfetch
      · rw [hr32] at hfetch
        exact decode_not_isSvc0 hfetch (ProofLib.noSvc0Window_getElem bs i hwin hi3)

/-! ## Word-Array Index Focusing -/

/-- Focus word `i` out of `ptr ↦₆₄* ws` as `((ptr + BitVec.ofNat 64 (8 * i)) ↦₆₄ ws.getD i 0#64)`
    paired with the prefix and suffix `pointsToArray` slices. -/
theorem pointsToWords64_focus (ptr : BitVec 64) (ws : List (BitVec 64)) (i : Nat)
    (hi : i < ws.length) :
    (ptr ↦₆₄* ws) = ((ptr + BitVec.ofNat 64 (8 * i)) ↦₆₄ ws.getD i 0#64) ∗
      (pointsToArray 8 (· ↦₆₄ ·) ptr (ws.take i) ∗
       pointsToArray 8 (· ↦₆₄ ·) (ptr + BitVec.ofNat 64 (8 * (i + 1))) (ws.drop (i + 1))) := by
  rw [pointsToWords64_eq_pointsToArray]; exact pointsToArray_focus 8 (· ↦₆₄ ·) ptr ws i hi

/-- Variant of `pointsToWords64_focus` using `BitVec` offset `ptr + (idx <<< 3)` for a bounded
    64-bit index `idx`. -/
theorem pointsToWords64_focus_idx (ptr : BitVec 64) (ws : List (BitVec 64))
    (idx : BitVec 64) (hi : idx.toNat < ws.length)
    (hsh : 8 * idx.toNat < 2 ^ 64) :
    (ptr ↦₆₄* ws) =
      ((ptr + (idx <<< 3)) ↦₆₄ ws.getD idx.toNat 0#64) ∗
        (pointsToArray 8 (· ↦₆₄ ·) ptr (ws.take idx.toNat) ∗
         pointsToArray 8 (· ↦₆₄ ·) (ptr + BitVec.ofNat 64 (8 * (idx.toNat + 1)))
           (ws.drop (idx.toNat + 1))) := by
  have hm : idx.toNat * 8 < 2 ^ 64 := by omega
  have hshift : idx <<< 3 = BitVec.ofNat 64 (8 * idx.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hm,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsh, Nat.mul_comm]
  rw [pointsToWords64_eq_pointsToArray, hshift]
  exact pointsToArray_focus 8 (· ↦₆₄ ·) ptr ws idx.toNat hi

/-- Focus the adjacent word pair `(i, i + 1)` out of `ptr ↦₆₄* ws` for `ldp` / two-slot reads. -/
theorem pointsToWords64_focus_pair (ptr : BitVec 64) (ws : List (BitVec 64)) (i : Nat)
    (hi : i + 1 < ws.length) :
    (ptr ↦₆₄* ws) = ((ptr + BitVec.ofNat 64 (8 * i)) ↦₆₄ ws.getD i 0#64) ∗
      (((ptr + BitVec.ofNat 64 (8 * i)) + 8#64) ↦₆₄ ws.getD (i + 1) 0#64) ∗
      ((ptr ↦₆₄* ws.take i) ∗
       ((((ptr + BitVec.ofNat 64 (8 * i)) + 8#64) + 8#64) ↦₆₄* ws.drop (i + 2))) := by
  have hi0 : i < ws.length := by omega
  conv => lhs; rw [← List.take_append_drop i ws, List.drop_eq_getElem_cons hi0,
    List.drop_eq_getElem_cons hi]
  rw [pointsToWords64_append, List.length_take_of_le (by omega),
    pointsToWords64_cons, pointsToWords64_cons]
  simp only [List.getD, getElem?_pos, hi0, hi, Option.getD_some]; ac_rfl

end ProofLib
