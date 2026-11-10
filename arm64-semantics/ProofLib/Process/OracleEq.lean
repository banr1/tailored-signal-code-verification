/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Invariant

/-!
# Oracle Preservation Across Standard Syscalls

Proves that `Syscall.standard` and hook-free `Program` execution preserve `State.oracle`
(`evalSvc_standard_oracle`, `evalInst_oracle_of_standard`, `Step.oracle_eq_of_standard`,
`Steps.oracle_eq_of_standard`). Note that `evalInst_oracle_of_standard` splits on `Instr` directly
to avoid generating the `execInstWithSvc` match splitter.
-/

@[expose] public section

set_option autoImplicit false

namespace Arm64

open Arm64.Process ProofLib

private def getOra (s : State) : Oracle := s.oracle

private theorem ora_adv (s : State) : getOra s.advancePC = getOra s := by cases s; rfl
private theorem ora_pc (s : State) (p : BitVec 64) : getOra (s.setPC p) = getOra s := by cases s; rfl
private theorem ora_w64 (s : State) (r : Reg) (v : BitVec 64) : getOra (s.writeReg64 r v) = getOra s := by cases s; cases r <;> rfl
private theorem ora_w32 (s : State) (r : Reg) (v : BitVec 32) : getOra (s.writeReg32 r v) = getOra s := ora_w64 s r _
private theorem ora_w (s : State) (w : Width) (r : Reg) (v : BitVec 64) : getOra (s.writeReg w r v) = getOra s := ora_w64 s r _
private theorem ora_v128 (s : State) (r : BitVec 5) (v : BitVec 128) : getOra (s.writeVReg128 r v) = getOra s := by cases s; rfl
private theorem ora_v64 (s : State) (r : BitVec 5) (v : BitVec 64) : getOra (s.writeVReg64 r v) = getOra s := ora_v128 s r _
private theorem ora_v32 (s : State) (r : BitVec 5) (v : BitVec 32) : getOra (s.writeVReg32 r v) = getOra s := ora_v128 s r _
private theorem ora_ps (s : State) (p : PState) : getOra (s.setPState p) = getOra s := by cases s; rfl
private theorem ora_fp (s : State) (f : BitVec 32) : getOra (s.setFpsr f) = getOra s := by cases s; rfl
private theorem ora_ofp (s : State) (f : BitVec 32) : getOra (s.orFpsr f) = getOra s := by cases s; rfl
private theorem ora_st (s : State) (st : ExecStatus) : getOra (s.setStatus st) = getOra s := by cases s; rfl
private theorem ora_mem (s : State) (m : Memory) : getOra (s.setMem m) = getOra s := by cases s; rfl
private theorem ora_ex (s : State) : getOra s.stepExclOracle = getOra s := by cases s; rfl
private theorem ora_as (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) :
    getOra (applySimdResult s rd r) = getOra s := by cases s; cases r <;> rfl
private theorem ora_ass (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) (sat : Option (BitVec 32)) :
    getOra (applySimdSatResult s rd r sat) = getOra s := by cases s; cases r <;> cases sat <;> rfl
private theorem ora_slr (sz : SimdMemSize) (m : Memory) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State), getOra (simdLoadRegs sz m n vt ea s) = getOra s
  | 0, _, _, _ => rfl | n + 1, _, _, s => (ora_slr sz m n _ _ _).trans (ora_v128 s _ _)
private theorem ora_fs (s : State) (f) : getOra (s.setFs f) = getOra s := by cases s; rfl
private theorem ora_tr (s : State) (e) : getOra (s.appendTrace e) = getOra s := by cases s; rfl
private theorem ora_pma (s : State) (v) : getOra (s.setPhysMemAvail v) = getOra s := by cases s; rfl
private theorem ora_next (s : State) : getOra s.nextOracle = getOra s := by cases s; rfl
private theorem ora_brk (s : State) (b) : getOra (s.setBrk b) = getOra s := by cases s; rfl
private theorem ora_sig (s : State) (sig act) : getOra (s.setSigAction sig act) = getOra s := by cases s; rfl
private theorem ora_sas (s : State) (sas) : getOra (s.setSigAltStack sas) = getOra s := by cases s; rfl

private theorem ora_ppoll (s : State) : getOra (execPpoll s) = getOra s := by
  unfold execPpoll; dsimp only; rcases evalPpollEntries s.fs s.mem (s.readReg64 .x0) (s.readReg32 .x1).toNat 0 0 with _ | ⟨m', count⟩ <;>
    simp (config := { decide := false }) only [apply_ite getOra, ora_adv, ora_w64, ora_mem, ora_st, ite_self]
private theorem ora_applyOpenVerdict (s : State) (v : OpenVerdict) : getOra (applyOpenVerdict s v) = getOra s := by
  cases s; rcases v with ⟨_, _, _ | _⟩ | _ | _ <;> rfl
private theorem ora_openat (s : State) : getOra (execOpenat s) = getOra s := by
  unfold execOpenat; dsimp only; cases checkOpenFlags (s.readReg32 .x2) <;>
    (try cases readCString s.mem (s.readReg64 .x1)) <;> simp only [ora_applyOpenVerdict, ora_adv, ora_w64, ora_st]
private theorem ora_write (s : State) : getOra (execWrite s) = getOra s := by
  unfold execWrite; dsimp only; cases s.fs.fds ((s.readReg32 .x0).zeroExtend 64) <;>
    simp (config := { decide := false }) only [apply_ite getOra, ora_adv, ora_w64, ora_st, ora_fs, ora_tr, ite_self]

private theorem ora_readCommon (s : State) (b : Bool) : getOra (execReadCommon s b) = getOra s := by
  unfold execReadCommon; dsimp only; cases s.fs.fds ((s.readReg32 .x0).zeroExtend 64) <;> cases b <;>
    simp (config := { decide := false }) only [apply_ite getOra, ora_adv, ora_w64, ora_mem, ora_st, ora_fs, ite_self]
private theorem ora_read (s : State) : getOra (execRead s) = getOra s := ora_readCommon s false
private theorem ora_pread64 (s : State) : getOra (execPread64 s) = getOra s := ora_readCommon s true
set_option linter.unusedSimpArgs false in
private theorem ora_lseek (s : State) : getOra (execLseek s) = getOra s := by
  unfold execLseek; dsimp only; cases s.fs.fds ((s.readReg32 .x0).zeroExtend 64)
  · simp (config := { decide := false }) only [apply_ite getOra, ora_adv, ora_w64, ora_st, ite_self]
  · simp (config := { decide := false }) only [apply_ite getOra, ora_adv, ora_w64, ora_st, ora_fs, ite_self]
    (repeat' split) <;>
      simp (config := { decide := false }) only [apply_ite getOra, ora_adv, ora_w64, ora_st, ora_fs, ite_self]
private theorem ora_rwvFrame : ProofLib.RwvFrame (fun a b => getOra b = getOra a) :=
  ProofLib.RwvFrame.eqOn getOra ora_w64 ora_adv ora_st (fun s _ _ => by cases s; rfl)
private theorem ora_readv (s : State) : getOra (execReadv s) = getOra s :=
  ProofLib.execReadv_preserves ora_rwvFrame ora_read s
private theorem ora_writev (s : State) : getOra (execWritev s) = getOra s :=
  ProofLib.execWritev_preserves ora_rwvFrame ora_write s

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem standardEntry_io_oracle (s : State) :
    ∀ p ∈ Syscall.stdioTable ++ Syscall.fileIoOnlyTable ++ Syscall.pollTable, getOra (p.2 s) = getOra s := by
  simp only [Syscall.stdioTable, Syscall.fileIoOnlyTable, Syscall.pollTable,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    (try dsimp (config := { zetaHave := true }) only [execFcntl, execIoctl, execClose, execFstat]
     (repeat' split) <;>
       (try simp (config := { decide := false }) only [ora_ppoll, ora_openat, ora_write, ora_read, ora_pread64, ora_lseek,
          ora_readv, ora_writev, ora_adv, ora_w64, ora_mem, ora_st, ora_fs, ora_tr, ora_pma, ora_next, ora_brk, ora_sig]
        try (cases s; dsimp only [getOra]; rfl)))

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem standardEntry_rest_oracle (s : State) :
    ∀ p ∈ Syscall.allocTable ++ Syscall.signalsTable ++ Syscall.timeTable ++ Syscall.randomTable ++ Syscall.miscTable,
      getOra (p.2 s) = getOra s := by
  simp only [Syscall.allocTable, Syscall.signalsTable, Syscall.timeTable, Syscall.randomTable, Syscall.miscTable,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    (try dsimp (config := { zetaHave := true }) only [execRtSigprocmask, execRtSigaction, execSigaltstack,
       execTkill, execTgkill, execSchedGetaffinity, execClockGettime, execMmap, execBrk, execMunmap,
       execMremap, execMprotect, execMadvise, execGetrandom]
     (repeat' split) <;>
       (try simp (config := { decide := false }) only [ora_adv, ora_w64, ora_mem, ora_st, ora_fs,
          ora_tr, ora_pma, ora_next, ora_brk, ora_sig, ora_sas]
        try (cases s; dsimp only [getOra]; rfl)))

private theorem standardEntry_oracle (s : State) : ∀ p ∈ Syscall.standardTable, getOra (p.2 s) = getOra s := by
  intro p hp; simp only [Syscall.standardTable, List.mem_append] at hp
  rcases hp with ((((((h | h) | h) | h) | h) | h) | h) | h
  · exact standardEntry_io_oracle s p (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h))))
  · exact standardEntry_io_oracle s p (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h))))
  · exact standardEntry_io_oracle s p (List.mem_append.mpr (Or.inr h))
  · exact standardEntry_rest_oracle s p (by simp [List.mem_append, h])
  · exact standardEntry_rest_oracle s p (by simp [List.mem_append, h])
  · exact standardEntry_rest_oracle s p (by simp [List.mem_append, h])
  · exact standardEntry_rest_oracle s p (by simp [List.mem_append, h])
  · exact standardEntry_rest_oracle s p (by simp [List.mem_append, h])

private theorem sysc_standard_oracle (s : State) : getOra (Syscall.standard s) = getOra s := by
  unfold Syscall.standard Syscall.dispatch; split
  · rename_i nr fn h; exact standardEntry_oracle s (nr, fn) (List.mem_of_find?_eq_some h)
  · exact ora_st s _

set_option linter.unusedSimpArgs false in
private theorem evalSvc_standard_getOra (s : State) : getOra (evalSvc Syscall.standard s) = getOra s := by
  unfold evalSvc; dsimp only; have hfn := sysc_standard_oracle s
  cases h : (Syscall.standard s).status <;> (try simp only [ora_st, hfn]) <;> (dsimp only [getOra] at hfn ⊢; exact hfn)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
/-- Under `prog.svc = Syscall.standard`, executing any instruction preserves `State.oracle`. -/
theorem evalInst_oracle_of_standard {prog : Program} (hsvc : prog.svc = Syscall.standard)
    (inst : Instr) (s : State) : (prog.evalInst inst s).oracle = s.oracle := by
  change getOra (prog.evalInst inst s) = getOra s
  unfold Program.evalInst; rw [hsvc]; cases inst
  case system isHalt imm =>
    cases isHalt
    · by_cases himm : imm == 0#16
      · dsimp only [execInstWithSvc]; simp [himm, evalSvc_standard_getOra, sysc_standard_oracle]
      · dsimp only [execInstWithSvc]; simp [himm, ora_st]
    · dsimp only [execInstWithSvc]; by_cases himm : imm == 1#16 <;> simp [himm, ora_st]
  case simdThreeSame q u size rm opcode rn rd =>
    dsimp only [execInstWithSvc]
    by_cases hop : opcode == 0b00011#5
    · simp only [hop, ↓reduceIte]; rcases size with ⟨_ | _ | _ | _ | _, _⟩ <;> try omega
      all_goals (cases u <;> first | exact (ora_adv _).trans (ora_v128 _ _ _) | exact ora_ass _ _ _ _)
    · simp (config := { decide := false }) only [hop, Bool.false_eq_true, ↓reduceIte, ora_adv,
        ora_v128, ora_st, ora_as, ora_ass, apply_ite getOra, ite_self]
      try (cases s; dsimp only [getOra]; (repeat' split) <;> rfl)
  case ldpSimd _ _ _ addr | stpSimd _ _ _ addr | ldrSimd _ _ addr | strSimd _ _ addr =>
    dsimp only [execInstWithSvc]; rcases evalAddrMode s addr with ⟨_, _ | ⟨_, _⟩⟩ <;>
      simp (config := { decide := false }) [ora_adv, ora_mem, ora_v128, ora_w64, ora_st, apply_ite getOra]
  case ldr | ldrLit | str | ldp | stp | ldnp | stnp | addSubImm | logicalImm | moveWide | bitfield
     | logicalShift | addSubShift | addSubExt | addSubCarry | condCompareReg | condCompareImm
     | condSelect | dataProc1 | dataProc2 | dataProc3 =>
    cases s; dsimp only [getOra, execInstWithSvc, execLdr, execLdrLit, execStr, execLdp, execStp,
      execAddSubImm, execLogicalImm, execMoveWide, execBitfield, execLogicalShift, execAddSubShift,
      execAddSubExt, execAddSubCarry, execCondCompare, execCondSelect, execDataProc1, execDataProc2,
      execDataProc3]
    (repeat' split) <;> rfl
  all_goals
    dsimp only [execInstWithSvc]
    simp (config := { decide := false }) only [ora_adv, ora_pc, ora_w64, ora_w32, ora_w, ora_v128,
      ora_v64, ora_v32, ora_ps, ora_fp, ora_ofp, ora_st, ora_mem, ora_ex, ora_as, ora_ass,
      ora_slr, apply_ite getOra, ite_self]
    try (cases s; dsimp only [getOra]; (repeat' split) <;> rfl)

/-- The standard syscall table never changes `State.oracle`. -/
theorem evalSvc_standard_oracle (s : State) :
    (evalSvc Syscall.standard s).oracle = s.oracle :=
  evalSvc_standard_getOra s

/-- One step of a hook-free `Syscall.standard` program preserves `State.oracle`. -/
theorem Step.oracle_eq_of_standard {prog : Program} (hsvc : prog.svc = Syscall.standard)
    (hext : ∀ pc, prog.externAt? pc = none) {s s' : State} (h : Step prog s s') :
    s'.oracle = s.oracle := by
  cases h with
  | exec _ _ => exact evalInst_oracle_of_standard hsvc _ _
  | halt_unmapped _ _ _ => rfl
  | extern _ he _ _ => rw [hext] at he; cases he
  | extern_fault _ he _ => rfl

/-- Any run of a hook-free `Syscall.standard` program preserves `State.oracle`. -/
theorem Steps.oracle_eq_of_standard {prog : Program} (hsvc : prog.svc = Syscall.standard)
    (hext : ∀ pc, prog.externAt? pc = none) {s0 sf : State} (h : Steps prog s0 sf) :
    sf.oracle = s0.oracle := by
  induction h with
  | refl _ => rfl
  | step h1 _ ih => exact ih.trans (Step.oracle_eq_of_standard hsvc hext h1)

end Arm64
