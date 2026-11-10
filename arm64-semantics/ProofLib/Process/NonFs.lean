/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Process.Core
import ProofLib.SepLogic.Model
import ProofLib.Hoare.Model

/-!
# `State.setFs` Commutation and `FsState`-Parametric Process Combinators

Proves `State.setFs` commutation for non-filesystem instructions (`Step.setFs_of_isNonFs`,
`stepStateNonFs_setFs`, `execUntilPCNonFs_setFs`, `execStepsNonFs_setFs`), `stdin`-parametric
ELF loading, and `FsState`-parametric `subroutine_ok`, `code_ok`, and `exit_ok` combinators.
-/

@[expose] public section

namespace Arm64.Process

open ProofLib

/-! ## `State.setFs` commutation for non-FS instructions and `stdin`-parametric loading -/

@[simp] private theorem readReg64_setFs' (s : State) (f : FsState) (r : Reg) :
    (s.setFs f).readReg64 r = s.readReg64 r := by cases s; cases r <;> rfl
@[simp] private theorem readReg32_setFs' (s : State) (f : FsState) (r : Reg) :
    (s.setFs f).readReg32 r = s.readReg32 r := by cases s; cases r <;> rfl
@[simp] private theorem readVReg128_setFs' (s : State) (f : FsState) (idx : BitVec 5) :
    (s.setFs f).readVReg128 idx = s.readVReg128 idx := by cases s; rfl
@[simp] private theorem pc_setFs' (s : State) (f : FsState) :
    (s.setFs f).pc = s.pc := by cases s; rfl
@[simp] private theorem sp_setFs' (s : State) (f : FsState) :
    (s.setFs f).sp = s.sp := by cases s; rfl
@[simp] private theorem mem_setFs' (s : State) (f : FsState) :
    (s.setFs f).mem = s.mem := by cases s; rfl
@[simp] private theorem pstate_setFs' (s : State) (f : FsState) :
    (s.setFs f).pstate = s.pstate := by cases s; rfl
@[simp] private theorem status_setFs' (s : State) (f : FsState) :
    (s.setFs f).status = s.status := by cases s; rfl
@[simp] private theorem tpidrEl0_setFs' (s : State) (f : FsState) :
    (s.setFs f).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
@[simp] private theorem brk_setFs' (s : State) (f : FsState) :
    (s.setFs f).brk = s.brk := by cases s; rfl
@[simp] private theorem fs_setFs' (s : State) (f : FsState) :
    (s.setFs f).fs = f := by cases s; rfl
@[simp] private theorem oracle_setFs' (s : State) (f : FsState) :
    (s.setFs f).oracle = s.oracle := by cases s; rfl
@[simp] private theorem oracleIdx_setFs' (s : State) (f : FsState) :
    (s.setFs f).oracleIdx = s.oracleIdx := by cases s; rfl
@[simp] private theorem exclFails_setFs' (s : State) (f : FsState) :
    (s.setFs f).exclFails = s.exclFails := by cases s; rfl
@[simp] private theorem exclWillFail_setFs' (s : State) (f : FsState) :
    (s.setFs f).exclWillFail = s.exclWillFail := by cases s; rfl
@[simp] private theorem trace_setFs' (s : State) (f : FsState) :
    (s.setFs f).trace = s.trace := by cases s; rfl
@[simp] private theorem brkStart_setFs' (s : State) (f : FsState) :
    (s.setFs f).brkStart = s.brkStart := by cases s; rfl
@[simp] private theorem fpsr_setFs' (s : State) (f : FsState) :
    (s.setFs f).fpsr = s.fpsr := by cases s; rfl
@[simp] private theorem sigActions_setFs' (s : State) (f : FsState) :
    (s.setFs f).sigActions = s.sigActions := by cases s; rfl
@[simp] private theorem sigAltStack_setFs' (s : State) (f : FsState) :
    (s.setFs f).sigAltStack = s.sigAltStack := by cases s; rfl
@[simp] private theorem mem_setSigAltStack' (s : State) (sas : SigAltStack) :
    (s.setSigAltStack sas).mem = s.mem := by cases s; rfl
@[simp] private theorem physMemAvail_setFs' (s : State) (f : FsState) :
    (s.setFs f).physMemAvail = s.physMemAvail := by cases s; rfl
@[simp] private theorem getSigAction_setFs' (s : State) (f : FsState) (signum : BitVec 32) :
    (s.setFs f).getSigAction signum = s.getSigAction signum := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.regs_setFs (s : State) (f : FsState) :
    (s.setFs f).regs = s.regs := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.vregs_setFs (s : State) (f : FsState) :
    (s.setFs f).vregs = s.vregs := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.spAligned_setFs (s : State) (f : FsState) :
    (s.setFs f).spAligned = s.spAligned := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.readReg_setFs (s : State) (f : FsState) (w : Width) (r : Reg) :
    (s.setFs f).readReg w r = s.readReg w r := by cases s; cases w <;> cases r <;> rfl
@[local simp] theorem _root_.Arm64.State.readVReg64_setFs (s : State) (f : FsState) (idx : BitVec 5) :
    (s.setFs f).readVReg64 idx = s.readVReg64 idx := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.readVReg32_setFs (s : State) (f : FsState) (idx : BitVec 5) :
    (s.setFs f).readVReg32 idx = s.readVReg32 idx := by cases s; rfl

@[local simp] theorem _root_.Arm64.State.writeReg64_setFs (s : State) (f : FsState) (r : Reg) (v : BitVec 64) :
    (s.setFs f).writeReg64 r v = (s.writeReg64 r v).setFs f := by cases s; cases r <;> rfl
@[local simp] theorem _root_.Arm64.State.writeReg32_setFs (s : State) (f : FsState) (r : Reg) (v : BitVec 32) :
    (s.setFs f).writeReg32 r v = (s.writeReg32 r v).setFs f := by cases s; cases r <;> rfl
@[local simp] theorem _root_.Arm64.State.writeReg_setFs (s : State) (f : FsState) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.setFs f).writeReg w r v = (s.writeReg w r v).setFs f := by cases s; cases w <;> cases r <;> rfl
@[local simp] theorem _root_.Arm64.State.writeVReg128_setFs (s : State) (f : FsState) (idx : BitVec 5) (v : BitVec 128) :
    (s.setFs f).writeVReg128 idx v = (s.writeVReg128 idx v).setFs f := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.writeVReg64_setFs (s : State) (f : FsState) (idx : BitVec 5) (v : BitVec 64) :
    (s.setFs f).writeVReg64 idx v = (s.writeVReg64 idx v).setFs f := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.writeVReg32_setFs (s : State) (f : FsState) (idx : BitVec 5) (v : BitVec 32) :
    (s.setFs f).writeVReg32 idx v = (s.writeVReg32 idx v).setFs f := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.advancePC_setFs (s : State) (f : FsState) :
    (s.setFs f).advancePC = s.advancePC.setFs f := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.setPC_setFs (s : State) (f : FsState) (p : BitVec 64) :
    (s.setFs f).setPC p = (s.setPC p).setFs f := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.setPState_setFs (s : State) (f : FsState) (ps : PState) :
    (s.setFs f).setPState ps = (s.setPState ps).setFs f := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.setMem_setFs (s : State) (f : FsState) (m : Memory) :
    (s.setFs f).setMem m = (s.setMem m).setFs f := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.setStatus_setFs (s : State) (f : FsState) (st : ExecStatus) :
    (s.setFs f).setStatus st = (s.setStatus st).setFs f := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.setBrk_setFs (s : State) (f : FsState) (b : BitVec 64) :
    (s.setFs f).setBrk b = (s.setBrk b).setFs f := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.nextOracle_setFs (s : State) (f : FsState) :
    (s.setFs f).nextOracle = s.nextOracle.setFs f := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.stepExclOracle_setFs (s : State) (f : FsState) :
    (s.setFs f).stepExclOracle = s.stepExclOracle.setFs f := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.stepExclLoop_setFs (s : State) (f : FsState) :
    (s.setFs f).stepExclLoop = s.stepExclLoop.setFs f := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.appendTrace_setFs (s : State) (f : FsState) (evs : List TraceEvent) :
    (s.setFs f).appendTrace evs = (s.appendTrace evs).setFs f := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.setFpsr_setFs (s : State) (f : FsState) (v : BitVec 32) :
    (s.setFs f).setFpsr v = (s.setFpsr v).setFs f := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.orFpsr_setFs (s : State) (f : FsState) (v : BitVec 32) :
    (s.setFs f).orFpsr v = (s.orFpsr v).setFs f := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.setSigAction_setFs (s : State) (f : FsState)
    (signum : BitVec 32) (act : SigAction) :
    (s.setFs f).setSigAction signum act = (s.setSigAction signum act).setFs f := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.setSigAltStack_setFs (s : State) (f : FsState)
    (sas : SigAltStack) :
    (s.setFs f).setSigAltStack sas = (s.setSigAltStack sas).setFs f := by cases s; rfl
@[local simp] theorem _root_.Arm64.State.setPhysMemAvail_setFs (s : State) (f : FsState) (n : Nat) :
    (s.setFs f).setPhysMemAvail n = (s.setPhysMemAvail n).setFs f := by cases s; rfl

@[simp] theorem _root_.Arm64.checkRegSPAligned_setFs (s : State) (f : FsState) (r : Reg) :
    checkRegSPAligned (s.setFs f) r = checkRegSPAligned s r := by
  cases s; cases r <;> rfl

@[simp] theorem _root_.Arm64.checkAddrSPAligned_setFs (s : State) (f : FsState) (addr : AddrMode) :
    checkAddrSPAligned (s.setFs f) addr = checkAddrSPAligned s addr := by
  cases s; rfl

@[simp] theorem _root_.Arm64.evalAddrMode_setFs (s : State) (f : FsState) (addr : AddrMode) :
    evalAddrMode (s.setFs f) addr = evalAddrMode s addr := by
  cases s; cases addr <;> rfl

@[simp] theorem _root_.Arm64.applySimdResult_setFs (s : State) (f : FsState) (rd : BitVec 5)
    (r : Except String (BitVec 128)) :
    applySimdResult (s.setFs f) rd r = (applySimdResult s rd r).setFs f := by
  cases s; cases r <;> rfl

@[simp] theorem _root_.Arm64.applySimdSatResult_setFs (s : State) (f : FsState) (rd : BitVec 5)
    (r : Except String (BitVec 128)) (satFlags : Option (BitVec 32)) :
    applySimdSatResult (s.setFs f) rd r satFlags = (applySimdSatResult s rd r satFlags).setFs f := by
  cases s; cases r <;> cases satFlags <;> rfl

@[simp] theorem _root_.Arm64.simdLoadRegs_setFs (sz : SimdMemSize) (m : Memory) (k : Nat)
    (vt : BitVec 5) (ea : BitVec 64) (s : State) (f : FsState) :
    simdLoadRegs sz m k vt ea (s.setFs f) = (simdLoadRegs sz m k vt ea s).setFs f := by
  induction k generalizing vt ea s with
  | zero => rfl
  | succ k ih =>
    simp only [simdLoadRegs, State.writeVReg128_setFs, ih]

/-- True when `nr` is one of the 12 Linux AArch64 filesystem or poll syscalls that inspect `s.fs`. -/
def isFsSyscallNr (nr : BitVec 64) : Bool :=
  nr == SYS_IOCTL || nr == SYS_OPENAT || nr == SYS_CLOSE || nr == SYS_LSEEK ||
  nr == SYS_READ || nr == SYS_WRITE || nr == SYS_READV || nr == SYS_WRITEV || nr == SYS_PREAD64 ||
  nr == SYS_FSTAT || nr == SYS_FCNTL || nr == SYS_PPOLL

/-- True when `inst` executed at state `s` does not inspect or modify `s.fs`.
    Every instruction other than `SVC #0` (`.system false 0#16`) with a filesystem
    syscall number in `X8` satisfies `isNonFs`. -/
def _root_.Arm64.Instr.isNonFs (inst : Instr) (s : State) : Bool :=
  match inst with
  | .system false 0#16 => !isFsSyscallNr (s.readReg64 Reg.x8)
  | _ => true

@[simp] theorem _root_.Arm64.Instr.isNonFs_setFs (inst : Instr) (s : State) (f : FsState) :
    inst.isNonFs (s.setFs f) = inst.isNonFs s := by
  cases s; rfl

@[simp] private theorem ite_setFs (c : Prop) [Decidable c] (a b : State) (f : FsState) :
    (if c then a else b).setFs f = if c then a.setFs f else b.setFs f := by
  split <;> rfl

@[simp] private theorem dite_setFs (c : Prop) [Decidable c] (a : c → State) (b : ¬c → State) (f : FsState) :
    (if h : c then a h else b h).setFs f = if h : c then (a h).setFs f else (b h).setFs f := by
  split <;> rfl

@[simp] private theorem match_opt_pstate_setFs (optPs : Option PState) (s : State) (f : FsState) :
    (match optPs with | some ps => (s.setPState ps).setFs f | none => s.setFs f) =
      (match optPs with | some ps => s.setPState ps | none => s).setFs f := by
  cases optPs <;> rfl

@[simp] private theorem match_wb_setFs (wb : Option (Reg × BitVec 64)) (s : State) (f : FsState) :
    (match wb with | some (base, newBase) => (s.writeReg64 base newBase).setFs f | none => s.setFs f) =
      (match wb with | some (base, newBase) => s.writeReg64 base newBase | none => s).setFs f := by
  cases wb <;> rfl

@[simp] theorem _root_.Arm64.execClockGettime_setFs (s : State) (f : FsState) :
    execClockGettime (s.setFs f) = (execClockGettime s).setFs f := by
  unfold execClockGettime; simp

@[simp] theorem _root_.Arm64.execBrk_setFs (s : State) (f : FsState) :
    execBrk (s.setFs f) = (execBrk s).setFs f := by
  unfold execBrk; simp

@[simp] theorem _root_.Arm64.execMunmap_setFs (s : State) (f : FsState) :
    execMunmap (s.setFs f) = (execMunmap s).setFs f := by
  unfold execMunmap; simp

@[simp] theorem _root_.Arm64.execMmap_setFs (s : State) (f : FsState) :
    execMmap (s.setFs f) = (execMmap s).setFs f := by
  dsimp (config := { zetaHave := true }) only [execMmap]
  simp only [readReg64_setFs', mem_setFs', oracle_setFs', oracleIdx_setFs', physMemAvail_setFs']
  cases hsan : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx)
      (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat) <;> simp

@[simp] theorem _root_.Arm64.execMremap_setFs (s : State) (f : FsState) :
    execMremap (s.setFs f) = (execMremap s).setFs f := by
  dsimp (config := { zetaHave := true }) only [execMremap]
  simp only [readReg64_setFs', mem_setFs', oracle_setFs', oracleIdx_setFs', physMemAvail_setFs']
  cases hsan : sanitizeMmapAddr
      (s.mem.unmapNonFrozen (s.readReg64 Reg.x0) (Arm64.pageAlignUp (s.readReg64 Reg.x1).toNat))
      (s.oracle.mmap s.oracleIdx) (Arm64.pageAlignUp (s.readReg64 Reg.x2).toNat) <;> simp

@[simp] theorem _root_.Arm64.execMprotect_setFs (s : State) (f : FsState) :
    execMprotect (s.setFs f) = (execMprotect s).setFs f := by
  unfold execMprotect; simp

@[simp] theorem _root_.Arm64.execMadvise_setFs (s : State) (f : FsState) :
    execMadvise (s.setFs f) = (execMadvise s).setFs f := by
  unfold execMadvise; simp

@[simp] theorem _root_.Arm64.execSetTidAddress_setFs (s : State) (f : FsState) :
    execSetTidAddress (s.setFs f) = (execSetTidAddress s).setFs f := by
  unfold execSetTidAddress; simp

@[simp] theorem _root_.Arm64.execSchedGetaffinity_setFs (s : State) (f : FsState) :
    execSchedGetaffinity (s.setFs f) = (execSchedGetaffinity s).setFs f := by
  unfold execSchedGetaffinity; simp

@[simp] theorem _root_.Arm64.execTkill_setFs (s : State) (f : FsState) :
    execTkill (s.setFs f) = (execTkill s).setFs f := by
  unfold execTkill; simp

@[simp] theorem _root_.Arm64.execTgkill_setFs (s : State) (f : FsState) :
    execTgkill (s.setFs f) = (execTgkill s).setFs f := by
  unfold execTgkill; simp

@[simp] theorem _root_.Arm64.execSigaltstack_setFs (s : State) (f : FsState) :
    execSigaltstack (s.setFs f) = (execSigaltstack s).setFs f := by
  dsimp (config := { zetaHave := true }) only [execSigaltstack]
  by_cases huss : s.readReg64 Reg.x0 == 0#64 <;>
    by_cases hdis : (s.mem.read32 (s.readReg64 Reg.x0 + 8#64) &&& ~~~SS_AUTODISARM) == SS_DISABLE <;>
    simp [huss, hdis]

@[simp] theorem _root_.Arm64.execRtSigaction_setFs (s : State) (f : FsState) :
    execRtSigaction (s.setFs f) = (execRtSigaction s).setFs f := by
  dsimp (config := { zetaHave := true }) only [execRtSigaction]
  by_cases hact : s.readReg64 Reg.x1 == 0#64 <;> simp [hact]

@[simp] theorem _root_.Arm64.execRtSigprocmask_setFs (s : State) (f : FsState) :
    execRtSigprocmask (s.setFs f) = (execRtSigprocmask s).setFs f := by
  unfold execRtSigprocmask; simp

@[simp] theorem _root_.Arm64.execGetpid_setFs (s : State) (f : FsState) :
    execGetpid (s.setFs f) = (execGetpid s).setFs f := by
  unfold execGetpid; simp

@[simp] theorem _root_.Arm64.execGetrandom_setFs (s : State) (f : FsState) :
    execGetrandom (s.setFs f) = (execGetrandom s).setFs f := by
  unfold execGetrandom; simp

/-- Typeclass witnessing that supervisor-call handler `svc` commutes with `State.setFs` on every
    syscall number outside `isFsSyscallNr`. -/
class SvcNonFsSetFs (svc : State → State) : Prop where
  setFs_of_nonFs : ∀ (s : State) (f : FsState),
    isFsSyscallNr (s.readReg64 Reg.x8) = false → svc (s.setFs f) = (svc s).setFs f

private theorem dispatch_setFs_of_nonFs (table : List (BitVec 64 × (State → State)))
    (htab : ∀ p ∈ table, isFsSyscallNr p.1 = true ∨ ∀ (s : State) (f : FsState), p.2 (s.setFs f) = (p.2 s).setFs f)
    (s : State) (f : FsState) (h : isFsSyscallNr (s.readReg64 Reg.x8) = false) :
    Syscall.dispatch table (s.setFs f) = (Syscall.dispatch table s).setFs f := by
  induction table with
  | nil => simp [Syscall.dispatch]
  | cons p rest ih =>
    rcases p with ⟨nr, handler⟩
    cases hnr : (nr == s.readReg64 Reg.x8)
    · dsimp only [Syscall.dispatch, List.find?]
      rw [readReg64_setFs', hnr]
      exact ih (fun q hq => htab q (.tail _ hq))
    · have heq : s.readReg64 Reg.x8 = nr := (of_decide_eq_true hnr).symm
      rcases htab (nr, handler) (.head _) with hfs | hcomm
      · rw [heq, hfs] at h; contradiction
      · simpa [Syscall.dispatch, readReg64_setFs', hnr] using hcomm s f

instance : SvcNonFsSetFs noSyscalls where
  setFs_of_nonFs _ _ _ := by simp [noSyscalls]

instance : SvcNonFsSetFs Syscall.none where
  setFs_of_nonFs := dispatch_setFs_of_nonFs _ fun _ h => nomatch h

private theorem stdioEntry_nonFs : ∀ p ∈ Syscall.stdioTable,
    isFsSyscallNr p.1 = true ∨ ∀ s f, p.2 (s.setFs f) = (p.2 s).setFs f := by
  intro p hp
  simp only [Syscall.stdioTable, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr fun s f => by cases s; rfl
  · exact Or.inr fun s f => by cases s; rfl

private theorem fileIoOnlyEntry_nonFs : ∀ p ∈ Syscall.fileIoOnlyTable,
    isFsSyscallNr p.1 = true ∨ ∀ s f, p.2 (s.setFs f) = (p.2 s).setFs f := by
  intro p hp
  simp only [Syscall.fileIoOnlyTable, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inl (by decide)

private theorem pollEntry_nonFs : ∀ p ∈ Syscall.pollTable,
    isFsSyscallNr p.1 = true ∨ ∀ s f, p.2 (s.setFs f) = (p.2 s).setFs f := by
  intro p hp
  simp only [Syscall.pollTable, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp; exact Or.inl (by decide)

private theorem allocEntry_nonFs : ∀ p ∈ Syscall.allocTable,
    isFsSyscallNr p.1 = true ∨ ∀ s f, p.2 (s.setFs f) = (p.2 s).setFs f := by
  intro p hp
  simp only [Syscall.allocTable, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Or.inr fun s f => by simp

private theorem signalsEntry_nonFs : ∀ p ∈ Syscall.signalsTable,
    isFsSyscallNr p.1 = true ∨ ∀ s f, p.2 (s.setFs f) = (p.2 s).setFs f := by
  intro p hp
  simp only [Syscall.signalsTable, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact Or.inr fun s f => by simp

private theorem timeEntry_nonFs : ∀ p ∈ Syscall.timeTable,
    isFsSyscallNr p.1 = true ∨ ∀ s f, p.2 (s.setFs f) = (p.2 s).setFs f := by
  intro p hp
  simp only [Syscall.timeTable, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp; exact Or.inr fun s f => by simp

private theorem randomEntry_nonFs : ∀ p ∈ Syscall.randomTable,
    isFsSyscallNr p.1 = true ∨ ∀ s f, p.2 (s.setFs f) = (p.2 s).setFs f := by
  intro p hp
  simp only [Syscall.randomTable, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp; exact Or.inr fun s f => by simp

private theorem miscEntry_nonFs : ∀ p ∈ Syscall.miscTable,
    isFsSyscallNr p.1 = true ∨ ∀ s f, p.2 (s.setFs f) = (p.2 s).setFs f := by
  intro p hp
  simp only [Syscall.miscTable, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> exact Or.inr fun s f => by simp

instance : SvcNonFsSetFs Syscall.stdioWrite where
  setFs_of_nonFs := dispatch_setFs_of_nonFs _ fun p hp => by
    simp only [Syscall.stdioWriteTable, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; exact Or.inl (by decide)

instance : SvcNonFsSetFs Syscall.stdioCli where
  setFs_of_nonFs := dispatch_setFs_of_nonFs _ stdioEntry_nonFs

instance : SvcNonFsSetFs Syscall.fileIo where
  setFs_of_nonFs := dispatch_setFs_of_nonFs _ fun p hp => by
    simp only [Syscall.fileIoTable, List.mem_append] at hp
    exact hp.elim (stdioEntry_nonFs p) (fileIoOnlyEntry_nonFs p)

instance : SvcNonFsSetFs Syscall.poll where
  setFs_of_nonFs := dispatch_setFs_of_nonFs _ pollEntry_nonFs

instance : SvcNonFsSetFs Syscall.alloc where
  setFs_of_nonFs := dispatch_setFs_of_nonFs _ allocEntry_nonFs

instance : SvcNonFsSetFs Syscall.signals where
  setFs_of_nonFs := dispatch_setFs_of_nonFs _ signalsEntry_nonFs

instance : SvcNonFsSetFs Syscall.time where
  setFs_of_nonFs := dispatch_setFs_of_nonFs _ timeEntry_nonFs

instance : SvcNonFsSetFs Syscall.random where
  setFs_of_nonFs := dispatch_setFs_of_nonFs _ randomEntry_nonFs

instance : SvcNonFsSetFs Syscall.misc where
  setFs_of_nonFs := dispatch_setFs_of_nonFs _ miscEntry_nonFs

instance : SvcNonFsSetFs Syscall.standard where
  setFs_of_nonFs := dispatch_setFs_of_nonFs _ fun p hp => by
    simp only [Syscall.standardTable, List.mem_append] at hp
    rcases hp with ((((((h1 | h2) | h3) | h4) | h5) | h6) | h7) | h8
    · exact stdioEntry_nonFs p h1
    · exact fileIoOnlyEntry_nonFs p h2
    · exact pollEntry_nonFs p h3
    · exact allocEntry_nonFs p h4
    · exact signalsEntry_nonFs p h5
    · exact timeEntry_nonFs p h6
    · exact randomEntry_nonFs p h7
    · exact miscEntry_nonFs p h8

instance {svc : State → State} [SvcNonFsSetFs svc] :
    SvcNonFsSetFs (Program.pureWithSvc svc).svc :=
  inferInstanceAs (SvcNonFsSetFs svc)

instance : SvcNonFsSetFs Program.noSyscalls.svc :=
  inferInstanceAs (SvcNonFsSetFs noSyscalls)
instance : SvcNonFsSetFs Program.stdioWrite.svc :=
  inferInstanceAs (SvcNonFsSetFs Syscall.stdioWrite)
instance : SvcNonFsSetFs Program.stdioCli.svc :=
  inferInstanceAs (SvcNonFsSetFs Syscall.stdioCli)
instance : SvcNonFsSetFs Program.fileIo.svc :=
  inferInstanceAs (SvcNonFsSetFs Syscall.fileIo)
instance : SvcNonFsSetFs Program.alloc.svc :=
  inferInstanceAs (SvcNonFsSetFs Syscall.alloc)

@[simp] theorem _root_.Arm64.execAddSubImm_setFs (w : Width) (op : AddSubOp) (rd rn : Reg)
    (imm12 : BitVec 12) (shift12 : Bool) (s : State) (f : FsState) :
    execAddSubImm w op rd rn imm12 shift12 (s.setFs f) = (execAddSubImm w op rd rn imm12 shift12 s).setFs f := by
  cases s
  simp only [execAddSubImm, State.setFs, State.readReg, State.readReg64, State.readReg32]
  (repeat' split) <;> rfl

@[simp] theorem _root_.Arm64.execAddSubExt_setFs (w : Width) (op : AddSubOp) (rd rn rm : Reg)
    (ext : ExtendType) (amt : Nat) (s : State) (f : FsState) :
    execAddSubExt w op rd rn rm ext amt (s.setFs f) = (execAddSubExt w op rd rn rm ext amt s).setFs f := by
  cases s
  simp only [execAddSubExt, State.setFs, State.readReg, State.readReg64, State.readReg32]
  (repeat' split) <;> rfl

@[simp] theorem _root_.Arm64.execAddSubShift_setFs (w : Width) (op : AddSubOp) (rd rn rm : Reg)
    (sh : ShiftType) (amt : Nat) (s : State) (f : FsState) :
    execAddSubShift w op rd rn rm sh amt (s.setFs f) = (execAddSubShift w op rd rn rm sh amt s).setFs f := by
  cases s
  simp only [execAddSubShift, State.setFs, State.readReg, State.readReg64, State.readReg32]
  (repeat' split) <;> rfl

@[simp] theorem _root_.Arm64.execAddSubCarry_setFs (w : Width) (op : AddSubOp) (rd rn rm : Reg)
    (s : State) (f : FsState) :
    execAddSubCarry w op rd rn rm (s.setFs f) = (execAddSubCarry w op rd rn rm s).setFs f := by
  cases s
  simp only [execAddSubCarry, State.setFs, State.readReg, State.readReg64, State.readReg32]
  (repeat' split) <;> rfl

@[simp] theorem _root_.Arm64.execLogicalImm_setFs (w : Width) (op : LogicalOp) (rd rn : Reg)
    (imm : BitVec 64) (s : State) (f : FsState) :
    execLogicalImm w op rd rn imm (s.setFs f) = (execLogicalImm w op rd rn imm s).setFs f := by
  cases s
  simp only [execLogicalImm, State.setFs, State.readReg, State.readReg64, State.readReg32]
  (repeat' split) <;> rfl

@[simp] theorem _root_.Arm64.execLogicalShift_setFs (w : Width) (op : LogicalOp) (rd rn rm : Reg)
    (sh : ShiftType) (amt : Nat) (s : State) (f : FsState) :
    execLogicalShift w op rd rn rm sh amt (s.setFs f) = (execLogicalShift w op rd rn rm sh amt s).setFs f := by
  cases s
  simp only [execLogicalShift, State.setFs, State.readReg, State.readReg64, State.readReg32]
  (repeat' split) <;> rfl

@[simp] theorem _root_.Arm64.execMoveWide_setFs (w : Width) (op : MoveWideOp) (rd : Reg)
    (imm : BitVec 16) (hw : Nat) (s : State) (f : FsState) :
    execMoveWide w op rd imm hw (s.setFs f) = (execMoveWide w op rd imm hw s).setFs f := by
  unfold execMoveWide; cases op <;> simp

@[simp] theorem _root_.Arm64.execBitfield_setFs (w : Width) (op : BitfieldOp) (rd rn : Reg)
    (immr imms : Nat) (s : State) (f : FsState) :
    execBitfield w op rd rn immr imms (s.setFs f) = (execBitfield w op rd rn immr imms s).setFs f := by
  unfold execBitfield; simp

@[simp] theorem _root_.Arm64.execCondSelect_setFs (w : Width) (op : CondSelectOp) (rd rn rm : Reg)
    (cond : CondCode) (s : State) (f : FsState) :
    execCondSelect w op rd rn rm cond (s.setFs f) = (execCondSelect w op rd rn rm cond s).setFs f := by
  unfold execCondSelect; simp

@[simp] theorem _root_.Arm64.execCondCompare_setFs (w : Width) (isSub isImm : Bool)
    (rn : Reg) (rhs : BitVec 64) (rm : Reg) (nzcv : BitVec 4) (cond : CondCode)
    (s : State) (f : FsState) :
    execCondCompare w isSub isImm rn rhs rm nzcv cond (s.setFs f) =
      (execCondCompare w isSub isImm rn rhs rm nzcv cond s).setFs f := by
  unfold execCondCompare
  rw [pstate_setFs', State.readReg_setFs]
  by_cases h : isImm = true
  · simp only [h, ↓reduceIte]
    rcases evalAddSub w (if isSub then .SUBS else .ADDS) (s.readReg w rn) rhs none with ⟨res, _ | ps⟩ <;> simp
  · simp only [h, Bool.false_eq_true, ↓reduceIte, State.readReg_setFs]
    rcases evalAddSub w (if isSub then .SUBS else .ADDS) (s.readReg w rn) (s.readReg w rm) none with ⟨res, _ | ps⟩ <;> simp

@[simp] theorem _root_.Arm64.execDataProc1_setFs (w : Width) (op : DataProc1Op) (rd rn : Reg)
    (s : State) (f : FsState) :
    execDataProc1 w op rd rn (s.setFs f) = (execDataProc1 w op rd rn s).setFs f := by
  unfold execDataProc1; cases w <;> cases op <;> simp

@[simp] theorem _root_.Arm64.execDataProc2_setFs (w : Width) (op : DataProc2Op) (rd rn rm : Reg)
    (s : State) (f : FsState) :
    execDataProc2 w op rd rn rm (s.setFs f) = (execDataProc2 w op rd rn rm s).setFs f := by
  unfold execDataProc2; cases w <;> cases op <;> simp

@[simp] theorem _root_.Arm64.execDataProc3_setFs (w : Width) (op : DataProc3Op) (rd rn rm ra : Reg)
    (s : State) (f : FsState) :
    execDataProc3 w op rd rn rm ra (s.setFs f) = (execDataProc3 w op rd rn rm ra s).setFs f := by
  unfold execDataProc3; cases w <;> cases op <;> simp

@[simp] theorem _root_.Arm64.execLdr_setFs (w : Width) (size : MemWidth) (signed : Bool)
    (rt : Reg) (addr : AddrMode) (s : State) (f : FsState) :
    execLdr w size signed rt addr (s.setFs f) = (execLdr w size signed rt addr s).setFs f := by
  unfold execLdr
  rw [checkAddrSPAligned_setFs, evalAddrMode_setFs, mem_setFs']
  rcases evalAddrMode s addr with ⟨ea, _ | ⟨base, newBase⟩⟩ <;> simp

@[simp] theorem _root_.Arm64.execLdrLit_setFs (w : Width) (size : MemWidth) (signed : Bool)
    (rt : Reg) (offset : BitVec 64) (s : State) (f : FsState) :
    execLdrLit w size signed rt offset (s.setFs f) = (execLdrLit w size signed rt offset s).setFs f := by
  unfold execLdrLit; simp

@[simp] theorem _root_.Arm64.execStr_setFs (size : MemWidth) (rt : Reg) (addr : AddrMode)
    (s : State) (f : FsState) :
    execStr size rt addr (s.setFs f) = (execStr size rt addr s).setFs f := by
  unfold execStr
  rw [checkAddrSPAligned_setFs, evalAddrMode_setFs, mem_setFs', readReg64_setFs']
  rcases evalAddrMode s addr with ⟨ea, _ | ⟨base, newBase⟩⟩ <;> simp

@[simp] theorem _root_.Arm64.execLdp_setFs (w : Width) (signed : Bool) (rt1 rt2 : Reg)
    (addr : AddrMode) (s : State) (f : FsState) :
    execLdp w signed rt1 rt2 addr (s.setFs f) = (execLdp w signed rt1 rt2 addr s).setFs f := by
  unfold execLdp
  rw [checkAddrSPAligned_setFs, evalAddrMode_setFs, mem_setFs']
  rcases evalAddrMode s addr with ⟨ea, _ | ⟨base, newBase⟩⟩ <;> simp

@[simp] theorem _root_.Arm64.execStp_setFs (w : Width) (rt1 rt2 : Reg) (addr : AddrMode)
    (s : State) (f : FsState) :
    execStp w rt1 rt2 addr (s.setFs f) = (execStp w rt1 rt2 addr s).setFs f := by
  unfold execStp
  rw [checkAddrSPAligned_setFs, evalAddrMode_setFs, mem_setFs', readReg64_setFs', readReg64_setFs']
  rcases evalAddrMode s addr with ⟨ea, _ | ⟨base, newBase⟩⟩ <;> simp

@[simp] private theorem state_mk_setFs (regs : RegFile) (vregs : VRegFile) (sp pc : BitVec 64)
    (pstate : PState) (mem : Memory) (tpidrEl0 : BitVec 64) (fpsr : BitVec 32) (brkStart brk : BitVec 64) (fs0 f : FsState)
    (oracle : Oracle) (oracleIdx : Nat) (exclFails : List Bool) (trace : List TraceEvent) (status : ExecStatus)
    (symtab : String → String → Option (BitVec 64)) (sigActions : BitVec 32 → SigAction)
    (sigAltStack : SigAltStack) (physMemAvail : Nat) :
    (State.mk regs vregs sp pc pstate mem tpidrEl0 fpsr brkStart brk fs0 oracle oracleIdx exclFails trace status symtab sigActions sigAltStack physMemAvail).setFs f =
    State.mk regs vregs sp pc pstate mem tpidrEl0 fpsr brkStart brk f oracle oracleIdx exclFails trace status symtab sigActions sigAltStack physMemAvail := rfl

@[simp] private theorem readVReg128_eta_setFs (s : State) (f : FsState) :
    (s.setFs f).readVReg128 = s.readVReg128 := by
  funext v; simp

@[simp] private theorem ite_setFs_writeReg (c : Prop) [Decidable c] (a b : State) (f : FsState)
    (w : Width) (r : Reg) (v : BitVec 64) :
    (if c then a.setFs f else b.setFs f).writeReg w r v =
      ((if c then a else b).writeReg w r v).setFs f := by
  split <;> simp

private theorem bitvec2_cases (P : BitVec 2 → Prop)
    (h0 : P 0#2) (h1 : P 1#2) (h2 : P 2#2) (h3 : P 3#2) (x : BitVec 2) : P x := by
  rcases x with ⟨n, hn⟩
  match n with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3
  | n + 4 => omega

theorem evalSvc_setFs_of_nonFs (svc : State → State) [SvcNonFsSetFs svc] (s : State) (f : FsState)
    (h : isFsSyscallNr (s.readReg64 Reg.x8) = false) :
    evalSvc svc (s.setFs f) = (evalSvc svc s).setFs f := by
  simp only [evalSvc, SvcNonFsSetFs.setFs_of_nonFs (svc := svc) s f h,
    mem_setFs', tpidrEl0_setFs', State.symtab_setFs]
  cases svc s; rfl

set_option maxHeartbeats 1600000 in
theorem execInstWithSvc_setFs_of_isNonFs (svc : State → State) [SvcNonFsSetFs svc]
    (inst : Instr) (s : State) (f : FsState)
    (h : inst.isNonFs s = true) :
    execInstWithSvc svc inst (s.setFs f) = (execInstWithSvc svc inst s).setFs f := by
  revert h
  cases inst
  case ldpSimd sz vt1 vt2 addr =>
    intro _
    dsimp only [execInstWithSvc]
    rw [checkAddrSPAligned_setFs, evalAddrMode_setFs, mem_setFs']
    rcases evalAddrMode s addr with ⟨ea, _ | ⟨base, newBase⟩⟩ <;> simp
  case stpSimd sz vt1 vt2 addr =>
    intro _
    dsimp only [execInstWithSvc]
    rw [checkAddrSPAligned_setFs, evalAddrMode_setFs, mem_setFs', readVReg128_setFs', readVReg128_setFs']
    rcases evalAddrMode s addr with ⟨ea, _ | ⟨base, newBase⟩⟩ <;> simp
  case ldrSimd sz vt addr =>
    intro _
    dsimp only [execInstWithSvc]
    rw [checkAddrSPAligned_setFs, evalAddrMode_setFs, mem_setFs']
    rcases evalAddrMode s addr with ⟨ea, _ | ⟨base, newBase⟩⟩ <;> simp
  case strSimd sz vt addr =>
    intro _
    dsimp only [execInstWithSvc]
    rw [checkAddrSPAligned_setFs, evalAddrMode_setFs, mem_setFs', readVReg128_setFs']
    rcases evalAddrMode s addr with ⟨ea, _ | ⟨base, newBase⟩⟩ <;> simp
  case simdLdStMulti isLoad q size selem rn postIdx rm vt =>
    intro _
    dsimp only [execInstWithSvc]
    by_cases hbad : (size == 3#2 && !q || !(selem == 2 || selem == 3 || selem == 4)) = true
    · simp only [hbad, ↓reduceIte]; cases s; rfl
    · by_cases h3 : selem ≥ 3 <;> by_cases h4 : selem ≥ 4 <;>
        simp only [hbad, h3, h4, Bool.false_eq_true, ↓reduceIte,
          readReg64_setFs', readVReg128_eta_setFs, mem_setFs',
          State.writeReg64_setFs, State.writeVReg128_setFs, State.advancePC_setFs,
          State.setMem_setFs, State.setStatus_setFs, checkRegSPAligned_setFs, ite_setFs]
  case simdThreeSame q u size rm opcode rn rd =>
    intro h_unused; clear h_unused
    dsimp only [execInstWithSvc]
    by_cases hop : opcode == 0b00011#5
    · simp only [hop, ↓reduceIte, readVReg128_setFs']
      revert size
      refine bitvec2_cases _ ?_ ?_ ?_ ?_ <;> cases u <;> simp <;> (cases s; split <;> rfl)
    · simp only [hop, Bool.false_eq_true, ↓reduceIte, readVReg128_setFs',
        State.writeVReg128_setFs, State.advancePC_setFs,
        applySimdSatResult_setFs, ite_setFs]
  case system isHalt imm =>
    intro h
    cases isHalt
    · by_cases himm : imm == 0#16
      · have h_eq : imm = 0#16 := of_decide_eq_true himm
        subst h_eq
        simp only [Instr.isNonFs, Bool.not_eq_true'] at h
        dsimp only [execInstWithSvc]
        simp [SvcNonFsSetFs.setFs_of_nonFs (svc := svc) s f h]
      · dsimp only [execInstWithSvc]
        simp [himm]
    · dsimp only [execInstWithSvc]
      simp
  all_goals
    intro _
    dsimp only [execInstWithSvc]
    first
    | exact execLdr_setFs _ _ _ _ _ _ _
    | exact execLdrLit_setFs _ _ _ _ _ _ _
    | exact execLdp_setFs _ _ _ _ _ _ _
    | exact execStr_setFs _ _ _ _ _
    | exact execStp_setFs _ _ _ _ _ _
    | exact execCondCompare_setFs _ _ _ _ _ _ _ _ _ _
    | (simp only [
        readReg64_setFs', readReg32_setFs', readVReg128_setFs', readVReg128_eta_setFs,
        pc_setFs', sp_setFs', mem_setFs', pstate_setFs', status_setFs', fpsr_setFs',
        tpidrEl0_setFs', brk_setFs', fs_setFs', oracle_setFs', oracleIdx_setFs',
        exclFails_setFs', exclWillFail_setFs',
        trace_setFs', brkStart_setFs', State.symtab_setFs, sigActions_setFs',
        State.regs_setFs,
        State.vregs_setFs, State.readReg_setFs,
        State.readVReg64_setFs, State.readVReg32_setFs,
        State.writeReg64_setFs, State.writeReg32_setFs, State.writeReg_setFs,
        State.writeVReg128_setFs, State.writeVReg64_setFs, State.writeVReg32_setFs,
        State.advancePC_setFs, State.setPC_setFs, State.setPState_setFs,
        State.setFpsr_setFs, State.orFpsr_setFs,
        State.setMem_setFs, State.setStatus_setFs,
        State.stepExclOracle_setFs,
        checkRegSPAligned_setFs,
        applySimdResult_setFs, applySimdSatResult_setFs, simdLoadRegs_setFs,
        execAddSubImm_setFs, execAddSubExt_setFs, execAddSubShift_setFs, execAddSubCarry_setFs,
        execLogicalImm_setFs, execLogicalShift_setFs, execMoveWide_setFs,
        execBitfield_setFs, execCondSelect_setFs,
        execDataProc1_setFs, execDataProc2_setFs, execDataProc3_setFs,
        ite_setFs, ite_setFs_writeReg, state_mk_setFs]
       try (cases s; (repeat' split) <;> rfl))

instance (svc : State → State) [SvcNonFsSetFs svc] : SvcNonFsSetFs (evalSvc svc) where
  setFs_of_nonFs := evalSvc_setFs_of_nonFs svc

theorem execInst_setFs_of_isNonFs (inst : Instr) (s : State) (f : FsState)
    (h : inst.isNonFs s = true) :
    execInst inst (s.setFs f) = (execInst inst s).setFs f :=
  execInstWithSvc_setFs_of_isNonFs Syscall.standard inst s f h

theorem evalInst_setFs_of_isNonFs (prog : Program) [SvcNonFsSetFs prog.svc]
    (inst : Instr) (s : State) (f : FsState)
    (h : inst.isNonFs s = true) :
    prog.evalInst inst (s.setFs f) = (prog.evalInst inst s).setFs f :=
  execInstWithSvc_setFs_of_isNonFs (evalSvc prog.svc) inst s f h

/-- General `fs`-commutation theorem for `Step`: any single-step transition of a fetched
    non-filesystem instruction commutes with replacing `s.fs`. -/
theorem _root_.Arm64.Step.setFs_of_isNonFs {prog : Program} [SvcNonFsSetFs prog.svc]
    {s s' : State} {inst : Instr}
    (h_step : Step prog s s')
    (h_fetch : prog.fetchMem s.mem s.pc = some inst)
    (h_nonFs : inst.isNonFs s = true)
    (f : FsState) :
    Step prog (s.setFs f) (s'.setFs f) := by
  have h_run : (s.setFs f).status = .Running := by
    rw [status_setFs']
    exact h_step.status_running
  have h_fetch' : prog.fetchMem (s.setFs f).mem (s.setFs f).pc = some inst := by
    rw [mem_setFs', pc_setFs']
    exact h_fetch
  have h_step2 : Step prog s (prog.evalInst inst s) := Step.exec h_step.status_running h_fetch
  have h_eq : s' = prog.evalInst inst s := Step.deterministic h_step h_step2
  subst h_eq
  rw [← evalInst_setFs_of_isNonFs prog inst s f h_nonFs]
  exact Step.exec h_run h_fetch'

/-- Deterministic single-step evaluator restricted to instructions that do not touch `s.fs`. -/
def stepStateNonFs (prog : Program) (s : State) : Option State :=
  match s.status with
  | .Running =>
    match prog.externAt? s.pc with
    | some _ => none
    | none =>
      match prog.fetchMem s.mem s.pc with
      | some inst => if inst.isNonFs s then some (prog.evalInst inst s) else none
      | none      => none
  | _ => none

theorem stepStateNonFs_sound {prog : Program} {s s' : State}
    (h : stepStateNonFs prog s = some s') : Step prog s s' := by
  unfold stepStateNonFs at h
  split at h
  · rename_i h_run
    split at h
    · contradiction
    · split at h
      · rename_i inst h_fetch
        split at h
        · injection h with hs'
          subst hs'
          exact Step.exec h_run h_fetch
        · contradiction
      · contradiction
  · contradiction

/-- `stepStateNonFs` commutes unconditionally with `State.setFs`. -/
@[simp] theorem stepStateNonFs_setFs (prog : Program) [SvcNonFsSetFs prog.svc]
    (s : State) (f : FsState) :
    stepStateNonFs prog (s.setFs f) = (stepStateNonFs prog s).map (·.setFs f) := by
  unfold stepStateNonFs
  simp only [status_setFs', pc_setFs', mem_setFs', Instr.isNonFs_setFs]
  cases s.status <;> try rfl
  cases prog.externAt? s.pc <;> try rfl
  cases prog.fetchMem s.mem s.pc with
  | none => rfl
  | some inst =>
    by_cases h_nf : inst.isNonFs s = true
    · simp [h_nf, evalInst_setFs_of_isNonFs prog inst s f h_nf]
    · simp [h_nf]

/-- Execute up to `n` non-FS small-step transitions of `prog` from `s`, stopping at `targetPC`,
    any non-`.Running` status, or any filesystem syscall / hook. -/
def execUntilPCNonFs : Nat → Program → BitVec 64 → State → State
  | 0, _, _, s => s
  | n + 1, prog, targetPC, s =>
    if s.pc == targetPC || s.status != .Running then
      s
    else
      match stepStateNonFs prog s with
      | some s' => execUntilPCNonFs n prog targetPC s'
      | none    => s

/-- Every `execUntilPCNonFs` trace is a valid `Steps` trace. -/
theorem execUntilPCNonFs_steps (prog : Program) (n : Nat) (targetPC : BitVec 64) (s : State) :
    Steps prog s (execUntilPCNonFs n prog targetPC s) := by
  induction n generalizing s with
  | zero => exact Steps.refl s
  | succ n ih =>
    unfold execUntilPCNonFs
    split
    · exact Steps.refl s
    · split
      · rename_i s' h_step
        exact Steps.step (stepStateNonFs_sound h_step) (ih s')
      · exact Steps.refl s

/-- `execUntilPCNonFs` commutes unconditionally with `State.setFs`. -/
@[simp] theorem execUntilPCNonFs_setFs (prog : Program) [SvcNonFsSetFs prog.svc]
    (n : Nat) (targetPC : BitVec 64) (s : State) (f : FsState) :
    execUntilPCNonFs n prog targetPC (s.setFs f) =
      (execUntilPCNonFs n prog targetPC s).setFs f := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    unfold execUntilPCNonFs
    simp only [pc_setFs', status_setFs', stepStateNonFs_setFs]
    by_cases h_stop : (s.pc == targetPC || s.status != .Running) = true
    · simp [h_stop]
    · simp only [h_stop]
      cases stepStateNonFs prog s with
      | none => rfl
      | some s' => exact ih s'

/-- `buildInitialStack` does not depend on `inputs.stdin`. -/
@[simp] theorem buildInitialStack_with_stdin (img : ElfImage) (inputs : ProcessInputs)
    (stdin' : List (BitVec 8)) :
    buildInitialStack img { inputs with stdin := stdin' } = buildInitialStack img inputs :=
  rfl

/-- Updating `inputs.stdin` in `img.loadState` succeeds with `s0.setFs (initFsState ...)`. -/
theorem ElfImage.loadState_with_stdin {img : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (stdin' : List (BitVec 8))
    (h_load : img.loadState inputs = .ok s0) :
    img.loadState { inputs with stdin := stdin' } =
      .ok (s0.setFs (initFsState { inputs with stdin := stdin' })) := by
  unfold ElfImage.loadState at h_load ⊢
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_load ⊢
  split at h_load
  · contradiction
  · rename_i h_wf
    split at h_load
    · contradiction
    · rename_i h_dirs
      split at h_load
      · contradiction
      · rename_i h_files
        simp only [h_wf, h_dirs, h_files, buildInitialStack_with_stdin]
        generalize hb : buildInitialStack img inputs = r at h_load ⊢
        cases r with
        | error _ => contradiction
        | ok pair =>
          rcases pair with ⟨sp, stackRegion⟩
          injection h_load with hs0
          subst hs0
          rfl

/-! ## `FsState`-parametric `subroutine_ok` and `exit_ok` combinators -/

/-- Execute up to `n` non-FS steps (`stepStateNonFs`) until `s.status != .Running`. -/
def execStepsNonFs : Nat → Program → State → State
  | 0, _, s => s
  | n + 1, prog, s =>
    if s.status != .Running then
      s
    else
      match stepStateNonFs prog s with
      | some s' => execStepsNonFs n prog s'
      | none    => s

/-- Every `execStepsNonFs` trace is a valid `Steps` trace. -/
theorem execStepsNonFs_steps (prog : Program) (n : Nat) (s : State) :
    Steps prog s (execStepsNonFs n prog s) := by
  induction n generalizing s with
  | zero => exact Steps.refl s
  | succ n ih =>
    unfold execStepsNonFs
    split
    · exact Steps.refl s
    · split
      · rename_i s' h_step
        exact Steps.step (stepStateNonFs_sound h_step) (ih s')
      · exact Steps.refl s

/-- `execStepsNonFs` commutes unconditionally with `State.setFs`. -/
@[simp] theorem execStepsNonFs_setFs (prog : Program) [SvcNonFsSetFs prog.svc]
    (n : Nat) (s : State) (f : FsState) :
    execStepsNonFs n prog (s.setFs f) = (execStepsNonFs n prog s).setFs f := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    unfold execStepsNonFs
    simp only [status_setFs', stepStateNonFs_setFs]
    by_cases h_stop : (s.status != .Running) = true
    · simp [h_stop]
    · simp only [h_stop]
      cases stepStateNonFs prog s with
      | none => rfl
      | some s' => exact ih s'

theorem CallingConventionPreserved.setFs {s0 sf : State} (f0 ff : FsState)
    (h : CallingConventionPreserved s0 sf) :
    CallingConventionPreserved (s0.setFs f0) (sf.setFs ff) := by
  cases s0; cases sf; exact h

theorem empty_complement_matches (m : Memory) :
    (Heap.empty.complement m).Matches m := by
  refine ⟨fun a c hc => ?_, ⟨0, fun _ _ _ => ⟨rfl, rfl⟩⟩, fun a hmap => ?_⟩
  · simp only [Heap.complement, Heap.empty] at hc
    split at hc
    · rename_i h_rw
      split at hc
      · injection hc with hc'; subst hc'; exact h_rw
      · rename_i h_lf
        injection hc with hc'; subst hc'
        exact ⟨rfl, h_rw, Bool.eq_false_iff.mpr h_lf⟩
    · split at hc
      · rename_i _ h_pn
        split at hc
        · injection hc with hc'; subst hc'; exact h_pn
        · rename_i h_lf
          injection hc with hc'; subst hc'
          exact ⟨rfl, h_pn, Bool.eq_false_iff.mpr h_lf⟩
      · contradiction
  · simp only [Heap.complement, Heap.empty, Bool.not_false, Bool.true_and, Bool.and_eq_true] at hmap
    exact ⟨hmap.1.1, hmap.2⟩

theorem empty_union_eq (h : Heap) :
    Heap.empty.union h = h := by
  ext a : 2
  · rfl
  · rfl
  · rfl
  · simp [Heap.union, Heap.empty]

/-- Every readable byte in `m` is either mapped read-write (`some Perm.rw`) or frozen (`m.Frozen a`).
    This holds for every memory without `rwx` (`w = true ∧ x = true`) mappings. -/
def _root_.Arm64.Memory.ReadableIsRwOrFrozen (m : Memory) : Prop :=
  ∀ a : BitVec 64, (m.perm a).r = true → m.perm a = some Perm.rw ∨ m.Frozen a

theorem empty_matches (m : Memory) : Heap.empty.Matches m :=
  ⟨fun _ _ hc => by contradiction, ⟨0, fun _ _ _ => ⟨rfl, rfl⟩⟩, fun _ hm => by contradiction⟩

theorem complementSep_emp_holds (m : Memory) :
    (SepProp.complementSep SepProp.emp m).holds (Heap.empty.complement m) :=
  SepProp.holds_complementSep_iff.mpr
    ⟨Heap.empty, SepProp.holds_emp_iff.mpr rfl, empty_matches m, rfl⟩

/-- Frame-preservation theorem for `SepProp.complementSep SepProp.emp` across any `Steps` trace. -/
theorem Steps.complementSep_frame {prog : Program} {s0 sf : State} {R : SepProp}
    (h_steps : Steps prog s0 sf)
    (h_wf : s0.mem.ReadableIsRwOrFrozen)
    (h_pre : s0.mem ⊨ SepProp.complementSep SepProp.emp s0.mem ∗ R) :
    sf.mem ⊨ SepProp.complementSep SepProp.emp sf.mem ∗ R := by
  have h_kf : s0.mem.KeepsFrozen sf.mem := Steps.keepsFrozen h_steps
  obtain ⟨h, hh, h_match, h_gv, h_map⟩ := SepProp.satisfies_iff.mp h_pre
  obtain ⟨h₁, hf, h_disj, rfl, hc, hR⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨he, hhe, _, rfl⟩ := SepProp.holds_complementSep_iff.mp hc
  rw [SepProp.holds_emp_iff] at hhe; subst hhe
  have hf_ro : ∀ a c, hf.phys a = some c →
      ∃ b, c = .ro b ∧ sf.mem.read8 a = b ∧ (sf.mem.perm a).r = true ∧
        sf.mem.isLazyFree a = false ∧
        sf.mem.perm a ≠ some Perm.rw ∧ sf.mem.perm a ≠ some Perm.protNone := by
    intro a c hfc
    have h_not_rw : s0.mem.perm a ≠ some Perm.rw := by
      intro hrw
      have h1a : (Heap.empty.complement s0.mem).phys a =
          (if s0.mem.isLazyFree a then some .lazy else some (.rw (s0.mem.read8 a))) := by
        simp [Heap.complement, Heap.empty, hrw]
      rcases h_disj.1 a with hnone | hnone | ⟨b, hro, _⟩
      · rw [h1a] at hnone; split at hnone <;> contradiction
      · rw [hfc] at hnone; contradiction
      · rw [h1a] at hro; split at hro <;> cases hro
    have h_not_pn : s0.mem.perm a ≠ some Perm.protNone := by
      intro hpn
      have hne_pn_rw : some Perm.protNone ≠ some Perm.rw := by decide
      have h1a : (Heap.empty.complement s0.mem).phys a =
          (if s0.mem.isLazyFree a then some .protNoneLazy else some (.protNone (s0.mem.read8 a))) := by
        simp only [Heap.complement, Heap.empty, hpn, hne_pn_rw, ↓reduceIte]
      rcases h_disj.1 a with hnone | hnone | ⟨b, hro, _⟩
      · rw [h1a] at hnone; split at hnone <;> contradiction
      · rw [hfc] at hnone; contradiction
      · rw [h1a] at hro; split at hro <;> cases hro
    have h1a : (Heap.empty.complement s0.mem).phys a = none := by
      simp [Heap.complement, Heap.empty, h_not_rw, h_not_pn]
    have hunion : ((Heap.empty.complement s0.mem).union hf).phys a = some c := by
      simp [Heap.union, h1a, hfc]
    have hm := h_match a c hunion
    cases c with
    | rw b =>
      exact False.elim (h_not_rw hm.2.1)
    | protNone b =>
      exact False.elim (h_not_pn hm.2.1)
    | lazy =>
      exact False.elim (h_not_rw hm)
    | protNoneLazy =>
      exact False.elim (h_not_pn hm)
    | ro b =>
      rcases h_wf a hm.2.1 with hrw | hfrz
      · exact False.elim (h_not_rw hrw)
      · obtain ⟨hr8, hperm, hlf, _⟩ := h_kf a hfrz
        refine ⟨b, rfl, hr8.trans hm.1, ?_, hlf.trans hm.2.2, ?_, ?_⟩
        · rw [hperm]; exact hm.2.1
        · rw [hperm]; exact h_not_rw
        · rw [hperm]; exact h_not_pn
  have hf_map : ∀ a, hf.mapped a = true →
      ((sf.mem.perm a).mapped = true ∧ sf.mem.isAnon a = true) ∧
      (sf.mem.perm a).frozen = true := by
    intro a hfa
    have hmap_u : (s0.mem.perm a).mapped = true ∧ s0.mem.isAnon a = true :=
      h_map a (by simp [Heap.union, hfa])
    have h1_map : (Heap.empty.complement s0.mem).mapped a = false := by
      rcases h_disj.2.2.2.2 a with h1 | h2
      · exact h1
      · rw [hfa] at h2; contradiction
    have hfrz : s0.mem.Frozen a := by
      simp only [Heap.complement, Heap.empty, Bool.not_false, Bool.true_and, hmap_u.1, hmap_u.2,
        Bool.and_true, Bool.not_eq_false'] at h1_map
      exact h1_map
    obtain ⟨_, hperm, _, hanon⟩ := h_kf a hfrz
    rw [hperm, hanon]
    exact ⟨hmap_u, hfrz⟩
  let h₁' := Heap.empty.complement sf.mem
  refine SepProp.satisfies_iff.mpr ⟨h₁'.union hf,
    SepProp.holds_sepConj_iff.mpr ⟨h₁', hf, ?_, rfl, complementSep_emp_holds sf.mem, hR⟩, ?_, h_gv, ?_⟩
  · refine ⟨fun a => ?_, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl, ?_, fun a => ?_⟩
    · cases hfc : hf.phys a with
      | none => exact Or.inr (Or.inl rfl)
      | some c =>
        obtain ⟨_, _, _, _, _, hnotrw, hnotpn⟩ := hf_ro a c hfc
        left
        simp [h₁', Heap.complement, Heap.empty, hnotrw, hnotpn]
    · intro _ _ _ _ h
      rcases h with ⟨ha, _⟩ | ⟨_, hf'⟩ <;> contradiction
    · cases hfa : hf.mapped a with
      | false => exact Or.inr rfl
      | true =>
        obtain ⟨_, hfrz⟩ := hf_map a hfa
        exact Or.inl (by simp [h₁', Heap.complement, Heap.empty, hfrz])
  · intro a c hc
    simp only [Heap.union] at hc
    cases h1c : h₁'.phys a with
    | some c1 =>
      rw [h1c] at hc
      injection hc with hc'
      subst hc'
      exact (empty_complement_matches sf.mem).1 a c1 h1c
    | none =>
      rw [h1c] at hc
      obtain ⟨b, rfl, hr8, hr, hlf, _⟩ := hf_ro a c hc
      exact ⟨hr8, hr, hlf⟩
  · intro a hmap_u
    simp only [Heap.union, Bool.or_eq_true] at hmap_u
    rcases hmap_u with h1 | h2
    · exact (empty_complement_matches sf.mem).2.2 a h1
    · exact (hf_map a h2).1

private theorem pure_complementSep_elim {φ : Prop} {m : Memory} {R : SepProp}
    (hpre : m ⊨ (⌜φ⌝ ∗ SepProp.complementSep SepProp.emp m) ∗ R) :
    φ ∧ (m ⊨ SepProp.complementSep SepProp.emp m ∗ R) := by
  obtain ⟨h, hh, h_match⟩ := SepProp.satisfies_iff.mp hpre
  obtain ⟨h_pre, hf, h_disj, rfl, hpc, hR⟩ := SepProp.holds_sepConj_iff.mp hh
  obtain ⟨he, h_comp, _, rfl, hpure, h_c⟩ := SepProp.holds_sepConj_iff.mp hpc
  obtain ⟨rfl, hφ⟩ := SepProp.holds_pure_iff.mp hpure
  rw [empty_union_eq] at h_disj h_match
  exact ⟨hφ, SepProp.satisfies_iff.mpr ⟨h_comp.union hf,
    SepProp.holds_sepConj_iff.mpr ⟨h_comp, hf, h_disj, rfl, h_c, hR⟩, h_match⟩⟩

private theorem pure_complementSep_intro {φ : Prop} {m : Memory} {R : SepProp}
    (hφ : φ)
    (hpost : m ⊨ SepProp.complementSep SepProp.emp m ∗ R) :
    m ⊨ (⌜φ⌝ ∗ SepProp.complementSep SepProp.emp m) ∗ R := by
  obtain ⟨h', hh', hm'⟩ := SepProp.satisfies_iff.mp hpost
  obtain ⟨h₁', hf', h_disj', rfl, hc', hR'⟩ := SepProp.holds_sepConj_iff.mp hh'
  refine SepProp.satisfies_iff.mpr
    ⟨h₁'.union hf', SepProp.holds_sepConj_iff.mpr ⟨h₁', hf', h_disj', rfl, ?_, hR'⟩, hm'⟩
  refine SepProp.holds_sepConj_iff.mpr ⟨Heap.empty, h₁', ⟨fun _ => Or.inl rfl, fun _ _ => Or.inl rfl, fun _ _ => Or.inl rfl, ?_,
    fun _ => Or.inl rfl⟩,
    (empty_union_eq h₁').symm, SepProp.holds_pure_iff.mpr ⟨rfl, hφ⟩, hc'⟩
  intro _ _ _ _ hh
  rcases hh with ⟨ha, _⟩ | ⟨_, hf0⟩ <;> contradiction

/-- Generic `FsState`-parametric `Spec` for a non-FS subroutine starting at `sEntry` and
    returning to `sEntry.readReg64 Reg.lr` within `fuel` non-FS instructions. -/
def nonFsSubroutineSpec (sEntry : State) (fuel : Nat) : Spec FsState where
  pre fs s0 :=
    ⌜s0 = sEntry.setFs fs ∧ sEntry.mem.ReadableIsRwOrFrozen⌝ ∗
      SepProp.complementSep SepProp.emp s0.mem
  post fs _ sf :=
    let sRet := execUntilPCNonFs fuel Program.pureMem (sEntry.readReg64 Reg.lr) sEntry
    ⌜sf = sRet.setFs fs ∧ sf.fs = fs ∧ sf.brk = sEntry.brk⌝ ∗
      SepProp.complementSep SepProp.emp sf.mem

/-- Generic `FsState`-parametric `Spec` for a non-FS code block or tail-calling function
    starting at `sEntry` and reaching `targetPC` within `fuel` non-FS instructions. -/
def nonFsCodeSpec (sEntry : State) (targetPC : BitVec 64) (fuel : Nat) : Spec FsState where
  pre fs s0 :=
    ⌜s0 = sEntry.setFs fs ∧ sEntry.mem.ReadableIsRwOrFrozen⌝ ∗
      SepProp.complementSep SepProp.emp s0.mem
  post fs _ sf :=
    let sRet := execUntilPCNonFs fuel Program.pureMem targetPC sEntry
    ⌜sf = sRet.setFs fs ∧ sf.fs = fs ∧ sf.brk = sEntry.brk⌝ ∗
      SepProp.complementSep SepProp.emp sf.mem

/-- Generic `FsState`-parametric `Spec` for a non-FS exiting function (`exit` / `_Exit`)
    starting at `sEntry` and terminating with `sf.status = .Exited code` within `fuel` steps. -/
def nonFsExitSpec (sEntry : State) (fuel : Nat) (code : BitVec 64) : Spec FsState where
  pre fs s0 :=
    ⌜s0 = sEntry.setFs fs ∧ sEntry.mem.ReadableIsRwOrFrozen⌝ ∗
      SepProp.complementSep SepProp.emp s0.mem
  post fs _ sf :=
    let sRet := execStepsNonFs fuel Program.pureMem sEntry
    ⌜sf = sRet.setFs fs ∧ sf.status = .Exited code ∧ sf.fs = fs⌝ ∗
      SepProp.complementSep SepProp.emp sf.mem
  onExit fs c _ sf :=
    let sRet := execStepsNonFs fuel Program.pureMem sEntry
    ⌜c = code ∧ sf = sRet.setFs fs ∧ sf.status = .Exited code ∧ sf.fs = fs⌝ ∗
      SepProp.complementSep SepProp.emp sf.mem

/-- Generic `FsState`-parametric `Spec` for a non-FS subroutine stepping from `sEntry` to `sRet`. -/
def nonFsSubroutinePairSpec (sEntry sRet : State) : Spec FsState where
  pre fs s0 :=
    ⌜s0 = sEntry.setFs fs ∧ sEntry.mem.ReadableIsRwOrFrozen⌝ ∗
      SepProp.complementSep SepProp.emp s0.mem
  post fs _ sf :=
    ⌜sf = sRet.setFs fs ∧ sf.fs = fs ∧ sf.brk = sEntry.brk⌝ ∗
      SepProp.complementSep SepProp.emp sf.mem

/-- Introduce `subroutine_ok Program.pureMem addr (nonFsSubroutinePairSpec sEntry sRet)`. -/
theorem subroutine_ok_of_pair {sEntry sRet : State} {addr : BitVec 64}
    (h_steps : ∀ fs : FsState, Steps Program.pureMem (sEntry.setFs fs) (sRet.setFs fs))
    (h_entry : sEntry.pc = addr)
    (h_pc : sRet.pc = sEntry.readReg64 Reg.lr)
    (h_st : sRet.status = .Running)
    (h_cc : CallingConventionPreserved sEntry sRet)
    (h_brk : sRet.brk = sEntry.brk) :
    subroutine_ok Program.pureMem addr (nonFsSubroutinePairSpec sEntry sRet) := by
  subst h_entry
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro fs R s0 _ _ hpre _ _
  obtain ⟨⟨hs0, hwf⟩, hpre'⟩ := pure_complementSep_elim hpre
  subst hs0
  have h_post_mem :
      (sRet.setFs fs).mem ⊨ SepProp.complementSep SepProp.emp (sRet.setFs fs).mem ∗ R :=
    Steps.complementSep_frame (h_steps fs) hwf hpre'
  refine ⟨sRet.setFs fs, h_steps fs, Or.inl ⟨⟨h_pc, h_cc.1, h_st⟩,
    CallingConventionPreserved.setFs fs fs h_cc, ?_⟩⟩
  exact pure_complementSep_intro ⟨rfl, rfl, h_brk⟩ h_post_mem

/-- Generic `FsState`-parametric `Spec` for a non-FS code block stepping from `sEntry` to `sRet`. -/
def nonFsCodePairSpec (sEntry sRet : State) : Spec FsState where
  pre fs s0 :=
    ⌜s0 = sEntry.setFs fs ∧ sEntry.mem.ReadableIsRwOrFrozen⌝ ∗
      SepProp.complementSep SepProp.emp s0.mem
  post fs _ sf :=
    ⌜sf = sRet.setFs fs ∧ sf.fs = fs ∧ sf.brk = sEntry.brk⌝ ∗
      SepProp.complementSep SepProp.emp sf.mem

/-- Introduce `code_ok Program.pureMem addr targetPC (nonFsCodePairSpec sEntry sRet)`. -/
theorem code_ok_of_pair {sEntry sRet : State} {addr targetPC : BitVec 64}
    (h_steps : ∀ fs : FsState, Steps Program.pureMem (sEntry.setFs fs) (sRet.setFs fs))
    (h_entry : sEntry.pc = addr)
    (h_pc : sRet.pc = targetPC)
    (h_st : sRet.status = .Running)
    (h_brk : sRet.brk = sEntry.brk) :
    code_ok Program.pureMem addr targetPC (nonFsCodePairSpec sEntry sRet) := by
  subst h_entry
  intro fs R s0 _ _ hpre _
  obtain ⟨⟨hs0, hwf⟩, hpre'⟩ := pure_complementSep_elim hpre
  subst hs0
  have h_post_mem :
      (sRet.setFs fs).mem ⊨ SepProp.complementSep SepProp.emp (sRet.setFs fs).mem ∗ R :=
    Steps.complementSep_frame (h_steps fs) hwf hpre'
  refine ⟨sRet.setFs fs, h_steps fs, Or.inl ⟨?_, ?_, ?_⟩⟩
  · simpa [State.setFs] using h_pc
  · simpa [State.setFs] using h_st
  · exact pure_complementSep_intro ⟨rfl, rfl, by simpa [State.setFs] using h_brk⟩ h_post_mem

/-- Generic `FsState`-parametric `Spec` for a non-FS exiting function stepping from `sEntry` to `sRet`. -/
def nonFsExitPairSpec (sEntry sRet : State) (code : BitVec 64) : Spec FsState where
  pre fs s0 :=
    ⌜s0 = sEntry.setFs fs ∧ sEntry.mem.ReadableIsRwOrFrozen⌝ ∗
      SepProp.complementSep SepProp.emp s0.mem
  post fs _ sf :=
    ⌜sf = sRet.setFs fs ∧ sf.status = .Exited code ∧ sf.fs = fs⌝ ∗
      SepProp.complementSep SepProp.emp sf.mem
  onExit fs c _ sf :=
    ⌜c = code ∧ sf = sRet.setFs fs ∧ sf.status = .Exited code ∧ sf.fs = fs⌝ ∗
      SepProp.complementSep SepProp.emp sf.mem

/-- Introduce `exit_ok Program.pureMem addr (fun _ => code) (nonFsExitPairSpec sEntry sRet code)`. -/
theorem exit_ok_of_pair {sEntry sRet : State} {addr code : BitVec 64}
    (h_steps : ∀ fs : FsState, Steps Program.pureMem (sEntry.setFs fs) (sRet.setFs fs))
    (h_entry : sEntry.pc = addr)
    (h_st : sRet.status = .Exited code) :
    exit_ok Program.pureMem addr (fun _ => code) (nonFsExitPairSpec sEntry sRet code) := by
  subst h_entry
  intro fs R s0 _ _ hpre _
  obtain ⟨⟨hs0, hwf⟩, hpre'⟩ := pure_complementSep_elim hpre
  subst hs0
  have h_post_mem :
      (sRet.setFs fs).mem ⊨ SepProp.complementSep SepProp.emp (sRet.setFs fs).mem ∗ R :=
    Steps.complementSep_frame (h_steps fs) hwf hpre'
  have h_ex : (sRet.setFs fs).status = .Exited code := by
    simpa [State.setFs] using h_st
  refine ⟨sRet.setFs fs, h_steps fs, Or.inl ⟨h_ex, ?_⟩⟩
  exact pure_complementSep_intro ⟨rfl, h_ex, rfl⟩ h_post_mem

/-- Introduce `subroutine_ok Program.pureMem addr (nonFsExitPairSpec sEntry sRet code)`. -/
theorem subroutine_ok_exit_of_pair {sEntry sRet : State} {addr code : BitVec 64}
    (h_steps : ∀ fs : FsState, Steps Program.pureMem (sEntry.setFs fs) (sRet.setFs fs))
    (h_entry : sEntry.pc = addr)
    (h_st : sRet.status = .Exited code) :
    subroutine_ok Program.pureMem addr (nonFsExitPairSpec sEntry sRet code) := by
  subst h_entry
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro fs R s0 _ _ hpre _ _
  obtain ⟨⟨hs0, hwf⟩, hpre'⟩ := pure_complementSep_elim hpre
  subst hs0
  have h_post_mem :
      (sRet.setFs fs).mem ⊨ SepProp.complementSep SepProp.emp (sRet.setFs fs).mem ∗ R :=
    Steps.complementSep_frame (h_steps fs) hwf hpre'
  have h_ex : (sRet.setFs fs).status = .Exited code := by
    simpa [State.setFs] using h_st
  refine ⟨sRet.setFs fs, h_steps fs, Or.inr (Or.inr (Or.inl ⟨code, h_ex, ?_⟩))⟩
  exact pure_complementSep_intro ⟨rfl, rfl, h_ex, rfl⟩ h_post_mem

/-- Concrete `Spec Unit` for a subroutine stepping from `sEntry` to `sRet`. -/
def concreteSubroutinePairSpec (sEntry sRet : State) : Spec Unit where
  pre _ s0 :=
    ⌜s0 = sEntry ∧ sEntry.mem.ReadableIsRwOrFrozen⌝ ∗
      SepProp.complementSep SepProp.emp s0.mem
  post _ _ sf :=
    ⌜sf = sRet ∧ sf.fs = sRet.fs ∧ sf.brk = sEntry.brk⌝ ∗
      SepProp.complementSep SepProp.emp sf.mem

/-- Introduce `subroutine_ok Program.pureMem addr (concreteSubroutinePairSpec sEntry sRet)`. -/
theorem concreteSubroutine_ok_of_pair {sEntry sRet : State} {addr : BitVec 64}
    (h_steps : Steps Program.pureMem sEntry sRet)
    (h_entry : sEntry.pc = addr)
    (h_pc : sRet.pc = sEntry.readReg64 Reg.lr)
    (h_st : sRet.status = .Running)
    (h_cc : CallingConventionPreserved sEntry sRet)
    (h_brk : sRet.brk = sEntry.brk) :
    subroutine_ok Program.pureMem addr (concreteSubroutinePairSpec sEntry sRet) := by
  subst h_entry
  simp only [subroutine_ok_iff, reaches_outcome_iff]
  intro _ R s0 _ _ hpre _ _
  obtain ⟨⟨hs0, hwf⟩, hpre'⟩ := pure_complementSep_elim hpre
  subst hs0
  have h_post_mem :
      sRet.mem ⊨ SepProp.complementSep SepProp.emp sRet.mem ∗ R :=
    Steps.complementSep_frame h_steps hwf hpre'
  refine ⟨sRet, h_steps, Or.inl ⟨⟨h_pc, h_cc.1, h_st⟩, h_cc, ?_⟩⟩
  exact pure_complementSep_intro ⟨rfl, rfl, h_brk⟩ h_post_mem

/-- Concrete `Spec Unit` for a code block stepping from `sEntry` to `sRet`. -/
def concreteCodePairSpec (sEntry sRet : State) : Spec Unit where
  pre _ s0 :=
    ⌜s0 = sEntry ∧ sEntry.mem.ReadableIsRwOrFrozen⌝ ∗
      SepProp.complementSep SepProp.emp s0.mem
  post _ _ sf :=
    ⌜sf = sRet ∧ sf.fs = sRet.fs ∧ sf.brk = sEntry.brk⌝ ∗
      SepProp.complementSep SepProp.emp sf.mem

/-- Introduce `code_ok Program.pureMem addr targetPC (concreteCodePairSpec sEntry sRet)`. -/
theorem concreteCode_ok_of_pair {sEntry sRet : State} {addr targetPC : BitVec 64}
    (h_steps : Steps Program.pureMem sEntry sRet)
    (h_entry : sEntry.pc = addr)
    (h_pc : sRet.pc = targetPC)
    (h_st : sRet.status = .Running)
    (h_brk : sRet.brk = sEntry.brk) :
    code_ok Program.pureMem addr targetPC (concreteCodePairSpec sEntry sRet) := by
  subst h_entry
  intro _ R s0 _ _ hpre _
  obtain ⟨⟨hs0, hwf⟩, hpre'⟩ := pure_complementSep_elim hpre
  subst hs0
  have h_post_mem :
      sRet.mem ⊨ SepProp.complementSep SepProp.emp sRet.mem ∗ R :=
    Steps.complementSep_frame h_steps hwf hpre'
  refine ⟨sRet, h_steps, Or.inl ⟨h_pc, h_st, ?_⟩⟩
  exact pure_complementSep_intro ⟨rfl, rfl, h_brk⟩ h_post_mem

end Arm64.Process
