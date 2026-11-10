/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Invariant
public import ProofLib.OpcodeExclusion
public import ProofLib.SepLogic.WP
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Virtual-Memory-Preserving Step and Cut Rules

Recovers virtual-memory preservation (`VmFieldsPreserved`, keeping `brk`, `brkStart`,
`physMemAvail`, and `mem.perm` unchanged) across arbitrary CPU instructions and non-VM Linux
syscalls (`nonVmSvc`, covering `Stdio`, `FileIo`, `Poll`, `Signals`, `Time`, `Random`, and `Misc`).
Any `Steps (prog.withSvc nonVmSvc) s sf` trace ending in `sf.status = .Running` agrees step-for-step
with `Steps prog s sf` and satisfies `VmFieldsPreserved s sf` even when intermediate steps used
abstract-memory `SepWP` load/store rules (`SepWP.of_nonVm`, `SepWP.seq_nonVm`).
-/

set_option autoImplicit false

@[expose] public section

namespace ProofLib.StdStartup

open Arm64 ProofLib

/-! ## State field normalization lemmas -/

@[simp, arm64_norm, wp_norm]
theorem State.writeReg64_sigActions (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).sigActions = s.sigActions := by cases s; cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.writeReg32_sigActions (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).sigActions = s.sigActions := State.writeReg64_sigActions s r _

@[simp, arm64_norm, wp_norm]
theorem State.writeReg_sigActions (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).sigActions = s.sigActions := State.writeReg64_sigActions s r _

@[simp, arm64_norm, wp_norm]
theorem State.setPC_sigActions (s : State) (pc : BitVec 64) :
    (s.setPC pc).sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.advancePC_sigActions (s : State) :
    s.advancePC.sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.setPState_sigActions (s : State) (ps : PState) :
    (s.setPState ps).sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.setMem_sigActions (s : State) (m : Memory) :
    (s.setMem m).sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.setFs_sigActions (s : State) (fs : FsState) :
    (s.setFs fs).sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.appendTrace_sigActions (s : State) (evs : List TraceEvent) :
    (s.appendTrace evs).sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.nextOracle_sigActions (s : State) :
    s.nextOracle.sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.writeVReg128_sigActions (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.writeVReg64_sigActions (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.writeVReg32_sigActions (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.setFpsr_sigActions (s : State) (f : BitVec 32) :
    (s.setFpsr f).sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.orFpsr_sigActions (s : State) (f : BitVec 32) :
    (s.orFpsr f).sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.setStatus_sigActions (s : State) (st : ExecStatus) :
    (s.setStatus st).sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.setBrk_sigActions (s : State) (b : BitVec 64) :
    (s.setBrk b).sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.setPhysMemAvail_sigActions (s : State) (n : Nat) :
    (s.setPhysMemAvail n).sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.stepExclOracle_sigActions (s : State) :
    s.stepExclOracle.sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.stepExclLoop_sigActions (s : State) :
    s.stepExclLoop.sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.setTpidrEl0_sigActions (s : State) (v : BitVec 64) :
    (setTpidrEl0 s v).sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.panicked_sigActions (s : State) :
    (Rust.panicked s).sigActions = s.sigActions := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.applyWriteback_sigActions (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).sigActions = s.sigActions := by cases wb <;> simp [applyWriteback]

@[simp, arm64_norm, wp_norm]
theorem State.applyWriteback_fs (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).fs = s.fs := by cases wb <;> simp [applyWriteback]

@[simp, arm64_norm, wp_norm]
theorem State.applyWriteback_trace (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).trace = s.trace := by cases wb <;> simp [applyWriteback]

@[simp, arm64_norm, wp_norm]
theorem State.applyWriteback_tpidrEl0 (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).tpidrEl0 = s.tpidrEl0 := by cases wb <;> simp [applyWriteback]

@[simp, arm64_norm, wp_norm]
theorem State.applyWriteback_brk (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).brk = s.brk := by cases wb <;> simp [applyWriteback]

@[simp, arm64_norm, wp_norm]
theorem State.applyWriteback_brkStart (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).brkStart = s.brkStart := by cases wb <;> simp [applyWriteback]

@[simp, arm64_norm, wp_norm]
theorem State.writeReg64_sigAltStack (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).sigAltStack = s.sigAltStack := by cases s; cases r <;> rfl

@[simp, arm64_norm, wp_norm]
theorem State.writeReg32_sigAltStack (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).sigAltStack = s.sigAltStack := State.writeReg64_sigAltStack s r _

@[simp, arm64_norm, wp_norm]
theorem State.writeReg_sigAltStack (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).sigAltStack = s.sigAltStack := State.writeReg64_sigAltStack s r _

@[simp, arm64_norm, wp_norm]
theorem State.setPC_sigAltStack (s : State) (pc : BitVec 64) :
    (s.setPC pc).sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.advancePC_sigAltStack (s : State) :
    s.advancePC.sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.setPState_sigAltStack (s : State) (ps : PState) :
    (s.setPState ps).sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.setMem_sigAltStack (s : State) (m : Memory) :
    (s.setMem m).sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.setFs_sigAltStack (s : State) (fs : FsState) :
    (s.setFs fs).sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.appendTrace_sigAltStack (s : State) (evs : List TraceEvent) :
    (s.appendTrace evs).sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.nextOracle_sigAltStack (s : State) :
    s.nextOracle.sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.writeVReg128_sigAltStack (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.writeVReg64_sigAltStack (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.writeVReg32_sigAltStack (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.setFpsr_sigAltStack (s : State) (f : BitVec 32) :
    (s.setFpsr f).sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.orFpsr_sigAltStack (s : State) (f : BitVec 32) :
    (s.orFpsr f).sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.setStatus_sigAltStack (s : State) (st : ExecStatus) :
    (s.setStatus st).sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.setBrk_sigAltStack (s : State) (b : BitVec 64) :
    (s.setBrk b).sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.setPhysMemAvail_sigAltStack (s : State) (n : Nat) :
    (s.setPhysMemAvail n).sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.stepExclOracle_sigAltStack (s : State) :
    s.stepExclOracle.sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.stepExclLoop_sigAltStack (s : State) :
    s.stepExclLoop.sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.setTpidrEl0_sigAltStack (s : State) (v : BitVec 64) :
    (setTpidrEl0 s v).sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.panicked_sigAltStack (s : State) :
    (Rust.panicked s).sigAltStack = s.sigAltStack := by cases s; rfl

@[simp, arm64_norm, wp_norm]
theorem State.applyWriteback_sigAltStack (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).sigAltStack = s.sigAltStack := by cases wb <;> simp [applyWriteback]

/-! ## Non-VM syscall bundle and `Program.withSvc` bridges -/

/-- All modeled Linux AArch64 syscalls except virtual-memory allocation (`Syscall.allocTable`). -/
def nonVmSyscallTable : List (BitVec 64 × (State → State)) :=
  Syscall.stdioTable ++ Syscall.fileIoOnlyTable ++ Syscall.pollTable ++
  Syscall.signalsTable ++ Syscall.timeTable ++ Syscall.randomTable ++ Syscall.miscTable

/-- Supervisor-call dispatcher excluding `brk`/`mmap`/`munmap`/`mremap`/`mprotect`/`madvise`. -/
def nonVmSvc : State → State := Syscall.dispatch nonVmSyscallTable

/-- Virtual-memory layout fields preserved across CPU instructions and `nonVmSvc`:
    program break (`brk`, `brkStart`), physical memory budget (`physMemAvail`), and per-byte page
    permissions (`mem.perm`). -/
structure VmFieldsPreserved (s0 sf : State) : Prop where
  brk_eq          : sf.brk = s0.brk
  brkStart_eq     : sf.brkStart = s0.brkStart
  physMemAvail_eq : sf.physMemAvail = s0.physMemAvail
  perm_eq         : ∀ a, sf.mem.perm a = s0.mem.perm a

theorem VmFieldsPreserved.refl (s : State) : VmFieldsPreserved s s :=
  ⟨rfl, rfl, rfl, fun _ => rfl⟩

theorem VmFieldsPreserved.trans {s0 s1 s2 : State}
    (h01 : VmFieldsPreserved s0 s1) (h12 : VmFieldsPreserved s1 s2) :
    VmFieldsPreserved s0 s2 :=
  ⟨h12.brk_eq.trans h01.brk_eq, h12.brkStart_eq.trans h01.brkStart_eq,
   h12.physMemAvail_eq.trans h01.physMemAvail_eq,
   fun a => (h12.perm_eq a).trans (h01.perm_eq a)⟩

theorem Program.withSvc_svc (prog : Program) (svc : State → State) :
    (prog.withSvc svc).svc = svc := by cases prog; rfl

theorem Program.withSvc_fetch (prog : Program) (svc : State → State) (pc : BitVec 64) :
    (prog.withSvc svc).fetch pc = prog.fetch pc := by cases prog; rfl

theorem Program.withSvc_externAt? (prog : Program) (svc : State → State) (pc : BitVec 64) :
    (prog.withSvc svc).externAt? pc = prog.externAt? pc := by cases prog; rfl

theorem Program.withSvc_codeLoaded (prog : Program) (svc : State → State) (m : Memory) :
    (prog.withSvc svc).CodeLoaded m ↔ prog.CodeLoaded m := by
  unfold Program.CodeLoaded Program.withSvc; rfl

@[simp 2100, arm64_norm 2100, wp_norm]
theorem Program.withSvc_nonVmSvc_svc (prog : Program) :
    (prog.withSvc nonVmSvc).svc = nonVmSvc := Program.withSvc_svc prog nonVmSvc

@[simp 2100, arm64_norm 2100, wp_norm]
theorem Program.withSvc_nonVmSvc_fetch (prog : Program) (pc : BitVec 64) :
    (prog.withSvc nonVmSvc).fetch pc = prog.fetch pc := Program.withSvc_fetch prog nonVmSvc pc

@[simp 2100, arm64_norm 2100, wp_norm]
theorem Program.withSvc_nonVmSvc_externAt? (prog : Program) (pc : BitVec 64) :
    (prog.withSvc nonVmSvc).externAt? pc = prog.externAt? pc :=
  Program.withSvc_externAt? prog nonVmSvc pc

@[simp 2100, arm64_norm 2100, wp_norm]
theorem Program.withSvc_nonVmSvc_codeLoaded (prog : Program) (m : Memory) :
    (prog.withSvc nonVmSvc).CodeLoaded m ↔ prog.CodeLoaded m :=
  Program.withSvc_codeLoaded prog nonVmSvc m

/-! ## Handler agreement and `VmFieldsPreserved` across `nonVmSyscallTable` -/

private theorem standardTable_find_of_nonVm_some {nr : BitVec 64} {p : BitVec 64 × (State → State)}
    (h : nonVmSyscallTable.find? (·.1 == nr) = some p) :
    Syscall.standardTable.find? (·.1 == nr) = some p := by
  let pre := Syscall.stdioTable ++ Syscall.fileIoOnlyTable ++ Syscall.pollTable
  let suf := Syscall.signalsTable ++ Syscall.timeTable ++ Syscall.randomTable ++ Syscall.miscTable
  have h1 : nonVmSyscallTable = pre ++ suf := by
    simp only [nonVmSyscallTable, pre, suf, List.append_assoc]
  have h2 : Syscall.standardTable = pre ++ (Syscall.allocTable ++ suf) := by
    simp only [Syscall.standardTable, pre, suf, List.append_assoc]
  rw [h1, List.find?_append] at h
  rw [h2, List.find?_append]
  cases hpre : pre.find? (·.1 == nr) with
  | some q => rw [hpre] at h; exact h
  | none =>
    rw [hpre] at h
    simp only [Option.none_or] at h ⊢
    rw [List.find?_append]
    have hmem := List.mem_of_find?_eq_some h
    have hpred : (p.1 == nr) = true :=
      List.find?_some (p := fun x : BitVec 64 × (State → State) => x.1 == nr) h
    have heq : p.1 = nr := beq_iff_eq.mp hpred
    subst heq
    simp only [suf, Syscall.signalsTable, Syscall.timeTable, Syscall.randomTable, Syscall.miscTable,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
    have halloc : Syscall.allocTable.find? (·.1 == p.1) = none := by
      rcases hmem with (((h0 | h0 | h0 | h0 | h0) | h0) | h0) | (h0 | h0 | h0 | h0) <;>
        (rw [congrArg Prod.fst h0]; rfl)
    rw [halloc, Option.none_or]; exact h

private theorem evalPpollEntries_perm {fs : FsState} {ufds : BitVec 64} :
    ∀ (rem idx count : Nat) (m m' : Memory) (c' : Nat),
      evalPpollEntries fs m ufds rem idx count = some (m', c') →
      m'.perm = m.perm
  | 0, _, _, m, m', _, h => by
    simp only [evalPpollEntries, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩; rfl
  | rem + 1, idx, count, m, m', c', h => by
    dsimp (config := { zetaHave := true }) only [evalPpollEntries] at h
    split at h
    · cases h
    · split at h
      · exact (evalPpollEntries_perm rem (idx + 1) (count + 1) _ m' c' h).trans
          (Memory.perm_write16 m _ _)
      · split at h
        · exact (evalPpollEntries_perm rem (idx + 1) count _ m' c' h).trans
            (Memory.perm_write16 m _ _)
        · cases h

private def projVm (s : State) := (s.brk, s.brkStart, s.physMemAvail, s.mem.perm)
private theorem vmPres_of_proj {s0 sf : State} (h : projVm sf = projVm s0) :
    VmFieldsPreserved s0 sf :=
  ⟨congrArg Prod.fst h, congrArg (fun p => p.2.1) h, congrArg (fun p => p.2.2.1) h,
   fun a => congrFun (congrArg (fun p => p.2.2.2) h) a⟩

private theorem projVm_adv (s : State) : projVm s.advancePC = projVm s := by cases s; rfl
private theorem projVm_w64 (s : State) (r : Reg) (v : BitVec 64) :
    projVm (s.writeReg64 r v) = projVm s := by cases s; cases r <;> rfl
private theorem projVm_st (s : State) (st : ExecStatus) :
    projVm (s.setStatus st) = projVm s := by cases s; rfl
private theorem projVm_fs (s : State) (fs : FsState) :
    projVm (s.setFs fs) = projVm s := by cases s; rfl
private theorem projVm_tr (s : State) (evs : List TraceEvent) :
    projVm (s.appendTrace evs) = projVm s := by cases s; rfl
private theorem projVm_or (s : State) : projVm s.nextOracle = projVm s := by cases s; rfl
private theorem projVm_sig (s : State) (sig : BitVec 32) (sa : SigAction) :
    projVm (s.setSigAction sig sa) = projVm s := by cases s; rfl
private theorem projVm_sas (s : State) (sas : SigAltStack) :
    projVm (s.setSigAltStack sas) = projVm s := by cases s; rfl
private theorem projVm_wb (s : State) (addr : BitVec 64) (bs : List (BitVec 8)) :
    projVm (s.setMem (s.mem.writeBytes addr bs)) = projVm s := by
  cases s; simp [projVm, State.setMem, Memory.perm_writeBytes]

private theorem projVm_readCommon (s : State) (isPread : Bool) :
    projVm (execReadCommon s isPread) = projVm s := by
  dsimp (config := { zetaHave := true }) only [execReadCommon]
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0)) <;>
    simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, projVm_fs, projVm_wb, ite_self]

private theorem projVm_write (s : State) : projVm (execWrite s) = projVm s := by
  dsimp (config := { zetaHave := true }) only [execWrite]
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0)) with
  | none => simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, projVm_tr, ite_self]
  | some desc =>
    cases desc.kind <;>
      simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, projVm_tr, projVm_fs, ite_self]

private theorem projVm_rwvFrame : ProofLib.RwvFrame (fun a b => projVm b = projVm a) :=
  ProofLib.RwvFrame.eqOn projVm projVm_w64 projVm_adv projVm_st (fun s _ _ => by cases s; rfl)

private theorem projVm_ppoll (s : State) :
    projVm (execPpoll s) = projVm s := by
  dsimp (config := { zetaHave := true }) only [execPpoll]
  cases hev : evalPpollEntries s.fs s.mem (s.readReg64 Reg.x0) (s.readReg32 Reg.x1).toNat 0 0 with
  | none =>
    simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, ite_self]
  | some mc =>
    rcases mc with ⟨m', cnt⟩
    have hm : projVm (s.setMem m') = projVm s := by
      cases s; simp [projVm, State.setMem, evalPpollEntries_perm _ 0 0 _ m' cnt hev]
    simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, hm, ite_self]

private theorem projVm_sigaltstack (s : State) :
    projVm (execSigaltstack s) = projVm s := by
  dsimp (config := { zetaHave := true }) only [execSigaltstack]
  by_cases huss : (s.readReg64 Reg.x0 == 0#64) = true
  · simp only [huss, ↓reduceIte, apply_ite projVm, projVm_adv, projVm_w64, projVm_st, projVm_wb, ite_self]
  · by_cases hdis : ((s.mem.read32 (s.readReg64 Reg.x0 + 8#64) &&& ~~~SS_AUTODISARM) == SS_DISABLE) = true
    · simp only [Bool.eq_false_iff.mpr huss, hdis, Bool.false_eq_true, ↓reduceIte,
        apply_ite projVm, projVm_adv, projVm_w64, projVm_st, projVm_wb, projVm_sas, ite_self]
    · simp only [Bool.eq_false_iff.mpr huss, Bool.eq_false_iff.mpr hdis, Bool.false_eq_true, ↓reduceIte,
        apply_ite projVm, projVm_adv, projVm_w64, projVm_st, projVm_wb, projVm_sas, ite_self]

private theorem projVm_rtSigaction (s : State) :
    projVm (execRtSigaction s) = projVm s := by
  dsimp (config := { zetaHave := true }) only [execRtSigaction]
  by_cases hact : (s.readReg64 Reg.x1 == 0#64) = true
  · simp only [hact, ↓reduceIte, apply_ite projVm, projVm_adv, projVm_w64, projVm_st, projVm_wb, ite_self]
  · simp only [Bool.eq_false_iff.mpr hact, Bool.false_eq_true, ↓reduceIte,
      apply_ite projVm, projVm_adv, projVm_w64, projVm_st, projVm_wb, projVm_sig, ite_self]

set_option linter.unusedSimpArgs false in
private theorem nonVmHandler_preserves {nr : BitVec 64} {fn : State → State}
    (hmem : (nr, fn) ∈ nonVmSyscallTable) (s : State) :
    VmFieldsPreserved s (fn s) := by
  apply vmPres_of_proj
  simp only [nonVmSyscallTable, Syscall.stdioTable, Syscall.fileIoOnlyTable, Syscall.pollTable,
    Syscall.signalsTable, Syscall.timeTable, Syscall.randomTable, Syscall.miscTable,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with ((((((h | h | h | h | h | h) | (h | h | h | h | h | h | h)) | h) | (h | h | h | h | h)) | h) | h) | (h | h | h | h) <;>
    injection h with _ hfn <;> subst hfn
  · exact projVm_readCommon s false
  · exact projVm_write s
  · exact ProofLib.execReadv_preserves projVm_rwvFrame (projVm_readCommon · false) s
  · exact ProofLib.execWritev_preserves projVm_rwvFrame projVm_write s
  · exact projVm_st s _
  · exact projVm_st s _
  · dsimp (config := { zetaHave := true }) only [execFcntl]
    cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0)) <;>
      simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, projVm_fs, ite_self]
  · dsimp (config := { zetaHave := true }) only [execIoctl]
    cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0)) with
    | none => simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, ite_self]
    | some desc =>
      cases desc.kind <;>
        simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, projVm_fs, projVm_wb,
          ite_self]
  · dsimp (config := { zetaHave := true }) only [execOpenat]
    have h_verdict : ∀ v, projVm (applyOpenVerdict s v) = projVm s := fun v => by
      rcases v with ⟨_, _, _ | _⟩ | _ | _ <;>
        simp only [applyOpenVerdict, projVm_adv, projVm_w64, projVm_st, projVm_tr, projVm_fs]
    cases checkOpenFlags (s.readReg32 Reg.x2) with
    | some v => exact h_verdict v
    | none =>
      cases readCString s.mem (s.readReg64 Reg.x1) with
      | trap _ => exact projVm_st s _
      | errno _ => simp only [projVm_adv, projVm_w64]
      | ok _ => exact h_verdict _
  · dsimp (config := { zetaHave := true }) only [execClose]
    cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0)) with
    | none => simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, ite_self]
    | some desc =>
      cases desc.kind <;>
        simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, projVm_fs, ite_self]
  · dsimp only [execLseek]
    cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0)) with
    | none => simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, ite_self]
    | some desc =>
      dsimp only
      let fileLen : Int := match s.fs.files desc.path with | some (.file bs) => bs.length | _ => 0
      let baseOff? : Option Int :=
        if s.readReg32 Reg.x2 == 0#32 then some 0
        else if s.readReg32 Reg.x2 == 1#32 then some (Int.ofNat desc.offset)
        else if s.readReg32 Reg.x2 == 2#32 then some fileLen
        else none
      change projVm (if (s.readReg32 Reg.x0).slt 0#32 then (s.writeReg64 Reg.x0 (-EBADF)).advancePC
        else if desc.kind != .localFile then s.setStatus (.Exception "unmodeled non-file fd")
        else if s.readReg32 Reg.x2 == 3#32 || s.readReg32 Reg.x2 == 4#32 then
          if decide ((s.readReg64 Reg.x1).toInt ≥ fileLen) then
            (s.writeReg64 Reg.x0 (-ENXIO)).advancePC
          else s.setStatus (.Exception "unmodeled SEEK_DATA/SEEK_HOLE in-bounds offset")
        else match baseOff? with
          | none => (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
          | some base =>
            if base + (s.readReg64 Reg.x1).toInt < 0 || base + (s.readReg64 Reg.x1).toInt ≥ 2 ^ 63 then
              (s.writeReg64 Reg.x0 (-EINVAL)).advancePC
            else if decide (base + (s.readReg64 Reg.x1).toInt ≥ Int.ofNat FS_SAFE_MAX_FILESIZE) then
              s.setStatus (.Exception "unmodeled lseek offset >= FS_SAFE_MAX_FILESIZE")
            else ((s.setFs (s.fs.setFd (BitVec.zeroExtend 64 (s.readReg32 Reg.x0))
              (some { desc with offset := (base + (s.readReg64 Reg.x1).toInt).toNat }))).writeReg64
                Reg.x0 (BitVec.ofNat 64 (base + (s.readReg64 Reg.x1).toInt).toNat)).advancePC) = projVm s
      cases baseOff? <;>
        simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, projVm_fs, ite_self]
  · exact projVm_readCommon s true
  · dsimp (config := { zetaHave := true }) only [execFstat]
    cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0)) with
    | none => simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, ite_self]
    | some desc =>
      cases desc.kind <;>
        simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, projVm_wb, ite_self]
  · exact projVm_ppoll s
  · dsimp (config := { zetaHave := true }) only [execTkill]
    simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, ite_self]
  · dsimp (config := { zetaHave := true }) only [execTgkill]
    simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, ite_self]
  · exact projVm_sigaltstack s
  · exact projVm_rtSigaction s
  · dsimp (config := { zetaHave := true }) only [execRtSigprocmask]
    simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, projVm_wb, ite_self]
  · dsimp (config := { zetaHave := true }) only [execClockGettime]
    simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_or, projVm_st, projVm_wb, ite_self]
  · dsimp (config := { zetaHave := true }) only [execGetrandom]
    simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_or, projVm_wb, ite_self]
  · dsimp only [execSetTidAddress]; simp only [projVm_adv, projVm_w64]
  · dsimp (config := { zetaHave := true }) only [execSchedGetaffinity]
    simp only [apply_ite projVm, projVm_adv, projVm_w64, projVm_st, projVm_wb, ite_self]
  · dsimp only [execGetpid]; simp only [projVm_adv, projVm_w64]
  · dsimp only [execGetpid]; simp only [projVm_adv, projVm_w64]

/-! ## `Step`, `Steps`, and `SepWP` lifting under `nonVmSvc` -/

private theorem steps_start_running {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private def projBrk (s : State) := (s.brk, s.brkStart, s.physMemAvail)
private theorem projBrk_adv (s : State) : projBrk s.advancePC = projBrk s := by cases s; rfl
private theorem projBrk_pc (s : State) (p : BitVec 64) : projBrk (s.setPC p) = projBrk s := by cases s; rfl
private theorem projBrk_w64 (s : State) (r : Reg) (v : BitVec 64) : projBrk (s.writeReg64 r v) = projBrk s := by
  cases s; cases r <;> rfl
private theorem projBrk_w32 (s : State) (r : Reg) (v : BitVec 32) : projBrk (s.writeReg32 r v) = projBrk s :=
  projBrk_w64 s r _
private theorem projBrk_w (s : State) (w : Width) (r : Reg) (v : BitVec 64) : projBrk (s.writeReg w r v) = projBrk s :=
  projBrk_w64 s r _
private theorem projBrk_v128 (s : State) (r : BitVec 5) (v : BitVec 128) : projBrk (s.writeVReg128 r v) = projBrk s := by
  cases s; rfl
private theorem projBrk_v64 (s : State) (r : BitVec 5) (v : BitVec 64) : projBrk (s.writeVReg64 r v) = projBrk s :=
  projBrk_v128 s r _
private theorem projBrk_v32 (s : State) (r : BitVec 5) (v : BitVec 32) : projBrk (s.writeVReg32 r v) = projBrk s :=
  projBrk_v128 s r _
private theorem projBrk_ps (s : State) (p : PState) : projBrk (s.setPState p) = projBrk s := by cases s; rfl
private theorem projBrk_fp (s : State) (f : BitVec 32) : projBrk (s.setFpsr f) = projBrk s := by cases s; rfl
private theorem projBrk_ofp (s : State) (f : BitVec 32) : projBrk (s.orFpsr f) = projBrk s := by cases s; rfl
private theorem projBrk_st (s : State) (st : ExecStatus) : projBrk (s.setStatus st) = projBrk s := by cases s; rfl
private theorem projBrk_wst (s : State) (st : ExecStatus) : projBrk { s with status := st } = projBrk s := by cases s; rfl
private theorem projBrk_mem (s : State) (m : Memory) : projBrk (s.setMem m) = projBrk s := by cases s; rfl
private theorem projBrk_tp (s : State) (v : BitVec 64) : projBrk (setTpidrEl0 s v) = projBrk s := by cases s; rfl
private theorem projBrk_ex (s : State) : projBrk s.stepExclOracle = projBrk s := by cases s; rfl
private theorem projBrk_as (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) :
    projBrk (applySimdResult s rd r) = projBrk s := by cases s; cases r <;> rfl
private theorem projBrk_ass (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) (sat : Option (BitVec 32)) :
    projBrk (applySimdSatResult s rd r sat) = projBrk s := by cases s; cases r <;> cases sat <;> rfl
private theorem projBrk_slr (sz : SimdMemSize) (m : Memory) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State), projBrk (simdLoadRegs sz m n vt ea s) = projBrk s
  | 0, _, _, _ => rfl
  | n + 1, _, _, s => (projBrk_slr sz m n _ _ _).trans (projBrk_v128 s _ _)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
theorem execInst_vmFields_of_not_isSvc0 {inst : Instr} (h : inst.isSvc0 = false) (s : State) :
    VmFieldsPreserved s (execInst inst s) := by
  have hbrk : projBrk (execInst inst s) = projBrk s := by
    cases inst
    case system isHalt imm =>
      cases isHalt
      · by_cases himm : imm == 0#16
        · have heq : imm = 0#16 := of_decide_eq_true himm; subst heq; simp [Instr.isSvc0] at h
        · dsimp only [execInst, execInstWithSvc]; simp [himm, projBrk_st]
      · dsimp only [execInst, execInstWithSvc]; by_cases himm : imm == 1#16 <;> simp [himm, projBrk_st]
    case simdThreeSame q u size rm opcode rn rd =>
      dsimp only [execInst, execInstWithSvc]
      by_cases hop : opcode == 0b00011#5
      · simp only [hop, ↓reduceIte]
        rcases size with ⟨_ | _ | _ | _ | _, _⟩ <;> try omega
        all_goals (cases u <;> first | exact (projBrk_adv _).trans (projBrk_v128 _ _ _) | exact projBrk_ass _ _ _ _)
      · simp only [hop, Bool.false_eq_true, ↓reduceIte, projBrk_adv, projBrk_v128, projBrk_st, projBrk_wst,
          projBrk_as, projBrk_ass, apply_ite projBrk, ite_self]
    case ldpSimd _ _ _ addr | stpSimd _ _ _ addr | ldrSimd _ _ addr | strSimd _ _ addr =>
      dsimp only [execInst, execInstWithSvc]
      rcases evalAddrMode s addr with ⟨_, _ | ⟨_, _⟩⟩ <;>
        simp [projBrk_adv, projBrk_mem, projBrk_v128, projBrk_w64, projBrk_st, apply_ite projBrk]
    case ldr | ldrLit | str | ldp | stp | ldnp | stnp | addSubImm | logicalImm | moveWide | bitfield
       | logicalShift | addSubShift | addSubExt | addSubCarry | condCompareReg | condCompareImm
       | condSelect | dataProc1 | dataProc2 | dataProc3 =>
      cases s; dsimp only [execInst, execInstWithSvc, execLdr, execLdrLit, execStr, execLdp, execStp,
        execAddSubImm, execLogicalImm, execMoveWide, execBitfield, execLogicalShift, execAddSubShift,
        execAddSubExt, execAddSubCarry, execCondCompare, execCondSelect, execDataProc1, execDataProc2,
        execDataProc3]; (repeat' split) <;> rfl
    all_goals
      dsimp only [execInst, execInstWithSvc]
      simp only [projBrk_adv, projBrk_pc, projBrk_w64, projBrk_w32, projBrk_w, projBrk_v128, projBrk_v64,
        projBrk_v32, projBrk_ps, projBrk_fp, projBrk_ofp, projBrk_st, projBrk_wst, projBrk_mem, projBrk_tp,
        projBrk_ex, projBrk_as, projBrk_ass, projBrk_slr, apply_ite projBrk, ite_self]
      try (cases s; (repeat' split) <;> rfl)
  exact ⟨congrArg Prod.fst hbrk, congrArg (fun p => p.2.1) hbrk,
    congrArg (fun p => p.2.2) hbrk, execInst_perm_apply_of_not_isSvc0 h s⟩

theorem evalInst_eq_execInst_of_not_isSvc0 (P : Program) {inst : Instr}
    (h : inst.isSvc0 = false) (s : State) : P.evalInst inst s = execInst inst s := by
  cases inst with
  | system isHalt imm =>
    cases isHalt
    · by_cases himm : imm == 0#16
      · have heq : imm = 0#16 := of_decide_eq_true himm; subst heq; simp [Instr.isSvc0] at h
      · simp [Program.evalInst, execInst, execInstWithSvc, himm]
    · rfl
  | _ => rfl

private theorem evalSvc_vmFields {svc : State → State} {s : State}
    (h : VmFieldsPreserved s (svc s)) : VmFieldsPreserved s (evalSvc svc s) := by
  refine ⟨h.brk_eq, h.brkStart_eq, h.physMemAvail_eq, fun a => ?_⟩
  by_cases hf : (s.mem.perm a).frozen = true
  · have hc : (evalSvc svc s).mem.cells a = s.mem.cells a := by
      simp only [evalSvc, hf, ↓reduceIte]
    unfold Memory.perm; rw [hc]
  · have hnf : (s.mem.perm a).frozen = false := Bool.eq_false_iff.mpr hf
    have hc : (evalSvc svc s).mem.cells a = (svc s).mem.cells a := by
      simp only [evalSvc, hnf, Bool.false_eq_true, ↓reduceIte]
    unfold Memory.perm; rw [hc]; exact h.perm_eq a

theorem svcKeepsFrozen_nonVmSvc : SvcKeepsFrozen nonVmSvc := by
  intro s
  cases hfind : nonVmSyscallTable.find? (·.1 == s.readReg64 Reg.x8) with
  | none =>
    have hs : nonVmSvc s = s.setStatus (.Exception "unmodeled syscall (svc)") := by
      dsimp [nonVmSvc, Syscall.dispatch]; rw [hfind]
    rw [hs]; cases s; exact ⟨Memory.KeepsFrozenCells.refl _, rfl, rfl⟩
  | some p =>
    have hstd := standardTable_find_of_nonVm_some hfind
    have hs : nonVmSvc s = Syscall.standard s := by
      dsimp [nonVmSvc, Syscall.standard, Syscall.dispatch]; rw [hfind, hstd]
    rw [hs]; exact svcKeepsFrozen_standard s

@[simp, arm64_norm, wp_norm]
theorem evalSvc_nonVmSvc (s : State) : evalSvc nonVmSvc s = nonVmSvc s :=
  evalSvc_eq_of_svcKeepsFrozen svcKeepsFrozen_nonVmSvc s

private theorem nonVmSvc_of_find {s : State} {p : BitVec 64 × (State → State)}
    (h : nonVmSyscallTable.find? (·.1 == s.readReg64 Reg.x8) = some p) :
    nonVmSvc s = p.2 s := by
  dsimp [nonVmSvc, Syscall.dispatch]; rw [h]

@[simp, arm64_norm, wp_norm]
theorem nonVmSvc_fcntl (s : State) (h : s.readReg64 .x8 = 25#64) :
    nonVmSvc s = execFcntl s := nonVmSvc_of_find (p := (25#64, execFcntl)) (by rw [h]; rfl)

@[simp, arm64_norm, wp_norm]
theorem nonVmSvc_openat (s : State) (h : s.readReg64 .x8 = 56#64) :
    nonVmSvc s = execOpenat s := nonVmSvc_of_find (p := (56#64, execOpenat)) (by rw [h]; rfl)

@[simp, arm64_norm, wp_norm]
theorem nonVmSvc_close (s : State) (h : s.readReg64 .x8 = 57#64) :
    nonVmSvc s = execClose s := nonVmSvc_of_find (p := (57#64, execClose)) (by rw [h]; rfl)

@[simp, arm64_norm, wp_norm]
theorem nonVmSvc_read (s : State) (h : s.readReg64 .x8 = 63#64) :
    nonVmSvc s = execRead s := nonVmSvc_of_find (p := (63#64, execRead)) (by rw [h]; rfl)

@[simp, arm64_norm, wp_norm]
theorem nonVmSvc_write (s : State) (h : s.readReg64 .x8 = 64#64) :
    nonVmSvc s = execWrite s := nonVmSvc_of_find (p := (64#64, execWrite)) (by rw [h]; rfl)

@[simp, arm64_norm, wp_norm]
theorem nonVmSvc_ppoll (s : State) (h : s.readReg64 .x8 = 73#64) :
    nonVmSvc s = execPpoll s := nonVmSvc_of_find (p := (73#64, execPpoll)) (by rw [h]; rfl)

@[simp, arm64_norm, wp_norm]
theorem nonVmSvc_fstat (s : State) (h : s.readReg64 .x8 = 80#64) :
    nonVmSvc s = execFstat s := nonVmSvc_of_find (p := (80#64, execFstat)) (by rw [h]; rfl)

@[simp, arm64_norm, wp_norm]
theorem nonVmSvc_exit_group (s : State) (h : s.readReg64 .x8 = 94#64) :
    nonVmSvc s = execExit s := nonVmSvc_of_find (p := (94#64, execExit)) (by rw [h]; rfl)

@[simp, arm64_norm, wp_norm]
theorem nonVmSvc_set_tid_address (s : State) (h : s.readReg64 .x8 = 96#64) :
    nonVmSvc s = execSetTidAddress s := nonVmSvc_of_find (p := (96#64, execSetTidAddress)) (by rw [h]; rfl)

@[simp, arm64_norm, wp_norm]
theorem nonVmSvc_sigaltstack (s : State) (h : s.readReg64 .x8 = 132#64) :
    nonVmSvc s = execSigaltstack s := nonVmSvc_of_find (p := (132#64, execSigaltstack)) (by rw [h]; rfl)

@[simp, arm64_norm, wp_norm]
theorem nonVmSvc_rt_sigaction (s : State) (h : s.readReg64 .x8 = 134#64) :
    nonVmSvc s = execRtSigaction s := nonVmSvc_of_find (p := (134#64, execRtSigaction)) (by rw [h]; rfl)

/-- Any `Steps (prog.withSvc nonVmSvc) s sf` reaching `sf.status = .Running` on a hook-free
    `Syscall.standard` program is a valid `Steps prog s sf` and preserves `VmFieldsPreserved`. -/
theorem Steps.of_nonVm_running {prog : Program} {s sf : State}
    (hext : ∀ pc, prog.externAt? pc = none)
    (hsvc : prog.svc = Syscall.standard)
    (hsteps : Steps (prog.withSvc nonVmSvc) s sf)
    (hrun_f : sf.status = .Running) :
    Steps prog s sf ∧ VmFieldsPreserved s sf := by
  induction hsteps with
  | refl => exact ⟨.refl _, VmFieldsPreserved.refl _⟩
  | @step s1 s2 s3 h1 hrest ih =>
    have hr2 : s2.status = .Running := steps_start_running hrest hrun_f
    rcases ih hrun_f with ⟨hsteps_rest, hvm_rest⟩
    have hf_eq : (prog.withSvc nonVmSvc).fetchMem s1.mem s1.pc = prog.fetchMem s1.mem s1.pc := rfl
    cases h1 with
    | @exec inst hr1 hfe =>
      by_cases hsvc0 : inst.isSvc0 = true
      · have hinst : inst = .system false 0#16 := by
          cases inst <;> simp [Instr.isSvc0] at hsvc0
          rcases hsvc0 with ⟨rfl, rfl⟩; rfl
        subst hinst
        have hr_svc : (nonVmSvc s1).status = .Running := by
          simpa [Program.evalInst, Program.withSvc, execInstWithSvc, evalSvc] using hr2
        dsimp [nonVmSvc, Syscall.dispatch] at hr_svc
        cases hfind : nonVmSyscallTable.find? (·.1 == s1.readReg64 Reg.x8) with
        | none =>
          rw [hfind] at hr_svc
          cases s1; cases hr_svc
        | some p =>
          rcases p with ⟨nr, fn⟩
          have hstd := standardTable_find_of_nonVm_some hfind
          have hmem := List.mem_of_find?_eq_some hfind
          have hs_eq : nonVmSvc s1 = prog.svc s1 := by
            rw [hsvc]; dsimp [nonVmSvc, Syscall.standard, Syscall.dispatch]; rw [hfind, hstd]
          have hev_eq : (prog.withSvc nonVmSvc).evalInst (.system false 0#16) s1 =
              prog.evalInst (.system false 0#16) s1 := by
            dsimp [Program.evalInst, Program.withSvc, execInstWithSvc, evalSvc]; rw [hs_eq]
          have hs_fn : nonVmSvc s1 = fn s1 := by dsimp [nonVmSvc, Syscall.dispatch]; rw [hfind]
          have hvm1 : VmFieldsPreserved s1 ((prog.withSvc nonVmSvc).evalInst (.system false 0#16) s1) := by
            dsimp [Program.evalInst, Program.withSvc, execInstWithSvc]
            exact evalSvc_vmFields (hs_fn ▸ nonVmHandler_preserves hmem s1)
          rw [hev_eq] at hsteps_rest hvm_rest hvm1
          exact ⟨.step (Step.exec hr1 (hf_eq ▸ hfe)) hsteps_rest,
            VmFieldsPreserved.trans hvm1 hvm_rest⟩
      · have hnsvc0 : inst.isSvc0 = false := Bool.eq_false_iff.mpr hsvc0
        have hev1 := evalInst_eq_execInst_of_not_isSvc0 (prog.withSvc nonVmSvc) hnsvc0 s1
        have hev2 := evalInst_eq_execInst_of_not_isSvc0 prog hnsvc0 s1
        rw [hev1] at hsteps_rest hvm_rest
        have hstepP : Step prog s1 (execInst inst s1) := hev2 ▸ Step.exec hr1 (hf_eq ▸ hfe)
        exact ⟨.step hstepP hsteps_rest,
          VmFieldsPreserved.trans (execInst_vmFields_of_not_isSvc0 hnsvc0 s1) hvm_rest⟩
    | halt_unmapped _ _ _ => cases s1; cases hr2
    | extern _ he _ _ => rw [Program.withSvc_externAt?, hext] at he; cases he
    | extern_fault _ he _ => rw [Program.withSvc_externAt?, hext] at he; cases he

/-- Lift a `SepWP (prog.withSvc nonVmSvc)` segment into `SepWP prog`, supplying
    `VmFieldsPreserved s sf` (`brk`, `brkStart`, and `mem.perm` preserved) to `post`. -/
theorem SepWP.of_nonVm {prog : Program} {target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hext : ∀ pc, prog.externAt? pc = none)
    (hsvc : prog.svc = Syscall.standard)
    (h : SepWP (prog.withSvc nonVmSvc) target s P
      (fun sf Pf => VmFieldsPreserved s sf → post sf Pf)) :
    SepWP prog target s P post := by
  unfold SepWP reaches_pc at *
  intro R hm hL
  have hL' : (prog.withSvc nonVmSvc).CodeLoaded s.mem := (Program.withSvc_codeLoaded ..).mpr hL
  rcases h R hm hL' with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hp⟩ | ⟨_, hoom⟩⟩
  · rcases Steps.of_nonVm_running hext hsvc hsteps hrun with ⟨hstepsP, hvm⟩
    exact ⟨sf, hstepsP, Or.inl ⟨hpc, hrun, Pf, hmf, hp hvm⟩⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩; exact False.elim hf

/-- Cut a `SepWP prog` proof at `mid` via `prog.withSvc nonVmSvc`, handing `VmFieldsPreserved s sm`
    to the continuation `SepWP prog target sm Pm post`. -/
theorem SepWP.seq_nonVm {prog : Program} {mid target : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hext : ∀ pc, prog.externAt? pc = none)
    (hsvc : prog.svc = Syscall.standard)
    (h : SepWP (prog.withSvc nonVmSvc) mid s P
      (fun sm Pm => VmFieldsPreserved s sm → SepWP prog target sm Pm post)) :
    SepWP prog target s P post := by
  unfold SepWP reaches_pc at *
  intro R hm hL
  have hL' : (prog.withSvc nonVmSvc).CodeLoaded s.mem := (Program.withSvc_codeLoaded ..).mpr hL
  rcases h R hm hL' with ⟨sm, hst1, ⟨_, hrun_m, Pm, hmm, hcont⟩ | ⟨_, hoom⟩⟩
  · rcases Steps.of_nonVm_running hext hsvc hst1 hrun_m with ⟨hst1P, hvm⟩
    obtain ⟨sf, hst2, hout⟩ := hcont hvm R hmm (hst1P.codeLoaded hL)
    exact ⟨sf, hst1P.trans hst2, hout⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩; exact False.elim hf
