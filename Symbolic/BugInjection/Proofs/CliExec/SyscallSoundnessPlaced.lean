/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Invariant
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.FastEval
public import Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore

/-!
# Relocatable FastState Syscall and Instruction Evaluator Soundness

Proves soundness of `PlacedExecCore.fastExecSyscallPlaced` and
`PlacedExecCore.fastEvalInstPlaced` against `Arm64.Syscall.standard` and
`Arm64.Program.evalInst`. Preserves `FastState.Agrees` and `HeapIntervalsAgree` across all CLI and
`mallocng` syscalls (`fcntl`, `openat`, `close`, `read`, `fstat`, `exit`, `exit_group`,
`set_tid_address`, `brk`, `munmap`, `mremap`, `mmap`, and `mprotect`) as well as single-instruction
evaluation.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.SyscallSoundnessPlaced

open Arm64 Arm64.Memory ProofLib
open CryptoVerification.E2E (heapSize)
open Symbolic.BugInjection.Proofs.CliExec.RadixMem
open Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced
open Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
open Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore

/-- Instruction-evaluator soundness contract against `Arm64.Syscall.standard` and
`Arm64.Program.evalInst`. -/
def EvalSoundPlaced (evalF : Arm64.Instr → FastState → Option FastState) : Prop :=
  ∀ {prog : Arm64.Program}, prog.svc = Arm64.Syscall.standard →
    ∀ {inst : Arm64.Instr} {fs fs' : FastState} {s : Arm64.State},
      fs.Agrees s → evalF inst fs = some fs' → fs'.Agrees (prog.evalInst inst s)

theorem evalInst_system_svc0 {prog : Program} (hsvc : prog.svc = Syscall.standard) (s : State) :
    prog.evalInst (.system false 0#16) s = Syscall.standard s := by
  simp only [Program.evalInst, hsvc, execInstWithSvc, Bool.false_eq_true, ↓reduceIte,
    beq_self_eq_true, evalSvc_standard]

theorem syscall_standard_fcntl {s : State} (hx8 : (s.readReg64 Reg.x8 == 25#64) = true) :
    Syscall.standard s = execFcntl s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_ioctl {s : State} (hx8 : (s.readReg64 Reg.x8 == 29#64) = true) :
    Syscall.standard s = execIoctl s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_openat {s : State} (hx8 : (s.readReg64 Reg.x8 == 56#64) = true) :
    Syscall.standard s = execOpenat s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_close {s : State} (hx8 : (s.readReg64 Reg.x8 == 57#64) = true) :
    Syscall.standard s = execClose s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_lseek {s : State} (hx8 : (s.readReg64 Reg.x8 == 62#64) = true) :
    Syscall.standard s = execLseek s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_read {s : State} (hx8 : (s.readReg64 Reg.x8 == 63#64) = true) :
    Syscall.standard s = execRead s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_write {s : State} (hx8 : (s.readReg64 Reg.x8 == 64#64) = true) :
    Syscall.standard s = execWrite s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_readv {s : State} (hx8 : (s.readReg64 Reg.x8 == 65#64) = true) :
    Syscall.standard s = execReadv s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_writev {s : State} (hx8 : (s.readReg64 Reg.x8 == 66#64) = true) :
    Syscall.standard s = execWritev s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_pread64 {s : State} (hx8 : (s.readReg64 Reg.x8 == 67#64) = true) :
    Syscall.standard s = execPread64 s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_ppoll {s : State} (hx8 : (s.readReg64 Reg.x8 == 73#64) = true) :
    Syscall.standard s = execPpoll s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_fstat {s : State} (hx8 : (s.readReg64 Reg.x8 == 80#64) = true) :
    Syscall.standard s = execFstat s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_exit {s : State} (hx8 : (s.readReg64 Reg.x8 == 93#64) = true) :
    Syscall.standard s = execExit s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_exitGroup {s : State} (hx8 : (s.readReg64 Reg.x8 == 94#64) = true) :
    Syscall.standard s = execExit s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_setTidAddress {s : State} (hx8 : (s.readReg64 Reg.x8 == 96#64) = true) :
    Syscall.standard s = execSetTidAddress s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_clockGettime {s : State} (hx8 : (s.readReg64 Reg.x8 == 113#64) = true) :
    Syscall.standard s = execClockGettime s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_schedGetaffinity {s : State} (hx8 : (s.readReg64 Reg.x8 == 123#64) = true) :
    Syscall.standard s = execSchedGetaffinity s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_sigaltstack {s : State} (hx8 : (s.readReg64 Reg.x8 == 132#64) = true) :
    Syscall.standard s = execSigaltstack s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_rtSigaction {s : State} (hx8 : (s.readReg64 Reg.x8 == 134#64) = true) :
    Syscall.standard s = execRtSigaction s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_rtSigprocmask {s : State} (hx8 : (s.readReg64 Reg.x8 == 135#64) = true) :
    Syscall.standard s = execRtSigprocmask s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_getpid {s : State} (hx8 : (s.readReg64 Reg.x8 == 172#64) = true) :
    Syscall.standard s = execGetpid s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_gettid {s : State} (hx8 : (s.readReg64 Reg.x8 == 178#64) = true) :
    Syscall.standard s = execGetpid s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_brk {s : State} (hx8 : (s.readReg64 Reg.x8 == 214#64) = true) :
    Syscall.standard s = execBrk s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_munmap {s : State} (hx8 : (s.readReg64 Reg.x8 == 215#64) = true) :
    Syscall.standard s = execMunmap s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_mremap {s : State} (hx8 : (s.readReg64 Reg.x8 == 216#64) = true) :
    Syscall.standard s = execMremap s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_mmap {s : State} (hx8 : (s.readReg64 Reg.x8 == 222#64) = true) :
    Syscall.standard s = execMmap s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_mprotect {s : State} (hx8 : (s.readReg64 Reg.x8 == 226#64) = true) :
    Syscall.standard s = execMprotect s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_madvise {s : State} (hx8 : (s.readReg64 Reg.x8 == 233#64) = true) :
    Syscall.standard s = execMadvise s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

theorem syscall_standard_getrandom {s : State} (hx8 : (s.readReg64 Reg.x8 == 278#64) = true) :
    Syscall.standard s = execGetrandom s := by
  unfold Syscall.standard Syscall.dispatch; rw [eq_of_beq hx8]; rfl

private theorem findUnmappedAreaLoop_bound (m : Memory) (size : Nat) :
    ∀ (fuel addr : Nat) {base : BitVec 64},
      findUnmappedAreaLoop m size fuel addr = some base →
      base.toNat + size ≤ USER_VA_LIMIT
  | 0, _, _, h => nomatch h
  | fuel + 1, addr, base, h => by
    unfold findUnmappedAreaLoop at h
    by_cases hlim : addr + size ≤ USER_VA_LIMIT
    · simp only [decide_eq_true hlim, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hm : findMappedByte m (BitVec.ofNat 64 addr) 0 size with
      | none =>
        rw [hm] at h; injection h with h; subst h
        have hlt : addr < 2 ^ 64 := by
          have : USER_VA_LIMIT = 2 ^ 48 := rfl
          omega
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
        exact hlim
      | some off =>
        rw [hm] at h
        exact findUnmappedAreaLoop_bound m size fuel _ h
    · simp [decide_eq_false hlim] at h

private theorem findUnmappedArea_bound {m : Memory} {size : Nat} {base : BitVec 64}
    (h : findUnmappedArea m size = some base) :
    base.toNat + size ≤ USER_VA_LIMIT := by
  unfold findUnmappedArea at h
  split at h
  · nomatch h
  · exact findUnmappedAreaLoop_bound m size _ _ h

theorem sanitizeMmapAddr_bound {m : Memory} {cand base : BitVec 64} {size : Nat}
    (h : sanitizeMmapAddr m cand size = some base) :
    base.toNat + size ≤ USER_VA_LIMIT := by
  unfold sanitizeMmapAddr at h
  split at h
  · nomatch h
  · split at h
    · rename_i hcond
      injection h with h; subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact hcond.1.2
    · exact findUnmappedArea_bound h

theorem heapIntervalsAgree_of_mapped_eq_above {ivs : List (Nat × Nat)} {m1 m2 : Memory}
    (h : HeapIntervalsAgree ivs m1)
    (heq : ∀ a : BitVec 64, 2 ^ 60 ≤ a.toNat → (m2.perm a).mapped = (m1.perm a).mapped) :
    HeapIntervalsAgree ivs m2 :=
  ⟨h.1, fun k hk => by
    have hk_le : k ≤ heapSize := Nat.le_of_lt hk
    have hheap : heapSize = 2 ^ 60 := heapSize_eq
    rw [heq _ (by rw [heapAddr_toNat hk_le]; omega)]
    exact h.2 k hk⟩

private theorem not_sub_lt_of_above {base a : BitVec 64} {len : Nat}
    (hb : base.toNat + len ≤ 2 ^ 60) (ha : 2 ^ 60 ≤ a.toNat) :
    ¬ ((a - base).toNat < len) := by
  have hle : base.toNat ≤ a.toNat := by omega
  have hsub : (a - base).toNat = a.toNat - base.toNat := by bv_omega
  omega

private theorem perm_eq_of_cells_eq {m1 m2 : Memory} {a : BitVec 64}
    (h : m1.cells a = m2.cells a) : m1.perm a = m2.perm a := by
  unfold Memory.perm; rw [h]

theorem mapped_setPermNonFrozen_eq (m : Memory) (base : BitVec 64) (len : Nat) (p : Perm)
    (a : BitVec 64) :
    ((m.setPermNonFrozen base len p).perm a).mapped = (m.perm a).mapped := by
  by_cases hc : (decide ((a - base).toNat < len) && (m.perm a).mapped && !(m.perm a).frozen) = true
  · have hm : (m.perm a).mapped = true := by
      simp only [Bool.and_eq_true] at hc
      exact hc.1.2
    have hcells : (m.setPermNonFrozen base len p).cells a =
        some (some { p with lazyFree := m.isLazyFree a, anon := m.isAnon a }, m.read8 a) := by
      change (if (decide ((a - base).toNat < len) && (m.perm a).mapped && !(m.perm a).frozen) = true
        then _ else _) = _
      simp only [hc, ↓reduceIte]
    have hlhs : ((m.setPermNonFrozen base len p).perm a).mapped = true := by
      unfold Memory.perm; rw [hcells]; rfl
    exact hlhs.trans hm.symm
  · have hcells : (m.setPermNonFrozen base len p).cells a = m.cells a := by
      change (if (decide ((a - base).toNat < len) && (m.perm a).mapped && !(m.perm a).frozen) = true
        then _ else _) = _
      simp only [Bool.eq_false_iff.mpr hc, Bool.false_eq_true, ↓reduceIte]
    rw [perm_eq_of_cells_eq hcells]

theorem heapIntervalsAgree_setPermNonFrozen {ivs : List (Nat × Nat)} {m : Memory}
    (h : HeapIntervalsAgree ivs m) (base : BitVec 64) (len : Nat) (p : Perm) :
    HeapIntervalsAgree ivs (m.setPermNonFrozen base len p) :=
  heapIntervalsAgree_of_mapped_eq_above h fun a _ => mapped_setPermNonFrozen_eq m base len p a

theorem heapIntervalsAgree_mapZero_of_bound {ivs : List (Nat × Nat)} {m : Memory}
    (h : HeapIntervalsAgree ivs m) {base : BitVec 64} {len : Nat}
    (hb : base.toNat + len ≤ 2 ^ 60) :
    HeapIntervalsAgree ivs (m.mapZero base len) :=
  heapIntervalsAgree_of_mapped_eq_above h fun a ha => by
    have hdec : decide ((a - base).toNat < len) = false :=
      decide_eq_false (not_sub_lt_of_above hb ha)
    have hcells : (m.mapZero base len).cells a = m.cells a := by
      unfold Memory.mapZero; dsimp only; rw [hdec]; rfl
    rw [perm_eq_of_cells_eq hcells]

theorem heapIntervalsAgree_unmapWritable_of_bound {ivs : List (Nat × Nat)} {m : Memory}
    (h : HeapIntervalsAgree ivs m) {base : BitVec 64} {len : Nat}
    (hb : base.toNat + len ≤ 2 ^ 60) :
    HeapIntervalsAgree ivs (m.unmapWritable base len) :=
  heapIntervalsAgree_of_mapped_eq_above h fun a ha => by
    have hdec : decide ((a - base).toNat < len) = false :=
      decide_eq_false (not_sub_lt_of_above hb ha)
    have hcells : (m.unmapWritable base len).cells a = m.cells a := by
      unfold Memory.unmapWritable; dsimp only; rw [hdec]; rfl
    rw [perm_eq_of_cells_eq hcells]

theorem heapIntervalsAgree_unmapNonFrozen_of_bound {ivs : List (Nat × Nat)} {m : Memory}
    (h : HeapIntervalsAgree ivs m) {base : BitVec 64} {len : Nat}
    (hb : base.toNat + len ≤ 2 ^ 60) :
    HeapIntervalsAgree ivs (m.unmapNonFrozen base len) :=
  heapIntervalsAgree_of_mapped_eq_above h fun a ha => by
    have hdec : decide ((a - base).toNat < len) = false :=
      decide_eq_false (not_sub_lt_of_above hb ha)
    have hcells : (m.unmapNonFrozen base len).cells a = m.cells a := by
      unfold Memory.unmapNonFrozen; dsimp only; rw [hdec]; rfl
    rw [perm_eq_of_cells_eq hcells]

theorem heapIntervalsAgree_remapRw_of_bound {ivs : List (Nat × Nat)} {m : Memory}
    (h : HeapIntervalsAgree ivs m) {oldBase newBase : BitVec 64} {oldSize newSize : Nat}
    (hold : oldBase.toNat + oldSize ≤ 2 ^ 60)
    (hnew : newBase.toNat + newSize ≤ 2 ^ 60) :
    HeapIntervalsAgree ivs (m.remapRw oldBase oldSize newBase newSize) :=
  heapIntervalsAgree_of_mapped_eq_above h fun a ha => by
    have hcells : (m.remapRw oldBase oldSize newBase newSize).cells a = m.cells a := by
      unfold Memory.remapRw
      dsimp only
      by_cases h1 : (m.perm a).frozen = true
      · simp only [h1, ↓reduceIte]
      · have h2 : ¬ ((a - newBase).toNat < newSize) := not_sub_lt_of_above hnew ha
        have h3 : ¬ ((a - oldBase).toNat < oldSize) := not_sub_lt_of_above hold ha
        simp only [Bool.eq_false_iff.mpr h1, Bool.false_eq_true, h2, h3, ↓reduceIte]
    rw [perm_eq_of_cells_eq hcells]

theorem heapIntervalsAgree_zeroNonFrozen_of_bound {ivs : List (Nat × Nat)} {m : Memory}
    (h : HeapIntervalsAgree ivs m) {base : BitVec 64} {len : Nat}
    (hb : base.toNat + len ≤ 2 ^ 60) :
    HeapIntervalsAgree ivs (m.zeroNonFrozen base len) :=
  heapIntervalsAgree_of_mapped_eq_above h fun a ha => by
    have hdec : decide ((a - base).toNat < len) = false :=
      decide_eq_false (not_sub_lt_of_above hb ha)
    have hcells : (m.zeroNonFrozen base len).cells a = m.cells a := by
      unfold Memory.zeroNonFrozen; dsimp only; rw [hdec]; rfl
    rw [perm_eq_of_cells_eq hcells]

theorem heapIntervalsAgree_madvFreeNonFrozen_of_bound {ivs : List (Nat × Nat)} {m : Memory}
    (h : HeapIntervalsAgree ivs m) {base : BitVec 64} {len : Nat}
    (hb : base.toNat + len ≤ 2 ^ 60) :
    HeapIntervalsAgree ivs (m.madvFreeNonFrozen base len) :=
  heapIntervalsAgree_of_mapped_eq_above h fun a ha => by
    have hdec : decide ((a - base).toNat < len) = false :=
      decide_eq_false (not_sub_lt_of_above hb ha)
    have hcells : (m.madvFreeNonFrozen base len).cells a = m.cells a := by
      unfold Memory.madvFreeNonFrozen; dsimp only; rw [hdec]; rfl
    rw [perm_eq_of_cells_eq hcells]

private theorem user_va_limit_le_heap : USER_VA_LIMIT ≤ 2 ^ 60 := by decide

private theorem setMem_fs (fs : FastState) (fm : FastMem) : (fs.setMem fm).fs = fs.fs := by
  rcases fs with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases fm with ⟨_, _, _⟩
  rfl

def OpenVerdictAgrees : FastOpenVerdict → OpenVerdict → Prop
  | .opened fd1 ffs' cp1, .opened fd2 sfs' cp2 => fd1 = fd2 ∧ ffs'.Agrees sfs' ∧ cp1 = cp2
  | .errno e1, .errno e2 => e1 = e2
  | .trap m1, .trap m2 => m1 = m2
  | _, _ => False

private theorem fastCheckOpenFlags_agrees (flags : BitVec 32) :
    match fastCheckOpenFlags flags, checkOpenFlags flags with
    | none, none => True
    | some fv, some sv => OpenVerdictAgrees fv sv
    | _, _ => False := by
  unfold fastCheckOpenFlags checkOpenFlags
  by_cases hc1 : ((flags &&& ~~~OPENAT_KNOWN_MASK) != 0#32 || (flags &&& 3#32) == 3#32) = true
  · simp only [hc1, ↓reduceIte, OpenVerdictAgrees]
  · simp only [Bool.eq_false_iff.mpr hc1, Bool.false_eq_true, ↓reduceIte]
    by_cases hc2 : ((flags &&& O_CREAT_W32) != 0#32 && (flags &&& O_DIRECTORY_W32) != 0#32) = true
    · simp only [hc2, ↓reduceIte, OpenVerdictAgrees]
    · simp only [Bool.eq_false_iff.mpr hc2, Bool.false_eq_true, ↓reduceIte]

private theorem fastApplyOpenVerdict_agrees {fs fs' : FastState} {s : State}
    {fv : FastOpenVerdict} {sv : OpenVerdict}
    (hag : fs.Agrees s) (hv : OpenVerdictAgrees fv sv)
    (h : fastApplyOpenVerdict fs fv = some fs') :
    fs'.Agrees (applyOpenVerdict s sv) := by
  cases fv with
  | opened fd1 ffs' cp1 =>
    cases sv with
    | opened fd2 sfs' cp2 =>
      rcases hv with ⟨rfl, hfs, rfl⟩
      cases cp1 with
      | none =>
        injection h with h; subst h
        exact FastState.advancePC_agrees
          (FastState.writeReg64_agrees (FastState.setFs_agrees hag hfs) Reg.x0 fd1)
      | some p =>
        injection h with h; subst h
        exact FastState.advancePC_agrees
          (FastState.writeReg64_agrees
            (FastState.appendTrace_agrees (FastState.setFs_agrees hag hfs) [.fileChanged p])
            Reg.x0 fd1)
    | _ => nomatch hv
  | errno e1 =>
    cases sv with
    | errno e2 =>
      subst hv
      injection h with h; subst h
      exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-e1))
    | _ => nomatch hv
  | trap _ => nomatch h

private theorem fastOpenatPure_agrees {ffs : FastFs} {sfs : FsState} (hfs : ffs.Agrees sfs)
    (dfd : BitVec 32) (rawPath : String) (flags mode : BitVec 32) :
    OpenVerdictAgrees (fastOpenatPure ffs dfd rawPath flags mode)
      (openatPure sfs dfd rawPath flags mode) := by
  unfold fastOpenatPure openatPure
  have hcf := fastCheckOpenFlags_agrees flags
  cases h1 : fastCheckOpenFlags flags <;> cases h2 : checkOpenFlags flags
  · rw [h1, h2] at hcf
    dsimp only
    set acc : FdAccessMode :=
      if (flags &&& 3#32) == 0#32 then .rdonly
      else if (flags &&& 3#32) == 1#32 then .wronly
      else .rdwr
    set hasCreat := (flags &&& O_CREAT_W32) != 0#32
    set hasExcl := (flags &&& O_EXCL_W32) != 0#32
    set hasTrunc := (flags &&& O_TRUNC_W32) != 0#32
    set hasAppend := (flags &&& O_APPEND_W32) != 0#32
    set hasDir := (flags &&& O_DIRECTORY_W32) != 0#32
    set hasCloexec := (flags &&& O_CLOEXEC_W32) != 0#32
    cases resolveCwdPath dfd rawPath with
    | trap msg => exact rfl
    | errno err => exact rfl
    | ok segs =>
      dsimp only
      rw [fastStrictAncestorWalkErrno?_eq hfs rawPath]
      cases strictAncestorWalkErrno? sfs rawPath with
      | some err => exact rfl
      | none =>
        dsimp only
        set isTrailDir := trailingDir rawPath
        set isTrailNormSlash := trailingNormSlash rawPath
        by_cases hct : (hasCreat && isTrailNormSlash) = true
        · simp only [hct, ↓reduceIte, OpenVerdictAgrees]
        · simp only [Bool.eq_false_iff.mpr hct, Bool.false_eq_true, ↓reduceIte]
          by_cases hnm : (((splitSlash rawPath).filter (!·.isEmpty)).getLast?.any (·.length > NAME_MAX)) = true
          · simp only [hnm, ↓reduceIte, OpenVerdictAgrees]
          · simp only [Bool.eq_false_iff.mpr hnm, Bool.false_eq_true, ↓reduceIte]
            rw [FastFs.getEntry_eq hfs segs, fastAllocFd_eq hfs]
            cases sfs.getEntry segs with
            | some e =>
              cases e with
              | dir =>
                dsimp only
                by_cases hd1 : (hasCreat && hasExcl && !isTrailNormSlash) = true
                · simp only [hd1, ↓reduceIte, OpenVerdictAgrees]
                · simp only [Bool.eq_false_iff.mpr hd1, Bool.false_eq_true, ↓reduceIte]
                  by_cases hd2 : (acc != .rdonly || hasTrunc || hasCreat) = true
                  · simp only [hd2, ↓reduceIte, OpenVerdictAgrees]
                  · simp only [Bool.eq_false_iff.mpr hd2, Bool.false_eq_true, ↓reduceIte]
                    cases sfs.allocFd with
                    | none => exact rfl
                    | some fd => exact ⟨rfl, FastFs.setFd_agrees hfs fd _, rfl⟩
              | file oldBytes =>
                dsimp only
                by_cases hf2 : (isTrailDir || hasDir) = true
                · simp only [hf2, ↓reduceIte, OpenVerdictAgrees]
                · simp only [Bool.eq_false_iff.mpr hf2, Bool.false_eq_true, ↓reduceIte]
                  by_cases hf3 : (hasCreat && hasExcl) = true
                  · simp only [hf3, ↓reduceIte, OpenVerdictAgrees]
                  · simp only [Bool.eq_false_iff.mpr hf3, Bool.false_eq_true, ↓reduceIte]
                    cases sfs.allocFd with
                    | none => exact rfl
                    | some fd =>
                      exact ⟨rfl, FastFs.setFd_agrees (FastFs.setEntry_agrees hfs segs _) fd _, rfl⟩
            | none =>
              dsimp only
              by_cases hn1 : (!hasCreat) = true
              · simp only [hn1, ↓reduceIte, OpenVerdictAgrees]
              · simp only [Bool.eq_false_iff.mpr hn1, Bool.false_eq_true, ↓reduceIte]
                cases sfs.allocFd with
                | none => exact rfl
                | some fd =>
                  dsimp only
                  by_cases hmd : ((mode &&& O_CREAT_OWNER_RW_MASK) != O_CREAT_OWNER_RW_MASK) = true
                  · simp only [hmd, ↓reduceIte, OpenVerdictAgrees]
                  · simp only [Bool.eq_false_iff.mpr hmd, Bool.false_eq_true, ↓reduceIte]
                    exact ⟨rfl, FastFs.setFd_agrees (FastFs.setEntry_agrees hfs segs _) fd _, rfl⟩
  · rw [h1, h2] at hcf; nomatch hcf
  · rw [h1, h2] at hcf; nomatch hcf
  · rw [h1, h2] at hcf; exact hcf

theorem fastExecFcntl_sound {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (h : fastExecFcntl fs = some fs') :
    fs'.Agrees (execFcntl s) := by
  unfold fastExecFcntl at h
  unfold execFcntl
  rw [FastState.readReg32_eq hag Reg.x0, FastState.readReg32_eq hag Reg.x1,
      FastState.readReg64_eq hag Reg.x2] at h
  dsimp only at h ⊢
  split at h
  · rename_i hc; simp only [hc, ↓reduceIte]; injection h with h; subst h
    exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-EBADF))
  · rename_i hc; simp only [hc, Bool.false_eq_true, ↓reduceIte]
    rw [FastFs.getFd_eq hag.fs] at h
    cases hfds : s.fs.fds ((s.readReg32 Reg.x0).zeroExtend 64) with
    | none =>
      rw [hfds] at h; dsimp only at h ⊢
      split at h; · nomatch h
      rename_i hge; simp only [hge, ↓reduceIte]
      injection h with h; subst h
      exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-EBADF))
    | some desc =>
      rw [hfds] at h; dsimp only at h ⊢
      split at h; · nomatch h
      rename_i hk; simp only [hk, Bool.false_eq_true, ↓reduceIte]
      split at h
      · rename_i hget; simp only [hget, ↓reduceIte]; injection h with h; subst h
        exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 _)
      · rename_i hget; simp only [hget, Bool.false_eq_true, ↓reduceIte]
        split at h
        · rename_i hset; simp only [hset, ↓reduceIte]; injection h with h; subst h
          exact FastState.advancePC_agrees
            (FastState.writeReg64_agrees
              (FastState.setFs_agrees hag (FastFs.setFd_agrees hag.fs _ _)) Reg.x0 0#64)
        · nomatch h

theorem fastExecOpenat_sound {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (h : fastExecOpenat fs = some fs') :
    fs'.Agrees (execOpenat s) := by
  unfold fastExecOpenat at h
  unfold execOpenat
  rw [FastState.readReg32_eq hag Reg.x0, FastState.readReg64_eq hag Reg.x1,
      FastState.readReg32_eq hag Reg.x2, FastState.readReg32_eq hag Reg.x3] at h
  dsimp only at h ⊢
  have hcf := fastCheckOpenFlags_agrees (s.readReg32 Reg.x2)
  cases h1 : fastCheckOpenFlags (s.readReg32 Reg.x2) <;>
    cases h2 : checkOpenFlags (s.readReg32 Reg.x2)
  · rw [h1, h2] at hcf; rw [h1] at h
    dsimp only at h ⊢
    rw [readCStringFast_eq hag.mem] at h
    cases hcs : readCString s.mem (s.readReg64 Reg.x1) with
    | trap _ => rw [hcs] at h; nomatch h
    | errno err =>
      rw [hcs] at h; injection h with h; subst h
      exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-err))
    | ok rawPath =>
      rw [hcs] at h
      exact fastApplyOpenVerdict_agrees hag (fastOpenatPure_agrees hag.fs _ _ _ _) h
  · rw [h1, h2] at hcf; nomatch hcf
  · rw [h1, h2] at hcf; nomatch hcf
  · rw [h1, h2] at hcf; rw [h1] at h
    exact fastApplyOpenVerdict_agrees hag hcf h

theorem fastExecClose_sound {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (h : fastExecClose fs = some fs') :
    fs'.Agrees (execClose s) := by
  unfold fastExecClose at h
  unfold execClose
  rw [FastState.readReg32_eq hag Reg.x0] at h
  dsimp only at h ⊢
  split at h
  · rename_i hc; simp only [hc, ↓reduceIte]; injection h with h; subst h
    exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-EBADF))
  · rename_i hc; simp only [hc, Bool.false_eq_true, ↓reduceIte]
    rw [FastFs.getFd_eq hag.fs] at h
    cases hfds : s.fs.fds ((s.readReg32 Reg.x0).zeroExtend 64) with
    | none =>
      rw [hfds] at h; dsimp only at h ⊢
      split at h; · nomatch h
      rename_i hge; simp only [hge, ↓reduceIte]
      injection h with h; subst h
      exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-EBADF))
    | some desc =>
      rw [hfds] at h; dsimp only at h ⊢
      split at h; · nomatch h
      rename_i hk; simp only [hk, Bool.false_eq_true, ↓reduceIte]
      injection h with h; subst h
      exact FastState.advancePC_agrees
        (FastState.writeReg64_agrees
          (FastState.setFs_agrees hag (FastFs.setFd_agrees hag.fs _ none)) Reg.x0 0#64)

theorem fastExecRead_sound {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (h : fastExecRead fs = some fs') :
    fs'.Agrees (execRead s) := by
  unfold fastExecRead at h
  unfold execRead execReadCommon
  rw [FastState.readReg32_eq hag Reg.x0, FastState.readReg64_eq hag Reg.x1,
      FastState.readReg64_eq hag Reg.x2] at h
  simp only [Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte] at h ⊢
  split at h
  · rename_i hc; simp only [hc, ↓reduceIte]; injection h with h; subst h
    exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-EBADF))
  · rename_i hc; simp only [hc, Bool.false_eq_true, ↓reduceIte]
    rw [FastFs.getFd_eq hag.fs] at h
    cases hfds : s.fs.fds ((s.readReg32 Reg.x0).zeroExtend 64) with
    | none =>
      rw [hfds] at h; dsimp only at h ⊢
      split at h; · nomatch h
      rename_i hge; simp only [hge, ↓reduceIte]
      injection h with h; subst h
      exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-EBADF))
    | some desc =>
      rw [hfds] at h; dsimp only at h ⊢
      by_cases hdir : (desc.kind == .localDir) = true
      · simp only [hdir, ↓reduceIte] at h ⊢
        by_cases h1 : (!desc.accMode.canRead) = true
        · simp only [h1, ↓reduceIte] at h ⊢; injection h with h; subst h
          exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-EBADF))
        · simp only [Bool.eq_false_iff.mpr h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
          set buf := s.readReg64 Reg.x1
          set count := s.readReg64 Reg.x2
          by_cases h2 : buf.toNat + count.toNat > USER_VA_LIMIT
          · simp only [decide_eq_true h2, ↓reduceIte] at h
            simp only [h2, ↓reduceIte]
            injection h with h; subst h
            exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 EFAULT_RET)
          · simp only [decide_eq_false h2, Bool.false_eq_true, ↓reduceIte] at h
            simp only [h2, ↓reduceIte]
            injection h with h; subst h
            exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-EISDIR))
      · simp only [Bool.eq_false_iff.mpr hdir, Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases hk : (!(desc.kind == .localFile || desc.kind == .stdio)) = true
        · simp only [hk, ↓reduceIte] at h; nomatch h
        · simp only [Bool.eq_false_iff.mpr hk, Bool.false_eq_true, ↓reduceIte] at h ⊢
          by_cases h1 : (!desc.accMode.canRead) = true
          · simp only [h1, ↓reduceIte] at h ⊢; injection h with h; subst h
            exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-EBADF))
          · simp only [Bool.eq_false_iff.mpr h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
            set buf := s.readReg64 Reg.x1
            set count := s.readReg64 Reg.x2
            by_cases h2 : buf.toNat + count.toNat > USER_VA_LIMIT
            · simp only [decide_eq_true h2, ↓reduceIte] at h
              simp only [h2]
              injection h with h; subst h
              exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 EFAULT_RET)
            · simp only [decide_eq_false h2, Bool.false_eq_true, ↓reduceIte] at h
              simp only [h2]
              by_cases hlfs : (desc.kind == .localFile && decide (desc.offset + count.toNat > MAX_LFS_FILESIZE)) = true
              · simp only [hlfs, ↓reduceIte] at h ⊢; injection h with h; subst h
                exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-EINVAL))
              · simp only [Bool.eq_false_iff.mpr hlfs, Bool.false_eq_true, ↓reduceIte] at h ⊢
                rw [fastFdBytes_eq hag.fs desc] at h
                set count' := min count.toNat MAX_RW_COUNT
                set chunk := ((s.fs.fdBytes desc).drop desc.offset).take count'
                rw [FastMem.canWrite_eq hag.mem] at h
                by_cases hcw : s.mem.canWrite buf chunk.length = true
                · simp only [hcw, ↓reduceIte] at h ⊢
                  injection h with h; subst h
                  have hmem := FastState.setMem_agrees hag (FastMem.writeBytes_agrees hag.mem buf chunk)
                    (HeapIntervalsAgree.of_perm_eq hag.heapIvs (perm_writeBytes_eq s.mem buf chunk))
                  rw [setMem_fs]
                  have hfd_ag := FastFs.setFd_agrees hag.fs ((s.readReg32 Reg.x0).zeroExtend 64)
                    (some { desc with offset := desc.offset + chunk.length })
                  have hfs2 := FastState.setFs_agrees hmem hfd_ag
                  exact FastState.advancePC_agrees (FastState.writeReg64_agrees hfs2 Reg.x0 _)
                · simp only [Bool.eq_false_iff.mpr hcw, Bool.false_eq_true, ↓reduceIte] at h ⊢
                  rw [FastMem.canWrite_eq hag.mem] at h
                  by_cases hcw1 : (!s.mem.canWrite buf 1) = true
                  · simp only [hcw1, ↓reduceIte] at h ⊢; injection h with h; subst h
                    exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 EFAULT_RET)
                  · simp only [Bool.eq_false_iff.mpr hcw1, Bool.false_eq_true, ↓reduceIte] at h; nomatch h

theorem fastExecFstat_sound {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (h : fastExecFstat fs = some fs') :
    fs'.Agrees (execFstat s) := by
  unfold fastExecFstat at h
  unfold execFstat
  rw [FastState.readReg32_eq hag Reg.x0, FastState.readReg64_eq hag Reg.x1] at h
  dsimp only at h ⊢
  split at h
  · rename_i hc; simp only [hc, ↓reduceIte]; injection h with h; subst h
    exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-EBADF))
  · rename_i hc; simp only [hc, Bool.false_eq_true, ↓reduceIte]
    rw [FastFs.getFd_eq hag.fs] at h
    cases hfds : s.fs.fds ((s.readReg32 Reg.x0).zeroExtend 64) with
    | none =>
      rw [hfds] at h; dsimp only at h ⊢
      split at h; · nomatch h
      rename_i hge; simp only [hge, ↓reduceIte]
      injection h with h; subst h
      exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-EBADF))
    | some desc =>
      rw [hfds] at h; dsimp only at h ⊢
      split at h; · nomatch h
      rename_i hk; simp only [hk, Bool.false_eq_true, ↓reduceIte]
      rw [FastFs.files_eq hag.fs desc.path, FastMem.canWrite_eq hag.mem] at h
      split at h
      · rename_i hcw; simp only [hcw, ↓reduceIte]; injection h with h; subst h
        exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 EFAULT_RET)
      · rename_i hcw; simp only [hcw, Bool.false_eq_true, ↓reduceIte]
        injection h with h; subst h
        set statbuf := s.readReg64 Reg.x1
        set bs := encodeLinuxStat ((s.fs.files desc.path).getD (.file []))
        have h1 := FastState.setMem_agrees hag (FastMem.writeBytes_agrees hag.mem statbuf bs)
          (HeapIntervalsAgree.of_perm_eq hag.heapIvs (perm_writeBytes_eq s.mem statbuf bs))
        exact FastState.advancePC_agrees (FastState.writeReg64_agrees h1 Reg.x0 0#64)

theorem fastExecExit_sound {fs : FastState} {s : State} (hag : fs.Agrees s) :
    (fs.setStatus (.Exited (fs.readReg64 Reg.x0))).Agrees (execExit s) := by
  unfold execExit
  rw [FastState.readReg64_eq hag Reg.x0]
  exact FastState.setStatus_agrees hag _

theorem fastExecSetTidAddress_sound {fs : FastState} {s : State} (hag : fs.Agrees s) :
    ((fs.writeReg64 Reg.x0 SIM_TID).advancePC).Agrees (execSetTidAddress s) := by
  unfold execSetTidAddress
  exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 SIM_TID)

theorem fastExecBrk_sound {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (h : fastExecBrk fs = some fs') :
    fs'.Agrees (execBrk s) := by
  unfold fastExecBrk at h
  unfold execBrk
  rw [FastState.readReg64_eq hag Reg.x0, hag.brkStart, hag.brk, hag.physMemAvail] at h
  set addr := s.readReg64 Reg.x0
  by_cases hc : (addr == 0#64 || addr.ult s.brkStart) = true
  · simp only [hc, ↓reduceIte] at h ⊢
    injection h with h; subst h
    exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 s.brk)
  · simp only [Bool.eq_false_iff.mpr hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
    set oldPage := Arm64.pageAlignUp s.brk.toNat
    set newPage := Arm64.pageAlignUp addr.toNat
    by_cases hle : newPage ≤ oldPage
    · simp only [decide_eq_true hle, ↓reduceIte] at h
      simp only [hle, ↓reduceIte]
      rw [FastMem.allPerm_eq hag.mem, FastMem.countRw_eq hag.mem] at h
      set shrinkBytes := oldPage - newPage
      by_cases hm : (!s.mem.allPerm (·.mapped) (BitVec.ofNat 64 newPage) shrinkBytes) = true
      · simp only [hm, ↓reduceIte] at h ⊢
        injection h with h; subst h
        exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 s.brk)
      · simp only [Bool.eq_false_iff.mpr hm, Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases hold_lim : oldPage ≤ USER_VA_LIMIT
        · simp only [decide_eq_true hold_lim, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          injection h with h; subst h
          have huva : USER_VA_LIMIT ≤ 2 ^ 60 := user_va_limit_le_heap
          have hnp_lt : newPage < 2 ^ 64 := by
            have : USER_VA_LIMIT = 2 ^ 48 := rfl
            omega
          have hbnd : (BitVec.ofNat 64 newPage).toNat + shrinkBytes ≤ 2 ^ 60 := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnp_lt]
            omega
          have hbrk := fastSetBrk_agrees hag addr
          have hm' := FastState.setMem_agrees hbrk
            (FastMem.unmapWritable_agrees hag.mem (BitVec.ofNat 64 newPage) shrinkBytes)
            (heapIntervalsAgree_unmapWritable_of_bound hbrk.heapIvs hbnd)
          exact FastState.advancePC_agrees
            (FastState.writeReg64_agrees (fastSetPhysMemAvail_agrees hm' _) Reg.x0 addr)
        · simp only [decide_eq_false hold_lim, Bool.not_false, ↓reduceIte] at h
          nomatch h
    · simp only [decide_eq_false hle, Bool.false_eq_true, ↓reduceIte] at h
      simp only [hle, ↓reduceIte]
      rw [FastMem.canMap_eq hag.mem] at h
      set growBytes := newPage - oldPage
      by_cases hg1 : ((!decide (newPage + BRK_GUARD_GAP ≤ USER_VA_LIMIT)) ||
          (!s.mem.canMap (BitVec.ofNat 64 oldPage) (growBytes + BRK_GUARD_GAP))) = true
      · simp only [hg1, ↓reduceIte] at h ⊢
        injection h with h; subst h
        exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 s.brk)
      · simp only [Bool.eq_false_iff.mpr hg1, Bool.false_eq_true, ↓reduceIte] at h ⊢
        have hnp_lim : newPage + BRK_GUARD_GAP ≤ USER_VA_LIMIT := by
          by_contra hgt
          exact hg1 (by simp only [decide_eq_false hgt, Bool.not_false, Bool.true_or])
        by_cases hoom : (!decide (growBytes ≤ s.physMemAvail)) = true
        · simp only [hoom, ↓reduceIte] at h ⊢
          injection h with h; subst h
          exact FastState.setStatus_agrees hag .OutOfMemory
        · simp only [Bool.eq_false_iff.mpr hoom, Bool.false_eq_true, ↓reduceIte] at h ⊢
          injection h with h; subst h
          have huva : USER_VA_LIMIT ≤ 2 ^ 60 := user_va_limit_le_heap
          have hop_lt : oldPage < 2 ^ 64 := by
            have : USER_VA_LIMIT = 2 ^ 48 := rfl
            omega
          have hbnd : (BitVec.ofNat 64 oldPage).toNat + growBytes ≤ 2 ^ 60 := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hop_lt]
            omega
          have hbrk := fastSetBrk_agrees hag addr
          have hm' := FastState.setMem_agrees hbrk
            (FastMem.mapZero_agrees hag.mem (BitVec.ofNat 64 oldPage) growBytes)
            (heapIntervalsAgree_mapZero_of_bound hbrk.heapIvs hbnd)
          exact FastState.advancePC_agrees
            (FastState.writeReg64_agrees (fastSetPhysMemAvail_agrees hm' _) Reg.x0 addr)

theorem fastExecMunmap_sound {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (h : fastExecMunmap fs = some fs') :
    fs'.Agrees (execMunmap s) := by
  unfold fastExecMunmap at h
  unfold execMunmap
  rw [FastState.readReg64_eq hag Reg.x0, FastState.readReg64_eq hag Reg.x1, hag.physMemAvail] at h
  set addr := s.readReg64 Reg.x0
  set len := (s.readReg64 Reg.x1).toNat
  by_cases hc : (addr.toNat % PAGE_SIZE != 0 || len == 0 || !decide (addr.toNat + pageAlignUp len ≤ 2 ^ 48)) = true
  · simp only [hc, ↓reduceIte] at h ⊢
    injection h with h; subst h
    exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-EINVAL))
  · simp only [Bool.eq_false_iff.mpr hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
    have hbnd48 : addr.toNat + pageAlignUp len ≤ 2 ^ 48 := by
      by_contra hgt
      exact hc (by simp only [decide_eq_false hgt, Bool.not_false, Bool.or_true])
    rw [FastMem.allPerm_eq hag.mem, FastMem.countRw_eq hag.mem] at h
    by_cases hnf : (!s.mem.allPerm (fun p => !p.frozen) addr (pageAlignUp len)) = true
    · simp only [hnf, ↓reduceIte] at h; nomatch h
    · simp only [Bool.eq_false_iff.mpr hnf, Bool.false_eq_true, ↓reduceIte] at h ⊢
      injection h with h; subst h
      have hbnd : addr.toNat + pageAlignUp len ≤ 2 ^ 60 := by omega
      have hm' := FastState.setMem_agrees hag
        (FastMem.unmapNonFrozen_agrees hag.mem addr (pageAlignUp len))
        (heapIntervalsAgree_unmapNonFrozen_of_bound hag.heapIvs hbnd)
      exact FastState.advancePC_agrees
        (FastState.writeReg64_agrees (fastSetPhysMemAvail_agrees hm' _) Reg.x0 0#64)

theorem fastExecMremap_sound {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (h : fastExecMremap fs = some fs') :
    fs'.Agrees (execMremap s) := by
  unfold fastExecMremap at h
  unfold execMremap
  rw [FastState.readReg64_eq hag Reg.x0, FastState.readReg64_eq hag Reg.x1,
      FastState.readReg64_eq hag Reg.x2, FastState.readReg64_eq hag Reg.x3,
      hag.oracle, hag.oracleIdx, hag.physMemAvail] at h
  set oldAddr := s.readReg64 Reg.x0
  set oldLen := (s.readReg64 Reg.x1).toNat
  set newLen := (s.readReg64 Reg.x2).toNat
  set flags := s.readReg64 Reg.x3
  by_cases hf1 : (flags != MREMAP_MAYMOVE) = true
  · simp only [hf1, ↓reduceIte] at h; nomatch h
  · simp only [Bool.eq_false_iff.mpr hf1, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hf2 : (oldAddr.toNat % PAGE_SIZE != 0 || newLen == 0 ||
        !decide (newLen ≤ 2 ^ 64 - PAGE_SIZE)) = true
    · simp only [hf2, ↓reduceIte] at h ⊢
      injection h with h; subst h
      exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-EINVAL))
    · simp only [Bool.eq_false_iff.mpr hf2, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hf3 : (oldLen == 0) = true
      · simp only [hf3, ↓reduceIte] at h; nomatch h
      · simp only [Bool.eq_false_iff.mpr hf3, Bool.false_eq_true, ↓reduceIte] at h ⊢
        set oldAligned := Arm64.pageAlignUp oldLen
        set newAligned := Arm64.pageAlignUp newLen
        by_cases hf4 : (!decide (oldAddr.toNat + oldAligned ≤ USER_VA_LIMIT)) = true
        · simp only [hf4, ↓reduceIte] at h ⊢
          injection h with h; subst h
          exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-EINVAL))
        · simp only [Bool.eq_false_iff.mpr hf4, Bool.false_eq_true, ↓reduceIte] at h ⊢
          have hold_lim : oldAddr.toNat + oldAligned ≤ USER_VA_LIMIT := by
            by_contra hgt
            exact hf4 (by simp only [decide_eq_false hgt, Bool.not_false])
          rw [FastMem.allPerm_eq hag.mem, FastMem.canMap_eq hag.mem,
              FastMem.allPerm_eq hag.mem, FastMem.allAnon_eq hag.mem] at h
          by_cases hf5 : (!s.mem.allPerm (fun p => !p.frozen) oldAddr oldAligned) = true
          · simp only [hf5, ↓reduceIte] at h; nomatch h
          · simp only [Bool.eq_false_iff.mpr hf5, Bool.false_eq_true, ↓reduceIte] at h ⊢
            by_cases hf6 : s.mem.canMap oldAddr oldAligned = true
            · simp only [hf6, ↓reduceIte] at h ⊢
              injection h with h; subst h
              exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 EFAULT_RET)
            · simp only [Bool.eq_false_iff.mpr hf6, Bool.false_eq_true, ↓reduceIte] at h ⊢
              by_cases hf7 : (!s.mem.allPerm (· == some Perm.rw) oldAddr oldAligned) = true
              · simp only [hf7, ↓reduceIte] at h; nomatch h
              · simp only [Bool.eq_false_iff.mpr hf7, Bool.false_eq_true, ↓reduceIte] at h ⊢
                by_cases hf8 : (!s.mem.allAnon oldAddr oldAligned) = true
                · simp only [hf8, ↓reduceIte] at h; nomatch h
                · simp only [Bool.eq_false_iff.mpr hf8, Bool.false_eq_true, ↓reduceIte] at h ⊢
                  by_cases hf9 : s.oracle.mremapFail s.oracleIdx = true
                  · simp only [hf9, ↓reduceIte] at h ⊢
                    injection h with h; subst h
                    exact FastState.advancePC_agrees
                      (FastState.writeReg64_agrees (fastNextOracle_agrees hag) Reg.x0 (-ENOMEM))
                  · simp only [Bool.eq_false_iff.mpr hf9, Bool.false_eq_true, ↓reduceIte] at h ⊢
                    have hunm_ag := FastMem.unmapNonFrozen_agrees hag.mem oldAddr oldAligned
                    rw [sanitizeMmapAddrFast_eq hunm_ag] at h
                    cases hsan : sanitizeMmapAddr (s.mem.unmapNonFrozen oldAddr oldAligned)
                        (s.oracle.mmap s.oracleIdx) newAligned with
                    | none =>
                      rw [hsan] at h
                      injection h with h; subst h
                      exact FastState.advancePC_agrees
                        (FastState.writeReg64_agrees (fastNextOracle_agrees hag) Reg.x0 (-ENOMEM))
                    | some newBase =>
                      rw [hsan] at h
                      by_cases hoom : (!decide (newAligned ≤ s.physMemAvail + oldAligned)) = true
                      · simp only [hoom, ↓reduceIte] at h ⊢
                        injection h with h; subst h
                        exact FastState.setStatus_agrees hag .OutOfMemory
                      · simp only [Bool.eq_false_iff.mpr hoom, Bool.false_eq_true, ↓reduceIte] at h ⊢
                        injection h with h; subst h
                        have huva : USER_VA_LIMIT ≤ 2 ^ 60 := user_va_limit_le_heap
                        have hnew_lim := sanitizeMmapAddr_bound hsan
                        have hm' := FastState.setMem_agrees hag
                          (FastMem.remapRw_agrees hag.mem oldAddr oldAligned newBase newAligned)
                          (heapIntervalsAgree_remapRw_of_bound hag.heapIvs (by omega) (by omega))
                        exact FastState.advancePC_agrees
                          (FastState.writeReg64_agrees
                            (fastNextOracle_agrees (fastSetPhysMemAvail_agrees hm' _)) Reg.x0 newBase)

theorem fastExecMmap_sound {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (h : fastExecMmap fs = some fs') :
    fs'.Agrees (execMmap s) := by
  unfold fastExecMmap at h
  unfold execMmap
  rw [FastState.readReg64_eq hag Reg.x0, FastState.readReg64_eq hag Reg.x1,
      FastState.readReg64_eq hag Reg.x2, FastState.readReg64_eq hag Reg.x3,
      FastState.readReg64_eq hag Reg.x5, hag.oracle, hag.oracleIdx, hag.physMemAvail] at h
  set len := (s.readReg64 Reg.x1).toNat
  set prot := s.readReg64 Reg.x2
  set flags := s.readReg64 Reg.x3
  by_cases hf1 : ((prot != MMAP_PROT_RW && prot != MMAP_PROT_NONE) ||
      (flags != MMAP_FLAGS_PRIVATE_ANON && flags != MMAP_FLAGS_PRIVATE_ANON_STACK &&
        flags != MMAP_FLAGS_PRIVATE_ANON_FIXED) ||
      s.readReg64 Reg.x5 != 0#64) = true
  · simp only [hf1, ↓reduceIte] at h; nomatch h
  · simp only [Bool.eq_false_iff.mpr hf1, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hf2 : (len == 0) = true
    · simp only [hf2, ↓reduceIte] at h ⊢
      injection h with h; subst h
      exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-EINVAL))
    · simp only [Bool.eq_false_iff.mpr hf2, Bool.false_eq_true, ↓reduceIte] at h ⊢
      set addr := s.readReg64 Reg.x0
      set size := Arm64.pageAlignUp len
      by_cases hfixed : (flags == MMAP_FLAGS_PRIVATE_ANON_FIXED) = true
      · simp only [hfixed, ↓reduceIte] at h ⊢
        by_cases hf3 : (addr.toNat % PAGE_SIZE != 0 || addr.toNat < MMAP_MIN_ADDR ||
            !decide (addr.toNat + size ≤ 2 ^ 48)) = true
        · simp only [hf3, ↓reduceIte] at h; nomatch h
        · simp only [Bool.eq_false_iff.mpr hf3, Bool.false_eq_true, ↓reduceIte] at h ⊢
          have hbnd48 : addr.toNat + size ≤ 2 ^ 48 := by
            by_contra hgt
            exact hf3 (by simp only [decide_eq_false hgt, Bool.not_false, Bool.or_true])
          have hbnd60 : addr.toNat + size ≤ 2 ^ 60 := by omega
          rw [FastMem.allPerm_eq hag.mem, FastMem.countRw_eq hag.mem] at h
          by_cases hf4 : (!s.mem.allPerm (fun p => !p.frozen) addr size) = true
          · simp only [hf4, ↓reduceIte] at h; nomatch h
          · simp only [Bool.eq_false_iff.mpr hf4, Bool.false_eq_true, ↓reduceIte] at h ⊢
            have hunm_ag := FastMem.unmapNonFrozen_agrees hag.mem addr size
            have hmz_ag := FastMem.mapZero_agrees hunm_ag addr size
            have hivs_mz := heapIntervalsAgree_mapZero_of_bound
              (heapIntervalsAgree_unmapNonFrozen_of_bound hag.heapIvs hbnd60) hbnd60
            by_cases hprot0 : (prot == MMAP_PROT_NONE) = true
            · simp only [hprot0, ↓reduceIte] at h ⊢
              injection h with h; subst h
              have hsp_ag := FastMem.setPermNonFrozen_agrees hmz_ag addr size Perm.protNone
              have hm' := FastState.setMem_agrees hag hsp_ag
                (heapIntervalsAgree_setPermNonFrozen hivs_mz addr size Perm.protNone)
              exact FastState.advancePC_agrees
                (FastState.writeReg64_agrees (fastSetPhysMemAvail_agrees hm' _) Reg.x0 addr)
            · simp only [Bool.eq_false_iff.mpr hprot0, Bool.false_eq_true, ↓reduceIte] at h ⊢
              by_cases hoom : (!decide (size ≤ s.physMemAvail + s.mem.countRw addr size)) = true
              · simp only [hoom, ↓reduceIte] at h ⊢
                injection h with h; subst h
                exact FastState.setStatus_agrees hag .OutOfMemory
              · simp only [Bool.eq_false_iff.mpr hoom, Bool.false_eq_true, ↓reduceIte] at h ⊢
                injection h with h; subst h
                have hm' := FastState.setMem_agrees hag hmz_ag hivs_mz
                exact FastState.advancePC_agrees
                  (FastState.writeReg64_agrees (fastSetPhysMemAvail_agrees hm' _) Reg.x0 addr)
      · simp only [Bool.eq_false_iff.mpr hfixed, Bool.false_eq_true, ↓reduceIte] at h ⊢
        rw [sanitizeMmapAddrFast_eq hag.mem] at h
        cases hsan : sanitizeMmapAddr s.mem (s.oracle.mmap s.oracleIdx) size with
        | none =>
          rw [hsan] at h
          injection h with h; subst h
          exact FastState.setStatus_agrees hag .OutOfMemory
        | some base =>
          rw [hsan] at h
          have huva : USER_VA_LIMIT ≤ 2 ^ 60 := user_va_limit_le_heap
          have hb_lim := sanitizeMmapAddr_bound hsan
          have hbnd60 : base.toNat + size ≤ 2 ^ 60 := by omega
          have hmz_ag := FastMem.mapZero_agrees hag.mem base size
          have hivs_mz := heapIntervalsAgree_mapZero_of_bound hag.heapIvs hbnd60
          by_cases hprot0 : (prot == MMAP_PROT_NONE) = true
          · simp only [hprot0, ↓reduceIte] at h ⊢
            injection h with h; subst h
            have hsp_ag := FastMem.setPermNonFrozen_agrees hmz_ag base size Perm.protNone
            have hm' := FastState.setMem_agrees hag hsp_ag
              (heapIntervalsAgree_setPermNonFrozen hivs_mz base size Perm.protNone)
            exact FastState.advancePC_agrees
              (FastState.writeReg64_agrees (fastNextOracle_agrees hm') Reg.x0 base)
          · simp only [Bool.eq_false_iff.mpr hprot0, Bool.false_eq_true, ↓reduceIte] at h ⊢
            by_cases hoom : (!decide (size ≤ s.physMemAvail)) = true
            · simp only [hoom, ↓reduceIte] at h ⊢
              injection h with h; subst h
              exact FastState.setStatus_agrees hag .OutOfMemory
            · simp only [Bool.eq_false_iff.mpr hoom, Bool.false_eq_true, ↓reduceIte] at h ⊢
              injection h with h; subst h
              have hm' := FastState.setMem_agrees hag hmz_ag hivs_mz
              exact FastState.advancePC_agrees
                (FastState.writeReg64_agrees
                  (fastNextOracle_agrees (fastSetPhysMemAvail_agrees hm' _)) Reg.x0 base)

theorem fastExecMprotect_sound {fs fs' : FastState} {s : State}
    (hag : fs.Agrees s) (h : fastExecMprotect fs = some fs') :
    fs'.Agrees (execMprotect s) := by
  unfold fastExecMprotect at h
  unfold execMprotect
  rw [FastState.readReg64_eq hag Reg.x0, FastState.readReg64_eq hag Reg.x1,
      FastState.readReg64_eq hag Reg.x2, hag.physMemAvail] at h
  set addr := s.readReg64 Reg.x0
  set len := (s.readReg64 Reg.x1).toNat
  set prot := s.readReg64 Reg.x2
  by_cases hf1 : (prot != MMAP_PROT_NONE && prot != MMAP_PROT_RW) = true
  · simp only [hf1, ↓reduceIte] at h; nomatch h
  · simp only [Bool.eq_false_iff.mpr hf1, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hf2 : (addr.toNat % PAGE_SIZE != 0) = true
    · simp only [hf2, ↓reduceIte] at h ⊢
      injection h with h; subst h
      exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-EINVAL))
    · simp only [Bool.eq_false_iff.mpr hf2, Bool.false_eq_true, ↓reduceIte] at h ⊢
      by_cases hf3 : (!decide (addr.toNat + pageAlignUp len ≤ 2 ^ 48)) = true
      · simp only [hf3, ↓reduceIte] at h; nomatch h
      · simp only [Bool.eq_false_iff.mpr hf3, Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases hf4 : (len == 0) = true
        · simp only [hf4, ↓reduceIte] at h ⊢
          injection h with h; subst h
          exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 0#64)
        · simp only [Bool.eq_false_iff.mpr hf4, Bool.false_eq_true, ↓reduceIte] at h ⊢
          rw [FastMem.allPerm_eq hag.mem, FastMem.allPerm_eq hag.mem,
              FastMem.canMap_eq hag.mem, FastMem.countRw_eq hag.mem] at h
          by_cases hf5 : (!s.mem.allPerm (fun p => !p.frozen) addr (pageAlignUp len)) = true
          · simp only [hf5, ↓reduceIte] at h; nomatch h
          · simp only [Bool.eq_false_iff.mpr hf5, Bool.false_eq_true, ↓reduceIte] at h ⊢
            by_cases hf6 : (!s.mem.allPerm (·.mapped) addr (pageAlignUp len)) = true
            · simp only [hf6, ↓reduceIte] at h ⊢
              by_cases hcm : s.mem.canMap addr (pageAlignUp len) = true
              · simp only [hcm, ↓reduceIte] at h ⊢
                injection h with h; subst h
                exact FastState.advancePC_agrees (FastState.writeReg64_agrees hag Reg.x0 (-ENOMEM))
              · simp only [Bool.eq_false_iff.mpr hcm, Bool.false_eq_true, ↓reduceIte] at h
                nomatch h
            · simp only [Bool.eq_false_iff.mpr hf6, Bool.false_eq_true, ↓reduceIte] at h ⊢
              by_cases hprot0 : (prot == MMAP_PROT_NONE) = true
              · simp only [hprot0, ↓reduceIte] at h ⊢
                injection h with h; subst h
                have hm' := FastState.setMem_agrees hag
                  (FastMem.setPermNonFrozen_agrees hag.mem addr (pageAlignUp len) Perm.protNone)
                  (heapIntervalsAgree_setPermNonFrozen hag.heapIvs addr (pageAlignUp len) Perm.protNone)
                exact FastState.advancePC_agrees (FastState.writeReg64_agrees hm' Reg.x0 0#64)
              · simp only [Bool.eq_false_iff.mpr hprot0, Bool.false_eq_true, ↓reduceIte] at h ⊢
                by_cases hoom : (!decide (pageAlignUp len - s.mem.countRw addr (pageAlignUp len) ≤ s.physMemAvail)) = true
                · simp only [hoom, ↓reduceIte] at h ⊢
                  injection h with h; subst h
                  exact FastState.setStatus_agrees hag .OutOfMemory
                · simp only [Bool.eq_false_iff.mpr hoom, Bool.false_eq_true, ↓reduceIte] at h ⊢
                  injection h with h; subst h
                  have hm' := FastState.setMem_agrees hag
                    (FastMem.setPermNonFrozen_agrees hag.mem addr (pageAlignUp len) Perm.rw)
                    (heapIntervalsAgree_setPermNonFrozen hag.heapIvs addr (pageAlignUp len) Perm.rw)
                  exact FastState.advancePC_agrees
                    (FastState.writeReg64_agrees (fastSetPhysMemAvail_agrees hm' _) Reg.x0 0#64)

theorem fastExecSyscallPlaced_agrees
    {fs fs' : FastState} {s : Arm64.State}
    (hag : fs.Agrees s)
    (heval : PlacedExecCore.fastExecSyscallPlaced fs = some fs') :
    fs'.Agrees (Arm64.Syscall.standard s) := by
  unfold PlacedExecCore.fastExecSyscallPlaced at heval
  rw [FastState.readReg64_eq hag Reg.x8] at heval
  dsimp only at heval
  by_cases h25 : (s.readReg64 Reg.x8 == 25#64) = true
  · simp only [h25, ↓reduceIte] at heval
    rw [syscall_standard_fcntl h25]
    exact fastExecFcntl_sound hag heval
  · simp only [h25, Bool.false_eq_true, ↓reduceIte] at heval
    by_cases h56 : (s.readReg64 Reg.x8 == 56#64) = true
    · simp only [h56, ↓reduceIte] at heval
      rw [syscall_standard_openat h56]
      exact fastExecOpenat_sound hag heval
    · simp only [h56, Bool.false_eq_true, ↓reduceIte] at heval
      by_cases h57 : (s.readReg64 Reg.x8 == 57#64) = true
      · simp only [h57, ↓reduceIte] at heval
        rw [syscall_standard_close h57]
        exact fastExecClose_sound hag heval
      · simp only [h57, Bool.false_eq_true, ↓reduceIte] at heval
        by_cases h63 : (s.readReg64 Reg.x8 == 63#64) = true
        · simp only [h63, ↓reduceIte] at heval
          rw [syscall_standard_read h63]
          exact fastExecRead_sound hag heval
        · simp only [h63, Bool.false_eq_true, ↓reduceIte] at heval
          by_cases h80 : (s.readReg64 Reg.x8 == 80#64) = true
          · simp only [h80, ↓reduceIte] at heval
            rw [syscall_standard_fstat h80]
            exact fastExecFstat_sound hag heval
          · simp only [h80, Bool.false_eq_true, ↓reduceIte] at heval
            by_cases h93 : (s.readReg64 Reg.x8 == 93#64) = true
            · simp only [h93, Bool.true_or, ↓reduceIte] at heval
              injection heval with heval; subst heval
              rw [syscall_standard_exit h93]
              exact fastExecExit_sound hag
            · by_cases h94 : (s.readReg64 Reg.x8 == 94#64) = true
              · have h93f : (s.readReg64 Reg.x8 == 93#64) = false :=
                  Bool.eq_false_iff.mpr h93
                simp only [h93f, h94, Bool.false_or, ↓reduceIte] at heval
                injection heval with heval; subst heval
                rw [syscall_standard_exitGroup h94]
                exact fastExecExit_sound hag
              · have h934f :
                    ((s.readReg64 Reg.x8 == 93#64) || (s.readReg64 Reg.x8 == 94#64)) = false := by
                  simp [Bool.eq_false_iff.mpr h93, Bool.eq_false_iff.mpr h94]
                simp only [h934f, Bool.false_eq_true, ↓reduceIte] at heval
                by_cases h96 : (s.readReg64 Reg.x8 == 96#64) = true
                · simp only [h96, ↓reduceIte] at heval
                  injection heval with heval; subst heval
                  rw [syscall_standard_setTidAddress h96]
                  exact fastExecSetTidAddress_sound hag
                · simp only [h96, Bool.false_eq_true, ↓reduceIte] at heval
                  by_cases h214 : (s.readReg64 Reg.x8 == 214#64) = true
                  · simp only [h214, ↓reduceIte] at heval
                    rw [syscall_standard_brk h214]
                    exact fastExecBrk_sound hag heval
                  · simp only [h214, Bool.false_eq_true, ↓reduceIte] at heval
                    by_cases h215 : (s.readReg64 Reg.x8 == 215#64) = true
                    · simp only [h215, ↓reduceIte] at heval
                      rw [syscall_standard_munmap h215]
                      exact fastExecMunmap_sound hag heval
                    · simp only [h215, Bool.false_eq_true, ↓reduceIte] at heval
                      by_cases h216 : (s.readReg64 Reg.x8 == 216#64) = true
                      · simp only [h216, ↓reduceIte] at heval
                        rw [syscall_standard_mremap h216]
                        exact fastExecMremap_sound hag heval
                      · simp only [h216, Bool.false_eq_true, ↓reduceIte] at heval
                        by_cases h222 : (s.readReg64 Reg.x8 == 222#64) = true
                        · simp only [h222, ↓reduceIte] at heval
                          rw [syscall_standard_mmap h222]
                          exact fastExecMmap_sound hag heval
                        · simp only [h222, Bool.false_eq_true, ↓reduceIte] at heval
                          by_cases h226 : (s.readReg64 Reg.x8 == 226#64) = true
                          · simp only [h226, ↓reduceIte] at heval
                            rw [syscall_standard_mprotect h226]
                            exact fastExecMprotect_sound hag heval
                          · simp only [h226, Bool.false_eq_true, ↓reduceIte] at heval
                            nomatch heval

theorem fastExecSyscallPlaced_sound
    {prog : Arm64.Program} (hsvc : prog.svc = Arm64.Syscall.standard)
    {fs fs' : FastState} {s : Arm64.State}
    (hag : fs.Agrees s)
    (heval : PlacedExecCore.fastExecSyscallPlaced fs = some fs') :
    fs'.Agrees (prog.evalInst (.system false 0#16) s) := by
  rw [evalInst_system_svc0 hsvc s]
  exact fastExecSyscallPlaced_agrees hag heval

theorem fastEvalInstPlaced_sound : EvalSoundPlaced PlacedExecCore.fastEvalInstPlaced := by
  intro prog hsvc inst fs fs' s hag heval
  unfold PlacedExecCore.fastEvalInstPlaced at heval
  split at heval
  · exact fastExecSyscallPlaced_sound hsvc hag heval
  · simpa only [Program.evalInst] using fastExecLdxr_sound hag (evalSvc prog.svc) heval
  · simpa only [Program.evalInst] using fastExecStxr_sound hag (evalSvc prog.svc) heval
  · injection heval with heval; subst heval
    simpa only [Program.evalInst] using fastExecBarrier_sound hag (evalSvc prog.svc) _ _
  · exact FastEval.fastEvalInst_sound hsvc hag heval

end Symbolic.BugInjection.Proofs.CliExec.SyscallSoundnessPlaced
