/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Invariant
public import ProofLib.Lemmas
public import ProofLib.OpcodeExclusion
public import ProofLib.Process

/-!
# File-System Change Tracing

Proves that every step and multi-step execution appends to `State.trace` (`Steps.trace_prefix`)
and modifies `FsState.files` only when emitting a `TraceEvent.isFsChange` event
(`Steps.fsTraced`, `Steps.files_eq_of_noFs`), and establishes preservation of the
`MAX_LFS_FILESIZE` regular-file length bound (`Steps.filesLeMaxLfs`).
-/

@[expose] public section

namespace Arm64

/-- The engine's events that come with a change of `FsState.files`: the bytes `write` writes to
    a file descriptor other than 1 and 2 (`OutputStream.ofFd`), and `openat`'s `fileChanged`. -/
def TraceEvent.isFsChange : TraceEvent → Bool
  | .writeByte (.fd _) _ => true
  | .fileChanged _ => true
  | _ => false

/-- `s'.trace` is `s.trace ++ d`, and if no event of `d` satisfies `isFs`, `s'` has the files of
    `s`. -/
def FsTraced (isFs : TraceEvent → Prop) (s s' : State) : Prop :=
  ∃ d, s'.trace = s.trace ++ d ∧ ((∀ e ∈ d, ¬ isFs e) → s'.fs.files = s.fs.files)

/-- Hook `f` only appends to the trace, and changes `fs.files` only together with an `isFs`
    event. -/
def HookFsTraced (isFs : TraceEvent → Prop) (f : State → State) : Prop :=
  ∀ s, FsTraced isFs s (f s)

namespace FsTraced

variable {isFs : TraceEvent → Prop}

theorem of_eq {s s' : State} (ht : s'.trace = s.trace) (hf : s'.fs.files = s.fs.files) :
    FsTraced isFs s s' :=
  ⟨[], by rw [ht, List.append_nil], fun _ => hf⟩

theorem refl (s : State) : FsTraced isFs s s := of_eq rfl rfl

/-- The trace grows by `d` and the files stay the same. -/
theorem of_files {s s' : State} (d : List TraceEvent) (ht : s'.trace = s.trace ++ d)
    (hf : s'.fs.files = s.fs.files) : FsTraced isFs s s' :=
  ⟨d, ht, fun _ => hf⟩

/-- The trace grows by `d`, which holds an `isFs` event: the files may change. -/
theorem of_fsEvent {s s' : State} (d : List TraceEvent) (ht : s'.trace = s.trace ++ d)
    (e : TraceEvent) (he : e ∈ d) (hfs : isFs e) : FsTraced isFs s s' :=
  ⟨d, ht, fun h => absurd hfs (h e he)⟩

theorem trans {s1 s2 s3 : State} (h12 : FsTraced isFs s1 s2) (h23 : FsTraced isFs s2 s3) :
    FsTraced isFs s1 s3 := by
  obtain ⟨d1, ht1, hf1⟩ := h12
  obtain ⟨d2, ht2, hf2⟩ := h23
  refine ⟨d1 ++ d2, by rw [ht2, ht1, List.append_assoc], fun h => ?_⟩
  rw [hf2 (fun e he => h e (List.mem_append_right _ he)),
    hf1 (fun e he => h e (List.mem_append_left _ he))]

end FsTraced

/-! ## Instructions other than `svc #0` keep the trace and the files -/

/-- Every instruction but `svc #0` keeps the trace (only `execSyscall`'s `write` appends to it);
    `execInst_trace_of_not_isSvc0` of `ProofLib.OpcodeExclusion`. -/
theorem execInst_trace_of_ne_svc0 (inst : Instr) (s : State)
    (hne : inst ≠ .system false 0#16) : (execInst inst s).trace = s.trace := by
  refine execInst_trace_of_not_isSvc0 ?_ s
  cases inst <;> try rfl
  rename_i isHalt imm
  cases isHalt
  · by_cases h0 : imm = 0#16
    · exact absurd (h0 ▸ rfl) hne
    · simp [Instr.isSvc0, h0]
  · rfl

/-- Every instruction but `svc #0` is `isNonFs`. -/
theorem isNonFs_of_ne_svc0 (inst : Instr) (s : State)
    (hne : inst ≠ .system false 0#16) : inst.isNonFs s = true := by
  unfold Instr.isNonFs
  split
  · exact absurd rfl hne
  · rfl

/-- Every instruction but `svc #0` keeps the file system (`Process.execInst_setFs_of_isNonFs`
    with `f := s.fs`). -/
theorem execInst_fs_of_ne_svc0 (inst : Instr) (s : State)
    (hne : inst ≠ .system false 0#16) : (execInst inst s).fs = s.fs := by
  have h := Process.execInst_setFs_of_isNonFs inst s s.fs (isNonFs_of_ne_svc0 inst s hne)
  have hs : s.setFs s.fs = s := by cases s; rfl
  rw [hs] at h
  exact (congrArg State.fs h).trans (ProofLib.State.fs_setFs _ _)

/-! ## System calls -/

section SyscallFsTraced

variable {isFs : TraceEvent → Prop}

local macro "fs_traced_eq" : tactic =>
  `(tactic| (repeat' split) <;> exact FsTraced.of_eq rfl rfl)

/-- `setEntry segs e` with `e` the entry `segs` already has leaves `files` as it is. -/
theorem FsState.files_setEntry_of_eq {fs : FsState} {segs : FsPath} {e : Option FsEntry}
    (h : fs.getEntry segs = e) : (fs.setEntry segs e).files = fs.files := by
  funext q
  simp only [FsState.files, FsState.getEntry, FsState.setEntry]
  split
  · rfl
  · split
    · rename_i hne hq; rw [eq_of_beq hq] at hne ⊢; simpa [FsState.getEntry, hne] using h.symm
    · rfl

/-- `setFile p (files p)` leaves `files` as it is. -/
theorem FsState.files_setFile_self (fs : FsState) (p : String) :
    (fs.setFile p (fs.files p)).files = fs.files :=
  FsState.files_setEntry_of_eq rfl

@[simp] theorem FsState.files_setFd (fs : FsState) (fd : BitVec 64) (e : Option FdEntry) :
    (fs.setFd fd e).files = fs.files := rfl

@[simp] theorem FsState.stdin_setEntry (fs : FsState) (p : FsPath) (e : Option FsEntry) :
    (fs.setEntry p e).stdin = fs.stdin := rfl

@[simp] theorem FsState.stdin_setFile (fs : FsState) (p : String) (e : Option FsEntry) :
    (fs.setFile p e).stdin = fs.stdin := rfl

@[simp] theorem FsState.stdin_setFd (fs : FsState) (fd : BitVec 64) (e : Option FdEntry) :
    (fs.setFd fd e).stdin = fs.stdin := rfl

/-- `write` to a file descriptor other than 1 and 2 of `count ≠ 0` bytes appends at least one
    `writeByte (.fd _)` event. -/
theorem fsTraced_of_writeEvents {isFs : TraceEvent → Prop}
    (hsem : ∀ e, e.isFsChange = true → isFs e) {s s' : State} {fd count buf : BitVec 64}
    {m : Memory}
    (ht : s'.trace = s.trace ++ TraceEvent.ofBytes (OutputStream.ofFd fd)
      (m.readBytes buf (min count.toNat MAX_RW_COUNT)))
    (hfd : ¬(fd == 1#64 || fd == 2#64) = true) (hc : ¬(count == 0#64) = true) :
    FsTraced isFs s s' := by
  have hofd : OutputStream.ofFd fd = .fd fd := by
    simp only [Bool.or_eq_true, not_or] at hfd
    simp only [OutputStream.ofFd, hfd.1, hfd.2, Bool.false_eq_true, ↓reduceIte]
  have h0 : min count.toNat MAX_RW_COUNT ≠ 0 := by
    intro h0
    apply hc
    have hcnt0 : count.toNat = 0 := by simp [MAX_RW_COUNT] at h0; omega
    have : count = 0#64 := BitVec.eq_of_toNat_eq (by simp [hcnt0])
    subst this
    simp
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero h0
  rw [hofd, hk, Memory.readBytes_succ] at ht
  exact FsTraced.of_fsEvent _ ht (.writeByte (.fd fd) (m.read8 buf))
    (List.mem_cons_self ..) (hsem _ rfl)

private theorem fsTraced_execIoctl (s : State) : FsTraced isFs s (execIoctl s) := by
  dsimp (config := { zetaHave := true }) only [execIoctl]; fs_traced_eq
private theorem fsTraced_execFcntl (s : State) : FsTraced isFs s (execFcntl s) := by
  dsimp (config := { zetaHave := true }) only [execFcntl]; fs_traced_eq
private theorem fsTraced_execClose (s : State) : FsTraced isFs s (execClose s) := by
  dsimp (config := { zetaHave := true }) only [execClose]; fs_traced_eq
private theorem fsTraced_ite {s s₁ s₂ : State} {c : Prop} [Decidable c]
    (h₁ : c → FsTraced isFs s s₁) (h₂ : ¬c → FsTraced isFs s s₂) :
    FsTraced isFs s (if c then s₁ else s₂) := by
  by_cases hc : c <;> simp [hc, h₁, h₂]

private theorem fsTraced_execLseek (s : State) : FsTraced isFs s (execLseek s) := by
  dsimp (config := { zetaHave := true }) only [execLseek]
  repeat' (apply fsTraced_ite <;> intro)
  any_goals exact FsTraced.of_eq rfl rfl
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0))
  · dsimp only; repeat' (apply fsTraced_ite <;> intro)
    all_goals exact FsTraced.of_eq rfl rfl
  · dsimp only; repeat' (apply fsTraced_ite <;> intro)
    any_goals exact FsTraced.of_eq rfl rfl
    fs_traced_eq
private theorem fsTraced_execReadCommon (s : State) (b : Bool) :
    FsTraced isFs s (execReadCommon s b) := by
  dsimp (config := { zetaHave := true }) only [execReadCommon]
  repeat' (apply fsTraced_ite <;> intro)
  any_goals exact FsTraced.of_eq rfl rfl
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0))
  · dsimp only; repeat' (apply fsTraced_ite <;> intro)
    all_goals exact FsTraced.of_eq rfl rfl
  · dsimp only; repeat' (apply fsTraced_ite <;> intro)
    all_goals (try cases b) <;> exact FsTraced.of_eq rfl rfl
private theorem fsTraced_execFstat (s : State) : FsTraced isFs s (execFstat s) := by
  dsimp (config := { zetaHave := true }) only [execFstat]; fs_traced_eq
private theorem fsTraced_execPpoll (s : State) : FsTraced isFs s (execPpoll s) := by
  dsimp (config := { zetaHave := true }) only [execPpoll]
  by_cases h1 : (s.readReg64 Reg.x2 == 0#64) = true
  · simp only [h1, ↓reduceIte]; exact FsTraced.of_eq rfl rfl
  simp only [eq_false h1, ↓reduceIte]
  by_cases h2 : (!decide ((s.readReg64 Reg.x2).toNat + 16 ≤ 2 ^ 64) || !s.mem.allPerm Option.r (s.readReg64 Reg.x2) 16) = true
  · simp only [h2, ↓reduceIte]; exact FsTraced.of_eq rfl rfl
  simp only [eq_false h2, ↓reduceIte]
  by_cases h3 : (!s.mem.canRead (s.readReg64 Reg.x2) 16) = true
  · simp only [h3, ↓reduceIte]; exact FsTraced.of_eq rfl rfl
  simp only [eq_false h3, ↓reduceIte]
  by_cases h4 : ((s.mem.read64 (s.readReg64 Reg.x2)).slt 0#64 || (s.mem.read64 (s.readReg64 Reg.x2 + 8#64)).slt 0#64 || !decide ((s.mem.read64 (s.readReg64 Reg.x2 + 8#64)).toNat < 1000000000)) = true
  · simp only [h4, ↓reduceIte]; exact FsTraced.of_eq rfl rfl
  simp only [eq_false h4, ↓reduceIte]
  fs_traced_eq
private theorem fsTraced_execSetTidAddress (s : State) :
    FsTraced isFs s (execSetTidAddress s) := FsTraced.of_eq rfl rfl
private theorem fsTraced_execSchedGetaffinity (s : State) :
    FsTraced isFs s (execSchedGetaffinity s) := by
  dsimp (config := { zetaHave := true }) only [execSchedGetaffinity]; fs_traced_eq
private theorem fsTraced_execClockGettime (s : State) : FsTraced isFs s (execClockGettime s) := by
  dsimp (config := { zetaHave := true }) only [execClockGettime]; fs_traced_eq
private theorem fsTraced_execMmap (s : State) : FsTraced isFs s (execMmap s) := by
  dsimp (config := { zetaHave := true }) only [execMmap]; fs_traced_eq
private theorem fsTraced_execBrk (s : State) : FsTraced isFs s (execBrk s) := by
  dsimp (config := { zetaHave := true }) only [execBrk]; fs_traced_eq
private theorem fsTraced_execMunmap (s : State) : FsTraced isFs s (execMunmap s) := by
  dsimp (config := { zetaHave := true }) only [execMunmap]; fs_traced_eq
private theorem fsTraced_execMremap (s : State) : FsTraced isFs s (execMremap s) := by
  dsimp (config := { zetaHave := true }) only [execMremap]; fs_traced_eq
private theorem fsTraced_execMprotect (s : State) : FsTraced isFs s (execMprotect s) := by
  dsimp (config := { zetaHave := true }) only [execMprotect]; fs_traced_eq
private theorem fsTraced_execMadvise (s : State) : FsTraced isFs s (execMadvise s) := by
  dsimp (config := { zetaHave := true }) only [execMadvise]; fs_traced_eq
private theorem fsTraced_execGetrandom (s : State) : FsTraced isFs s (execGetrandom s) := by
  dsimp (config := { zetaHave := true }) only [execGetrandom]; fs_traced_eq
private theorem fsTraced_execGetpid (s : State) : FsTraced isFs s (execGetpid s) :=
  FsTraced.of_eq rfl rfl
private theorem fsTraced_execRtSigprocmask (s : State) :
    FsTraced isFs s (execRtSigprocmask s) := by
  dsimp (config := { zetaHave := true }) only [execRtSigprocmask]; fs_traced_eq
private theorem fsTraced_execSigaltstack (s : State) : FsTraced isFs s (execSigaltstack s) := by
  dsimp (config := { zetaHave := true }) only [execSigaltstack]; fs_traced_eq
private theorem fsTraced_execRtSigaction (s : State) : FsTraced isFs s (execRtSigaction s) := by
  dsimp (config := { zetaHave := true }) only [execRtSigaction]; fs_traced_eq
private theorem fsTraced_execTkill (s : State) : FsTraced isFs s (execTkill s) := by
  dsimp (config := { zetaHave := true }) only [execTkill]; fs_traced_eq
private theorem fsTraced_execTgkill (s : State) : FsTraced isFs s (execTgkill s) := by
  dsimp (config := { zetaHave := true }) only [execTgkill]; fs_traced_eq

/-- Unfolding equation connecting `execOpenat` to `applyOpenVerdict s (openatPure ...)`
    when `checkOpenFlags` returns `none` and `readCString` succeeds. -/
theorem execOpenat_eq_applyOpenVerdict_openatPure (s : State) (rawPath : String)
    (hflags : checkOpenFlags (s.readReg32 Reg.x2) = none)
    (hcs : readCString s.mem (s.readReg64 Reg.x1) = .ok rawPath) :
    execOpenat s =
      applyOpenVerdict s
        (openatPure s.fs (s.readReg32 Reg.x0) rawPath (s.readReg32 Reg.x2) (s.readReg32 Reg.x3)) := by
  simp [execOpenat, hflags, hcs]

private theorem fsTraced_openatPure (hsem : ∀ e, e.isFsChange = true → isFs e)
    (s : State) (dfd : BitVec 32) (rawPath : String) (flags mode : BitVec 32) :
    FsTraced isFs s (applyOpenVerdict s (openatPure s.fs dfd rawPath flags mode)) := by
  dsimp (config := { zetaHave := true }) only [openatPure]
  cases hchk : checkOpenFlags flags with
  | some v =>
    unfold checkOpenFlags at hchk
    (repeat' split at hchk) <;> cases hchk <;> exact FsTraced.of_eq rfl rfl
  | none =>
    dsimp only
    generalize s.fs.allocFd = fd?
    (repeat' split) <;> dsimp only [applyOpenVerdict] <;> (repeat' split)
    all_goals first
      | exact FsTraced.of_eq rfl rfl
      | exact FsTraced.of_fsEvent [.fileChanged _] rfl _ (List.mem_singleton_self _) (hsem _ rfl)
      | exact FsTraced.of_eq rfl (FsState.files_setEntry_of_eq ‹_›)

/-- `openat`: the files change only when it creates or truncates a file, and then it appends
    `fileChanged`. -/
theorem fsTraced_execOpenat (hsem : ∀ e, e.isFsChange = true → isFs e) (s : State) :
    FsTraced isFs s (execOpenat s) := by
  dsimp (config := { zetaHave := true }) only [execOpenat]
  cases hchk : checkOpenFlags (s.readReg32 Reg.x2) with
  | some v =>
    unfold checkOpenFlags at hchk
    (repeat' split at hchk) <;> cases hchk <;> exact FsTraced.of_eq rfl rfl
  | none =>
    cases readCString s.mem (s.readReg64 Reg.x1) with
    | trap _ => exact FsTraced.of_eq rfl rfl
    | errno _ => exact FsTraced.of_eq rfl rfl
    | ok rawPath => exact fsTraced_openatPure hsem s _ rawPath _ _

/-- `write`: on a file descriptor other than 1 and 2 with `count > 0`, the files change and the
    events are `writeByte (.fd fd)`; otherwise the files stay. -/
theorem fsTraced_execWrite (hsem : ∀ e, e.isFsChange = true → isFs e) (s : State) :
    FsTraced isFs s (execWrite s) := by
  dsimp (config := { zetaHave := true }) only [execWrite]
  repeat' (apply fsTraced_ite <;> intro)
  any_goals first
    | exact FsTraced.of_eq rfl rfl
    | exact FsTraced.of_files _ rfl rfl
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0))
  · dsimp only; repeat' (apply fsTraced_ite <;> intro)
    all_goals exact FsTraced.of_eq rfl rfl
  · dsimp only; repeat' (apply fsTraced_ite <;> intro)
    all_goals first
      | exact FsTraced.of_eq rfl rfl
      | exact FsTraced.of_files _ rfl rfl
      | exact fsTraced_of_writeEvents hsem rfl ‹_› ‹_›

private theorem fsTraced_rwvFrame : ProofLib.RwvFrame (FsTraced isFs) where
  refl := FsTraced.refl
  trans _ _ _ := FsTraced.trans
  reg _ _ _ := FsTraced.of_eq rfl rfl
  pc _ := FsTraced.of_eq rfl rfl
  status _ _ := FsTraced.of_eq rfl rfl
  regsPc _ _ _ := FsTraced.of_eq rfl rfl

/-- `readv`: sequential `read`s, which never change the files or the trace. -/
theorem fsTraced_execReadv (_hsem : ∀ e, e.isFsChange = true → isFs e) (s : State) :
    FsTraced isFs s (execReadv s) :=
  ProofLib.execReadv_preserves fsTraced_rwvFrame (fsTraced_execReadCommon · false) s

/-- `writev`: sequential `write`s. -/
theorem fsTraced_execWritev (hsem : ∀ e, e.isFsChange = true → isFs e) (s : State) :
    FsTraced isFs s (execWritev s) :=
  ProofLib.execWritev_preserves fsTraced_rwvFrame (fsTraced_execWrite hsem) s

theorem dispatch_fsTraced
    (table : List (BitVec 64 × (State → State))) (s : State)
    (htab : ∀ p ∈ table, FsTraced isFs s (p.2 s)) :
    FsTraced isFs s (Syscall.dispatch table s) := by
  unfold Syscall.dispatch
  split
  · rename_i nr fn h
    exact htab (nr, fn) (List.mem_of_find?_eq_some h)
  · exact FsTraced.of_eq rfl rfl

private theorem standardEntry_fsTraced (hsem : ∀ e, e.isFsChange = true → isFs e) (s : State) :
    ∀ p ∈ Syscall.standardTable, FsTraced isFs s (p.2 s) := by
  simp only [Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable, Syscall.timeTable,
    Syscall.randomTable, Syscall.miscTable,
    List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact fsTraced_execReadCommon s false
  · exact fsTraced_execWrite hsem s
  · exact fsTraced_execReadv hsem s
  · exact fsTraced_execWritev hsem s
  · exact FsTraced.of_eq rfl rfl
  · exact FsTraced.of_eq rfl rfl
  · exact fsTraced_execFcntl s
  · exact fsTraced_execIoctl s
  · exact fsTraced_execOpenat hsem s
  · exact fsTraced_execClose s
  · exact fsTraced_execLseek s
  · exact fsTraced_execReadCommon s true
  · exact fsTraced_execFstat s
  · exact fsTraced_execPpoll s
  · exact fsTraced_execBrk s
  · exact fsTraced_execMunmap s
  · exact fsTraced_execMremap s
  · exact fsTraced_execMmap s
  · exact fsTraced_execMprotect s
  · exact fsTraced_execMadvise s
  · exact fsTraced_execTkill s
  · exact fsTraced_execTgkill s
  · exact fsTraced_execSigaltstack s
  · exact fsTraced_execRtSigaction s
  · exact fsTraced_execRtSigprocmask s
  · exact fsTraced_execClockGettime s
  · exact fsTraced_execGetrandom s
  · exact fsTraced_execSetTidAddress s
  · exact fsTraced_execSchedGetaffinity s
  · exact fsTraced_execGetpid s
  · exact fsTraced_execGetpid s

theorem execSyscall_fsTraced (hsem : ∀ e, e.isFsChange = true → isFs e) (s : State) :
    FsTraced isFs s (execSyscall s) :=
  dispatch_fsTraced Syscall.standardTable s (standardEntry_fsTraced hsem s)

end SyscallFsTraced

/-! ## Steps -/

variable {isFs : TraceEvent → Prop}

private theorem evalInst_eq_execInst_of_ne_svc0 (prog : Program) (inst : Instr) (s : State)
    (his : inst ≠ .system false 0#16) : prog.evalInst inst s = execInst inst s := by
  cases inst <;> try rfl
  rename_i isHalt imm
  cases isHalt
  · by_cases h0 : imm = 0#16
    · exact absurd (h0 ▸ rfl) his
    · simp [Program.evalInst, execInstWithSvc, execInst, h0]
  · rfl

/-- One step is `FsTraced` under custom `prog.svc` when every `svc #0` handler (`hsvc`) and extern
    hook (`hhooks`) is `HookFsTraced`. -/
theorem Step.fsTracedWithSvc {prog : Program}
    (hsvc : HookFsTraced isFs prog.svc)
    (hhooks : ∀ pc f, prog.externAt? pc = some f → HookFsTraced isFs f)
    {s s' : State} (h : Step prog s s') :
    FsTraced isFs s s' := by
  cases h with
  | @exec inst _ _ =>
    by_cases his : inst = .system false 0#16
    · subst his
      exact hsvc s
    · rw [evalInst_eq_execInst_of_ne_svc0 prog inst s his]
      exact FsTraced.of_eq (execInst_trace_of_ne_svc0 inst s his)
        (congrArg FsState.files (execInst_fs_of_ne_svc0 inst s his))
  | halt_unmapped _ _ _ => exact FsTraced.of_eq rfl rfl
  | extern _ hext _ _ => exact hhooks _ _ hext s
  | extern_fault _ _ _ => exact FsTraced.of_eq rfl rfl

theorem Steps.fsTracedWithSvc {prog : Program}
    (hsvc : HookFsTraced isFs prog.svc)
    (hhooks : ∀ pc f, prog.externAt? pc = some f → HookFsTraced isFs f)
    {s s' : State} (h : Steps prog s s') :
    FsTraced isFs s s' := by
  induction h with
  | refl _ => exact FsTraced.refl _
  | step h1 _ ih => exact (h1.fsTracedWithSvc hsvc hhooks).trans ih

/-- One step is `FsTraced` when every `isFsChange` event is an `isFs` event and every hook of
    `prog` is `HookFsTraced`. -/
theorem Step.fsTraced {prog : Program} (hsem : ∀ e, e.isFsChange = true → isFs e)
    (hhooks : ∀ pc f, prog.externAt? pc = some f → HookFsTraced isFs f)
    {s s' : State} (h : Step prog s s')
    (hsvc : prog.svc = execSyscall := by first | rfl | simp [ProofLib.wp_norm, ProofLib.arm64_norm]) :
    FsTraced isFs s s' :=
  h.fsTracedWithSvc (hsvc ▸ execSyscall_fsTraced hsem) hhooks

theorem Steps.fsTraced {prog : Program} (hsem : ∀ e, e.isFsChange = true → isFs e)
    (hhooks : ∀ pc f, prog.externAt? pc = some f → HookFsTraced isFs f)
    {s s' : State} (h : Steps prog s s')
    (hsvc : prog.svc = execSyscall := by first | rfl | simp [ProofLib.wp_norm, ProofLib.arm64_norm]) :
    FsTraced isFs s s' :=
  h.fsTracedWithSvc (hsvc ▸ execSyscall_fsTraced hsem) hhooks

/-- Files are unchanged across a run whose trace delta contains no `isFs` event (`Steps.fsTraced`
    written out). -/
theorem Steps.files_eq_of_noFs {prog : Program} (hsem : ∀ e, e.isFsChange = true → isFs e)
    (hhooks : ∀ pc f, prog.externAt? pc = some f → HookFsTraced isFs f)
    {s s' : State} (h : Steps prog s s')
    (hsvc : prog.svc = execSyscall := by first | rfl | simp [ProofLib.wp_norm, ProofLib.arm64_norm]) :
    ∃ d, s'.trace = s.trace ++ d ∧ ((∀ e ∈ d, ¬ isFs e) → s'.fs.files = s.fs.files) :=
  h.fsTraced hsem hhooks hsvc

theorem Step.files_eq_of_noFs {prog : Program} (hsem : ∀ e, e.isFsChange = true → isFs e)
    (hhooks : ∀ pc f, prog.externAt? pc = some f → HookFsTraced isFs f)
    {s s' : State} (h : Step prog s s')
    (hsvc : prog.svc = execSyscall := by first | rfl | simp [ProofLib.wp_norm, ProofLib.arm64_norm]) :
    ∃ d, s'.trace = s.trace ++ d ∧ ((∀ e ∈ d, ¬ isFs e) → s'.fs.files = s.fs.files) :=
  h.fsTraced hsem hhooks hsvc

/-- One step only appends to the trace under custom `prog.svc` when `prog.svc` and every hook
    do. -/
theorem Step.trace_prefixWithSvc {prog : Program}
    (hsvc : ∀ s, ∃ d, (prog.svc s).trace = s.trace ++ d)
    (hhooks : ∀ pc f, prog.externAt? pc = some f → ∀ s, ∃ d, (f s).trace = s.trace ++ d)
    {s s' : State} (h : Step prog s s') :
    ∃ d, s'.trace = s.trace ++ d := by
  cases h with
  | @exec inst _ _ =>
    by_cases his : inst = .system false 0#16
    · subst his
      exact hsvc s
    · rw [evalInst_eq_execInst_of_ne_svc0 prog inst s his]
      exact ⟨[], by rw [execInst_trace_of_ne_svc0 inst s his, List.append_nil]⟩
  | halt_unmapped _ _ _ => exact ⟨[], (List.append_nil _).symm⟩
  | extern _ hext _ _ => exact hhooks _ _ hext s
  | extern_fault _ _ _ => exact ⟨[], (List.append_nil _).symm⟩

theorem Steps.trace_prefixWithSvc {prog : Program}
    (hsvc : ∀ s, ∃ d, (prog.svc s).trace = s.trace ++ d)
    (hhooks : ∀ pc f, prog.externAt? pc = some f → ∀ s, ∃ d, (f s).trace = s.trace ++ d)
    {s s' : State} (h : Steps prog s s') :
    ∃ d, s'.trace = s.trace ++ d := by
  induction h with
  | refl _ => exact ⟨[], (List.append_nil _).symm⟩
  | step h1 _ ih =>
    obtain ⟨d1, hd1⟩ := h1.trace_prefixWithSvc hsvc hhooks
    obtain ⟨d2, hd2⟩ := ih
    exact ⟨d1 ++ d2, by rw [hd2, hd1, List.append_assoc]⟩

/-- One step only appends to the trace when every hook of `prog` does. -/
theorem Step.trace_prefix {prog : Program}
    (hhooks : ∀ pc f, prog.externAt? pc = some f → ∀ s, ∃ d, (f s).trace = s.trace ++ d)
    {s s' : State} (h : Step prog s s')
    (hsvc : prog.svc = execSyscall := by first | rfl | simp [ProofLib.wp_norm, ProofLib.arm64_norm]) :
    ∃ d, s'.trace = s.trace ++ d :=
  h.trace_prefixWithSvc
    (fun t => hsvc ▸ (execSyscall_fsTraced (isFs := fun _ => True) (fun _ _ => trivial) t).elim
      fun d hd => ⟨d, hd.1⟩)
    hhooks

/-- A run only appends to the trace when every hook of `prog` does. -/
theorem Steps.trace_prefix {prog : Program}
    (hhooks : ∀ pc f, prog.externAt? pc = some f → ∀ s, ∃ d, (f s).trace = s.trace ++ d)
    {s s' : State} (h : Steps prog s s')
    (hsvc : prog.svc = execSyscall := by first | rfl | simp [ProofLib.wp_norm, ProofLib.arm64_norm]) :
    ∃ d, s'.trace = s.trace ++ d :=
  h.trace_prefixWithSvc
    (fun t => hsvc ▸ (execSyscall_fsTraced (isFs := fun _ => True) (fun _ _ => trivial) t).elim
      fun d hd => ⟨d, hd.1⟩)
    hhooks

/-! ## Regular-File `MAX_LFS_FILESIZE` Invariant Across Steps -/

/-- Every regular file in `fs.files` has byte length `≤ MAX_LFS_FILESIZE` (`2^63 - 1`). -/
def FsState.FilesLeMaxLfs (fs : FsState) : Prop :=
  ∀ p bs, fs.files p = some (.file bs) → bs.length ≤ MAX_LFS_FILESIZE

namespace FsState.FilesLeMaxLfs

theorem of_files_eq {fs fs' : FsState} (h : fs.FilesLeMaxLfs) (heq : fs'.files = fs.files) :
    fs'.FilesLeMaxLfs :=
  fun p bs hp => h p bs (heq ▸ hp)

theorem setFd {fs : FsState} (h : fs.FilesLeMaxLfs) (fd : BitVec 64) (e : Option FdEntry) :
    (fs.setFd fd e).FilesLeMaxLfs :=
  h.of_files_eq rfl

theorem setEntry_file {fs : FsState} (h : fs.FilesLeMaxLfs)
    (segs : FsPath) {bs : List (BitVec 8)} (hle : bs.length ≤ MAX_LFS_FILESIZE) :
    (fs.setEntry segs (some (.file bs))).FilesLeMaxLfs := by
  intro q b hq
  have hq' : (if (normalizePath q).isEmpty then some .dir
              else if normalizePath q == segs then some (.file bs)
              else fs.entries (normalizePath q)) = some (.file b) := hq
  cases hne : (normalizePath q).isEmpty
  · cases heq : (normalizePath q == segs)
    · rw [hne, heq] at hq'
      apply h q b
      change (if (normalizePath q).isEmpty = true then some .dir else fs.entries (normalizePath q)) = some (.file b)
      rw [hne]; exact hq'
    · rw [hne, heq] at hq'
      cases hq'; exact hle
  · rw [hne] at hq'; cases hq'

theorem setFile_file {fs : FsState} (h : fs.FilesLeMaxLfs)
    (p : String) {bs : List (BitVec 8)} (hle : bs.length ≤ MAX_LFS_FILESIZE) :
    (fs.setFile p (some (.file bs))).FilesLeMaxLfs :=
  h.setEntry_file (normalizePath p) hle

end FsState.FilesLeMaxLfs

/-- Writing `chunk` at offset `pos` into `old` preserves `length ≤ MAX_LFS_FILESIZE`
    whenever `old.length ≤ MAX_LFS_FILESIZE` and `pos + chunk.length ≤ MAX_LFS_FILESIZE`. -/
theorem writeFileBytes_length_le_max_lfs {old chunk : List (BitVec 8)} {pos : Nat}
    (hold : old.length ≤ MAX_LFS_FILESIZE) (hpos : pos + chunk.length ≤ MAX_LFS_FILESIZE) :
    (writeFileBytes old pos chunk).length ≤ MAX_LFS_FILESIZE := by
  unfold writeFileBytes
  split <;> simp only [List.length_append, List.length_take, List.length_drop,
    List.length_replicate] <;> omega

private theorem openatPure_filesLeMaxLfs {s : State} (h : s.fs.FilesLeMaxLfs)
    (dfd : BitVec 32) (rawPath : String) (flags mode : BitVec 32) :
    (applyOpenVerdict s (openatPure s.fs dfd rawPath flags mode)).fs.FilesLeMaxLfs := by
  dsimp (config := { zetaHave := true }) only [openatPure]
  cases hchk : checkOpenFlags flags with
  | some v =>
    unfold checkOpenFlags at hchk
    (repeat' split at hchk) <;> cases hchk <;> exact h
  | none =>
    dsimp only
    generalize s.fs.allocFd = fd?
    (repeat' split) <;> dsimp only [applyOpenVerdict] <;> (repeat' split)
    all_goals first
      | exact h
      | exact (h.setEntry_file _ (Nat.zero_le _)).setFd _ _
      | exact h.of_files_eq (FsState.files_setEntry_of_eq ‹_›)

theorem execOpenat_filesLeMaxLfs {s : State} (h : s.fs.FilesLeMaxLfs) :
    (execOpenat s).fs.FilesLeMaxLfs := by
  dsimp (config := { zetaHave := true }) only [execOpenat]
  cases hchk : checkOpenFlags (s.readReg32 Reg.x2) with
  | some v =>
    unfold checkOpenFlags at hchk
    (repeat' split at hchk) <;> cases hchk <;> exact h
  | none =>
    cases readCString s.mem (s.readReg64 Reg.x1) with
    | trap _ => exact h
    | errno _ => exact h
    | ok rawPath => exact openatPure_filesLeMaxLfs h _ rawPath _ _

private theorem filesLeMaxLfs_ite {s₁ s₂ : State} {c : Prop} [Decidable c]
    (h₁ : c → s₁.fs.FilesLeMaxLfs) (h₂ : ¬c → s₂.fs.FilesLeMaxLfs) :
    (if c then s₁ else s₂).fs.FilesLeMaxLfs := by
  by_cases hc : c <;> simp [hc, h₁, h₂]

theorem execWrite_filesLeMaxLfs {s : State} (h : s.fs.FilesLeMaxLfs) :
    (execWrite s).fs.FilesLeMaxLfs := by
  dsimp (config := { zetaHave := true }) only [execWrite]
  repeat' (apply filesLeMaxLfs_ite <;> intro)
  any_goals exact h
  cases s.fs.fds (BitVec.zeroExtend 64 (s.readReg32 Reg.x0))
  · dsimp only; repeat' (apply filesLeMaxLfs_ite <;> intro)
    all_goals exact h
  · dsimp only; repeat' (apply filesLeMaxLfs_ite <;> intro)
    all_goals first
      | exact h
      | (refine (h.setFile_file _ (writeFileBytes_length_le_max_lfs ?_ ?_)).setFd _ _
         · dsimp only [FsState.fileBytes]; split <;> first | exact h _ _ ‹_› | exact Nat.zero_le _
         · have hle : ¬ s.fs.writePos _ + min (s.readReg64 Reg.x2).toNat MAX_RW_COUNT > MAX_LFS_FILESIZE := ‹_›
           simp only [Memory.readBytes_length] at *; omega)

private theorem filesLeMaxLfs_rwvFrame :
    ProofLib.RwvFrame (fun a b => a.fs.FilesLeMaxLfs → b.fs.FilesLeMaxLfs) where
  refl _ := id
  trans _ _ _ h1 h2 := h2 ∘ h1
  reg _ _ _ := id
  pc _ := id
  status _ _ := id
  regsPc _ _ _ := id

theorem execReadv_filesLeMaxLfs {s : State} (h : s.fs.FilesLeMaxLfs) :
    (execReadv s).fs.FilesLeMaxLfs :=
  ProofLib.execReadv_preserves filesLeMaxLfs_rwvFrame
    (fun s h => by
      obtain ⟨d, _, hf⟩ := fsTraced_execReadCommon (isFs := fun _ => False) s false
      exact h.of_files_eq (hf (fun _ _ hp => hp))) s h

theorem execWritev_filesLeMaxLfs {s : State} (h : s.fs.FilesLeMaxLfs) :
    (execWritev s).fs.FilesLeMaxLfs :=
  ProofLib.execWritev_preserves filesLeMaxLfs_rwvFrame (fun _ h => execWrite_filesLeMaxLfs h) s h

theorem execSyscall_filesLeMaxLfs {s : State} (h : s.fs.FilesLeMaxLfs) :
    (execSyscall s).fs.FilesLeMaxLfs := by
  have htab : ∀ p ∈ Syscall.standardTable, (p.2 s).fs.FilesLeMaxLfs := by
    simp only [Syscall.standardTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
      Syscall.pollTable, Syscall.allocTable, Syscall.signalsTable, Syscall.timeTable,
      Syscall.randomTable, Syscall.miscTable,
      List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · obtain ⟨d, _, hf⟩ := fsTraced_execReadCommon (isFs := fun _ => False) s false
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · exact execWrite_filesLeMaxLfs h
    · exact execReadv_filesLeMaxLfs h
    · exact execWritev_filesLeMaxLfs h
    · exact h
    · exact h
    · obtain ⟨d, _, hf⟩ := fsTraced_execFcntl (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execIoctl (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · exact execOpenat_filesLeMaxLfs h
    · obtain ⟨d, _, hf⟩ := fsTraced_execClose (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execLseek (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execReadCommon (isFs := fun _ => False) s true
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execFstat (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execPpoll (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execBrk (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execMunmap (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execMremap (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execMmap (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execMprotect (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execMadvise (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execTkill (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execTgkill (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execSigaltstack (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execRtSigaction (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execRtSigprocmask (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execClockGettime (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · obtain ⟨d, _, hf⟩ := fsTraced_execGetrandom (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · exact h
    · obtain ⟨d, _, hf⟩ := fsTraced_execSchedGetaffinity (isFs := fun _ => False) s
      exact h.of_files_eq (hf (fun _ _ hp => hp))
    · exact h
    · exact h
  unfold execSyscall Syscall.standard Syscall.dispatch
  split
  · rename_i nr fn hfind
    exact htab (nr, fn) (List.mem_of_find?_eq_some hfind)
  · exact h

/-- One step preserves `FsState.FilesLeMaxLfs` when every extern hook preserves it. -/
theorem Step.filesLeMaxLfs {prog : Program}
    (hhooks : ∀ pc f, prog.externAt? pc = some f → ∀ t, t.fs.FilesLeMaxLfs → (f t).fs.FilesLeMaxLfs)
    {s s' : State} (hstep : Step prog s s') (h : s.fs.FilesLeMaxLfs)
    (hsvc : prog.svc = execSyscall := by first | rfl | simp [ProofLib.wp_norm, ProofLib.arm64_norm]) :
    s'.fs.FilesLeMaxLfs := by
  cases hstep with
  | @exec inst _ _ =>
    by_cases his : inst = .system false 0#16
    · subst his
      change (prog.svc s).fs.FilesLeMaxLfs
      rw [hsvc]
      exact execSyscall_filesLeMaxLfs h
    · rw [evalInst_eq_execInst_of_ne_svc0 prog inst s his]
      exact h.of_files_eq (congrArg FsState.files (execInst_fs_of_ne_svc0 inst s his))
  | halt_unmapped _ _ _ => exact h
  | extern _ hext _ _ => exact hhooks _ _ hext s h
  | extern_fault _ _ _ => exact h

/-- Multi-step execution preserves `FsState.FilesLeMaxLfs` when every extern hook preserves it. -/
theorem Steps.filesLeMaxLfs {prog : Program}
    (hhooks : ∀ pc f, prog.externAt? pc = some f → ∀ t, t.fs.FilesLeMaxLfs → (f t).fs.FilesLeMaxLfs)
    {s s' : State} (hsteps : Steps prog s s') (h : s.fs.FilesLeMaxLfs)
    (hsvc : prog.svc = execSyscall := by first | rfl | simp [ProofLib.wp_norm, ProofLib.arm64_norm]) :
    s'.fs.FilesLeMaxLfs := by
  induction hsteps with
  | refl _ => exact h
  | step h1 _ ih => exact ih (h1.filesLeMaxLfs hhooks h hsvc)

section ApiCheck
private example {pred : TraceEvent → Prop}
    (hk : ∀ pc f, Program.pureMem.externAt? pc = some f → HookFsTraced pred f)
    {a b : State} (run : Steps Program.pureMem a b)
    (semOk : ∀ e, e.isFsChange = true → pred e) :
    ∃ d, b.trace = a.trace ++ d ∧ ((∀ e ∈ d, ¬ pred e) → b.fs.files = a.fs.files) :=
  run.files_eq_of_noFs (fun e he => semOk e he) hk

private example (ext : String → Option (State → State))
    (hk : ∀ pc f, ({ externs := ext } : Program).externAt? pc = some f → ∀ t, ∃ d, (f t).trace = t.trace ++ d)
    {a b : State} (run : Steps { externs := ext } a b) :
    ∃ d, b.trace = a.trace ++ d :=
  run.trace_prefix hk

private example (img : Obj.Image) (ext : String → Option (State → State))
    (hk : ∀ pc f, (Program.ofImage img ext).externAt? pc = some f → ∀ t, ∃ d, (f t).trace = t.trace ++ d)
    {a b : State} (run : Steps (Program.ofImage img ext) a b) :
    ∃ d, b.trace = a.trace ++ d :=
  run.trace_prefix hk
end ApiCheck

end Arm64
