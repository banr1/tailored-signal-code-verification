/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import Arm64.Trusted.Process

/-!
# Syscall Family Dispatch Equivalence and Bundle Regression Tests

Proves pointwise equivalence between table-driven `Syscall.standard` (`Syscall.dispatch
Syscall.standardTable`) and a reference 31-way `if`/`else if` dispatch, together with fail-closed
trap checks for minimal syscall bundles (`Syscall.stdioCli`, `Syscall.fileIo`, `Syscall.poll`,
`Syscall.alloc`).
-/

@[expose] public section

namespace Arm64.Testing.Regression.SyscallFamilies

open Arm64

/-- Reference 31-syscall `if`/`else if` dispatch corresponding to `Syscall.standard`. -/
def legacyExecSyscall (s : State) : State :=
  let nr := s.readReg64 Reg.x8
  if nr == SYS_IOCTL then execIoctl s
  else if nr == SYS_OPENAT then execOpenat s
  else if nr == SYS_CLOSE then execClose s
  else if nr == SYS_LSEEK then execLseek s
  else if nr == SYS_READ then execReadCommon s false
  else if nr == SYS_WRITE then execWrite s
  else if nr == SYS_READV then execReadv s
  else if nr == SYS_WRITEV then execWritev s
  else if nr == SYS_PREAD64 then execReadCommon s true
  else if nr == SYS_PPOLL then execPpoll s
  else if nr == SYS_FSTAT then execFstat s
  else if nr == SYS_CLOCK_GETTIME then execClockGettime s
  else if nr == SYS_BRK then execBrk s
  else if nr == SYS_MUNMAP then execMunmap s
  else if nr == SYS_MREMAP then execMremap s
  else if nr == SYS_MMAP then execMmap s
  else if nr == SYS_MPROTECT then execMprotect s
  else if nr == SYS_MADVISE then execMadvise s
  else if nr == SYS_GETRANDOM then execGetrandom s
  else if nr == SYS_EXIT || nr == SYS_EXIT_GROUP then
    s.setStatus (.Exited (s.readReg64 Reg.x0))
  else if nr == SYS_SET_TID_ADDRESS then execSetTidAddress s
  else if nr == SYS_SCHED_GETAFFINITY then execSchedGetaffinity s
  else if nr == SYS_FCNTL then execFcntl s
  else if nr == SYS_GETPID || nr == SYS_GETTID then execGetpid s
  else if nr == SYS_SIGALTSTACK then execSigaltstack s
  else if nr == SYS_RT_SIGPROCMASK then execRtSigprocmask s
  else if nr == SYS_RT_SIGACTION then execRtSigaction s
  else if nr == SYS_TKILL then execTkill s
  else if nr == SYS_TGKILL then execTgkill s
  else
    s.setStatus (.Exception "unmodeled syscall (svc)")

private theorem ne_beq_false {a b : BitVec 64} (h : a ≠ b) :
    (a == b) = false ∧ (b == a) = false :=
  ⟨beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h.symm⟩

private theorem dispatch_standard_eq_ite (s : State) (nr : BitVec 64)
    (f_readCommon : State → Bool → State)
    (f_write f_readv f_writev f_exit f_fcntl f_ioctl f_openat f_close f_lseek f_fstat f_ppoll
     f_brk f_munmap f_mremap f_mmap f_mprotect f_madvise f_tkill f_tgkill f_sigaltstack
     f_rtSigaction f_rtSigprocmask f_clockGettime f_getrandom
     f_setTidAddress f_schedGetaffinity f_getpid f_unmodeled : State → State) :
    (match
      ([(SYS_READ, fun s => f_readCommon s false), (SYS_WRITE, f_write),
        (SYS_READV, f_readv), (SYS_WRITEV, f_writev),
        (SYS_EXIT, f_exit), (SYS_EXIT_GROUP, f_exit)] ++
       [(SYS_FCNTL, f_fcntl), (SYS_IOCTL, f_ioctl), (SYS_OPENAT, f_openat), (SYS_CLOSE, f_close),
        (SYS_LSEEK, f_lseek), (SYS_PREAD64, fun s => f_readCommon s true), (SYS_FSTAT, f_fstat)] ++
       [(SYS_PPOLL, f_ppoll)] ++
       [(SYS_BRK, f_brk), (SYS_MUNMAP, f_munmap), (SYS_MREMAP, f_mremap), (SYS_MMAP, f_mmap),
        (SYS_MPROTECT, f_mprotect), (SYS_MADVISE, f_madvise)] ++
       [(SYS_TKILL, f_tkill), (SYS_TGKILL, f_tgkill), (SYS_SIGALTSTACK, f_sigaltstack),
        (SYS_RT_SIGACTION, f_rtSigaction), (SYS_RT_SIGPROCMASK, f_rtSigprocmask)] ++
       [(SYS_CLOCK_GETTIME, f_clockGettime)] ++
       [(SYS_GETRANDOM, f_getrandom)] ++
       [(SYS_SET_TID_ADDRESS, f_setTidAddress), (SYS_SCHED_GETAFFINITY, f_schedGetaffinity),
        (SYS_GETPID, f_getpid), (SYS_GETTID, f_getpid)]).find? (·.1 == nr) with
     | some (_, h) => h s
     | none        => f_unmodeled s) =
    (if nr == SYS_IOCTL then f_ioctl s
     else if nr == SYS_OPENAT then f_openat s
     else if nr == SYS_CLOSE then f_close s
     else if nr == SYS_LSEEK then f_lseek s
     else if nr == SYS_READ then f_readCommon s false
     else if nr == SYS_WRITE then f_write s
     else if nr == SYS_READV then f_readv s
     else if nr == SYS_WRITEV then f_writev s
     else if nr == SYS_PREAD64 then f_readCommon s true
     else if nr == SYS_PPOLL then f_ppoll s
     else if nr == SYS_FSTAT then f_fstat s
     else if nr == SYS_CLOCK_GETTIME then f_clockGettime s
     else if nr == SYS_BRK then f_brk s
     else if nr == SYS_MUNMAP then f_munmap s
     else if nr == SYS_MREMAP then f_mremap s
     else if nr == SYS_MMAP then f_mmap s
     else if nr == SYS_MPROTECT then f_mprotect s
     else if nr == SYS_MADVISE then f_madvise s
     else if nr == SYS_GETRANDOM then f_getrandom s
     else if nr == SYS_EXIT || nr == SYS_EXIT_GROUP then f_exit s
     else if nr == SYS_SET_TID_ADDRESS then f_setTidAddress s
     else if nr == SYS_SCHED_GETAFFINITY then f_schedGetaffinity s
     else if nr == SYS_FCNTL then f_fcntl s
     else if nr == SYS_GETPID || nr == SYS_GETTID then f_getpid s
     else if nr == SYS_SIGALTSTACK then f_sigaltstack s
     else if nr == SYS_RT_SIGPROCMASK then f_rtSigprocmask s
     else if nr == SYS_RT_SIGACTION then f_rtSigaction s
     else if nr == SYS_TKILL then f_tkill s
     else if nr == SYS_TGKILL then f_tgkill s
     else f_unmodeled s) := by
  by_cases h1 : nr = SYS_IOCTL
  · subst h1; rfl
  · by_cases h2 : nr = SYS_OPENAT
    · subst h2; rfl
    · by_cases h3 : nr = SYS_CLOSE
      · subst h3; rfl
      · by_cases h4 : nr = SYS_LSEEK
        · subst h4; rfl
        · by_cases h5 : nr = SYS_READ
          · subst h5; rfl
          · by_cases h6 : nr = SYS_WRITE
            · subst h6; rfl
            by_cases h6a : nr = SYS_READV
            · subst h6a; rfl
            · by_cases h6b : nr = SYS_WRITEV
              · subst h6b; rfl
              · by_cases h7 : nr = SYS_PREAD64
                · subst h7; rfl
                · by_cases h8 : nr = SYS_PPOLL
                  · subst h8; rfl
                  · by_cases h9 : nr = SYS_FSTAT
                    · subst h9; rfl
                    · by_cases h10 : nr = SYS_CLOCK_GETTIME
                      · subst h10; rfl
                      · by_cases h11 : nr = SYS_BRK
                        · subst h11; rfl
                        · by_cases h12 : nr = SYS_MUNMAP
                          · subst h12; rfl
                          · by_cases h12b : nr = SYS_MREMAP
                            · subst h12b; rfl
                            · by_cases h13 : nr = SYS_MMAP
                              · subst h13; rfl
                              · by_cases h14 : nr = SYS_MPROTECT
                                · subst h14; rfl
                                · by_cases h15 : nr = SYS_MADVISE
                                  · subst h15; rfl
                                  · by_cases h16 : nr = SYS_GETRANDOM
                                    · subst h16; rfl
                                    · by_cases h17 : nr = SYS_EXIT
                                      · subst h17; rfl
                                      · by_cases h18 : nr = SYS_EXIT_GROUP
                                        · subst h18; rfl
                                        · by_cases h19 : nr = SYS_SET_TID_ADDRESS
                                          · subst h19; rfl
                                          · by_cases h20 : nr = SYS_SCHED_GETAFFINITY
                                            · subst h20; rfl
                                            · by_cases h21 : nr = SYS_FCNTL
                                              · subst h21; rfl
                                              · by_cases h22 : nr = SYS_GETPID
                                                · subst h22; rfl
                                                · by_cases h23 : nr = SYS_GETTID
                                                  · subst h23; rfl
                                                  · by_cases h23b : nr = SYS_SIGALTSTACK
                                                    · subst h23b; rfl
                                                    · by_cases h24 : nr = SYS_RT_SIGPROCMASK
                                                      · subst h24; rfl
                                                      · by_cases h25 : nr = SYS_RT_SIGACTION
                                                        · subst h25; rfl
                                                        · by_cases h26 : nr = SYS_TKILL
                                                          · subst h26; rfl
                                                          · by_cases h27 : nr = SYS_TGKILL
                                                            · subst h27; rfl
                                                            · dsimp only [List.append_assoc,
                                                                List.cons_append, List.nil_append,
                                                                List.find?]
                                                              rw [(ne_beq_false h1).1, (ne_beq_false h1).2,
                                                                  (ne_beq_false h2).1, (ne_beq_false h2).2,
                                                                  (ne_beq_false h3).1, (ne_beq_false h3).2,
                                                                  (ne_beq_false h4).1, (ne_beq_false h4).2,
                                                                  (ne_beq_false h5).1, (ne_beq_false h5).2,
                                                                  (ne_beq_false h6).1, (ne_beq_false h6).2,
                                                                  (ne_beq_false h6a).1, (ne_beq_false h6a).2,
                                                                  (ne_beq_false h6b).1, (ne_beq_false h6b).2,
                                                                  (ne_beq_false h7).1, (ne_beq_false h7).2,
                                                                  (ne_beq_false h8).1, (ne_beq_false h8).2,
                                                                  (ne_beq_false h9).1, (ne_beq_false h9).2,
                                                                  (ne_beq_false h10).1, (ne_beq_false h10).2,
                                                                  (ne_beq_false h11).1, (ne_beq_false h11).2,
                                                                  (ne_beq_false h12).1, (ne_beq_false h12).2,
                                                                  (ne_beq_false h12b).1, (ne_beq_false h12b).2,
                                                                  (ne_beq_false h13).1, (ne_beq_false h13).2,
                                                                  (ne_beq_false h14).1, (ne_beq_false h14).2,
                                                                  (ne_beq_false h15).1, (ne_beq_false h15).2,
                                                                  (ne_beq_false h16).1, (ne_beq_false h16).2,
                                                                  (ne_beq_false h17).1, (ne_beq_false h17).2,
                                                                  (ne_beq_false h18).1, (ne_beq_false h18).2,
                                                                  (ne_beq_false h19).1, (ne_beq_false h19).2,
                                                                  (ne_beq_false h20).1, (ne_beq_false h20).2,
                                                                  (ne_beq_false h21).1, (ne_beq_false h21).2,
                                                                  (ne_beq_false h22).1, (ne_beq_false h22).2,
                                                                  (ne_beq_false h23).1, (ne_beq_false h23).2,
                                                                  (ne_beq_false h23b).1, (ne_beq_false h23b).2,
                                                                  (ne_beq_false h24).1, (ne_beq_false h24).2,
                                                                  (ne_beq_false h25).1, (ne_beq_false h25).2,
                                                                  (ne_beq_false h26).1, (ne_beq_false h26).2,
                                                                  (ne_beq_false h27).1, (ne_beq_false h27).2]
                                                              rfl

/-- `Syscall.standard` agrees on every `State` with the 31-way `legacyExecSyscall` dispatch. -/
theorem standard_eq_legacyExecSyscall (s : State) :
    Syscall.standard s = legacyExecSyscall s :=
  dispatch_standard_eq_ite s (s.readReg64 Reg.x8) execReadCommon execWrite execReadv execWritev execExit execFcntl
    execIoctl execOpenat execClose execLseek execFstat execPpoll execBrk execMunmap execMremap
    execMmap execMprotect execMadvise execTkill execTgkill execSigaltstack execRtSigaction
    execRtSigprocmask execClockGettime execGetrandom execSetTidAddress execSchedGetaffinity
    execGetpid (fun s => s.setStatus (.Exception "unmodeled syscall (svc)"))

theorem standard_eq_legacyExecSyscall_fun : Syscall.standard = legacyExecSyscall :=
  funext standard_eq_legacyExecSyscall

theorem execSyscall_eq_legacyExecSyscall (s : State) :
    execSyscall s = legacyExecSyscall s :=
  standard_eq_legacyExecSyscall s

/-- Linux AArch64 syscall numbers for `ppoll` (`73`), `brk` (`214`), `mremap` (`216`), and
    `mmap` (`222`). -/
theorem allocator_and_poll_nr_values :
    SYS_PPOLL = 73#64 ∧ SYS_BRK = 214#64 ∧ SYS_MREMAP = 216#64 ∧ SYS_MMAP = 222#64 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `Syscall.stdioCli` traps fail-closed on `__NR_mmap` (`222#64`). -/
theorem stdioCli_traps_mmap (s : State) (h : s.readReg64 Reg.x8 = 222#64) :
    Syscall.stdioCli s = s.setStatus (.Exception "unmodeled syscall (svc)") := by
  rw [show Syscall.stdioCli s = Syscall.dispatch Syscall.stdioTable s from rfl]
  simp [Syscall.stdioTable, Syscall.dispatch, List.find?, h,
    SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, SYS_EXIT, SYS_EXIT_GROUP]

/-- `Syscall.fileIo` traps fail-closed on `__NR_mmap` (`222#64`). -/
theorem fileIo_traps_mmap (s : State) (h : s.readReg64 Reg.x8 = 222#64) :
    Syscall.fileIo s = s.setStatus (.Exception "unmodeled syscall (svc)") := by
  rw [show Syscall.fileIo s = Syscall.dispatch Syscall.fileIoTable s from rfl]
  simp [Syscall.fileIoTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    Syscall.dispatch, List.find?, h, SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, SYS_EXIT, SYS_EXIT_GROUP,
    SYS_OPENAT, SYS_CLOSE, SYS_LSEEK, SYS_PREAD64,
    SYS_FSTAT, SYS_FCNTL, SYS_IOCTL]

theorem fileIo_traps_brk (s : State) (h : s.readReg64 Reg.x8 = 214#64) :
    Syscall.fileIo s = s.setStatus (.Exception "unmodeled syscall (svc)") := by
  rw [show Syscall.fileIo s = Syscall.dispatch Syscall.fileIoTable s from rfl]
  simp [Syscall.fileIoTable, Syscall.stdioTable, Syscall.fileIoOnlyTable,
    Syscall.dispatch, List.find?, h, SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV, SYS_EXIT, SYS_EXIT_GROUP,
    SYS_OPENAT, SYS_CLOSE, SYS_LSEEK, SYS_PREAD64,
    SYS_FSTAT, SYS_FCNTL, SYS_IOCTL]

/-- `Syscall.poll` dispatches `SYS_PPOLL` (`73#64`) to `execPpoll`. -/
theorem poll_dispatches_ppoll (s : State) (h : s.readReg64 Reg.x8 = SYS_PPOLL) :
    Syscall.poll s = execPpoll s := by
  rw [show Syscall.poll s = Syscall.dispatch Syscall.pollTable s from rfl]
  simp [Syscall.pollTable, Syscall.dispatch, h]

theorem poll_traps_mmap (s : State) (h : s.readReg64 Reg.x8 = 222#64) :
    Syscall.poll s = s.setStatus (.Exception "unmodeled syscall (svc)") := by
  rw [show Syscall.poll s = Syscall.dispatch Syscall.pollTable s from rfl]
  simp [Syscall.pollTable, Syscall.dispatch, List.find?, h, SYS_PPOLL]

/-- `Syscall.alloc` dispatches `SYS_MREMAP` (`216#64`) to `execMremap`. -/
theorem alloc_dispatches_mremap (s : State) (h : s.readReg64 Reg.x8 = SYS_MREMAP) :
    Syscall.alloc s = execMremap s := by
  rw [show Syscall.alloc s = Syscall.dispatch Syscall.allocTable s from rfl]
  simp [Syscall.allocTable, Syscall.dispatch, List.find?, h,
    SYS_BRK, SYS_MUNMAP, SYS_MREMAP]

theorem alloc_traps_openat (s : State) (h : s.readReg64 Reg.x8 = SYS_OPENAT) :
    Syscall.alloc s = s.setStatus (.Exception "unmodeled syscall (svc)") := by
  rw [show Syscall.alloc s = Syscall.dispatch Syscall.allocTable s from rfl]
  simp [Syscall.allocTable, Syscall.dispatch, List.find?, h,
    SYS_OPENAT, SYS_MMAP, SYS_MUNMAP, SYS_MREMAP, SYS_MPROTECT, SYS_MADVISE, SYS_BRK]

theorem alloc_traps_ppoll (s : State) (h : s.readReg64 Reg.x8 = SYS_PPOLL) :
    Syscall.alloc s = s.setStatus (.Exception "unmodeled syscall (svc)") := by
  rw [show Syscall.alloc s = Syscall.dispatch Syscall.allocTable s from rfl]
  simp [Syscall.allocTable, Syscall.dispatch, List.find?, h,
    SYS_PPOLL, SYS_MMAP, SYS_MUNMAP, SYS_MREMAP, SYS_MPROTECT, SYS_MADVISE, SYS_BRK]

end Arm64.Testing.Regression.SyscallFamilies
