/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process
public import ProofLib.Process
public import Arm64.Testing.Harness.TestCase
public import Arm64.Testing.Regression.Process

/-!
# Per-Syscall Linux `7.3` & QEMU Differential Test Suite (`Arm64.Testing.Regression.SyscallDiff`)

- **Layer / Role:** Untrusted differential & conformance test suite (`Lib::Testing`, `Role::Test`,
  outside the TCB).
- **Purpose & Key Exports:**
  1. `KNOWN_QEMU_USER_DEVIATIONS`: Explicit, structured table documenting all 12 cases where
     `qemu-aarch64` user-mode deviates from real Linux `7.3` (`QEMU-DEV-1` .. `QEMU-DEV-12`).
  2. `all_29_syscalls_boundary_conformance`: Kernel-checked (`by decide`) boundary conformance
     theorem exercising `Arm64.execSyscall` across all 29 modeled Linux AArch64 syscalls,
     specifically including the `linux-7.3` edge cases where `qemu-aarch64` user-mode deviates
     (`brk` VMA collision, `mremap` `new_size == 0 -> -EINVAL`, `madvise` unmapped `-ENOMEM`,
     `ppoll` `nfds > maxOpenFds -> -EINVAL`, `sched_getaffinity` `pid < 0 -> -ESRCH`,
     `pread64` `pos < 0 -> -EINVAL` before `fd`, and `sigaltstack` AArch64 `MINSIGSTKSZ = 5120`,
     `(sp, sp + size]` bounds, `SS_AUTODISARM`, and post-commit `uoss` `-EFAULT`).
  3. `checkSyscallProbeVsQemuIO` / `runSyscallDiffSuiteIO`: End-to-end differential execution of
     `Arm64/Testing/SyscallDiff/bin/syscall_probe.elf` across all 5 modes (`all`, `exit_one`,
     `tkill_abrt`, `tgkill_abrt`, and `record-json`) comparing `qemu-aarch64` against
     `runElfImageFastMmap` (`Arm64.execSyscall`) for identical exit status, signal, `stdout`,
     `stderr`, and post-run `"probe_file.bin"` contents.
- **When to run:** Executed automatically in `lake test` (`.lake/build/bin/unit_tests`) and
  standalone via `.lake/build/bin/unit_tests --syscall-diff`.
-/

@[expose] public section

namespace Testing.SyscallDiff

open Arm64 Arm64.Process ProofLib
open Testing.Harness (TestCase)
open Testing.Process (runElfImageFastMmap)

set_option maxRecDepth 100000

/-! ## 1. Structured `KNOWN_QEMU_USER_DEVIATIONS` Table (`qemu-aarch64` vs. `linux-7.3`) -/

/-- Structured entry documenting a known divergence between `qemu-aarch64` user-mode emulation
    (`linux-user/syscall.c` / `linux-user/mmap.c`) and real Linux `7.3` kernel semantics
    (`third_party/linux-7.3`). -/
structure QemuUserDeviation where
  id             : String
  syscallNr      : Nat
  syscallName    : String
  linux73Source  : String
  qemuBehavior   : String
  linux73AndLean : String
  probeHandling  : String
  deriving Repr, DecidableEq, Inhabited

/-- Complete catalog of known deviations between `qemu-aarch64` user-mode and Linux `7.3` across
    the 29 modeled AArch64 syscalls. -/
def KNOWN_QEMU_USER_DEVIATIONS : List QemuUserDeviation := [
  { id             := "QEMU-DEV-1"
    syscallNr      := 214
    syscallName    := "brk"
    linux73Source  := "mm/mmap.c:115 (SYSCALL_DEFINE1(brk)), mm/vma.c:2183 (check_brk_limits)"
    qemuBehavior   := "QEMU user-mode `target_brk` reserves a fixed guest brk segment and does not reject collisions with subsequent `mmap` VMAs on growth or unmap shrunk pages via `do_brk_munmap`."
    linux73AndLean := "Linux 7.3 `sys_brk` and `Arm64.execBrk` check `[oldPage, newPage)` for existing mappings (`find_vma_intersection` / `s.mem.canMap`), leave `brk` unchanged on collision, and unmap `[newPage, oldPage)` on shrink."
    probeHandling  := "Tested within the initial brk reserve in `syscall_probe.elf`; VMA collision rejection is kernel-checked directly against `Arm64.execSyscall` in `all_29_syscalls_boundary_conformance`." },
  { id             := "QEMU-DEV-2"
    syscallNr      := 123
    syscallName    := "sched_getaffinity"
    linux73Source  := "kernel/sched/syscalls.c:1278,1307 (SYSCALL_DEFINE3(sched_getaffinity) -> sched_getaffinity -> find_process_by_pid)"
    qemuBehavior   := "QEMU user-mode forwards `sched_getaffinity` to the host kernel, returning the host's `cpumask_size()` (e.g. 8, 16, or 128 bytes) and host active CPU bitmask."
    linux73AndLean := "`Arm64.execSchedGetaffinity` models a deterministic single-core 64-CPU mask (`ret = 8`, `mask = [1, 0, 0, 0, 0, 0, 0, 0]`) while matching Linux 7.3's `-EINVAL` (-22) on `cpusetsize < 8` / `cpusetsize % 8 != 0` and `-ESRCH` (-3) on `pid < 0`."
    probeHandling  := "`syscall_probe.elf` asserts `ret > 0 && ret % 8 == 0 && (mask & 1) != 0` and tests `len = 0` (`-EINVAL`), `len = 7` (`-EINVAL`), `pid = -1` (`-ESRCH`), and unmapped `user_mask_ptr` (`-EFAULT`); exact `ret = 8` and `pid = -1 -> -ESRCH` are kernel-checked in `all_29_syscalls_boundary_conformance`." },
  { id             := "QEMU-DEV-3"
    syscallNr      := 172
    syscallName    := "getpid / gettid / set_tid_address"
    linux73Source  := "kernel/sys.c:966 (getpid), kernel/sys.c:979 (gettid), kernel/fork.c:1866 (set_tid_address)"
    qemuBehavior   := "QEMU user-mode forwards `getpid`, `gettid`, and `set_tid_address` to the host Linux kernel, returning the host process's dynamic PID/TID (> 0)."
    linux73AndLean := "`Arm64.execGetpid` and `Arm64.execSetTidAddress` return `SIM_TID = 1` in the deterministic single-threaded process model."
    probeHandling  := "`syscall_probe.elf` checks self-consistency (`getpid() > 0 && getpid() == gettid() && set_tid_address(&tid_slot) == gettid()`) and uses the runtime `tid` in `tkill`/`tgkill`." },
  { id             := "QEMU-DEV-4"
    syscallNr      := 113
    syscallName    := "clock_gettime / getrandom"
    linux73Source  := "kernel/time/posix-timers.c:1150 (clock_gettime), drivers/char/random.c:1395 (getrandom)"
    qemuBehavior   := "QEMU user-mode reads the live host wall/monotonic clock and `/dev/urandom` entropy."
    linux73AndLean := "`Arm64.execClockGettime` and `Arm64.execGetrandom` draw from `State.oracle` (`Oracle.clockGettime` and `Oracle.getrandom`) while enforcing identical UAPI validation (`0 <= tv_nsec < 10^9`, flag masks, `-EFAULT`)."
    probeHandling  := "`syscall_probe.elf` asserts `0 <= tv_nsec < 1_000_000_000` and exact byte count `getrandom(buf, 16, 0) == 16` without printing raw nondeterministic timestamps or random bytes." },
  { id             := "QEMU-DEV-5"
    syscallNr      := 73
    syscallName    := "ppoll"
    linux73Source  := "fs/select.c:1109 (SYSCALL_DEFINE5(ppoll)), fs/select.c:1022 (do_sys_poll)"
    qemuBehavior   := "`do_sys_poll` compares `nfds` against the host process's `RLIMIT_NOFILE` (often 65536 or 1048576 on developer workstations rather than 1024)."
    linux73AndLean := "`Arm64.execPpoll` caps `nfds` at `FsState.maxOpenFds = 1024` (`nfds > 1024 -> -EINVAL`)."
    probeHandling  := "`syscall_probe.elf` probes `nfds = 0x7fff_ffff` (which exceeds both `maxOpenFds` and `MAX_STACK_ALLOC` / `RLIMIT_NOFILE`, returning `-EINVAL` on both); `nfds = 1025 -> -EINVAL` is kernel-checked in `all_29_syscalls_boundary_conformance`." },
  { id             := "QEMU-DEV-6"
    syscallNr      := 216
    syscallName    := "mremap"
    linux73Source  := "mm/mremap.c:1828 (check_mremap_params: `if (!new_len) return -EINVAL;`)"
    qemuBehavior   := "QEMU user-mode `target_mremap` returns `-ENOMEM` (-12) when `new_size == 0`."
    linux73AndLean := "Linux 7.3 `mm/mremap.c:1828` (`if (!new_len) return -EINVAL;`) and `Arm64.execMremap` return `-EINVAL` (-22) when `new_size == 0`."
    probeHandling  := "`mremap` `new_size == 0 -> -EINVAL` is kernel-checked directly against `Arm64.execSyscall` in `all_29_syscalls_boundary_conformance`." },
  { id             := "QEMU-DEV-7"
    syscallNr      := 233
    syscallName    := "madvise"
    linux73Source  := "mm/madvise.c:2003 (SYSCALL_DEFINE3(madvise) -> do_madvise)"
    qemuBehavior   := "QEMU user-mode `target_madvise` short-circuits `MADV_NORMAL` / `MADV_WILLNEED` to `0` without walking guest VMAs, returning `0` even on unmapped pages."
    linux73AndLean := "Linux 7.3 `do_madvise` and `Arm64.execMadvise` walk `[addr, addr + alignUp(len, 4096))` and return `-ENOMEM` (-12) if any page in the range is unmapped."
    probeHandling  := "`madvise` on an unmapped page (`-ENOMEM` = `-12`) is kernel-checked directly against `Arm64.execSyscall` in `all_29_syscalls_boundary_conformance`." },
  { id             := "QEMU-DEV-8"
    syscallNr      := 56
    syscallName    := "openat"
    linux73Source  := "fs/open.c:1254 (build_open_flags: `if ((flags & (O_DIRECTORY | O_CREAT)) == (O_DIRECTORY | O_CREAT)) return -EINVAL;`)"
    qemuBehavior   := "QEMU user-mode forwards `openat` to the host kernel; on pre-5.7 container host kernels, `O_CREAT | O_DIRECTORY` returns `-ENOTDIR` (-20) instead of `-EINVAL` (-22)."
    linux73AndLean := "Linux 7.3 `build_open_flags` (`fs/open.c:1254`) and `Arm64.execOpenat` (`Fs/Open.lean:182`) reject `O_CREAT | O_DIRECTORY` upfront with `-EINVAL` (-22)."
    probeHandling  := "`syscall_probe.elf` tests `O_RDONLY | O_DIRECTORY` on a regular file (`-ENOTDIR` = `-20` across all kernel versions); `O_CREAT | O_DIRECTORY -> -EINVAL` (-22) is kernel-checked in `all_29_syscalls_boundary_conformance`." },
  { id             := "QEMU-DEV-9"
    syscallNr      := 132
    syscallName    := "sigaltstack"
    linux73Source  := "kernel/signal.c:4458-4527 (do_sigaltstack), include/linux/sched/signal.h:591-608 (on_sig_stack), arch/arm64/include/uapi/asm/signal.h:23 (MINSIGSTKSZ = 5120)"
    qemuBehavior   := "QEMU user-mode `do_sigaltstack` (`linux-user/signal.c`) uses generic `TARGET_MINSIGSTKSZ = 2048` instead of AArch64 `5120`, checks `[sp, sp + size)` instead of full-descending `(sp, sp + size]`, rejects `SS_AUTODISARM` (`1 << 31`) with `-EINVAL`, and locks `uoss` upfront before validating `uss`."
    linux73AndLean := "Linux 7.3 `do_sigaltstack` and `Arm64.execSigaltstack` enforce AArch64 `MINSIGSTKSZ = 5120`, full-descending `(sp, sp + size]` (`sp - sas_sp - 1 < sas_size`), `SS_AUTODISARM`, and post-commit `copy_to_user(uoss, &oss)`."
    probeHandling  := "`syscall_probe.elf` tests `ss_size = 1024 -> -ENOMEM`, `ss_size = 8192 -> 0`, interior `on_sig_stack -> -EPERM`, `SS_DISABLE` with non-zero `ss_size`, invalid flags `-EINVAL`, and `-EFAULT`; `5119` vs `5120`, `(sp, sp + size]` endpoints, `SS_AUTODISARM`, and `uoss` commit order are kernel-checked in `all_29_syscalls_boundary_conformance` and differentially verified against the live host Linux kernel in `sigaltstack_and_map_stack_trace_matches_linux_kernel`." },
  { id             := "QEMU-DEV-10"
    syscallNr      := 134
    syscallName    := "rt_sigaction"
    linux73Source  := "kernel/signal.c:4401-4411 (do_sigaction: `act->sa.sa_flags &= UAPI_SA_FLAGS`; `sigdelsetmask(&act->sa.sa_mask, sigmask(SIGKILL) | sigmask(SIGSTOP))`)"
    qemuBehavior   := "QEMU user-mode `do_sigaction` (`linux-user/signal.c`) stores the guest `sa_flags` and `sa_mask` raw, so `oldact` reads back unknown flag bits and `SIGKILL` / `SIGSTOP` in `sa_mask`."
    linux73AndLean := "Linux 7.3 and `Arm64.execRtSigaction` mask `sa_flags` with `UAPI_SA_FLAGS` (`0xdc000807` on arm64) and drop `SIGKILL` / `SIGSTOP` from `sa_mask` before storing the action."
    probeHandling  := "Pinned by the focused case `rt_sigaction_flags_mask.elf` (`CaseGap.qemuDeviates`): the Lean model must match Linux and `qemu-aarch64` must still exit `1`." },
  { id             := "QEMU-DEV-11"
    syscallNr      := 66
    syscallName    := "writev"
    linux73Source  := "fs/read_write.c (do_writev: `CLASS(fd_pos, f)(fd)` returns `-EBADF` before `vfs_writev` / `import_iovec`)"
    qemuBehavior   := "QEMU user-mode `lock_iovec` returns early for `iovcnt == 0`, so `writev(99, NULL, 0)` returns `0` without looking up the fd."
    linux73AndLean := "Linux 7.3 and `Arm64.execWritev` return `-EBADF` (-9) for a bad fd even when `iovcnt == 0`."
    probeHandling  := "Pinned by the focused case `writev_cnt0_ebadf.elf` (`CaseGap.qemuDeviates`)." },
  { id             := "QEMU-DEV-12"
    syscallNr      := 278
    syscallName    := "getrandom"
    linux73Source  := "drivers/char/random.c (SYSCALL_DEFINE3(getrandom): flag check first, then `import_ubuf(ITER_DEST, ubuf, len)`; `access_ok(NULL, 0)` passes)"
    qemuBehavior   := "QEMU user-mode `lock_user(VERIFY_WRITE, buf, len)` runs before the flag check and rejects guest address `0` even for `len == 0`, returning `-EFAULT`."
    linux73AndLean := "Linux 7.3 and `Arm64.execGetrandom` return `0` for `getrandom(NULL, 0, 0)` and `-EINVAL` (-22) for invalid flags with a NULL buffer."
    probeHandling  := "Pinned by the focused cases `getrandom_zero_null.elf` and `getrandom_einval_null.elf` (`CaseGap.qemuDeviates`)." },
  { id             := "QEMU-DEV-13"
    syscallNr      := 63
    syscallName    := "read"
    linux73Source  := "fs/read_write.c + mm/filemap.c (`rw_verify_area` clamps `count` to `MAX_RW_COUNT`, and `filemap_read -> copy_page_to_iter` faults user pages lazily only for the `chunk.length` bytes actually copied; at EOF nothing is copied)"
    qemuBehavior   := "QEMU user-mode `lock_user(VERIFY_WRITE, buf, count, 0)` validates the entire requested `count` upfront, returning `-EFAULT` when `count` (including `count > MAX_RW_COUNT`) extends into unmapped memory past a shorter file or when `buf == NULL` at EOF."
    linux73AndLean := "Linux 7.3 and `Arm64.execReadCommon` clamp `count` to `MAX_RW_COUNT` (`0x7ffff000`) and check writability only on the `chunk.length` bytes transferred (`0` bytes at EOF), returning the short file contents and `0` at EOF."
    probeHandling  := "Pinned by the focused cases `read_short_unmapped.elf` and `read_max_rw_count.elf` (`CaseGap.qemuDeviates`)." }
]

/-! ## 2. Kernel-Checked Conformance Theorem Over All 29 Syscalls & `linux-7.3` Edge Cases -/

/-- Run a single `Arm64.execSyscall` call with syscall number `nr` in `x8` and up to 6 arguments
    in `x0..x5`. -/
def callSyscall (s : State) (nr : BitVec 64)
    (a0 : BitVec 64 := 0#64) (a1 : BitVec 64 := 0#64) (a2 : BitVec 64 := 0#64)
    (a3 : BitVec 64 := 0#64) (a4 : BitVec 64 := 0#64) (a5 : BitVec 64 := 0#64) : State :=
  execSyscall
    (((((((s.writeReg64 .x8 nr).writeReg64 .x0 a0).writeReg64 .x1 a1).writeReg64 .x2 a2).writeReg64
      .x3 a3).writeReg64 .x4 a4).writeReg64 .x5 a5)

/-- Helper: if `p (m.perm (addr + k)) = true` for all `k < n`, then `m.allPerm p addr n = true`. -/
private theorem allPerm_of_forall (m : Memory) (p : Option Perm → Bool) (addr : BitVec 64) :
    ∀ n : Nat, (∀ k : Nat, k < n → p (m.perm (addr + BitVec.ofNat 64 k)) = true) →
      m.allPerm p addr n = true
  | 0, _ => rfl
  | n + 1, h => by
    simp only [Memory.allPerm]
    have h0 : p (m.perm addr) = true := by simpa using h 0 (Nat.zero_lt_succ n)
    have ih : m.allPerm p (addr + 1#64) n = true :=
      allPerm_of_forall m p (addr + 1#64) n (fun k hk => by
        have hk' := h (k + 1) (Nat.succ_lt_succ hk)
        have hadd : addr + 1#64 + BitVec.ofNat 64 k = addr + BitVec.ofNat 64 (k + 1) := by bv_omega
        rwa [hadd])
    rw [h0, ih]; rfl

/-- Shared 256-byte scratch state at `0x2000_0000` with `brkStart = brk = 0x1000_0000`. -/
abbrev sScratchState : State :=
  let s0 : State := {
    pc           := 0x1000#64
    brkStart     := 0x1000_0000#64
    brk          := 0x1000_0000#64
    physMemAvail := 2 ^ 30
  }
  s0.setMem (s0.mem.mapZero 0x2000_0000#64 0x100)

private theorem sScratch_canMap_brk_grow :
    sScratchState.mem.canMap (BitVec.ofNat 64 0x1000_0000) (0x1000_1000 - 0x1000_0000 + BRK_GUARD_GAP) = true := by
  apply allPerm_of_forall
  intro k hk
  have hout : decide ((0x1000_0000#64 + BitVec.ofNat 64 k - 0x2000_0000#64).toNat < 0x100) = false := by
    rw [decide_eq_false_iff_not]; unfold BRK_GUARD_GAP PAGE_SIZE at hk; bv_omega
  dsimp only [sScratchState, State.setMem, Memory.perm, Memory.mapZero, Memory.empty, Option.mapped]
  simp only [hout, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rfl

private theorem execBrk_grow_ok_eq (s : State) (m : Memory) (addr : BitVec 64) (oldPage newPage : Nat)
    (hm : s.mem = m)
    (hx0 : s.readReg64 Reg.x0 = addr)
    (h1 : (addr == 0#64 || addr.ult s.brkStart) = false)
    (hold : Arm64.pageAlignUp s.brk.toNat = oldPage)
    (hnew : Arm64.pageAlignUp addr.toNat = newPage)
    (hlt : ¬(newPage ≤ oldPage))
    (hlim : decide (newPage + BRK_GUARD_GAP ≤ USER_VA_LIMIT) = true)
    (hcan : m.canMap (BitVec.ofNat 64 oldPage) (newPage - oldPage + BRK_GUARD_GAP) = true)
    (hphys : decide (newPage - oldPage ≤ s.physMemAvail) = true) :
    execBrk s =
      ((((s.setBrk addr).setMem (m.mapZero (BitVec.ofNat 64 oldPage) (newPage - oldPage))).setPhysMemAvail
        (s.physMemAvail - (newPage - oldPage))).writeReg64 Reg.x0 addr).advancePC := by
  unfold execBrk
  simp only [hm, hx0, h1, Bool.false_eq_true, ↓reduceIte, hold, hnew, hlt, hlim, hcan,
    hphys, Bool.not_true, Bool.or_self]

/-- Helper for `QEMU-DEV-1` (`brk` VMA collision, grow, and shrink) parameterized by `sBrkGrow`. -/
def checkBrkBoundaryAux (sScratch sBrkGrow : State) : Bool :=
  let sBrkObstacle := sScratch.setMem (sScratch.mem.mapZero 0x1000_0000#64 16)
  let sBrkCollide := callSyscall sBrkObstacle SYS_BRK 0x1000_0010#64
  let brkCollideOk := sBrkCollide.status == .Running && sBrkCollide.readReg64 .x0 == 0x1000_0000#64
  let sBrkShrink := callSyscall sBrkGrow SYS_BRK 0x1000_0000#64
  brkCollideOk &&
    sBrkGrow.readReg64 .x0 == 0x1000_0010#64 &&
    sBrkShrink.readReg64 .x0 == 0x1000_0000#64

/-- Helper for `QEMU-DEV-1` (`brk` VMA collision, grow, and shrink) factored out so its
    `1 MiB` `BRK_GUARD_GAP` check can be discharged symbolically in `all_29_syscalls_boundary_conformance`. -/
def checkBrkBoundary (sScratch : State) : Bool :=
  checkBrkBoundaryAux sScratch (callSyscall sScratch SYS_BRK 0x1000_0010#64)

private theorem checkBrkBoundary_eq_true : checkBrkBoundary sScratchState = true := by
  let sGrowIn : State :=
    (((((((sScratchState.writeReg64 .x8 SYS_BRK).writeReg64 .x0 0x1000_0010#64).writeReg64 .x1 0#64).writeReg64
      .x2 0#64).writeReg64 .x3 0#64).writeReg64 .x4 0#64).writeReg64 .x5 0#64)
  let sGrowVal : State :=
    ((((sGrowIn.setBrk 0x1000_0010#64).setMem (sScratchState.mem.mapZero (BitVec.ofNat 64 0x1000_0000) (0x1000_1000 - 0x1000_0000))).setPhysMemAvail
      (sGrowIn.physMemAvail - (0x1000_1000 - 0x1000_0000))).writeReg64 Reg.x0 0x1000_0010#64).advancePC
  have hGrow : callSyscall sScratchState SYS_BRK 0x1000_0010#64 = sGrowVal :=
    execBrk_grow_ok_eq sGrowIn sScratchState.mem 0x1000_0010#64 0x1000_0000 0x1000_1000
      rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) sScratch_canMap_brk_grow (by decide +kernel)
  exact (congrArg (checkBrkBoundaryAux sScratchState) hGrow).trans (by decide +kernel)

/-- Boolean check exercising boundary cases across the remaining 28 modeled syscalls in `Arm64.execSyscall`. -/
def checkOther28SyscallsBoundary : Bool :=
  let sScratch := sScratchState

  -- 2. QEMU-DEV-2: `sched_getaffinity` (123) exact 8-byte mask, 32-bit `cpusetsize` before `pid`, and `pid = -1 -> -ESRCH` (-3)
  let sAffNegPid := callSyscall sScratch SYS_SCHED_GETAFFINITY (-1#64) 8#64 0x2000_0000#64
  let sAffNegPidBadSz := callSyscall sScratch SYS_SCHED_GETAFFINITY (-1#64) 4#64 0x2000_0000#64
  let sAffLen32Wrap := callSyscall sScratch SYS_SCHED_GETAFFINITY 0#64 0x1_0000_0000#64 0x2000_0000#64
  let sAffOk := callSyscall sScratch SYS_SCHED_GETAFFINITY 0#64 8#64 0x2000_0000#64
  let affOk := sAffNegPid.readReg64 .x0 == -3#64 &&
    sAffNegPidBadSz.readReg64 .x0 == -22#64 &&
    sAffLen32Wrap.readReg64 .x0 == -22#64 &&
    sAffOk.readReg64 .x0 == 8#64 &&
    sAffOk.mem.read64 0x2000_0000#64 == 1#64

  -- 3. QEMU-DEV-3: `getpid` (172), `gettid` (178), `set_tid_address` (96) -> `SIM_TID = 1`
  let sPid := callSyscall sScratch SYS_GETPID
  let sTid := callSyscall sScratch SYS_GETTID
  let sSetTid := callSyscall sScratch SYS_SET_TID_ADDRESS 0x2000_0010#64
  let idsOk := sPid.readReg64 .x0 == 1#64 &&
    sTid.readReg64 .x0 == 1#64 &&
    sSetTid.readReg64 .x0 == 1#64

  -- 4. QEMU-DEV-4: `clock_gettime` (113) & `getrandom` (278)
  let sClkEfault := callSyscall sScratch SYS_CLOCK_GETTIME 0#64 0#64
  let sClkOk := callSyscall sScratch SYS_CLOCK_GETTIME 0#64 0x2000_0000#64
  let sRndBadFlags := callSyscall sScratch SYS_GETRANDOM 0x2000_0000#64 8#64 0x100#64
  let sRndExclFlags := callSyscall sScratch SYS_GETRANDOM 0x2000_0000#64 8#64 0x6#64
  let sRndOk := callSyscall sScratch SYS_GETRANDOM 0x2000_0000#64 8#64 0#64
  let clkRndOk := sClkEfault.readReg64 .x0 == -14#64 &&
    sClkOk.readReg64 .x0 == 0#64 &&
    sRndBadFlags.readReg64 .x0 == -22#64 &&
    sRndExclFlags.readReg64 .x0 == -22#64 &&
    sRndOk.readReg64 .x0 == 8#64

  -- 5. QEMU-DEV-5: `ppoll` (73) with `nfds = 1025 > FsState.maxOpenFds` -> `-EINVAL` (-22)
  -- Zero timespec is at `0x2000_0000`
  let sPpollBigNfds := callSyscall sScratch SYS_PPOLL 0x2000_0010#64 1025#64 0x2000_0000#64 0#64 8#64
  let sPpollZero := callSyscall sScratch SYS_PPOLL 0#64 0#64 0x2000_0000#64 0#64 8#64
  let ppollOk := sPpollBigNfds.readReg64 .x0 == -22#64 &&
    sPpollZero.readReg64 .x0 == 0#64

  -- 6. QEMU-DEV-6 & QEMU-DEV-7: `mmap` (222), `mprotect` (226), `madvise` (233), `mremap` (216), `munmap` (215)
  let sMmapZeroLen := callSyscall sScratch SYS_MMAP 0#64 0#64 3#64 0x22#64 (-1#64) 0#64
  -- QEMU-DEV-7: `madvise` on unmapped address `0x5000_0000` returns `-ENOMEM` (-12) in Linux 7.3 & Lean
  let sMadvUnmapped := callSyscall sScratch SYS_MADVISE 0x5000_0000#64 4096#64 0#64
  let sMadvZeroLen := callSyscall sScratch SYS_MADVISE 0x2000_0000#64 0#64 4#64 -- len == 0 -> 0
  let sMadvHugeUnmapped := callSyscall sScratch SYS_MADVISE 0x5000_0000#64 4096#64 14#64 -- MADV_HUGEPAGE on unmapped -> -ENOMEM (-12)
  let sMadvNohugeZeroLen := callSyscall sScratch SYS_MADVISE 0x2000_0000#64 0#64 15#64 -- MADV_NOHUGEPAGE len == 0 -> 0
  -- QEMU-DEV-6: `mremap` with `new_size == 0` returns `-EINVAL` (-22) in Linux 7.3 & Lean
  let sMremapZeroNew := callSyscall sScratch SYS_MREMAP 0x2000_0000#64 4096#64 0#64 1#64 0#64
  let sMremapUnmapped := callSyscall sScratch SYS_MREMAP 0x5000_0000#64 4096#64 8192#64 1#64 0#64
  let sMprotectZeroLen := callSyscall sScratch SYS_MPROTECT 0x2000_0000#64 0#64 0#64 -- len == 0 -> 0
  let sMunmapUnaligned := callSyscall sScratch SYS_MUNMAP 0x2000_0001#64 4096#64 -- unaligned -> -EINVAL (-22)
  let mmOk := sMmapZeroLen.readReg64 .x0 == -22#64 &&
    sMadvUnmapped.readReg64 .x0 == -12#64 &&
    sMadvZeroLen.readReg64 .x0 == 0#64 &&
    sMadvHugeUnmapped.readReg64 .x0 == -12#64 &&
    sMadvNohugeZeroLen.readReg64 .x0 == 0#64 &&
    sMremapZeroNew.readReg64 .x0 == -22#64 &&
    sMremapUnmapped.readReg64 .x0 == -14#64 &&
    sMprotectZeroLen.readReg64 .x0 == 0#64 &&
    sMunmapUnaligned.readReg64 .x0 == -22#64

  -- 7. VFS / FD family: `openat` (56), `fcntl` (25), `ioctl` (29), `write` (64), `lseek` (62),
  -- `pread64` (67), `read` (63), `fstat` (80), `close` (57)
  -- Write "f.txt\x00" at 0x2000_0020 and "HI!" at 0x2000_0030
  let sFsInit := sScratch.setMem
    ((sScratch.mem.writeBytes 0x2000_0020#64 (bytesOfString "f.txt" ++ [0#8])).writeBytes
      0x2000_0030#64 (bytesOfString "HI!"))
  -- O_CREAT (0x40) | O_DIRECTORY (0x4000) | O_RDWR (0x2) = 0x4042 -> -EINVAL (-22) in Linux 7.3
  let sOpenCreatDir := callSyscall sFsInit SYS_OPENAT (-100#64) 0x2000_0020#64 0x4042#64 0o644#64
  -- O_CREAT (0x40) | O_RDWR (0x2) = 0x42
  let sOpen := callSyscall sFsInit SYS_OPENAT (-100#64) 0x2000_0020#64 0x42#64 0o644#64
  let fd := sOpen.readReg64 .x0
  let sFcntl := callSyscall sOpen SYS_FCNTL fd 1#64 0#64 -- F_GETFD
  let sIoctl := callSyscall sOpen SYS_IOCTL fd 0x5401#64 0x2000_0040#64 -- TCGETS on regular file -> -ENOTTY (-25)
  let sWrite := callSyscall sOpen SYS_WRITE fd 0x2000_0030#64 3#64
  let sLseek := callSyscall sWrite SYS_LSEEK fd 0#64 0#64 -- SEEK_SET 0
  -- F-2: `pread64(-1, buf, 1, -1)` checks `pos < 0` (`-EINVAL = -22`) before `fd < 0` (`-EBADF = -9`)
  let sPreadNegFdNegPos := callSyscall sLseek SYS_PREAD64 (-1#64) 0x2000_0050#64 1#64 (-1#64)
  let sPreadNegFdZeroPos := callSyscall sLseek SYS_PREAD64 (-1#64) 0x2000_0050#64 1#64 0#64
  let sPread := callSyscall sLseek SYS_PREAD64 fd 0x2000_0050#64 2#64 1#64
  let sRead  := callSyscall sPread SYS_READ fd 0x2000_0060#64 3#64
  let sFstat := callSyscall sRead SYS_FSTAT fd 0x2000_0080#64
  let sClose := callSyscall sFstat SYS_CLOSE fd
  let fsOk := sOpenCreatDir.readReg64 .x0 == -22#64 &&
    fd == 3#64 &&
    sFcntl.readReg64 .x0 == 0#64 &&
    sIoctl.readReg64 .x0 == -25#64 &&
    sWrite.readReg64 .x0 == 3#64 &&
    sLseek.readReg64 .x0 == 0#64 &&
    sPreadNegFdNegPos.readReg64 .x0 == -22#64 &&
    sPreadNegFdZeroPos.readReg64 .x0 == -9#64 &&
    sPread.readReg64 .x0 == 2#64 &&
    sRead.readReg64 .x0 == 3#64 &&
    sFstat.readReg64 .x0 == 0#64 &&
    sClose.readReg64 .x0 == 0#64

  -- 8. Signals & exit family: `sigaltstack` (132), `rt_sigprocmask` (135), `rt_sigaction` (134),
  -- `tkill` (130), `tgkill` (131), `exit` (93), `exit_group` (94), plus `MAP_STACK` (`0x20022`)
  let sMmapStack := callSyscall ({ pc := 0x1000#64, physMemAvail := 2 ^ 30 } : State)
    SYS_MMAP 0#64 4096#64 3#64 0x20022#64 (-1#64) 0#64
  -- QEMU-DEV-9: `sigaltstack` (132) AArch64 `MINSIGSTKSZ = 5120`, `(sp, sp + size]` bounds,
  -- `SS_AUTODISARM`, and post-commit `uoss` `-EFAULT` (within `[0x2000_0000, 0x2000_0100)`)
  let sSasMem := sScratch.setMem
    ((((sScratch.mem.writeBytes 0x2000_0060#64
          (leBytes64 0x80000#64 ++ leBytes32 0#32 ++ leBytes32 0#32 ++ leBytes64 5119#64)).writeBytes
        0x2000_0080#64
          (leBytes64 0x80000#64 ++ leBytes32 0#32 ++ leBytes32 0xdeadbeef#32 ++ leBytes64 5120#64)).writeBytes
        0x2000_00a0#64
          (leBytes64 0x80000#64 ++ leBytes32 (SS_AUTODISARM ||| SS_DISABLE) ++ leBytes32 0#32 ++ leBytes64 16#64)).write64
        0x2000_00e0#64 0x400500#64)
  let sSas5119 := callSyscall sSasMem SYS_SIGALTSTACK 0x2000_0060#64 0#64
  let sSas5120 := callSyscall sSasMem SYS_SIGALTSTACK 0x2000_0080#64 0x2000_00c0#64
  let sSasAtLo := callSyscall { sSas5120 with sp := 0x80000#64 } SYS_SIGALTSTACK 0x2000_00a0#64 0#64
  let sSasAtHi := callSyscall { sSas5120 with sp := 0x80000#64 + 5120#64 } SYS_SIGALTSTACK 0x2000_00a0#64 0#64
  let sSasUossEf := callSyscall sSasMem SYS_SIGALTSTACK 0x2000_0080#64 0x5000_0000#64
  let sSigActSegv := callSyscall sSasMem SYS_RT_SIGACTION 11#64 0x2000_00e0#64 0#64 8#64
  let sSigActBus := callSyscall sSasMem SYS_RT_SIGACTION 7#64 0x2000_00e0#64 0#64 8#64
  let sSigMask := callSyscall sScratch SYS_RT_SIGPROCMASK 0#64 0#64 0x2000_0010#64 8#64
  let sSigActKill := callSyscall sScratch SYS_RT_SIGACTION 9#64 0x2000_0000#64 0#64 8#64 -- SIGKILL with non-null act -> -EINVAL (-22)
  let sTkillFatal := callSyscall sScratch SYS_TKILL 1#64 6#64 -- SIGABRT (6) -> .Signaled 6#7
  let sTgkillFatal := callSyscall sScratch SYS_TGKILL 1#64 1#64 6#64 -- SIGABRT (6) -> .Signaled 6#7
  let sExit := callSyscall sScratch SYS_EXIT 7#64
  let sExitGrp := callSyscall sScratch SYS_EXIT_GROUP 9#64
  let sigExitOk :=
    sMmapStack.status == .Running && sMmapStack.readReg64 .x0 == 0x10000#64 &&
    sSas5119.readReg64 .x0 == -12#64 &&
    sSas5120.readReg64 .x0 == 0#64 &&
    sSas5120.sigAltStack == { sp := 0x80000#64, size := 5120#64, ssFlags := 0#32 } &&
    sSas5120.mem.read32 0x2000_00c8#64 == SS_DISABLE &&
    sSas5120.mem.read32 0x2000_00cc#64 == 0#32 &&
    sSasAtLo.readReg64 .x0 == 0#64 &&
    sSasAtLo.sigAltStack == { sp := 0#64, size := 0#64, ssFlags := SS_AUTODISARM ||| SS_DISABLE } &&
    sSasAtHi.readReg64 .x0 == -1#64 &&
    sSasUossEf.readReg64 .x0 == -14#64 &&
    sSasUossEf.sigAltStack == { sp := 0x80000#64, size := 5120#64, ssFlags := 0#32 } &&
    sSigActSegv.readReg64 .x0 == 0#64 && (sSigActSegv.getSigAction 11#32).handler == 0x400500#64 &&
    sSigActBus.readReg64 .x0 == 0#64 && (sSigActBus.getSigAction 7#32).handler == 0x400500#64 &&
    sSigMask.readReg64 .x0 == 0#64 &&
    sSigActKill.readReg64 .x0 == -22#64 &&
    sTkillFatal.status == .Signaled 6#7 &&
    sTgkillFatal.status == .Signaled 6#7 &&
    sExit.status == .Exited 7#64 &&
    sExitGrp.status == .Exited 9#64

  affOk && idsOk && clkRndOk && ppollOk && mmOk && fsOk && sigExitOk

/-- Boolean check exercising boundary cases across all 29 modeled syscalls in `Arm64.execSyscall`,
    specifically including all `linux-7.3` edge cases where `qemu-aarch64` user-mode deviates
    (`QEMU-DEV-1` .. `QEMU-DEV-9`; `QEMU-DEV-10` .. `QEMU-DEV-12` are pinned by focused case
    binaries in `syscallCaseTable`). -/
def checkAll29SyscallsBoundary : Bool :=
  checkBrkBoundary sScratchState && checkOther28SyscallsBoundary

/-- Full page-aligned VM lifecycle check (`mmap(4096)`, `madvise(MADV_FREE)`, store + load,
    `madvise(MADV_DONTNEED)`, `mprotect`, and `munmap(4096)`), verified at elaboration time via
    `#guard` and at runtime in `unit_tests`. -/
def checkMmapPageLifecycle : Bool :=
  let s0 : State := { pc := 0x1000#64, physMemAvail := 2 ^ 30 }
  let sMmap := callSyscall s0 SYS_MMAP 0#64 4096#64 3#64 0x22#64 (-1#64) 0#64
  let mappedVa := sMmap.readReg64 .x0
  let sMadvFree := callSyscall sMmap SYS_MADVISE mappedVa 4096#64 8#64
  let sStore := sMadvFree.setMem (sMadvFree.mem.write64 mappedVa 0x55aa_55aa_55aa_55aa#64)
  let sMadvOk := callSyscall sStore SYS_MADVISE mappedVa 4096#64 4#64
  let sMprotectOk := callSyscall sMadvOk SYS_MPROTECT mappedVa 4096#64 0#64
  let sMunmapOk := callSyscall sMprotectOk SYS_MUNMAP mappedVa 4096#64
  mappedVa == 0x10000#64 &&
    sMadvFree.readReg64 .x0 == 0#64 &&
    sMadvFree.mem.isLazyFree mappedVa == true &&
    sStore.mem.isLazyFree mappedVa == false &&
    sStore.mem.canRead mappedVa 8 == true &&
    sMadvOk.readReg64 .x0 == 0#64 &&
    sMadvOk.mem.isLazyFree (mappedVa + 8#64) == false &&
    sMprotectOk.readReg64 .x0 == 0#64 &&
    sMunmapOk.readReg64 .x0 == 0#64 &&
    sMunmapOk.physMemAvail == 2 ^ 30 - 4096

#guard checkMmapPageLifecycle = true

/-- Kernel-checked boundary conformance theorem over all 29 modeled syscalls in `Arm64.execSyscall`. -/
theorem all_29_syscalls_boundary_conformance :
    checkAll29SyscallsBoundary = true := by
  unfold checkAll29SyscallsBoundary
  rw [checkBrkBoundary_eq_true, Bool.true_and]
  decide +kernel

/-! ## 3. Differential Execution of `syscall_probe.elf` (`qemu-aarch64` vs. `Arm64.execSyscall`) -/

/-- Path to the freestanding `#![no_std]` AArch64 syscall probe binary. -/
def syscallProbeElfPath : String :=
  "Arm64/Testing/SyscallDiff/bin/syscall_probe.elf"

/-- Run `elfPath` under `qemu-aarch64` inside a fresh temporary directory, returning
    `(exitCode, stdoutBytes, stderrBytes, watchedFileBytes?)`. -/
def runQemuProbeCase (elfPath : String) (args : List String) (watchFile : Option String) :
    IO (Option (Nat × List (BitVec 8) × List (BitVec 8) × Option (List (BitVec 8)))) := do
  let absElf ← IO.FS.realPath (← Testing.Harness.resolveRepoFilePath elfPath)
  let absFetch ← IO.FS.realPath (← Testing.Harness.resolveRepoFilePath "scripts/fetch-qemu-aarch64")
  let quotedArgs := String.intercalate " " ((absElf.toString :: args).map fun s => "\"" ++ s ++ "\"")
  let tmpDirRes ← IO.Process.output { cmd := "mktemp", args := #["-d"] }
  let tmpDir := tmpDirRes.stdout.trimAscii.toString
  if tmpDir.isEmpty then return none
  let outFile := tmpDir ++ "/__stdout.bin"
  let errFile := tmpDir ++ "/__stderr.bin"
  let closeInheritedFds :=
    "for fd in /proc/self/fd/*; do f=\"${fd##*/}\"; case \"$f\" in 0|1|2) ;; *) eval \"exec ${f}>&-\" 2>/dev/null || true ;; esac; done"
  let script :=
    s!"cd \"{tmpDir}\" && ulimit -c 0 && {closeInheritedFds} && " ++
    s!"QEMU=\"$(command -v qemu-aarch64 || \"{absFetch}\")\" && " ++
    s!"\"$QEMU\" {quotedArgs} </dev/null >\"{outFile}\" 2>\"{errFile}\"; printf '%u' \"$?\""
  let res ← IO.Process.output { cmd := "bash", args := #["-c", script] }
  let outP : System.FilePath := outFile
  let errP : System.FilePath := errFile
  let outBytes ← if ← outP.pathExists then IO.FS.readBinFile outP else pure ByteArray.empty
  let errBytes ← if ← errP.pathExists then IO.FS.readBinFile errP else pure ByteArray.empty
  let watchedBytes? ← match watchFile with
    | none => pure none
    | some rel =>
      let p : System.FilePath := tmpDir ++ "/" ++ rel
      if ← p.pathExists then
        let b ← IO.FS.readBinFile p
        pure (some (b.toList.map fun x => BitVec.ofNat 8 x.toNat))
      else
        pure none
  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", tmpDir] }
  match res.stdout.trimAscii.toString.toNat? with
  | some code =>
    return some (
      code,
      outBytes.toList.map (fun b => BitVec.ofNat 8 b.toNat),
      errBytes.toList.map (fun b => BitVec.ofNat 8 b.toNat),
      watchedBytes?)
  | none =>
    return none

/-- Build parallelizable work items for `Arm64/Testing/SyscallDiff/bin/syscall_probe.elf` across
    the boundary conformance suite and all 5 differential modes (`all`, `record-json`, `exit_one`,
    `tkill_abrt`, and `tgkill_abrt`) in deterministic order. -/
def buildSyscallProbeWorkItemsIO :
    IO (Array (Testing.Harness.ParallelWorkItem Testing.Harness.ParallelTestBatch)) := do
  let resolvedProbeElf ← Testing.Harness.resolveRepoFilePath syscallProbeElfPath
  if !(← resolvedProbeElf.pathExists) then
    let tcName := s!"SyscallDiff: differential qemu-aarch64 vs runElf on {syscallProbeElfPath}"
    return #[{
      label := tcName
      run   := fun () => pure
        { cases := [Testing.Harness.UnitTestCase.skipMissingFiles tcName [syscallProbeElfPath]] }
    }]
  let initBytes ← IO.FS.readBinFile resolvedProbeElf
  match ElfImage.parseByteArray initBytes with
  | .error err =>
    let tcName := s!"SyscallDiff: parse {syscallProbeElfPath} ({err})"
    return #[{
      label := tcName
      run   := fun () => pure { cases := [{ name := tcName, check := false }] }
    }]
  | .ok _ =>
    -- Parse `ElfImage` inside each worker task so `img` and `seg.perm` stay thread-local.
    let runLocalSim (maxSteps : Nat) (argv : List String) :
        IO (Except String (State × Option ProcessOutcome)) := do
      let b ← IO.FS.readBinFile resolvedProbeElf
      match fastParse (bytesOfByteArray b) with
      | .error err => return .error err
      | .ok img =>
        return runElfImageFastMmap maxSteps img { argv := argv.map bytesOfString }
    let expectedFileBytes := bytesOfString "ABCDEFGH"
    let expectedAllStderr := bytesOfString "syscall_probe:ok\n"
    let bytesToStr (bs : List (BitVec 8)) : String :=
      String.ofList (bs.map fun b => Char.ofNat b.toNat)
    let boundaryName :=
      "SyscallDiff: kernel-checked boundary conformance across all 29 modeled syscalls + KNOWN_QEMU_USER_DEVIATIONS (QEMU-DEV-1..13)"
    let allName :=
      "SyscallDiff: differential qemu-aarch64 vs runElf on syscall_probe.elf `all` (132 boundary probes across 29 syscalls + probe_file.bin)"
    let jsonName :=
      "SyscallDiff: differential qemu-aarch64 vs runElf on syscall_probe.elf `record-json` (ground-truth JSON vector mode)"
    let exitName :=
      "SyscallDiff: differential qemu-aarch64 vs runElf on syscall_probe.elf `exit_one` (SYS_exit(42) -> exit 42)"
    let tkillName :=
      "SyscallDiff: differential qemu-aarch64 vs runElf on syscall_probe.elf `tkill_abrt` (SYS_tkill(tid, SIGABRT) -> 134 / signal 6)"
    let tgkillName :=
      "SyscallDiff: differential qemu-aarch64 vs runElf on syscall_probe.elf `tgkill_abrt` (SYS_tgkill(pid, tid, SIGABRT) -> 134 / signal 6)"
    return #[
      { label    := boundaryName
        priority := 250
        run      := fun () => pure {
          cases := [{
            name  := boundaryName
            check := checkAll29SyscallsBoundary && checkMmapPageLifecycle &&
                     KNOWN_QEMU_USER_DEVIATIONS.length == 13
          }]
        } },
      { label    := allName
        priority := 600
        run      := fun () => do
          let qAll? ← runQemuProbeCase syscallProbeElfPath ["all"] (some "probe_file.bin")
          let sAll ← runLocalSim 200000 ["syscall_probe", "all"]
          let (allOk, errs) := match qAll?, sAll with
            | some (qCode, qOut, qErr, qFile?), .ok (_, some rAll) =>
              let ok :=
                qCode == 0 && qErr == expectedAllStderr && qFile? == some expectedFileBytes &&
                rAll.exitCode == 0#64 && rAll.signal == none &&
                rAll.stdout == qOut && rAll.stderr == qErr &&
                rAll.fileBytes? "probe_file.bin" == some expectedFileBytes
              if ok then (true, #[]) else Id.run do
                let mut es := #[s!"[SyscallDiff] all mismatch: qCode={qCode} rExit={rAll.exitCode} qErr={repr (bytesToStr qErr)}"]
                let qLines := (bytesToStr qOut).splitOn "\n"
                let rLines := (bytesToStr rAll.stdout).splitOn "\n"
                for (ql, rl) in qLines.zip rLines do
                  if ql != rl then
                    es := es.push s!"[SyscallDiff]   qemu: {ql} | lean: {rl}"
                (false, es)
            | _, _ =>
              (false, #["[SyscallDiff] all failed to run qemu or runElfImageFastMmap"])
          return { cases := [{ name := allName, check := allOk }], stderr := errs } },
      { label    := jsonName
        priority := 600
        run      := fun () => do
          let qJson? ← runQemuProbeCase syscallProbeElfPath ["record-json"] (some "probe_file.bin")
          let sJson ← runLocalSim 200000 ["syscall_probe", "record-json"]
          let (jsonOk, errs) := match qJson?, sJson with
            | some (qCode, qOut, qErr, qFile?), .ok (_, some rJson) =>
              let ok :=
                qCode == 0 && qErr == [] && qFile? == some expectedFileBytes &&
                rJson.exitCode == 0#64 && rJson.signal == none &&
                rJson.stdout == qOut && rJson.stderr == [] &&
                rJson.fileBytes? "probe_file.bin" == some expectedFileBytes
              if ok then (true, #[])
              else (false, #[s!"[SyscallDiff] record-json mismatch: qCode={qCode} rExit={rJson.exitCode}"])
            | _, _ =>
              (false, #["[SyscallDiff] record-json failed to run qemu or runElfImageFastMmap"])
          return { cases := [{ name := jsonName, check := jsonOk }], stderr := errs } },
      { label    := exitName
        priority := 250
        run      := fun () => do
          let qExit? ← runQemuProbeCase syscallProbeElfPath ["exit_one"] none
          let sExit ← runLocalSim 50000 ["syscall_probe", "exit_one"]
          let exitOk := match qExit?, sExit with
            | some (qCode, qOut, qErr, _), .ok (_, some rExit) =>
              qCode == 42 && qOut == [] && qErr == [] &&
              rExit.exitCode == 42#64 && rExit.signal == none &&
              rExit.stdout == [] && rExit.stderr == []
            | _, _ => false
          return { cases := [{ name := exitName, check := exitOk }] } },
      { label    := tkillName
        priority := 250
        run      := fun () => do
          let qTkill? ← runQemuProbeCase syscallProbeElfPath ["tkill_abrt"] none
          let sTkill ← runLocalSim 50000 ["syscall_probe", "tkill_abrt"]
          let tkillOk := match qTkill?, sTkill with
            | some (qCode, qOut, _, _), .ok (_, some rTkill) =>
              qCode == 134 && qOut == [] &&
              rTkill.exitCode == 134#64 && rTkill.signal == some 6 &&
              rTkill.stdout == [] && rTkill.stderr == []
            | _, _ => false
          return { cases := [{ name := tkillName, check := tkillOk }] } },
      { label    := tgkillName
        priority := 250
        run      := fun () => do
          let qTgkill? ← runQemuProbeCase syscallProbeElfPath ["tgkill_abrt"] none
          let sTgkill ← runLocalSim 50000 ["syscall_probe", "tgkill_abrt"]
          let tgkillOk := match qTgkill?, sTgkill with
            | some (qCode, qOut, _, _), .ok (_, some rTgkill) =>
              qCode == 134 && qOut == [] &&
              rTgkill.exitCode == 134#64 && rTgkill.signal == some 6 &&
              rTgkill.stdout == [] && rTgkill.stderr == []
            | _, _ => false
          return { cases := [{ name := tgkillName, check := tgkillOk }] } }
    ]

/-! ## 4. Focused Per-Behavior Case Binaries (`Arm64/Testing/SyscallDiff/bin/<case>.elf`)

Each case is one small freestanding static ELF built from `src/cases/<case>.c` (+ `sd_rt.h`) by
`scripts/syscall-diff-cases build`. A case issues raw `svc #0` calls, prints `label=<ret>` for each
call on `stdout`, records any mismatch against the Linux `7.3` result it expects on `stderr`, and
exits `1` on any mismatch (else `0`, or a case-chosen status / signal).

Every case runs under both `qemu-aarch64` (`-0 <case>`, empty `stdin` unless given, fresh empty
temporary working directory) and `runElfImageFastMmap` (`argv = [<case>, args...]`). The check
requires byte-for-byte identical `stdout` and `stderr` (`stderr` is skipped for signal deaths,
where `qemu-aarch64` prints its own diagnostic), identical exit status and signal, **and** the
exit status / signal recorded in the table. -/

/-- A documented divergence pinned by a case. The table's `exitCode` / `signal` / output is
    always the Linux `7.3` behavior that the case binary checks for. A gap case still runs under
    both `qemu-aarch64` and the Lean model, and it **fails** once the gap closes (for example,
    when the model is fixed). The table entry must then be moved back to a plain case, so a gap
    can never silently hide a change in either runner. -/
inductive CaseGap where
  /-- The Lean model fails closed: execution ends in a non-exit status (`.Exception msg` /
      `.OutOfMemory`) whose `repr` contains `needle`. `qemu-aarch64` matches the table, and
      Lean's `stdout` up to the trap is a prefix of QEMU's. -/
  | leanFailsClosed (needle : String) (note : String)
  /-- The Lean model returns a value that differs from Linux, and the case exits with status
      `leanExit` under Lean while `qemu-aarch64` matches the table. A model bug or documented
      model scope limit. -/
  | leanDiverges (leanExit : Nat) (note : String)
  /-- `qemu-aarch64` deviates from Linux `7.3` (`devId` in `KNOWN_QEMU_USER_DEVIATIONS`) and
      exits `qemuExit`, while the Lean model matches the table. -/
  | qemuDeviates (devId : String) (qemuExit : Nat)
  /-- `qemu-aarch64` and the Lean model agree byte for byte (the plain check), but both differ
      from Linux `7.3`. The table records the status both runners produce. -/
  | bothDifferFromLinux (note : String)
  deriving Repr

/-- One focused differential case binary. -/
structure SyscallCase where
  /-- Checked-in ELF path; always `Arm64/Testing/SyscallDiff/bin/<case>.elf`. -/
  elfPath : String
  /-- One-line description of the behavior exercised. -/
  desc : String
  /-- Extra `argv` entries after `argv[0] = <case>`. -/
  args : List String := []
  /-- Bytes on the guest's `stdin` (`fd 0`). -/
  stdin : String := ""
  /-- Expected exit status (`128 + sig` for a signal death, as reported by the shell). -/
  exitCode : Nat := 0
  /-- Expected fatal signal, if any. -/
  signal : Option Nat := none
  /-- Lean step budget. -/
  maxSteps : Nat := 200000
  /-- A documented divergence this case pins, if any (see `CaseGap`). -/
  gap : Option CaseGap := none

/-- `<case>` for `Arm64/Testing/SyscallDiff/bin/<case>.elf`. -/
def SyscallCase.name (c : SyscallCase) : String :=
  ((System.FilePath.mk c.elfPath).fileStem).getD c.elfPath

/-- Every focused case binary, grouped by syscall family. `syscallCaseTableMatchesSources`
    checks that this table lists exactly the `src/cases/*.c` sources. -/
def syscallCaseTable : List SyscallCase := [
  -- write (64)
  { elfPath := "Arm64/Testing/SyscallDiff/bin/write_ok.elf"
    desc := "write: stdout/stderr full, zero-length, and NULL zero-length writes" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/write_err.elf"
    desc := "write: EBADF (fd 99, fd -1) and EFAULT (NULL, unmapped, count 0 at kernel addr)" },
  -- exit (93) / exit_group (94), signals (129-135), getpid/gettid (172/178), set_tid_address (96), sched_getaffinity (123)
  { elfPath := "Arm64/Testing/SyscallDiff/bin/exit_group_after_output.elf"
    desc := "exit_group: status 3 after stdout and stderr output"
    exitCode := 3 },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/exit_255.elf"
    desc := "exit (SYS_exit, not exit_group): maximal 8-bit status 255, single-threaded"
    exitCode := 255 },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/tkill_einval.elf"
    desc := "tkill: tid <= 0 and sig outside [0, 64] return -EINVAL" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/tgkill_einval.elf"
    desc := "tgkill: tgid <= 0, tid <= 0, and sig outside [0, 64] return -EINVAL" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_signal_abrt_ignored.elf"
    desc := "rt_sigaction(SIGABRT, SIG_IGN) then tkill/tgkill(self, SIGABRT) are dropped, return 0" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/rt_sigaction_roundtrip.elf"
    desc := "rt_sigaction: SIGUSR1 SIG_DFL -> SIG_IGN -> SIG_DFL, old action read back via oldact" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/rt_sigaction_kernel_only.elf"
    desc := "rt_sigaction: setting SIGKILL/SIGSTOP -> -EINVAL; query with act = NULL succeeds" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/rt_sigaction_einval.elf"
    desc := "rt_sigaction: sigsetsize != 8 and signum outside [1, 64] -> -EINVAL, no change" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/rt_sigaction_efault.elf"
    desc := "rt_sigaction: unmapped act, and unmapped oldact on a query, return -EFAULT" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/rt_sigprocmask_query.elf"
    desc := "rt_sigprocmask: set = NULL queries the empty initial mask and ignores how" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/rt_sigprocmask_unblockable.elf"
    desc := "rt_sigprocmask: blocking SIGKILL/SIGSTOP succeeds but the mask read back stays empty" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/rt_sigprocmask_einval.elf"
    desc := "rt_sigprocmask: sigsetsize != 8 and invalid how (set != NULL) return -EINVAL" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/rt_sigprocmask_efault.elf"
    desc := "rt_sigprocmask: unmapped or wrapping (+8 > 2^64) set/oldset return -EFAULT" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/sigaltstack_query_default.elf"
    desc := "sigaltstack: uss = NULL reports the initial disabled stack (0, SS_DISABLE, 0)" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/sigaltstack_roundtrip.elf"
    desc := "sigaltstack: install 8192-byte stack, read back, replace with 16384, old one via uoss" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/sigaltstack_einval.elf"
    desc := "sigaltstack: ss_flags 3, 4, 1<<30 return -EINVAL and leave the stack disabled" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/sigaltstack_enomem.elf"
    desc := "sigaltstack: ss_size 0, 1024, 2047 (< MINSIGSTKSZ) return -ENOMEM, no change" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/sigaltstack_disable.elf"
    desc := "sigaltstack: SS_DISABLE ignores sp/size, clears the installed stack, returns old one" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/sigaltstack_efault.elf"
    desc := "sigaltstack: unmapped uss, and unmapped uoss on a query, return -EFAULT" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/getpid_gettid.elf"
    desc := "getpid/gettid: positive, stable across calls, equal in a single-threaded process" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/set_tid_address.elf"
    desc := "set_tid_address: returns gettid() for valid, NULL, unmapped tidptr; never writes it" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/sched_getaffinity_einval.elf"
    desc := "sched_getaffinity: len 0, 4, 7, 9 (too small / not a multiple of 8) return -EINVAL" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/sched_getaffinity_efault.elf"
    desc := "sched_getaffinity: unmapped or NULL user_mask_ptr with len 1024 returns -EFAULT" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/sched_getaffinity_esrch.elf"
    desc := "sched_getaffinity: pid -1 and INT_MIN with len 1024 return -ESRCH" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/sched_getaffinity_ok.elf"
    desc := "sched_getaffinity: non-empty mask, ret > 0 and % 8 == 0, bytes past ret untouched" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/exit_group_truncate.elf"
    desc := "exit_group: status 0x1ff is reported as 0x1ff & 0xff = 255"
    exitCode := 255
    gap := some (.leanDiverges 511 "exit status kept as full X0, not & 0xff (Exit.lean [INTENTIONAL_SCOPE])") },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/tkill_sig0.elf"
    desc := "tkill/tgkill(self, 0): signal 0 is an existence probe and returns 0"
    gap := some (.leanFailsClosed "unmodeled tkill" "tkill/tgkill sig 0 probe not modeled (Signal.lean)") },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/tkill_sigterm.elf"
    desc := "tkill(self, SIGTERM) with default disposition terminates the process by signal 15"
    exitCode := 143
    signal := some 15
    gap := some (.leanFailsClosed "unmodeled tkill" "only SIGABRT delivery is modeled (Signal.lean)") },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/tgkill_esrch.elf"
    desc := "tgkill with tgid not owning tid, and tkill of tid 0x7fffffff, return -ESRCH"
    gap := some (.leanFailsClosed "unmodeled tgkill" "ESRCH for foreign tgid/tid not modeled (Signal.lean)") },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_signal_usr1_ignored.elf"
    desc := "rt_sigaction(SIGUSR1, SIG_IGN) then tkill(self, SIGUSR1) is dropped and returns 0"
    gap := some (.leanFailsClosed "unmodeled tkill" "SIG_IGN only modeled for SIGABRT (Signal.lean)") },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/rt_sigprocmask_block_query.elf"
    desc := "rt_sigprocmask: SIG_BLOCK then SIG_UNBLOCK SIGUSR1; oldset reports the tracked mask"
    gap := some (.leanFailsClosed "unmodeled non-zero signal mask in rt_sigprocmask"
      "non-zero blocked signal masks are out of scope (Signal.lean execRtSigprocmask)") },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_signal_blocked_abrt.elf"
    desc := "blocked SIGABRT: tkill/tgkill queue pending SIGABRT without killing; SIG_IGN flushes; exit 0 while blocked"
    gap := some (.leanFailsClosed "unmodeled non-zero signal mask in rt_sigprocmask"
      "non-zero blocked signal masks are out of scope (Signal.lean execRtSigprocmask)") },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_signal_unblock_pending_abrt.elf"
    desc := "blocked SIGABRT queued by tkill terminates with signal 6 upon SIG_UNBLOCK"
    exitCode := 134
    signal := some 6
    gap := some (.leanFailsClosed "unmodeled non-zero signal mask in rt_sigprocmask"
      "non-zero blocked signal masks are out of scope (Signal.lean execRtSigprocmask)") },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/rt_sigaction_flags_mask.elf"
    desc := "rt_sigaction: sa_flags masked to UAPI_SA_FLAGS, SIGKILL/SIGSTOP dropped from sa_mask"
    gap := some (.qemuDeviates "QEMU-DEV-10" 1) },
  -- openat (56) / close (57) / read (63) / write (64) / lseek (62) / pread64 (67)
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_file_roundtrip.elf"
    desc := "openat/write/close/read: create, write, reopen O_RDONLY (reuses fd), read back, EOF" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/openat_excl.elf"
    desc := "openat: O_CREAT|O_EXCL creates once then EEXIST; O_EXCL without O_CREAT ignored" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/openat_enoent.elf"
    desc := "openat: ENOENT for missing file, missing parent dir (with/without O_CREAT), empty path" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/openat_enotdir.elf"
    desc := "openat: regular file used as dir (O_DIRECTORY, \"reg/\", \"reg/.\", \"reg/x\") -> ENOTDIR" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/openat_trailing_slash_creat.elf"
    desc := "openat: O_CREAT with trailing '/' -> EISDIR (missing name and existing file); nothing created" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/openat_efault.elf"
    desc := "openat: NULL / unmapped pathname -> EFAULT" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/openat_path_max.elf"
    desc := "openat: no NUL within PATH_MAX or len 4096 -> ENAMETOOLONG; 4095-byte path walked -> ENOENT" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/openat_trunc.elf"
    desc := "openat: open without O_TRUNC keeps contents; O_RDWR|O_TRUNC empties the file" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/openat_append.elf"
    desc := "openat: O_APPEND writes land at EOF even after lseek(0); offset ends at new size" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/openat_dir.elf"
    desc := "openat: \".\" O_RDONLY (+O_DIRECTORY) ok; read -> EISDIR, write -> EBADF, close -> 0" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/openat_dir_err.elf"
    desc := "openat: \".\" with WRONLY/RDWR/O_TRUNC/O_CREAT -> EISDIR, O_CREAT|O_EXCL -> EEXIST" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/openat_dot_paths.elf"
    desc := "openat: \"./f\", \".//f\" and \"f\" name the same file" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/close_ebadf.elf"
    desc := "close: EBADF for unopened fd 99, -1, 1023, INT_MAX" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_file_double_close.elf"
    desc := "close twice -> EBADF; read/write/lseek/pread64 on the closed fd -> EBADF" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/read_ebadf.elf"
    desc := "read: EBADF for unopened fd, -1, and O_WRONLY fd (also count 0)" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/write_rdonly.elf"
    desc := "write: O_RDONLY fd -> EBADF (also count 0); file unchanged" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/read_efault.elf"
    desc := "read: NULL / unmapped buffer on non-empty file -> EFAULT; offset not advanced" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/read_zero_len.elf"
    desc := "read: count 0 returns 0 (NULL/mapped buf, offset kept), EFAULT at kernel addr" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/read_max_rw_count.elf"
    desc := "read: count > MAX_RW_COUNT (0x80000000) clamps to 0x7ffff000 and reads 4-byte file (QEMU lock_user -> EFAULT)"
    gap := some (.qemuDeviates "QEMU-DEV-13" 1) },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/write_file_efault.elf"
    desc := "write: NULL / unmapped buffer to a file -> EFAULT; size and offset unchanged" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/write_zero_past_eof.elf"
    desc := "write: count 0 at offset past EOF returns 0 and does not extend the file" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/lseek_whence.elf"
    desc := "lseek: SEEK_SET/CUR/END incl. negative deltas and past-EOF; reads at new offsets" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/lseek_einval.elf"
    desc := "lseek: negative result (SET/CUR/END), SEEK_END overflow, bad whence -> EINVAL; offset kept" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/lseek_ebadf.elf"
    desc := "lseek: EBADF for unopened fd and -1 (EBADF before bad-whence check)" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_file_hole.elf"
    desc := "lseek past EOF then write creates a hole that reads back as zeros" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/pread64_offsets.elf"
    desc := "pread64: reads at middle/tail/EOF/2^40 and count 0 without moving the file offset" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/pread64_einval.elf"
    desc := "pread64: negative pos (-1, LLONG_MIN) on a valid fd -> EINVAL" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/pread64_ebadf.elf"
    desc := "pread64: EBADF (pos >= 0) for unopened fd, -1, and O_WRONLY fd" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/pread64_efault.elf"
    desc := "pread64: NULL / unmapped buffer at an offset with data -> EFAULT" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_file_fd_reuse.elf"
    desc := "openat: lowest free fd reused after close (single and two freed fds)" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_file_many_fds.elf"
    desc := "openat x64: distinct increasing fds; two freed mid fds reused lowest-first; all close" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_file_two_fds.elf"
    desc := "two fds on one file: independent offsets, shared contents" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/read_short_unmapped.elf"
    desc := "read: tail-unmapped buf copies file bytes (8 of 16); NULL buf at EOF -> 0"
    gap := some (.qemuDeviates "QEMU-DEV-13" 1) },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/write_short_unmapped.elf"
    desc := "write: buffer with unmapped tail -> short write (QEMU -> EFAULT; Lean fails closed)"
    exitCode := 1
    gap := some (.leanFailsClosed "unmodeled partial-fault short write"
      "Linux short-writes the readable prefix; QEMU lock_user returns -EFAULT and Lean fails closed on partial-fault short writes (Fs/ReadWrite.lean)") },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/openat_name_max.elf"
    desc := "openat: 255-byte name created; 256-byte -> ENAMETOOLONG; trailing '/' + O_CREAT -> EISDIR" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/openat_creat_mode_readonly.elf"
    desc := "openat: O_CREAT on missing file with mode 0444 (no owner write) creates file (model gap: traps)"
    gap := some (.leanFailsClosed "unmodeled non-owner-rw O_CREAT mode"
      "FsState does not track per-inode mode bits; creating a file without 0600 fails closed (Fs/Open.lean)") },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/openat_trunc_rdonly.elf"
    desc := "openat: O_RDONLY|O_TRUNC on writable file opens and truncates to 0" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/pread64_pos_overflow.elf"
    desc := "pread64: pos + count overflows loff_t -> EINVAL; count 0 at kernel addr -> EFAULT" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/lseek_seek_data_enxio.elf"
    desc := "lseek: SEEK_DATA/SEEK_HOLE past EOF (== i_size, > i_size) -> ENXIO" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/lseek_seek_data.elf"
    desc := "lseek: in-bounds SEEK_DATA/SEEK_HOLE on sparse file (model gap: traps)"
    gap := some (.leanFailsClosed "unmodeled SEEK_DATA/SEEK_HOLE in-bounds offset"
      "FsState stores flat byte sequences without sparse hole/extent metadata; in-bounds SEEK_DATA/SEEK_HOLE fails closed (Fs/ReadWrite.lean)") },
  -- readv/writev (65/66), fstat (80), fcntl (25), ioctl (29), ppoll (73), clock_gettime (113), getrandom (278)
  { elfPath := "Arm64/Testing/SyscallDiff/bin/writev_ok.elf"
    desc := "writev: multi-segment gather to stdout/stderr incl. NULL/zero-length segments" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/writev_zero.elf"
    desc := "writev: iovcnt = 0 (NULL/valid vector) and all-zero-length segments return 0" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/writev_einval.elf"
    desc := "writev: EINVAL for iovcnt 1025 > UIO_MAXIOV and negative (ssize_t) iov_len" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/writev_efault.elf"
    desc := "writev: EFAULT for NULL/unmapped iovec array and unmapped/NULL first segment base" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/writev_ebadf.elf"
    desc := "writev: EBADF for fd 99, -1, an O_RDONLY regular file, and a closed fd" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/writev_cnt0_ebadf.elf"
    desc := "writev: iovcnt = 0 on bad fd 99 is EBADF (QEMU returns 0: lock_iovec short-circuit)"
    gap := some (.qemuDeviates "QEMU-DEV-11" 1) },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/readv_file.elf"
    desc := "readv: exact-fit 3-segment scatter from a created file, offset advance, 0 at EOF" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/readv_short.elf"
    desc := "readv: short read from mid-file offset ends inside segment 1; later segments untouched" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/readv_stdin.elf"
    desc := "readv: scatter 11 stdin bytes over 5+1+16 segments, then 0 at EOF"
    stdin := "hello world" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/readv_ebadf.elf"
    desc := "readv: EBADF for fd 99/-1/O_WRONLY file; EISDIR for an O_DIRECTORY fd of \".\"" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/readv_err.elf"
    desc := "readv: EINVAL (iovcnt 1025, negative len) and EFAULT (NULL vec, unmapped/rodata segment)" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_iov_roundtrip.elf"
    desc := "writev/fstat/readv: gather 18 bytes into a file, st_size, scatter back with a new split" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/fstat_file.elf"
    desc := "fstat: S_IFREG/nlink/st_size of a created file across writes and sparse extend; dir S_IFDIR" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/fstat_err.elf"
    desc := "fstat: EBADF (99/-1/closed, wins over bad buf) and EFAULT (NULL/unmapped/rodata statbuf)" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/fcntl_cloexec.elf"
    desc := "fcntl: F_GETFD/F_SETFD FD_CLOEXEC round trip, only bit 0 honoured, O_CLOEXEC, dir fd" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/fcntl_ebadf.elf"
    desc := "fcntl: EBADF for F_GETFD/F_SETFD on fd 99, -1, 0x1_0000_0063 (fd 99), and a closed fd" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/fcntl_badcmd.elf"
    desc := "fcntl: unknown cmd 0x7fff on an open regular file returns EINVAL (model gap: traps)"
    gap := some (.leanFailsClosed "unmodeled fcntl cmd" "unknown fcntl cmd -> EINVAL not modeled (Fs/Fcntl.lean)") },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/ioctl_file.elf"
    desc := "ioctl: TCGETS/TIOCGWINSZ/TCSETS on a regular file return ENOTTY" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/ioctl_ebadf.elf"
    desc := "ioctl: TCGETS EBADF on fd 99, -1, and a closed fd" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/ioctl_fioclex.elf"
    desc := "ioctl: FIOCLEX/FIONCLEX on a regular file return 0 and toggle FD_CLOEXEC" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/ioctl_fionread.elf"
    desc := "ioctl: FIONREAD on a regular file returns 0 and stores i_size - f_pos" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/ioctl_fionbio.elf"
    desc := "ioctl: FIONBIO/FIOASYNC on a regular file return 0 (model gap: traps)"
    gap := some (.leanFailsClosed "unmodeled ioctl cmd" "FIONBIO/FIOASYNC not modeled; fail closed instead of -ENOTTY (Fs/Ioctl.lean)") },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/ppoll_stdio.elf"
    desc := "ppoll: zero timeout on fds 0/1/2 with events 0 clears revents; dup fd; nfds = 0" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/ppoll_einval.elf"
    desc := "ppoll: EINVAL for nsec >= 1e9, negative nsec/sec, and sigsetsize 4/16 with a mask" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/ppoll_efault.elf"
    desc := "ppoll: EFAULT for unmapped tsp, NULL/unmapped ufds, and read-only ufds (revents put_user)" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/clock_gettime_ok.elf"
    desc := "clock_gettime: clocks 0,1,4,5,6,7 return 0 with valid timespec; MONOTONIC non-decreasing" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/clock_gettime_efault.elf"
    desc := "clock_gettime: EFAULT for NULL, unmapped, and read-only tp" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/clock_gettime_einval.elf"
    desc := "clock_gettime: EINVAL for unregistered clock ids 10, 12, 64 (model gap: traps)"
    gap := some (.leanFailsClosed "unmodeled clock_gettime clockid" "clock ids > 7 trap instead of EINVAL (Kernel/Time.lean)") },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/getrandom_ok.elf"
    desc := "getrandom: full count for each valid flag set, upper flag bits ignored, unaligned len 7" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/getrandom_zero.elf"
    desc := "getrandom: zero length on a valid buffer returns 0 and writes nothing" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/getrandom_zero_null.elf"
    desc := "getrandom: zero length with NULL buf returns 0 (QEMU returns EFAULT)"
    gap := some (.qemuDeviates "QEMU-DEV-12" 1) },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/getrandom_einval.elf"
    desc := "getrandom: EINVAL for unknown flag bits and INSECURE|RANDOM, before the length check" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/getrandom_efault.elf"
    desc := "getrandom: EFAULT for NULL, unmapped, and read-only buffers" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/getrandom_einval_null.elf"
    desc := "getrandom: invalid flags win over NULL buf -> EINVAL (QEMU returns EFAULT)"
    gap := some (.qemuDeviates "QEMU-DEV-12" 1) },
  -- brk (214) / mmap (222) / munmap (215) / mprotect (226) / mremap (216) / madvise (233)
  { elfPath := "Arm64/Testing/SyscallDiff/bin/brk_query.elf"
    desc := "brk: brk(0), brk(below start_brk), brk(cur) all return the current break unchanged" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/brk_grow.elf"
    desc := "brk: grow by 4 pages returns new break; new heap pages read zero and are writable" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/brk_grow_unaligned.elf"
    desc := "brk: unaligned new break returned exactly; whole final page mapped, zeroed, writable" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_mm_brk_shrink_regrow.elf"
    desc := "brk: grow 4, shrink to 1, regrow to 3 pages: kept page keeps data, regrown pages read zero" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/mmap_anon_rw.elf"
    desc := "mmap: private anon RW is page-aligned, zero-filled, writable; munmap returns 0" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/mmap_len_zero.elf"
    desc := "mmap: len == 0 -> EINVAL for both PROT_READ|PROT_WRITE and PROT_NONE" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/mmap_len_unaligned.elf"
    desc := "mmap: unaligned len rounds up to pages; tail of last page zero and writable" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_mm_mmap_fixed_overlay.elf"
    desc := "mmap: MAP_FIXED over middle page returns addr, zeroes it, keeps neighbour pages" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/mmap_flags_stack.elf"
    desc := "mmap: MAP_PRIVATE|MAP_ANONYMOUS|MAP_STACK RW is page-aligned, zero-filled, writable" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/mmap_anon_fd_ignored.elf"
    desc := "mmap: MAP_ANONYMOUS ignores fd (unopened fd 99 still gives a zeroed RW mapping)" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/munmap_einval.elf"
    desc := "munmap: EINVAL on unaligned addr, len 0, len 2^62; mapping stays intact" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_mm_munmap_twice.elf"
    desc := "munmap: unmapping an already-unmapped range returns 0 again" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_mm_munmap_split.elf"
    desc := "munmap: middle page splits mapping; outer data kept, mprotect on hole -> ENOMEM" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_mm_mprotect_roundtrip.elf"
    desc := "mprotect: RW -> NONE -> RW on middle page of three preserves all page contents" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/mprotect_boundary.elf"
    desc := "mprotect: unaligned addr -> EINVAL; len 0 -> 0; unaligned len rounds up, data kept" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_mm_prot_none_then_rw.elf"
    desc := "mprotect: PROT_NONE mmap reservation then RW on 2 pages: zero-filled and writable" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_mm_mremap_grow.elf"
    desc := "mremap: MAYMOVE grow 1 -> 4 pages keeps contents; new tail zero and writable" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_mm_mremap_shrink.elf"
    desc := "mremap: MAYMOVE shrink 3 -> 1 page keeps first page contents (address not checked)" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/mremap_err.elf"
    desc := "mremap: unaligned old_address -> EINVAL; unmapped old range -> EFAULT" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/madvise_dontneed.elf"
    desc := "madvise: MADV_DONTNEED on private anon pages returns 0; they read back zero" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/madvise_boundary.elf"
    desc := "madvise: unaligned start -> EINVAL; len 0 -> 0; unaligned len rounds up (DONTNEED)" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/madvise_hints.elf"
    desc := "madvise: NORMAL/RANDOM/SEQUENTIAL/WILLNEED on mapped anon pages return 0, keep data" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/seq_mm_madvise_free.elf"
    desc := "madvise: MADV_FREE then store-before-load returns 0; stored bytes read back" },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/mremap_shrink_in_place.elf"
    desc := "mremap: MAYMOVE shrink 2 -> 1 page should return old_address (QEMU and Lean both move)"
    exitCode := 1
    gap := some (.bothDifferFromLinux "Linux shrinks in place; QEMU target_mremap and Lean execMremap ([INTENTIONAL_OVERAPPROX]) move") },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/mmap_prot_none_segv.elf"
    desc := "mmap: load from a PROT_NONE anon page kills the process with SIGSEGV"
    exitCode := 139
    signal := some 11
    gap := some (.leanFailsClosed "permission fault" "data abort is not delivered as a SIGSEGV death (fail-closed)") },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/mprotect_none_segv.elf"
    desc := "mprotect: store after RW -> PROT_NONE kills the process with SIGSEGV"
    exitCode := 139
    signal := some 11
    gap := some (.leanFailsClosed "permission fault" "data abort is not delivered as a SIGSEGV death (fail-closed)") },
  { elfPath := "Arm64/Testing/SyscallDiff/bin/mmap_len_huge.elf"
    desc := "mmap: len 2^62 (RW and PROT_NONE) returns -ENOMEM and the process continues"
    gap := some (.leanFailsClosed "OutOfMemory" "len > TASK_SIZE ends execution as OutOfMemory instead of -ENOMEM (Mm/Mmap.lean)") }
]

/-- Run case `c` under `qemu-aarch64` in a fresh empty working directory with `argv[0] = <case>`,
    returning `(exitStatus, stdout, stderr)`. -/
def runQemuSyscallCase (c : SyscallCase) :
    IO (Option (Nat × List (BitVec 8) × List (BitVec 8))) := do
  let absElf ← IO.FS.realPath (← Testing.Harness.resolveRepoFilePath c.elfPath)
  let absFetch ← IO.FS.realPath (← Testing.Harness.resolveRepoFilePath "scripts/fetch-qemu-aarch64")
  let quote (s : String) : String := "'" ++ s.replace "'" "'\\''" ++ "'"
  let quotedArgs := String.intercalate " " ((absElf.toString :: c.args).map quote)
  let tmpDirRes ← IO.Process.output { cmd := "mktemp", args := #["-d"] }
  let tmpDir := tmpDirRes.stdout.trimAscii.toString
  if tmpDir.isEmpty then return none
  let cwd := tmpDir ++ "/cwd"
  let inFile := tmpDir ++ "/stdin.bin"
  let outFile := tmpDir ++ "/stdout.bin"
  let errFile := tmpDir ++ "/stderr.bin"
  IO.FS.createDirAll cwd
  IO.FS.writeBinFile inFile c.stdin.toUTF8
  let closeInheritedFds :=
    "for fd in /proc/self/fd/*; do f=\"${fd##*/}\"; case \"$f\" in 0|1|2) ;; *) eval \"exec ${f}>&-\" 2>/dev/null || true ;; esac; done"
  let script :=
    s!"cd \"{cwd}\" && ulimit -c 0 && {closeInheritedFds} && " ++
    s!"QEMU=\"$(command -v qemu-aarch64 || \"{absFetch}\")\" && " ++
    s!"env -i \"$QEMU\" -0 {quote c.name} {quotedArgs} <\"{inFile}\" >\"{outFile}\" 2>\"{errFile}\"; " ++
    "printf '%u' \"$?\""
  let res ← IO.Process.output { cmd := "bash", args := #["-c", script] }
  let readBytes (p : String) : IO (List (BitVec 8)) := do
    let fp : System.FilePath := p
    if ← fp.pathExists then
      return (← IO.FS.readBinFile fp).toList.map fun b => BitVec.ofNat 8 b.toNat
    else
      return []
  let outBytes ← readBytes outFile
  let errBytes ← readBytes errFile
  let _ ← IO.Process.output { cmd := "rm", args := #["-rf", tmpDir] }
  return (res.stdout.trimAscii.toString.toNat?).map fun code => (code, outBytes, errBytes)

/-- The plain check: identical exit status, signal, `stdout` and (unless a signal death) `stderr`
    on both runners, all equal to the table. -/
def syscallCasePlainOk (c : SyscallCase) (qCode : Nat) (qOut qErr : List (BitVec 8))
    (r : ProcessOutcome) : Bool :=
  qCode == c.exitCode && r.exitCode == BitVec.ofNat 64 c.exitCode && r.signal == c.signal &&
    r.stdout == qOut && (c.signal.isSome || r.stderr == qErr)

/-- Verdict for one case given the QEMU result `(qCode, qOut, qErr)` and the Lean final status,
    `stdout` and outcome (`none` if Lean did not exit). A gap case passes only while its documented
    divergence is still present (see `CaseGap`). -/
def syscallCaseVerdict (c : SyscallCase) (qCode : Nat) (qOut qErr : List (BitVec 8))
    (status : ExecStatus) (leanOut : List (BitVec 8)) : Option ProcessOutcome → Bool
  | some r =>
    match c.gap with
    | none => syscallCasePlainOk c qCode qOut qErr r
    | some (.bothDifferFromLinux _) => syscallCasePlainOk c qCode qOut qErr r
    | some (.leanDiverges leanExit _) =>
      leanExit != c.exitCode && qCode == c.exitCode &&
        r.exitCode == BitVec.ofNat 64 leanExit && r.signal == none
    | some (.qemuDeviates _ qemuExit) =>
      qemuExit != c.exitCode && qCode == qemuExit &&
        r.exitCode == BitVec.ofNat 64 c.exitCode && r.signal == c.signal
    | some (.leanFailsClosed _ _) => false
  | none =>
    match c.gap with
    | some (.leanFailsClosed needle _) =>
      qCode == c.exitCode && ((toString (repr status)).splitOn needle).length > 1 &&
        leanOut.isPrefixOf qOut
    | _ => false

/-- Differential check of one focused case: `(ok, diagnostics)`. -/
def checkSyscallCaseIO (c : SyscallCase) : IO (Bool × Array String) := do
  let bytesToStr (bs : List (BitVec 8)) : String :=
    String.ofList (bs.map fun b => Char.ofNat b.toNat)
  let resolved ← Testing.Harness.resolveRepoFilePath c.elfPath
  unless ← resolved.pathExists do
    return (false, #[s!"[SyscallDiff] {c.name}: missing {c.elfPath}"])
  let q? ← runQemuSyscallCase c
  let b ← IO.FS.readBinFile resolved
  let sim : Except String (State × Option ProcessOutcome) :=
    match fastParse (bytesOfByteArray b) with
    | .error err => .error err
    | .ok img =>
      runElfImageFastMmap c.maxSteps img
        { argv := (c.name :: c.args).map bytesOfString, stdin := bytesOfString c.stdin }
  match q?, sim with
  | none, _ => return (false, #[s!"[SyscallDiff] {c.name}: failed to run qemu-aarch64"])
  | _, .error err => return (false, #[s!"[SyscallDiff] {c.name}: Lean run failed: {err}"])
  | some (qCode, qOut, qErr), .ok (s, r?) =>
    let leanOut : List (BitVec 8) :=
      (r?.map (·.stdout)).getD (ProcessOutcome.traceStreamBytes .stdout s.trace)
    let ok := syscallCaseVerdict c qCode qOut qErr s.status leanOut r?
    if ok then return (true, #[])
    let leanDesc := match r? with
      | some r => s!"exit={r.exitCode.toNat} signal={r.signal}"
      | none => s!"status {repr s.status} pc {s.pc}"
    let mut es := #[s!"[SyscallDiff] {c.name} mismatch (gap {repr c.gap}): qemu exit={qCode} lean {leanDesc} (want exit={c.exitCode} signal={c.signal})"]
    let qLines := (bytesToStr qOut).splitOn "\n"
    let rLines := (bytesToStr leanOut).splitOn "\n"
    for i in [0:Nat.max qLines.length rLines.length] do
      let ql := qLines.getD i "<none>"
      let rl := rLines.getD i "<none>"
      if ql != rl then
        es := es.push s!"[SyscallDiff]   qemu: {ql} | lean: {rl}"
    if let some r := r? then
      unless c.signal.isSome || r.stderr == qErr do
        es := es.push s!"[SyscallDiff]   stderr qemu: {repr (bytesToStr qErr)} | lean: {repr (bytesToStr r.stderr)}"
    return (false, es)

/-- `syscallCaseTable` lists exactly the case sources `src/cases/*.c` (no unlisted source, no
    listed binary without a source). -/
def syscallCaseTableMatchesSources : IO (Bool × Array String) := do
  let dir ← Testing.Harness.resolveRepoFilePath "Arm64/Testing/SyscallDiff/src/cases"
  let entries ← dir.readDir
  let srcNames := (entries.toList.filterMap fun e =>
    let p : System.FilePath := e.fileName
    if p.extension == some "c" then p.fileStem else none)
  let tableNames := syscallCaseTable.map (·.name)
  let missing := srcNames.filter (fun n => !tableNames.contains n)
  let extra := tableNames.filter (fun n => !srcNames.contains n)
  let pathsOk := syscallCaseTable.all fun c =>
    c.elfPath == s!"Arm64/Testing/SyscallDiff/bin/{c.name}.elf"
  let dupFree := tableNames.eraseDups.length == tableNames.length
  let ok := missing.isEmpty && extra.isEmpty && pathsOk && dupFree
  let es := if ok then #[] else
    #[s!"[SyscallDiff] case table drift: unlisted sources {missing}, sourceless entries {extra}, pathsOk={pathsOk}, dupFree={dupFree}"]
  return (ok, es)

/-- Work items for every case of `syscallCaseTable`, plus the table/source consistency check. -/
def buildSyscallCaseWorkItemsIO :
    IO (Array (Testing.Harness.ParallelWorkItem Testing.Harness.ParallelTestBatch)) := do
  let tableName := s!"SyscallDiff: syscallCaseTable lists exactly the {syscallCaseTable.length} src/cases/*.c case binaries"
  let mut items := #[{
    label := tableName
    priority := 250
    run := fun () => do
      let (ok, es) ← syscallCaseTableMatchesSources
      return { cases := [{ name := tableName, check := ok }], stderr := es } }]
  for c in syscallCaseTable do
    let nm := s!"SyscallDiff: case {c.name}.elf qemu-aarch64 vs runElf ({c.desc})"
    items := items.push {
      label := nm
      priority := 250
      run := fun () => do
        let missing ← Testing.Harness.missingTestFilesIO
          [← Testing.Harness.resolveRepoFilePath c.elfPath]
        if !missing.isEmpty then
          return { cases := [Testing.Harness.UnitTestCase.skipMissingFiles nm [c.elfPath]] }
        let (ok, es) ← checkSyscallCaseIO c
        return { cases := [{ name := nm, check := ok }], stderr := es } }
  return items

/-- All SyscallDiff work items: `syscall_probe.elf` modes plus the focused case binaries. -/
def buildSyscallDiffWorkItemsIO :
    IO (Array (Testing.Harness.ParallelWorkItem Testing.Harness.ParallelTestBatch)) := do
  return (← buildSyscallProbeWorkItemsIO) ++ (← buildSyscallCaseWorkItemsIO)

/-- Run `Arm64/Testing/SyscallDiff/bin/syscall_probe.elf` across all 5 modes (`all`, `exit_one`,
    `tkill_abrt`, `tgkill_abrt`, and `record-json`) on both `qemu-aarch64` and
    `runElfImageFastMmap` (`Arm64.execSyscall`), plus every focused case of `syscallCaseTable`,
    in parallel, returning individual `TestCase` outcomes. -/
def runSyscallDiffSuiteIO : IO (List TestCase) := do
  let items ← buildSyscallDiffWorkItemsIO
  Testing.Harness.runParallelTestBatchesIO items

/-- Boolean summary wrapper around `runSyscallDiffSuiteIO`. -/
def checkSyscallProbeVsQemuIO : IO Bool := do
  let cases ← runSyscallDiffSuiteIO
  return cases.all fun c => c.check || c.skipped?.isSome

end Testing.SyscallDiff
