# Linux AArch64 Syscall Families (`Arm64/Trusted/Syscalls/`)

This directory organizes the 31 modeled Linux AArch64 supervisor calls (`SVC #0`, dispatched on
`X8`) along the upstream `linux-7.3` kernel directory hierarchy (`Include/`, `Fs/`, `Mm/`,
`Kernel/`, `Drivers/`), paired with composable per-family dispatch bundles (`Stdio.lean`,
`FileIo.lean`, `Poll.lean`, `Alloc.lean`, `Signals.lean`, `Time.lean`, `Random.lean`, `Misc.lean`).

## Upstream Linux `7.3` Source Mapping

Every handler in `Arm64/Trusted/Syscalls/` is audited against the pinned upstream `linux-7.3`
kernel source tree (`./scripts/dev/fetch-campaign-sources.sh linux-kernel` -> `third_party/linux-7.3`)
using `tools/dev/linux-syscall-extract` and
`.agents/skills/review-linux-syscalls/SKILL.md`,
and differentially tested against `qemu-aarch64` in
[`Arm64/Testing/SyscallDiff/`](../../Testing/SyscallDiff/README.md).

| Subtree / Module | Upstream `linux-7.3` Source | Syscall numbers (`__NR_*`) | Key exports |
|---|---|---|---|
| [`Include/Errno.lean`](Include/Errno.lean) | `include/uapi/asm-generic/{errno-base,errno}.h` | — | `EPERM` (`1`) .. `ENAMETOOLONG` (`36`), `EFAULT_RET` (`-14`) |
| [`Include/Uapi.lean`](Include/Uapi.lean) | `arch/arm64/kernel/syscall.c`, `include/uapi/asm-generic/unistd.h`, `include/linux/fs.h` | — | `SIM_TID`, `USER_VA_LIMIT` (`2 ^ 48`, `[INTENTIONAL_SCOPE]`: 48-bit VA / 4 KiB `PAGE_SIZE`), `MAX_RW_COUNT` (`0x7ffff000 = INT_MAX & PAGE_MASK`, `[INTENTIONAL_SCOPE]`: assumes 4 KiB `PAGE_SIZE`; 16 KiB / 64 KiB kernels clamp at `0x7fffc000` / `0x7fff0000`), `leBytes32`, `leBytes64`, `Syscall.dispatch` |
| [`Fs/ReadWrite.lean`](Fs/ReadWrite.lean) | `fs/read_write.c` | `lseek` (`62`), `read` (`63`), `write` (`64`), `pread64` (`67`) | `FS_SAFE_MAX_FILESIZE`, `writeFileBytes`, `execReadCommon`, `execRead`, `execWrite`, `execLseek`, `execPread64` |
| [`Fs/ReadWritev.lean`](Fs/ReadWritev.lean) | `fs/read_write.c`, `lib/iov_iter.c`, `include/uapi/linux/uio.h` | `readv` (`65`), `writev` (`66`) | `UIO_MAXIOV`, `readIovecs`, `execIovLoop`, `execRwvCommon`, `execReadv`, `execWritev` (sequential `execRead`/`execWrite` per segment) |
| [`Fs/Open.lean`](Fs/Open.lean) | `fs/open.c`, `fs/namei.c`, `fs/libfs.c`, `include/uapi/linux/limits.h` | `openat` (`56`), `close` (`57`) | `PATH_MAX`, `NAME_MAX`, `AT_FDCWD_W32`, `O_*`, `O_CREAT_OWNER_RW_MASK`, `readCString`, `resolveCwdPath`, `ancestorWalkErrno?`, `strictAncestorWalkErrno?`, `execOpenat`, `execClose` |
| [`Fs/Stat.lean`](Fs/Stat.lean) | `fs/stat.c`, `include/uapi/asm-generic/stat.h` | `fstat` (`80`) | `encodeLinuxStat`, `execFstat` |
| [`Fs/Fcntl.lean`](Fs/Fcntl.lean) | `fs/fcntl.c` | `fcntl` (`25`) | `F_GETFD_W32`, `F_SETFD_W32`, `execFcntl` |
| [`Fs/Ioctl.lean`](Fs/Ioctl.lean) | `fs/ioctl.c` | `ioctl` (`29`) | `execIoctl` |
| [`Fs/Select.lean`](Fs/Select.lean) | `fs/select.c` | `ppoll` (`73`) | `POLLNVAL`, `evalPpollEntries`, `execPpoll` |
| [`Mm/Mmap.lean`](Mm/Mmap.lean) | `mm/mmap.c`, `mm/vma.c` | `brk` (`214`), `munmap` (`215`), `mmap` (`222`) | `PAGE_SIZE`, `USER_VA_LIMIT`, `pageAlignUp`, `MMAP_*`, `findMappedByte`, `findUnmappedArea`, `sanitizeMmapAddr`, `execMmap`, `execMunmap`, `execBrk` |
| [`Mm/Mprotect.lean`](Mm/Mprotect.lean) | `mm/mprotect.c` | `mprotect` (`226`) | `execMprotect` |
| [`Mm/Mremap.lean`](Mm/Mremap.lean) | `mm/mremap.c` | `mremap` (`216`) | `MREMAP_MAYMOVE`, `Memory.remapRw`, `execMremap` |
| [`Mm/Madvise.lean`](Mm/Madvise.lean) | `mm/madvise.c` | `madvise` (`233`) | `MADV_*`, `Memory.zeroNonFrozen`, `Memory.madvFreeNonFrozen`, `execMadvise` |
| [`Kernel/Exit.lean`](Kernel/Exit.lean) | `kernel/exit.c` | `exit` (`93`), `exit_group` (`94`) | `execExit` |
| [`Kernel/Signal.lean`](Kernel/Signal.lean) | `kernel/signal.c` | `tkill` (`130`), `tgkill` (`131`), `sigaltstack` (`132`), `rt_sigaction` (`134`), `rt_sigprocmask` (`135`) | `LINUX_SIG*`, `SIG_DFL`, `SIG_IGN`, `SIG_UNBLOCKABLE_MASK`, `UAPI_SA_FLAGS`, `SS_*`, `MINSIGSTKSZ`, `SigAction.toBytes`, `SigAltStack.*`, `execRtSigprocmask`, `execSigaltstack`, `execRtSigaction`, `execTkill`, `execTgkill` |
| [`Kernel/Sys.lean`](Kernel/Sys.lean) | `kernel/fork.c`, `kernel/sched/syscalls.c`, `kernel/sys.c` | `set_tid_address` (`96`), `sched_getaffinity` (`123`), `getpid` (`172`), `gettid` (`178`) | `SCHED_AFFINITY_MASK`, `execSetTidAddress`, `execGetpid`, `execSchedGetaffinity` |
| [`Kernel/Time.lean`](Kernel/Time.lean) | `kernel/time/posix-timers.c` | `clock_gettime` (`113`) | `encodeTimespec`, `execClockGettime` |
| [`Drivers/Random.lean`](Drivers/Random.lean) | `drivers/char/random.c` | `getrandom` (`278`) | `GRND_*`, `execGetrandom` (uses `MAX_RW_COUNT` from [`Include/Uapi.lean`](Include/Uapi.lean)) |

## Why per-family tables?

What a reader must trust for a Lean theorem is the transitive closure of constants reachable from
its **statement** (`Expr.getUsedConstants`). Because each bundle (`Syscall.stdioWrite`,
`Syscall.stdioCli`, `Syscall.fileIo`, `Syscall.poll`, `Syscall.alloc`, ...) constructs its
`Syscall.dispatch` table directly from that family's handlers rather than filtering
`Syscall.standard` at run time, a specification parameterized by `(svc := Syscall.stdioCli)` or
`(svc := noSyscalls)` has **zero** constants from `Arm64.Trusted.Syscalls.Alloc` (`execMmap`,
`execMunmap`, `execMremap`, `execMprotect`, `execMadvise`, `execBrk`) in its kernel dependency
closure.

CI enforces this invariant via `#trusted_closure` (`ProofLib/TrustedClosure.lean` and
`scripts/trusted-closure`).

## Family Bundle Modules

| Module | Syscall numbers (`__NR_*`) | Key exports & bundles |
|---|---|---|
| [`Common.lean`](Common.lean) | — | Re-exports [`Include/Errno.lean`](Include/Errno.lean) and [`Include/Uapi.lean`](Include/Uapi.lean) |
| [`Stdio.lean`](Stdio.lean) | `read` (`63`), `write` (`64`), `readv` (`65`), `writev` (`66`), `exit` (`93`), `exit_group` (`94`) | Re-exports [`Fs/ReadWrite.lean`](Fs/ReadWrite.lean), [`Fs/ReadWritev.lean`](Fs/ReadWritev.lean), and [`Kernel/Exit.lean`](Kernel/Exit.lean); defines `Syscall.stdioWrite`, `Syscall.stdioCli` |
| [`FileIo.lean`](FileIo.lean) | `fcntl` (`25`), `ioctl` (`29`), `openat` (`56`), `close` (`57`), `lseek` (`62`), `pread64` (`67`), `fstat` (`80`) | Re-exports `Fs/{ReadWrite,Open,Stat,Fcntl,Ioctl}.lean`; defines `Syscall.fileIo` (`stdioTable ++ fileIoOnlyTable`) |
| [`Poll.lean`](Poll.lean) | `ppoll` (`73`) | Re-exports [`Fs/Select.lean`](Fs/Select.lean); defines `Syscall.poll` |
| [`Alloc.lean`](Alloc.lean) | `brk` (`214`), `munmap` (`215`), `mremap` (`216`), `mmap` (`222`), `mprotect` (`226`), `madvise` (`233`) | Re-exports `Mm/{Mmap,Mprotect,Mremap,Madvise}.lean`; defines `Syscall.alloc` |
| [`Signals.lean`](Signals.lean) | `tkill` (`130`), `tgkill` (`131`), `sigaltstack` (`132`), `rt_sigaction` (`134`), `rt_sigprocmask` (`135`) | Re-exports [`Kernel/Signal.lean`](Kernel/Signal.lean); defines `Syscall.signals` |
| [`Time.lean`](Time.lean) | `clock_gettime` (`113`) | Re-exports [`Kernel/Time.lean`](Kernel/Time.lean); defines `Syscall.time` |
| [`Random.lean`](Random.lean) | `getrandom` (`278`) | Re-exports [`Drivers/Random.lean`](Drivers/Random.lean); defines `Syscall.random` |
| [`Misc.lean`](Misc.lean) | `set_tid_address` (`96`), `sched_getaffinity` (`123`), `getpid` (`172`), `gettid` (`178`) | Re-exports [`Kernel/Sys.lean`](Kernel/Sys.lean); defines `Syscall.misc` |
| [`../Syscalls.lean`](../Syscalls.lean) | All `31` modeled syscalls | `Syscall.none`, `Syscall.standardTable`, `Syscall.standard`, `execSyscall` |

## Statically Present but Unreachable Syscalls in Static Rust + musl Binaries

Static linking against Rust `std` and musl `libc.a` retains object files containing `svc #0`
sites whose surrounding code paths are unreachable on modeled single-threaded executions.
Unmodeled syscall numbers are intentionally omitted from `Syscall.standard` (and modeled handlers
restrict their domain) so that any unexpected dynamic reachability fails closed with `.Exception`
(e.g. `.Exception "unmodeled syscall (svc)"`) rather than silently approximating kernel behavior:

- **`futex` (`98`)**: linked via musl `__lock` / `__unlock` and `std::sync::Once` / `Parker`. In a
  single-threaded process (`__libc.threaded == 0`, no `clone`), uncontended atomic
  compare-and-swap fast paths succeed immediately without entering the kernel `FUTEX_WAIT` /
  `FUTEX_WAKE` slow path.
- **`tkill` (`130`) / `tgkill` (`131`) (outside `abort()`)**: `tkill` is linked via musl `raise` /
  `abort`. Normal execution paths compiled with `-Cpanic=immediate-abort` emit `brk` / `udf` traps
  on panic rather than calling `abort()`, and `execTkill` / `execTgkill` remain fail-closed outside
  `tid = 1, sig = SIGABRT`.
- **`rt_sigreturn` (`139`)**: linked as `__restore_rt` (`sa_restorer` trampoline referenced by
  `__libc_sigaction`). Because asynchronous signals are never delivered, hardware faults in
  `ISA/Eval.lean` fail closed with `.Exception` rather than invoking recorded `SIGSEGV` / `SIGBUS`
  handlers, and custom handlers for all other signals are rejected fail-closed by `execRtSigaction`,
  the kernel signal-frame return trampoline is never entered.
- **`dup` (`23`)**: linked only in `sanitize_standard_fds` / descriptor fallback helpers when
  `openat("/dev/null")` returns an unexpected descriptor `< 0` or `> 2`, or in unused `libc`
  helpers. When standard descriptors `0, 1, 2` are already open at `execve` (`ppoll` returns `0`),
  the fallback branch is never taken.
- **`getrlimit` (`163`) / `prlimit64` (`261`)**: linked only in optional stack-guard /
  descriptor-limit query helpers that are not called on standard `lang_start` startup without
  backtrace or thread spawning.
- **`sysinfo` (`179`)**: linked only in unused musl memory-query helpers not invoked by the
  allocator or startup path.
- **`newfstatat` (`79`)**: linked via path-based metadata helpers (`fs::metadata` / `stat`).
  Descriptor-based `fs::read` opens the file with `openat` (`56`) and queries its size via `fstat`
  (`80`) on the open file descriptor.
