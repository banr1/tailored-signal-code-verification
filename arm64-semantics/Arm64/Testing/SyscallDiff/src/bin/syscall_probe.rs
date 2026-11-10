// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `syscall_probe`: freestanding `#![no_std]` static AArch64 Linux `7.3` syscall differential probe
//! binary (`[TEST ONLY]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[TEST ONLY]` (guest AArch64 probe binary executed under both `qemu-aarch64`
//!   user mode, native AArch64 Linux `7.3`, and Lean's `Arm64.execSyscall` whole-ELF runner).
//! - **Purpose:** Exercises positive and negative boundary cases across all 29 modeled AArch64
//!   system calls in `Arm64/Trusted/Syscalls/`:
//!   - Mode `"all"` (default): runs 27 syscall probe groups and exits via `exit_group(0)` (`94`).
//!   - Mode `"exit_one"`: exits via `exit(42)` (`93`).
//!   - Mode `"tkill_abrt"`: sends fatal `SIGABRT` (`6`) to self via `tkill(gettid(), 6)` (`130`).
//!   - Mode `"tgkill_abrt"`: sends fatal `SIGABRT` (`6`) to self via `tgkill(getpid(), gettid(), 6)` (`131`).
//!   - Mode `"record-json"`: standalone native AArch64 Linux runner mode emitting a self-contained
//!     JSON ground-truth vector to `stdout`.

#![no_std]
#![no_main]

use core::arch::{asm, global_asm};
use core::panic::PanicInfo;

// All 29 modeled AArch64 LP64 syscall numbers (`include/uapi/asm-generic/unistd.h`).
const SYS_FCNTL: usize = 25;
const SYS_IOCTL: usize = 29;
const SYS_OPENAT: usize = 56;
const SYS_CLOSE: usize = 57;
const SYS_LSEEK: usize = 62;
const SYS_READ: usize = 63;
const SYS_WRITE: usize = 64;
const SYS_PREAD64: usize = 67;
const SYS_PPOLL: usize = 73;
const SYS_FSTAT: usize = 80;
const SYS_EXIT: usize = 93;
const SYS_EXIT_GROUP: usize = 94;
const SYS_SET_TID_ADDRESS: usize = 96;
const SYS_CLOCK_GETTIME: usize = 113;
const SYS_SCHED_GETAFFINITY: usize = 123;
const SYS_TKILL: usize = 130;
const SYS_TGKILL: usize = 131;
const SYS_SIGALTSTACK: usize = 132;
const SYS_RT_SIGACTION: usize = 134;
const SYS_RT_SIGPROCMASK: usize = 135;
const SYS_GETPID: usize = 172;
const SYS_GETTID: usize = 178;
const SYS_BRK: usize = 214;
const SYS_MUNMAP: usize = 215;
const SYS_MREMAP: usize = 216;
const SYS_MMAP: usize = 222;
const SYS_MPROTECT: usize = 226;
const SYS_MADVISE: usize = 233;
const SYS_GETRANDOM: usize = 278;

// UAPI constants (`arch/arm64/include/uapi/asm/fcntl.h`, `include/uapi/asm-generic/*`).
const AT_FDCWD: isize = -100;
const O_RDONLY: usize = 0;
const O_RDWR: usize = 2;
const O_CREAT: usize = 0x40;
const O_EXCL: usize = 0x80;
const O_TRUNC: usize = 0x200;
const O_DIRECTORY: usize = 0x4000; // AArch64-specific override (`1 << 14`)
const O_CLOEXEC: usize = 0x80000;
const F_GETFD: usize = 1;
const F_SETFD: usize = 2;
const FD_CLOEXEC: usize = 1;

const PROT_NONE: usize = 0x0;
const PROT_RW: usize = 0x3;
const MAP_PRIV_ANON: usize = 0x22;
const MAP_PRIV_ANON_FIXED: usize = 0x32;
const MAP_PRIV_ANON_STACK: usize = 0x20022;
const MREMAP_MAYMOVE: usize = 1;
const MADV_NORMAL: usize = 0;
const MADV_WILLNEED: usize = 3;
const MADV_DONTNEED: usize = 4;
const MADV_FREE: usize = 8;

const SIGABRT: usize = 6;
const SIGBUS: usize = 7;
const SIGKILL: usize = 9;
const SIGSEGV: usize = 11;
const SIG_DFL: u64 = 0;
const SIG_IGN: u64 = 1;
const SS_ONSTACK: i32 = 1;
const SS_DISABLE: i32 = 2;
const GRND_NONBLOCK: usize = 0x1;
const GRND_RANDOM: usize = 0x2;
const GRND_INSECURE: usize = 0x4;

global_asm!(
    ".global _start",
    "_start:",
    "mov x0, sp",
    "bl rust_entry",
    "brk #0",
);

#[inline(always)]
unsafe fn sys0(nr: usize) -> isize {
    let ret: isize;
    unsafe {
        asm!("svc #0", in("x8") nr, lateout("x0") ret, options(nostack));
    }
    ret
}

#[inline(always)]
unsafe fn sys1(nr: usize, a0: usize) -> isize {
    let ret: isize;
    unsafe {
        asm!("svc #0", in("x8") nr, inout("x0") a0 => ret, options(nostack));
    }
    ret
}

#[inline(always)]
unsafe fn sys2(nr: usize, a0: usize, a1: usize) -> isize {
    let ret: isize;
    unsafe {
        asm!(
            "svc #0",
            in("x8") nr,
            inout("x0") a0 => ret,
            in("x1") a1,
            options(nostack)
        );
    }
    ret
}

#[inline(always)]
unsafe fn sys3(nr: usize, a0: usize, a1: usize, a2: usize) -> isize {
    let ret: isize;
    unsafe {
        asm!(
            "svc #0",
            in("x8") nr,
            inout("x0") a0 => ret,
            in("x1") a1,
            in("x2") a2,
            options(nostack)
        );
    }
    ret
}

#[inline(always)]
unsafe fn sys4(nr: usize, a0: usize, a1: usize, a2: usize, a3: usize) -> isize {
    let ret: isize;
    unsafe {
        asm!(
            "svc #0",
            in("x8") nr,
            inout("x0") a0 => ret,
            in("x1") a1,
            in("x2") a2,
            in("x3") a3,
            options(nostack)
        );
    }
    ret
}

#[inline(always)]
unsafe fn sys5(nr: usize, a0: usize, a1: usize, a2: usize, a3: usize, a4: usize) -> isize {
    let ret: isize;
    unsafe {
        asm!(
            "svc #0",
            in("x8") nr,
            inout("x0") a0 => ret,
            in("x1") a1,
            in("x2") a2,
            in("x3") a3,
            in("x4") a4,
            options(nostack)
        );
    }
    ret
}

#[inline(always)]
unsafe fn sys6(
    nr: usize,
    a0: usize,
    a1: usize,
    a2: usize,
    a3: usize,
    a4: usize,
    a5: usize,
) -> isize {
    let ret: isize;
    unsafe {
        asm!(
            "svc #0",
            in("x8") nr,
            inout("x0") a0 => ret,
            in("x1") a1,
            in("x2") a2,
            in("x3") a3,
            in("x4") a4,
            in("x5") a5,
            options(nostack)
        );
    }
    ret
}

fn write_all_fd(fd: usize, mut buf: &[u8]) {
    while !buf.is_empty() {
        let n = unsafe { sys3(SYS_WRITE, fd, buf.as_ptr() as usize, buf.len()) };
        if n <= 0 {
            break;
        }
        buf = &buf[n as usize..];
    }
}

fn fmt_isize<'a>(scratch: &'a mut [u8; 32], v: isize) -> &'a [u8] {
    if v == 0 {
        scratch[31] = b'0';
        return &scratch[31..32];
    }
    let neg = v < 0;
    let mut mag: usize = if neg { v.wrapping_neg() as usize } else { v as usize };
    let mut pos = 32;
    while mag > 0 {
        pos -= 1;
        scratch[pos] = b'0' + (mag % 10) as u8;
        mag /= 10;
    }
    if neg {
        pos -= 1;
        scratch[pos] = b'-';
    }
    &scratch[pos..32]
}

fn emit_kv(json_mode: bool, first: &mut bool, key: &[u8], val: isize) {
    let mut scratch = [0u8; 32];
    let val_bytes = fmt_isize(&mut scratch, val);
    if json_mode {
        if !*first {
            write_all_fd(1, b",\n");
        }
        *first = false;
        write_all_fd(1, b"    \"");
        write_all_fd(1, key);
        write_all_fd(1, b"\": ");
        write_all_fd(1, val_bytes);
    } else {
        write_all_fd(1, key);
        write_all_fd(1, b"=");
        write_all_fd(1, val_bytes);
        write_all_fd(1, b"\n");
    }
}

unsafe fn cstr_slice(p: *const u8) -> &'static [u8] {
    let mut len = 0usize;
    while unsafe { *p.add(len) } != 0 {
        len += 1;
    }
    unsafe { core::slice::from_raw_parts(p, len) }
}

#[repr(C)]
struct PollFd {
    fd: i32,
    events: i16,
    revents: i16,
}

#[repr(C)]
struct KernelTimespec {
    tv_sec: i64,
    tv_nsec: i64,
}

#[repr(C)]
struct KernelSigAction {
    sa_handler: u64,
    sa_flags: u64,
    sa_restorer: u64,
    sa_mask: u64,
}

#[repr(C)]
struct KernelStackT {
    ss_sp: u64,
    ss_flags: i32,
    ss_pad: u32,
    ss_size: u64,
}

extern "C" fn dummy_fault_handler(_sig: i32) {}

#[unsafe(no_mangle)]
extern "C" fn rust_entry(sp: *const usize) -> ! {
    let argc = unsafe { *sp };
    let argv = unsafe { sp.add(1) as *const *const u8 };
    let mode: &[u8] = if argc >= 2 {
        unsafe { cstr_slice(*argv.add(1)) }
    } else {
        b"all"
    };

    // Dedicated modes for terminal syscalls (`exit`, fatal `tkill`, fatal `tgkill`).
    if mode == b"exit_one" {
        let _ = unsafe { sys1(SYS_EXIT, 42) };
        loop {
            unsafe { asm!("udf #0", options(nomem, nostack)) };
        }
    }
    if mode == b"tkill_abrt" {
        let tid = unsafe { sys0(SYS_GETTID) };
        let _ = unsafe { sys2(SYS_TKILL, tid as usize, SIGABRT) };
        loop {
            unsafe { asm!("udf #0", options(nomem, nostack)) };
        }
    }
    if mode == b"tgkill_abrt" {
        let pid = unsafe { sys0(SYS_GETPID) };
        let tid = unsafe { sys0(SYS_GETTID) };
        let _ = unsafe { sys3(SYS_TGKILL, pid as usize, tid as usize, SIGABRT) };
        loop {
            unsafe { asm!("udf #0", options(nomem, nostack)) };
        }
    }

    let json_mode = mode == b"record-json";
    if json_mode {
        write_all_fd(1, b"{\n  \"probes\": {\n");
    }
    let mut first = true;

    // Map `m0` (8 KiB) first, then map a 3-page (12 KiB) `PROT_NONE` guard sandwich and unmap
    // its middle 4 KiB page so `unmapped_va` remains an isolated unmapped VMA hole for all
    // subsequent `-EFAULT` and `-ENOMEM` probes.
    let m0 = unsafe { sys6(SYS_MMAP, 0, 8192, PROT_RW, MAP_PRIV_ANON, usize::MAX, 0) };
    let guard_base = unsafe { sys6(SYS_MMAP, 0, 12288, PROT_NONE, MAP_PRIV_ANON, usize::MAX, 0) };
    let unmapped_va = (guard_base as usize) + 4096;
    let _ = unsafe { sys2(SYS_MUNMAP, unmapped_va, 4096) };

    // 1. Thread & process identity (`getpid` 172, `gettid` 178, `set_tid_address` 96)
    let pid = unsafe { sys0(SYS_GETPID) };
    let tid = unsafe { sys0(SYS_GETTID) };
    let tid_addr = unsafe { sys1(SYS_SET_TID_ADDRESS, 0) };
    let id_consistent = if pid > 0 && pid == tid && tid == tid_addr { 1 } else { 0 };
    emit_kv(json_mode, &mut first, b"id_consistent", id_consistent);

    // 2. `sched_getaffinity` (`123`)
    // Use a 1024-byte (8192-bit) buffer so host kernels with `nr_cpu_ids` up to `CONFIG_NR_CPUS=8192`
    // and container `cpuset` masks pinned to CPUs >= 64 both succeed deterministically.
    let mut cpu_mask = [0u64; 128]; // 1024 bytes = 8192 bits
    let aff_zero_len =
        unsafe { sys3(SYS_SCHED_GETAFFINITY, 0, 0, cpu_mask.as_mut_ptr() as usize) };
    let aff_unaligned_len =
        unsafe { sys3(SYS_SCHED_GETAFFINITY, 0, 7, cpu_mask.as_mut_ptr() as usize) };
    let aff_neg_pid = unsafe {
        sys3(
            SYS_SCHED_GETAFFINITY,
            (-1isize) as usize,
            1024,
            cpu_mask.as_mut_ptr() as usize,
        )
    };
    let aff_efault = unsafe { sys3(SYS_SCHED_GETAFFINITY, 0, 1024, unmapped_va) };
    let aff_ok = unsafe { sys3(SYS_SCHED_GETAFFINITY, 0, 1024, cpu_mask.as_mut_ptr() as usize) };
    let mut any_cpu_bit = false;
    if aff_ok >= 8 {
        let words = (aff_ok as usize) / 8;
        let mut i = 0usize;
        while i < words && i < 128 {
            if cpu_mask[i] != 0 {
                any_cpu_bit = true;
            }
            i += 1;
        }
    }
    let aff_valid = if aff_ok >= 8 && (aff_ok % 8 == 0) && any_cpu_bit {
        1
    } else {
        0
    };
    emit_kv(json_mode, &mut first, b"sched_getaffinity_zero_len", aff_zero_len);
    emit_kv(json_mode, &mut first, b"sched_getaffinity_unaligned", aff_unaligned_len);
    emit_kv(json_mode, &mut first, b"sched_getaffinity_neg_pid", aff_neg_pid);
    emit_kv(json_mode, &mut first, b"sched_getaffinity_efault", aff_efault);
    emit_kv(json_mode, &mut first, b"sched_getaffinity_ok", aff_valid);

    // 3. `clock_gettime` (`113`)
    let mut ts = KernelTimespec {
        tv_sec: -1,
        tv_nsec: -1,
    };
    let clk_efault = unsafe { sys2(SYS_CLOCK_GETTIME, 1, unmapped_va) };
    let clk_ok = unsafe { sys2(SYS_CLOCK_GETTIME, 1, (&mut ts as *mut KernelTimespec) as usize) };
    let clk_nsec_valid = if clk_ok == 0 && ts.tv_nsec >= 0 && ts.tv_nsec < 1_000_000_000 {
        1
    } else {
        0
    };
    emit_kv(json_mode, &mut first, b"clock_gettime_efault", clk_efault);
    emit_kv(json_mode, &mut first, b"clock_gettime_ok", clk_ok);
    emit_kv(json_mode, &mut first, b"clock_gettime_nsec_valid", clk_nsec_valid);

    // 4. `getrandom` (`278`)
    let mut rnd_buf = [0x5au8; 16];
    let grnd_bad_flags =
        unsafe { sys3(SYS_GETRANDOM, rnd_buf.as_mut_ptr() as usize, 8, 0xff) };
    let grnd_excl_flags = unsafe {
        sys3(
            SYS_GETRANDOM,
            rnd_buf.as_mut_ptr() as usize,
            8,
            GRND_RANDOM | GRND_INSECURE,
        )
    };
    let grnd_efault = unsafe { sys3(SYS_GETRANDOM, unmapped_va, 8, 0) };
    let grnd_zero = unsafe { sys3(SYS_GETRANDOM, unmapped_va, 0, 0) };
    let grnd_ok =
        unsafe { sys3(SYS_GETRANDOM, rnd_buf.as_mut_ptr() as usize, 16, GRND_NONBLOCK) };
    emit_kv(json_mode, &mut first, b"getrandom_bad_flags", grnd_bad_flags);
    emit_kv(json_mode, &mut first, b"getrandom_excl_flags", grnd_excl_flags);
    emit_kv(json_mode, &mut first, b"getrandom_efault", grnd_efault);
    emit_kv(json_mode, &mut first, b"getrandom_zero", grnd_zero);
    emit_kv(json_mode, &mut first, b"getrandom_ok", grnd_ok);

    // 5. `ppoll` (`73`)
    let mut pfds = [
        PollFd {
            fd: 0,
            events: 0,
            revents: 0x7ff,
        },
        PollFd {
            fd: 1,
            events: 0,
            revents: 0x7ff,
        },
        PollFd {
            fd: 2,
            events: 0,
            revents: 0x7ff,
        },
    ];
    let zero_ts = KernelTimespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    let neg_ts = KernelTimespec {
        tv_sec: -1,
        tv_nsec: 0,
    };
    let bad_nsec_ts = KernelTimespec {
        tv_sec: 0,
        tv_nsec: 1_000_000_000,
    };
    let ppoll_bad_tsp =
        unsafe { sys5(SYS_PPOLL, pfds.as_mut_ptr() as usize, 1, unmapped_va, 0, 8) };
    let ppoll_neg_sec = unsafe {
        sys5(
            SYS_PPOLL,
            pfds.as_mut_ptr() as usize,
            1,
            (&neg_ts as *const KernelTimespec) as usize,
            0,
            8,
        )
    };
    let ppoll_bad_nsec = unsafe {
        sys5(
            SYS_PPOLL,
            pfds.as_mut_ptr() as usize,
            1,
            (&bad_nsec_ts as *const KernelTimespec) as usize,
            0,
            8,
        )
    };
    let ppoll_bad_sigsz = unsafe {
        sys5(
            SYS_PPOLL,
            pfds.as_mut_ptr() as usize,
            1,
            (&zero_ts as *const KernelTimespec) as usize,
            (&zero_ts as *const KernelTimespec) as usize,
            16,
        )
    };
    let ppoll_nfds_big = unsafe {
        sys5(
            SYS_PPOLL,
            pfds.as_mut_ptr() as usize,
            0x7fff_ffff,
            (&zero_ts as *const KernelTimespec) as usize,
            0,
            8,
        )
    };
    let ppoll_bad_ufds = unsafe {
        sys5(
            SYS_PPOLL,
            unmapped_va,
            1,
            (&zero_ts as *const KernelTimespec) as usize,
            0,
            8,
        )
    };
    let ppoll_zero_nfds = unsafe {
        sys5(
            SYS_PPOLL,
            0,
            0,
            (&zero_ts as *const KernelTimespec) as usize,
            0,
            8,
        )
    };
    let ppoll_stdio_ok = unsafe {
        sys5(
            SYS_PPOLL,
            pfds.as_mut_ptr() as usize,
            3,
            (&zero_ts as *const KernelTimespec) as usize,
            0,
            8,
        )
    };
    let ppoll_revents_zero =
        if pfds[0].revents == 0 && pfds[1].revents == 0 && pfds[2].revents == 0 {
            1
        } else {
            0
        };
    emit_kv(json_mode, &mut first, b"ppoll_bad_tsp", ppoll_bad_tsp);
    emit_kv(json_mode, &mut first, b"ppoll_neg_sec", ppoll_neg_sec);
    emit_kv(json_mode, &mut first, b"ppoll_bad_nsec", ppoll_bad_nsec);
    emit_kv(json_mode, &mut first, b"ppoll_bad_sigsz", ppoll_bad_sigsz);
    emit_kv(json_mode, &mut first, b"ppoll_nfds_big", ppoll_nfds_big);
    emit_kv(json_mode, &mut first, b"ppoll_bad_ufds", ppoll_bad_ufds);
    emit_kv(json_mode, &mut first, b"ppoll_zero_nfds", ppoll_zero_nfds);
    emit_kv(json_mode, &mut first, b"ppoll_stdio_ok", ppoll_stdio_ok);
    emit_kv(json_mode, &mut first, b"ppoll_revents_zero", ppoll_revents_zero);

    // 6. VFS lifecycle: `openat` (56), `fcntl` (25), `ioctl` (29), `write` (64), `lseek` (62),
    //    `read` (63), `pread64` (67), `fstat` (80), `close` (57).
    let missing_path = b"no_such_file.txt\0";
    let empty_path = b"\0";
    let probe_path = b"probe_file.bin\0";

    let open_missing = unsafe {
        sys4(
            SYS_OPENAT,
            AT_FDCWD as usize,
            missing_path.as_ptr() as usize,
            O_RDONLY,
            0,
        )
    };
    let open_empty = unsafe {
        sys4(
            SYS_OPENAT,
            AT_FDCWD as usize,
            empty_path.as_ptr() as usize,
            O_RDONLY,
            0,
        )
    };
    let open_efault = unsafe { sys4(SYS_OPENAT, AT_FDCWD as usize, unmapped_va, O_RDONLY, 0) };
    let fd = unsafe {
        sys4(
            SYS_OPENAT,
            AT_FDCWD as usize,
            probe_path.as_ptr() as usize,
            O_RDWR | O_CREAT | O_TRUNC | O_CLOEXEC,
            0o644,
        )
    };
    let open_notdir = unsafe {
        sys4(
            SYS_OPENAT,
            AT_FDCWD as usize,
            probe_path.as_ptr() as usize,
            O_RDONLY | O_DIRECTORY,
            0,
        )
    };
    let open_excl_exists = unsafe {
        sys4(
            SYS_OPENAT,
            AT_FDCWD as usize,
            probe_path.as_ptr() as usize,
            O_RDWR | O_CREAT | O_EXCL,
            0o644,
        )
    };
    emit_kv(json_mode, &mut first, b"openat_missing", open_missing);
    emit_kv(json_mode, &mut first, b"openat_empty", open_empty);
    emit_kv(json_mode, &mut first, b"openat_notdir", open_notdir);
    emit_kv(json_mode, &mut first, b"openat_efault", open_efault);
    emit_kv(json_mode, &mut first, b"openat_fd_valid", if fd >= 3 { 1 } else { 0 });
    emit_kv(json_mode, &mut first, b"openat_excl_exists", open_excl_exists);

    // `fcntl` (25)
    let fcntl_neg_fd = unsafe { sys3(SYS_FCNTL, (-1isize) as usize, F_GETFD, 0) };
    let fcntl_closed_fd = unsafe { sys3(SYS_FCNTL, 99, F_GETFD, 0) };
    let fcntl_get0 = unsafe { sys3(SYS_FCNTL, fd as usize, F_GETFD, 0) };
    let fcntl_set0 = unsafe { sys3(SYS_FCNTL, fd as usize, F_SETFD, 0) };
    let fcntl_get1 = unsafe { sys3(SYS_FCNTL, fd as usize, F_GETFD, 0) };
    let fcntl_set1 = unsafe { sys3(SYS_FCNTL, fd as usize, F_SETFD, FD_CLOEXEC) };
    let fcntl_get2 = unsafe { sys3(SYS_FCNTL, fd as usize, F_GETFD, 0) };
    emit_kv(json_mode, &mut first, b"fcntl_neg_fd", fcntl_neg_fd);
    emit_kv(json_mode, &mut first, b"fcntl_closed_fd", fcntl_closed_fd);
    emit_kv(json_mode, &mut first, b"fcntl_get_init_cloexec", fcntl_get0);
    emit_kv(json_mode, &mut first, b"fcntl_clear_cloexec", fcntl_set0);
    emit_kv(json_mode, &mut first, b"fcntl_get_after_clear", fcntl_get1);
    emit_kv(json_mode, &mut first, b"fcntl_set_cloexec", fcntl_set1);
    emit_kv(json_mode, &mut first, b"fcntl_get_after_set", fcntl_get2);

    // `ioctl` (29)
    let ioctl_neg_fd = unsafe { sys3(SYS_IOCTL, (-1isize) as usize, 0x5401, 0) };
    let ioctl_closed_fd = unsafe { sys3(SYS_IOCTL, 99, 0x5401, 0) };
    let ioctl_reg_file = unsafe { sys3(SYS_IOCTL, fd as usize, 0x5401, 0) };
    emit_kv(json_mode, &mut first, b"ioctl_neg_fd", ioctl_neg_fd);
    emit_kv(json_mode, &mut first, b"ioctl_closed_fd", ioctl_closed_fd);
    emit_kv(json_mode, &mut first, b"ioctl_reg_file", ioctl_reg_file);

    // `write` (64)
    let payload = b"ABCDEFGH";
    let write_neg_fd = unsafe { sys3(SYS_WRITE, (-1isize) as usize, payload.as_ptr() as usize, 4) };
    let write_closed_fd = unsafe { sys3(SYS_WRITE, 99, payload.as_ptr() as usize, 4) };
    let write_efault = unsafe { sys3(SYS_WRITE, fd as usize, unmapped_va, 4) };
    let write_ok = unsafe { sys3(SYS_WRITE, fd as usize, payload.as_ptr() as usize, 8) };
    let write_zero = unsafe { sys3(SYS_WRITE, fd as usize, payload.as_ptr() as usize, 0) };
    emit_kv(json_mode, &mut first, b"write_neg_fd", write_neg_fd);
    emit_kv(json_mode, &mut first, b"write_closed_fd", write_closed_fd);
    emit_kv(json_mode, &mut first, b"write_efault", write_efault);
    emit_kv(json_mode, &mut first, b"write_ok", write_ok);
    emit_kv(json_mode, &mut first, b"write_zero", write_zero);

    // `lseek` (62)
    let lseek_neg_fd = unsafe { sys3(SYS_LSEEK, (-1isize) as usize, 0, 0) };
    let lseek_closed_fd = unsafe { sys3(SYS_LSEEK, 99, 0, 0) };
    let lseek_bad_whence = unsafe { sys3(SYS_LSEEK, fd as usize, 0, 99) };
    let lseek_neg_off = unsafe { sys3(SYS_LSEEK, fd as usize, (-5isize) as usize, 0) };
    let lseek_end_m2 = unsafe { sys3(SYS_LSEEK, fd as usize, (-2isize) as usize, 2) };
    let lseek_cur_m1 = unsafe { sys3(SYS_LSEEK, fd as usize, (-1isize) as usize, 1) };
    let lseek_set_2 = unsafe { sys3(SYS_LSEEK, fd as usize, 2, 0) };
    emit_kv(json_mode, &mut first, b"lseek_neg_fd", lseek_neg_fd);
    emit_kv(json_mode, &mut first, b"lseek_closed_fd", lseek_closed_fd);
    emit_kv(json_mode, &mut first, b"lseek_bad_whence", lseek_bad_whence);
    emit_kv(json_mode, &mut first, b"lseek_neg_off", lseek_neg_off);
    emit_kv(json_mode, &mut first, b"lseek_end_m2", lseek_end_m2);
    emit_kv(json_mode, &mut first, b"lseek_cur_m1", lseek_cur_m1);
    emit_kv(json_mode, &mut first, b"lseek_set_2", lseek_set_2);

    // `pread64` (67) and `read` (63)
    let mut rbuf = [0u8; 8];
    let pread_neg_fd =
        unsafe { sys4(SYS_PREAD64, (-1isize) as usize, rbuf.as_mut_ptr() as usize, 3, 0) };
    let pread_neg_pos =
        unsafe { sys4(SYS_PREAD64, fd as usize, rbuf.as_mut_ptr() as usize, 3, (-1isize) as usize) };
    let pread_neg_fd_neg_pos = unsafe {
        sys4(
            SYS_PREAD64,
            (-1isize) as usize,
            rbuf.as_mut_ptr() as usize,
            1,
            (-1isize) as usize,
        )
    };
    let pread_efault = unsafe { sys4(SYS_PREAD64, fd as usize, unmapped_va, 3, 0) };
    let pread_ok = unsafe { sys4(SYS_PREAD64, fd as usize, rbuf.as_mut_ptr() as usize, 4, 3) };
    let pread_match = if &rbuf[..4] == b"DEFG" { 1 } else { 0 };

    let read_neg_fd = unsafe { sys3(SYS_READ, (-1isize) as usize, rbuf.as_mut_ptr() as usize, 2) };
    let read_efault = unsafe { sys3(SYS_READ, fd as usize, unmapped_va, 2) };
    let read_ok = unsafe { sys3(SYS_READ, fd as usize, rbuf.as_mut_ptr() as usize, 3) };
    let read_match = if &rbuf[..3] == b"CDE" { 1 } else { 0 };
    let lseek_after_read = unsafe { sys3(SYS_LSEEK, fd as usize, 0, 1) }; // SEEK_CUR == 5
    emit_kv(json_mode, &mut first, b"pread64_neg_fd", pread_neg_fd);
    emit_kv(json_mode, &mut first, b"pread64_neg_pos", pread_neg_pos);
    emit_kv(json_mode, &mut first, b"pread64_neg_fd_neg_pos", pread_neg_fd_neg_pos);
    emit_kv(json_mode, &mut first, b"pread64_efault", pread_efault);
    emit_kv(json_mode, &mut first, b"pread64_ok", pread_ok);
    emit_kv(json_mode, &mut first, b"pread64_match", pread_match);
    emit_kv(json_mode, &mut first, b"read_neg_fd", read_neg_fd);
    emit_kv(json_mode, &mut first, b"read_efault", read_efault);
    emit_kv(json_mode, &mut first, b"read_ok", read_ok);
    emit_kv(json_mode, &mut first, b"read_match", read_match);
    emit_kv(json_mode, &mut first, b"lseek_after_read", lseek_after_read);

    // `fstat` (80)
    let mut stat_buf = [0u8; 128];
    let fstat_neg_fd = unsafe { sys2(SYS_FSTAT, (-1isize) as usize, stat_buf.as_mut_ptr() as usize) };
    let fstat_efault = unsafe { sys2(SYS_FSTAT, fd as usize, unmapped_va) };
    let fstat_ok = unsafe { sys2(SYS_FSTAT, fd as usize, stat_buf.as_mut_ptr() as usize) };
    let st_mode = u32::from_le_bytes([stat_buf[16], stat_buf[17], stat_buf[18], stat_buf[19]]);
    let st_size = i64::from_le_bytes([
        stat_buf[48],
        stat_buf[49],
        stat_buf[50],
        stat_buf[51],
        stat_buf[52],
        stat_buf[53],
        stat_buf[54],
        stat_buf[55],
    ]);
    let fstat_is_reg = if (st_mode & 0o170000) == 0o100000 { 1 } else { 0 };
    emit_kv(json_mode, &mut first, b"fstat_neg_fd", fstat_neg_fd);
    emit_kv(json_mode, &mut first, b"fstat_efault", fstat_efault);
    emit_kv(json_mode, &mut first, b"fstat_ok", fstat_ok);
    emit_kv(json_mode, &mut first, b"fstat_is_reg", fstat_is_reg);
    emit_kv(json_mode, &mut first, b"fstat_size", st_size as isize);

    // `close` (57)
    let close_neg_fd = unsafe { sys1(SYS_CLOSE, (-1isize) as usize) };
    let close_ok = unsafe { sys1(SYS_CLOSE, fd as usize) };
    let close_again = unsafe { sys1(SYS_CLOSE, fd as usize) };
    emit_kv(json_mode, &mut first, b"close_neg_fd", close_neg_fd);
    emit_kv(json_mode, &mut first, b"close_ok", close_ok);
    emit_kv(json_mode, &mut first, b"close_again", close_again);

    // 7. Signal handling: `rt_sigprocmask` (135), `rt_sigaction` (134), `tkill` (130), `tgkill` (131)
    let sigmask_buf: u64 = 0;
    let mut oldmask_buf: u64 = 0xffff_ffff_ffff_ffff;
    let sigpm_bad_sz = unsafe { sys4(SYS_RT_SIGPROCMASK, 0, 0, 0, 4) };
    let sigpm_efault_set = unsafe { sys4(SYS_RT_SIGPROCMASK, 0, unmapped_va, 0, 8) };
    let sigpm_bad_how =
        unsafe { sys4(SYS_RT_SIGPROCMASK, 99, (&sigmask_buf as *const u64) as usize, 0, 8) };
    let sigpm_efault_old = unsafe { sys4(SYS_RT_SIGPROCMASK, 0, 0, unmapped_va, 8) };
    let sigpm_ok = unsafe {
        sys4(
            SYS_RT_SIGPROCMASK,
            0,
            (&sigmask_buf as *const u64) as usize,
            (&mut oldmask_buf as *mut u64) as usize,
            8,
        )
    };
    emit_kv(json_mode, &mut first, b"rt_sigprocmask_bad_sz", sigpm_bad_sz);
    emit_kv(json_mode, &mut first, b"rt_sigprocmask_efault_set", sigpm_efault_set);
    emit_kv(json_mode, &mut first, b"rt_sigprocmask_bad_how", sigpm_bad_how);
    emit_kv(json_mode, &mut first, b"rt_sigprocmask_efault_old", sigpm_efault_old);
    emit_kv(json_mode, &mut first, b"rt_sigprocmask_ok", sigpm_ok);

    let sa_ign = KernelSigAction {
        sa_handler: SIG_IGN,
        sa_flags: 0,
        sa_restorer: 0,
        sa_mask: 0,
    };
    let sa_dfl = KernelSigAction {
        sa_handler: SIG_DFL,
        sa_flags: 0,
        sa_restorer: 0,
        sa_mask: 0,
    };
    let mut sa_old = KernelSigAction {
        sa_handler: 99,
        sa_flags: 0,
        sa_restorer: 0,
        sa_mask: 0,
    };
    let sigact_bad_sz = unsafe { sys4(SYS_RT_SIGACTION, SIGABRT, 0, 0, 4) };
    let sigact_efault_act = unsafe { sys4(SYS_RT_SIGACTION, SIGABRT, unmapped_va, 0, 8) };
    let sigact_sig0 = unsafe { sys4(SYS_RT_SIGACTION, 0, 0, 0, 8) };
    let sigact_sig65 = unsafe { sys4(SYS_RT_SIGACTION, 65, 0, 0, 8) };
    let sigact_sigkill = unsafe {
        sys4(
            SYS_RT_SIGACTION,
            SIGKILL,
            (&sa_ign as *const KernelSigAction) as usize,
            0,
            8,
        )
    };
    let sigact_efault_old = unsafe { sys4(SYS_RT_SIGACTION, SIGABRT, 0, unmapped_va, 8) };
    let sigact_set_ign = unsafe {
        sys4(
            SYS_RT_SIGACTION,
            SIGABRT,
            (&sa_ign as *const KernelSigAction) as usize,
            (&mut sa_old as *mut KernelSigAction) as usize,
            8,
        )
    };
    let sigact_prev_dfl = if sa_old.sa_handler == SIG_DFL { 1 } else { 0 };

    // With `SIGABRT` set to `SIG_IGN`, `tkill(tid, SIGABRT)` and `tgkill(pid, tid, SIGABRT)`
    // return `0` without terminating!
    let tkill_bad_tid = unsafe { sys2(SYS_TKILL, 0, SIGABRT) };
    let tkill_bad_sig = unsafe { sys2(SYS_TKILL, tid as usize, 65) };
    let tkill_ign_ok = unsafe { sys2(SYS_TKILL, tid as usize, SIGABRT) };

    let tgkill_bad_tgid = unsafe { sys3(SYS_TGKILL, 0, tid as usize, SIGABRT) };
    let tgkill_bad_tid = unsafe { sys3(SYS_TGKILL, pid as usize, 0, SIGABRT) };
    let tgkill_bad_sig = unsafe { sys3(SYS_TGKILL, pid as usize, tid as usize, 65) };
    let tgkill_ign_ok = unsafe { sys3(SYS_TGKILL, pid as usize, tid as usize, SIGABRT) };

    // Restore `SIGABRT` to `SIG_DFL` and verify `sa_old.sa_handler == SIG_IGN`.
    let sigact_restore_dfl = unsafe {
        sys4(
            SYS_RT_SIGACTION,
            SIGABRT,
            (&sa_dfl as *const KernelSigAction) as usize,
            (&mut sa_old as *mut KernelSigAction) as usize,
            8,
        )
    };
    let sigact_prev_ign = if sa_old.sa_handler == SIG_IGN { 1 } else { 0 };

    emit_kv(json_mode, &mut first, b"rt_sigaction_bad_sz", sigact_bad_sz);
    emit_kv(json_mode, &mut first, b"rt_sigaction_efault_act", sigact_efault_act);
    emit_kv(json_mode, &mut first, b"rt_sigaction_sig0", sigact_sig0);
    emit_kv(json_mode, &mut first, b"rt_sigaction_sig65", sigact_sig65);
    emit_kv(json_mode, &mut first, b"rt_sigaction_sigkill", sigact_sigkill);
    emit_kv(json_mode, &mut first, b"rt_sigaction_efault_old", sigact_efault_old);
    emit_kv(json_mode, &mut first, b"rt_sigaction_set_ign", sigact_set_ign);
    emit_kv(json_mode, &mut first, b"rt_sigaction_prev_dfl", sigact_prev_dfl);
    emit_kv(json_mode, &mut first, b"tkill_bad_tid", tkill_bad_tid);
    emit_kv(json_mode, &mut first, b"tkill_bad_sig", tkill_bad_sig);
    emit_kv(json_mode, &mut first, b"tkill_ign_ok", tkill_ign_ok);
    emit_kv(json_mode, &mut first, b"tgkill_bad_tgid", tgkill_bad_tgid);
    emit_kv(json_mode, &mut first, b"tgkill_bad_tid", tgkill_bad_tid);
    emit_kv(json_mode, &mut first, b"tgkill_bad_sig", tgkill_bad_sig);
    emit_kv(json_mode, &mut first, b"tgkill_ign_ok", tgkill_ign_ok);
    emit_kv(json_mode, &mut first, b"rt_sigaction_restore_dfl", sigact_restore_dfl);
    emit_kv(json_mode, &mut first, b"rt_sigaction_prev_ign", sigact_prev_ign);

    // Custom `sa_handler` on `SIGSEGV` (`11`) and `SIGBUS` (`7`) + `sigaltstack` (`132`) + `MAP_STACK`.
    let custom_fn = (dummy_fault_handler as *const () as usize) as u64;
    let sa_custom = KernelSigAction {
        sa_handler: custom_fn,
        sa_flags: 0x0800_0000, // SA_ONSTACK
        sa_restorer: 0,
        sa_mask: 0,
    };
    let segv_set = unsafe {
        sys4(
            SYS_RT_SIGACTION,
            SIGSEGV,
            (&sa_custom as *const KernelSigAction) as usize,
            (&mut sa_old as *mut KernelSigAction) as usize,
            8,
        )
    };
    let segv_was_dfl = sa_old.sa_handler == SIG_DFL;
    let segv_rst = unsafe {
        sys4(
            SYS_RT_SIGACTION,
            SIGSEGV,
            (&sa_dfl as *const KernelSigAction) as usize,
            (&mut sa_old as *mut KernelSigAction) as usize,
            8,
        )
    };
    let segv_custom_ok =
        if segv_set == 0 && segv_was_dfl && segv_rst == 0 && sa_old.sa_handler == custom_fn {
            1
        } else {
            0
        };
    let bus_set = unsafe {
        sys4(
            SYS_RT_SIGACTION,
            SIGBUS,
            (&sa_custom as *const KernelSigAction) as usize,
            (&mut sa_old as *mut KernelSigAction) as usize,
            8,
        )
    };
    let bus_was_dfl = sa_old.sa_handler == SIG_DFL;
    let bus_rst = unsafe {
        sys4(
            SYS_RT_SIGACTION,
            SIGBUS,
            (&sa_dfl as *const KernelSigAction) as usize,
            (&mut sa_old as *mut KernelSigAction) as usize,
            8,
        )
    };
    let bus_custom_ok =
        if bus_set == 0 && bus_was_dfl && bus_rst == 0 && sa_old.sa_handler == custom_fn {
            1
        } else {
            0
        };

    let m_stack = unsafe { sys6(SYS_MMAP, 0, 8192, PROT_RW, MAP_PRIV_ANON_STACK, usize::MAX, 0) };
    let mmap_stack_ok = if m_stack > 0 && (m_stack as usize & 0xfff) == 0 {
        1
    } else {
        0
    };
    let mut oss = KernelStackT {
        ss_sp: 0xffff_ffff_ffff_ffff,
        ss_flags: -1,
        ss_pad: 0xffff_ffff,
        ss_size: 0xffff_ffff_ffff_ffff,
    };
    let sas_init_q = unsafe { sys2(SYS_SIGALTSTACK, 0, (&mut oss as *mut KernelStackT) as usize) };
    let sas_init_dis = if oss.ss_sp == 0
        && oss.ss_flags == SS_DISABLE
        && oss.ss_pad == 0
        && oss.ss_size == 0
    {
        1
    } else {
        0
    };
    let uss_small = KernelStackT {
        ss_sp: m_stack as u64,
        ss_flags: 0,
        ss_pad: 0,
        ss_size: 1024,
    };
    let sas_enomem = unsafe { sys2(SYS_SIGALTSTACK, (&uss_small as *const KernelStackT) as usize, 0) };
    let uss_bad = KernelStackT {
        ss_sp: m_stack as u64,
        ss_flags: 4,
        ss_pad: 0,
        ss_size: 8192,
    };
    let sas_bad_flags = unsafe { sys2(SYS_SIGALTSTACK, (&uss_bad as *const KernelStackT) as usize, 0) };
    let sas_efault_uss = unsafe { sys2(SYS_SIGALTSTACK, unmapped_va, 0) };
    let sas_efault_uoss = unsafe { sys2(SYS_SIGALTSTACK, 0, unmapped_va) };

    let uss_inst = KernelStackT {
        ss_sp: m_stack as u64,
        ss_flags: 0,
        ss_pad: 0xdead_beef,
        ss_size: 8192,
    };
    oss.ss_pad = 0xffff_ffff;
    let sas_inst = unsafe {
        sys2(
            SYS_SIGALTSTACK,
            (&uss_inst as *const KernelStackT) as usize,
            (&mut oss as *mut KernelStackT) as usize,
        )
    };
    let sas_inst_ok = if sas_inst == 0 && oss.ss_flags == SS_DISABLE && oss.ss_pad == 0 {
        1
    } else {
        0
    };
    oss.ss_pad = 0xffff_ffff;
    let sas_q_act = unsafe { sys2(SYS_SIGALTSTACK, 0, (&mut oss as *mut KernelStackT) as usize) };
    let sas_active_ok = if sas_q_act == 0
        && oss.ss_sp == m_stack as u64
        && oss.ss_flags == 0
        && oss.ss_pad == 0
        && oss.ss_size == 8192
    {
        1
    } else {
        0
    };
    let uss_dis_nz = KernelStackT {
        ss_sp: m_stack as u64,
        ss_flags: SS_DISABLE,
        ss_pad: 0x1234_5678,
        ss_size: 8192,
    };
    let sas_onstack_eperm: isize;
    unsafe {
        let alt_mid = (m_stack as usize) + 4096;
        let oss_ptr = (&mut oss as *mut KernelStackT) as usize;
        let dis_ptr = (&uss_dis_nz as *const KernelStackT) as usize;
        asm!(
            "mov x9, sp",
            "mov sp, {alt_mid}",
            "mov x8, {nr}",
            "mov x0, #0",
            "mov x1, {oss_ptr}",
            "svc #0",
            "mov x8, {nr}",
            "mov x0, {dis_ptr}",
            "mov x1, #0",
            "svc #0",
            "mov sp, x9",
            alt_mid = in(reg) alt_mid,
            nr = const SYS_SIGALTSTACK,
            oss_ptr = in(reg) oss_ptr,
            dis_ptr = in(reg) dis_ptr,
            out("x0") sas_onstack_eperm,
            out("x1") _,
            out("x8") _,
            out("x9") _,
        );
    }
    let sas_onstack_flag = if oss.ss_flags == SS_ONSTACK { 1 } else { 0 };
    let sas_dis_nz = unsafe {
        sys2(
            SYS_SIGALTSTACK,
            (&uss_dis_nz as *const KernelStackT) as usize,
            (&mut oss as *mut KernelStackT) as usize,
        )
    };
    let _ = unsafe { sys2(SYS_SIGALTSTACK, 0, (&mut oss as *mut KernelStackT) as usize) };
    let sas_dis_again = if oss.ss_sp == 0 && oss.ss_flags == SS_DISABLE && oss.ss_size == 0 {
        1
    } else {
        0
    };
    let _ = unsafe { sys2(SYS_MUNMAP, m_stack as usize, 8192) };

    emit_kv(json_mode, &mut first, b"rt_sigaction_segv_custom_ok", segv_custom_ok);
    emit_kv(json_mode, &mut first, b"rt_sigaction_bus_custom_ok", bus_custom_ok);
    emit_kv(json_mode, &mut first, b"mmap_stack_ok", mmap_stack_ok);
    emit_kv(json_mode, &mut first, b"sigaltstack_init_query", sas_init_q);
    emit_kv(json_mode, &mut first, b"sigaltstack_init_disabled", sas_init_dis);
    emit_kv(json_mode, &mut first, b"sigaltstack_enomem", sas_enomem);
    emit_kv(json_mode, &mut first, b"sigaltstack_bad_flags", sas_bad_flags);
    emit_kv(json_mode, &mut first, b"sigaltstack_efault_uss", sas_efault_uss);
    emit_kv(json_mode, &mut first, b"sigaltstack_efault_uoss", sas_efault_uoss);
    emit_kv(json_mode, &mut first, b"sigaltstack_install_ok", sas_inst_ok);
    emit_kv(json_mode, &mut first, b"sigaltstack_query_active", sas_active_ok);
    emit_kv(json_mode, &mut first, b"sigaltstack_onstack_flag", sas_onstack_flag);
    emit_kv(json_mode, &mut first, b"sigaltstack_onstack_eperm", sas_onstack_eperm);
    emit_kv(json_mode, &mut first, b"sigaltstack_disable_nz_ok", sas_dis_nz);
    emit_kv(json_mode, &mut first, b"sigaltstack_disabled_again", sas_dis_again);

    // 8. Virtual memory management: `brk` (214), `mmap` (222), `mprotect` (226), `madvise` (233),
    //    `mremap` (216), `munmap` (215)
    let brk0 = unsafe { sys1(SYS_BRK, 0) } as usize;
    let brk_below = unsafe { sys1(SYS_BRK, brk0 - 4096) } as usize;
    let brk1 = unsafe { sys1(SYS_BRK, brk0 + 4096) } as usize;
    let brk_ptr = brk0 as *mut u64;
    unsafe { brk_ptr.write_volatile(0x1122_3344_5566_7788) };
    let brk_read_ok = if unsafe { brk_ptr.read_volatile() } == 0x1122_3344_5566_7788 {
        1
    } else {
        0
    };
    let brk_shrink = unsafe { sys1(SYS_BRK, brk0) } as usize;
    emit_kv(json_mode, &mut first, b"brk_below_unchanged", if brk_below == brk0 { 1 } else { 0 });
    emit_kv(json_mode, &mut first, b"brk_grow_ok", if brk1 == brk0 + 4096 { 1 } else { 0 });
    emit_kv(json_mode, &mut first, b"brk_rw_ok", brk_read_ok);
    emit_kv(json_mode, &mut first, b"brk_shrink_ok", if brk_shrink == brk0 { 1 } else { 0 });

    let mmap_zero_len = unsafe { sys6(SYS_MMAP, 0, 0, PROT_RW, MAP_PRIV_ANON, usize::MAX, 0) };
    let m0_valid = if m0 > 0 && (m0 as usize & 0xfff) == 0 { 1 } else { 0 };
    let m0_va = m0 as usize;
    unsafe { (m0_va as *mut u64).write_volatile(0xcafe_babe_dead_beef) };

    // Overwrite `m0` with `MAP_FIXED | PROT_NONE`, then re-enable `PROT_RW` via `mprotect`.
    let m_fixed = unsafe {
        sys6(
            SYS_MMAP,
            m0_va,
            8192,
            PROT_NONE,
            MAP_PRIV_ANON_FIXED,
            usize::MAX,
            0,
        )
    };
    let m_fixed_ok = if m_fixed as usize == m0_va { 1 } else { 0 };

    let mprot_unaligned = unsafe { sys3(SYS_MPROTECT, m0_va + 1, 4096, PROT_RW) };
    let mprot_zero_len = unsafe { sys3(SYS_MPROTECT, m0_va, 0, PROT_RW) };
    let mprot_unmapped = unsafe { sys3(SYS_MPROTECT, unmapped_va, 4096, PROT_RW) };
    let mprot_ok = unsafe { sys3(SYS_MPROTECT, m0_va, 8192, PROT_RW) };
    unsafe { (m0_va as *mut u64).write_volatile(0x1234_5678_9abc_def0) };
    unsafe { ((m0_va + 4096) as *mut u64).write_volatile(0x0fed_cba9_8765_4321) };

    // `madvise` (233)
    let madv_unaligned = unsafe { sys3(SYS_MADVISE, m0_va + 1, 4096, MADV_NORMAL) };
    let madv_zero_len = unsafe { sys3(SYS_MADVISE, m0_va, 0, MADV_NORMAL) };
    let madv_willneed = unsafe { sys3(SYS_MADVISE, m0_va, 4096, MADV_WILLNEED) };
    let madv_free = unsafe { sys3(SYS_MADVISE, m0_va, 4096, MADV_FREE) };
    unsafe { (m0_va as *mut u64).write_volatile(0x55aa_55aa_55aa_55aa) };
    let madv_free_store_load =
        if unsafe { (m0_va as *const u64).read_volatile() } == 0x55aa_55aa_55aa_55aa {
            1
        } else {
            0
        };
    let madv_dontneed = unsafe { sys3(SYS_MADVISE, m0_va, 4096, MADV_DONTNEED) };
    let madv_zeroed = if unsafe { (m0_va as *const u64).read_volatile() } == 0 {
        1
    } else {
        0
    };

    // `mremap` (216): keep `[m0_va + 1, m0_va + 4097)` strictly inside the 8 KiB `m0` mapping
    // so QEMU user-mode's `page_check_range(old_addr, old_size, PAGE_VALID)` never touches `m0_va + 8192`.
    let mremap_unaligned = unsafe { sys4(SYS_MREMAP, m0_va + 1, 4096, 8192, MREMAP_MAYMOVE) };
    let mremap_unmapped = unsafe { sys4(SYS_MREMAP, unmapped_va, 4096, 8192, MREMAP_MAYMOVE) };
    let m1 = unsafe { sys4(SYS_MREMAP, m0_va, 8192, 16384, MREMAP_MAYMOVE) };
    let m1_valid = if m1 > 0 && (m1 as usize & 0xfff) == 0 { 1 } else { 0 };
    let m1_va = m1 as usize;
    let m1_preserved =
        if unsafe { ((m1_va + 4096) as *const u64).read_volatile() } == 0x0fed_cba9_8765_4321 {
            1
        } else {
            0
        };

    // `munmap` (215)
    let munmap_unaligned = unsafe { sys2(SYS_MUNMAP, m1_va + 1, 4096) };
    let munmap_zero_len = unsafe { sys2(SYS_MUNMAP, m1_va, 0) };
    let munmap_ok = unsafe { sys2(SYS_MUNMAP, m1_va, 16384) };
    let _ = unsafe { sys2(SYS_MUNMAP, guard_base as usize, 12288) };

    emit_kv(json_mode, &mut first, b"mmap_zero_len", mmap_zero_len);
    emit_kv(json_mode, &mut first, b"mmap_anon_ok", m0_valid);
    emit_kv(json_mode, &mut first, b"mmap_fixed_prot_none_ok", m_fixed_ok);
    emit_kv(json_mode, &mut first, b"mprotect_unaligned", mprot_unaligned);
    emit_kv(json_mode, &mut first, b"mprotect_zero_len", mprot_zero_len);
    emit_kv(json_mode, &mut first, b"mprotect_unmapped", mprot_unmapped);
    emit_kv(json_mode, &mut first, b"mprotect_ok", mprot_ok);
    emit_kv(json_mode, &mut first, b"madvise_unaligned", madv_unaligned);
    emit_kv(json_mode, &mut first, b"madvise_zero_len", madv_zero_len);
    emit_kv(json_mode, &mut first, b"madvise_willneed", madv_willneed);
    emit_kv(json_mode, &mut first, b"madvise_free", madv_free);
    emit_kv(json_mode, &mut first, b"madvise_free_store_load", madv_free_store_load);
    emit_kv(json_mode, &mut first, b"madvise_dontneed", madv_dontneed);
    emit_kv(json_mode, &mut first, b"madvise_dontneed_zeroed", madv_zeroed);
    emit_kv(json_mode, &mut first, b"mremap_unaligned", mremap_unaligned);
    emit_kv(json_mode, &mut first, b"mremap_unmapped", mremap_unmapped);
    emit_kv(json_mode, &mut first, b"mremap_ok", m1_valid);
    emit_kv(json_mode, &mut first, b"mremap_preserved", m1_preserved);
    emit_kv(json_mode, &mut first, b"munmap_unaligned", munmap_unaligned);
    emit_kv(json_mode, &mut first, b"munmap_zero_len", munmap_zero_len);
    emit_kv(json_mode, &mut first, b"munmap_ok", munmap_ok);

    if json_mode {
        write_all_fd(1, b"\n  }\n}\n");
    } else {
        write_all_fd(2, b"syscall_probe:ok\n");
    }

    let _ = unsafe { sys1(SYS_EXIT_GROUP, 0) };
    loop {
        unsafe { asm!("udf #0", options(nomem, nostack)) };
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn strlen(s: *const u8) -> usize {
    let mut n = 0usize;
    while unsafe { core::ptr::read_volatile(s.add(n)) } != 0 {
        n += 1;
    }
    n
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn memset(
    s: *mut core::ffi::c_void,
    c: i32,
    n: usize,
) -> *mut core::ffi::c_void {
    let dst = s as *mut u8;
    let mut i = 0usize;
    while i < n {
        unsafe { core::ptr::write_volatile(dst.add(i), c as u8) };
        i += 1;
    }
    s
}

#[unsafe(no_mangle)]
pub extern "C" fn rust_eh_personality() {}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    unsafe { asm!("udf #0", options(noreturn)) }
}
