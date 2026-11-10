// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Linux AArch64 system call wrappers (`write`, `brk`/`sbrk`, `mmap`, `exit`, `exit_group`),
//! minimal bump/page allocators (`sbrk_alloc`, `mmap_alloc`), and verified safe Rust entry points.
//!
//! All `unsafe` inline assembly (`svc #0`) and raw pointer casts are confined to [`sys`].
//! The verified application functions in [`app`] carry `#[forbid(unsafe_code)]`.

/// Low-level Linux AArch64 (`svc #0`) system call wrappers and minimal allocator primitives.
pub mod sys {
    use core::arch::asm;

    pub const STDOUT_FILENO: usize = 1;
    pub const STDERR_FILENO: usize = 2;

    pub const SYS_WRITE: usize = 64;
    pub const SYS_EXIT: usize = 93;
    pub const SYS_EXIT_GROUP: usize = 94;
    pub const SYS_BRK: usize = 214;
    pub const SYS_MMAP: usize = 222;

    pub const PROT_READ: usize = 0x1;
    pub const PROT_WRITE: usize = 0x2;
    pub const MAP_PRIVATE: usize = 0x02;
    pub const MAP_ANONYMOUS: usize = 0x20;

    /// Raw `write(fd, buf, count)` syscall (`X8 = 64`).
    #[inline(always)]
    pub unsafe fn sys_write(fd: usize, buf: *const u8, count: usize) -> usize {
        let ret: usize;
        // SAFETY: Invokes the modeled Linux AArch64 `write` syscall (`svc #0`, `x8 = 64`).
        unsafe {
            asm!(
                "svc #0",
                in("x8") SYS_WRITE,
                inlateout("x0") fd => ret,
                in("x1") buf,
                in("x2") count,
                options(nostack, preserves_flags)
            );
        }
        ret
    }

    /// Raw `brk(addr)` syscall (`X8 = 214`).
    #[inline(always)]
    pub unsafe fn sys_brk(addr: usize) -> usize {
        let ret: usize;
        // SAFETY: Invokes the modeled Linux AArch64 `brk` syscall (`svc #0`, `x8 = 214`).
        unsafe {
            asm!(
                "svc #0",
                in("x8") SYS_BRK,
                inlateout("x0") addr => ret,
                options(nostack, preserves_flags)
            );
        }
        ret
    }

    /// Minimal `sbrk(increment)` built on `brk(0)` followed by `brk(old_brk + increment)`.
    #[inline(always)]
    pub unsafe fn sys_sbrk(increment: usize) -> *mut u8 {
        // SAFETY: Queries current program break via `brk(0)` and advances it by `increment`.
        let old_brk = unsafe { sys_brk(0) };
        let _new_brk = unsafe { sys_brk(old_brk.wrapping_add(increment)) };
        old_brk as *mut u8
    }

    /// Raw `mmap(addr, len, prot, flags, fd, offset)` syscall (`X8 = 222`).
    #[inline(always)]
    pub unsafe fn sys_mmap(
        addr: usize,
        len: usize,
        prot: usize,
        flags: usize,
        fd: isize,
        offset: usize,
    ) -> *mut u8 {
        let ret: usize;
        // SAFETY: Invokes the modeled Linux AArch64 `mmap` syscall (`svc #0`, `x8 = 222`).
        unsafe {
            asm!(
                "svc #0",
                in("x8") SYS_MMAP,
                inlateout("x0") addr => ret,
                in("x1") len,
                in("x2") prot,
                in("x3") flags,
                in("x4") fd as usize,
                in("x5") offset,
                options(nostack, preserves_flags)
            );
        }
        ret as *mut u8
    }

    /// Raw `exit(code)` syscall (`X8 = 93`).
    #[inline(always)]
    pub fn exit(code: u64) -> ! {
        // SAFETY: Terminates execution via Linux AArch64 `exit` (`svc #0`, `x8 = 93`).
        unsafe {
            asm!(
                "svc #0",
                in("x8") SYS_EXIT,
                in("x0") code,
                options(noreturn, nostack)
            )
        }
    }

    /// Raw `exit_group(code)` syscall (`X8 = 94`).
    #[inline(always)]
    pub fn exit_group(code: u64) -> ! {
        // SAFETY: Terminates execution via Linux AArch64 `exit_group` (`svc #0`, `x8 = 94`).
        unsafe {
            asm!(
                "svc #0",
                in("x8") SYS_EXIT_GROUP,
                in("x0") code,
                options(noreturn, nostack)
            )
        }
    }

    /// Safe wrapper around `write` to `stdout` (`fd = 1`).
    #[inline(always)]
    pub fn write_stdout(buf: &[u8]) -> usize {
        // SAFETY: `buf.as_ptr()` and `buf.len()` describe a valid byte slice.
        unsafe { sys_write(STDOUT_FILENO, buf.as_ptr(), buf.len()) }
    }

    /// Safe wrapper around `write` to `stderr` (`fd = 2`).
    #[inline(always)]
    pub fn write_stderr(buf: &[u8]) -> usize {
        // SAFETY: `buf.as_ptr()` and `buf.len()` describe a valid byte slice.
        unsafe { sys_write(STDERR_FILENO, buf.as_ptr(), buf.len()) }
    }

    /// Minimal `brk`/`sbrk` bump allocator returning a freshly allocated `[u8; N]` on the heap.
    #[inline(always)]
    pub fn sbrk_alloc<const N: usize>() -> &'static mut [u8; N] {
        // SAFETY: `sys_sbrk(N)` allocates `N` fresh bytes at the current program break.
        unsafe { &mut *(sys_sbrk(N) as *mut [u8; N]) }
    }

    /// Minimal `mmap` anonymous allocator returning a freshly mapped `[u8; N]`.
    #[inline(always)]
    pub fn mmap_alloc<const N: usize>() -> &'static mut [u8; N] {
        // SAFETY: `sys_mmap` maps a fresh `N`-byte anonymous read/write region at `mmapBase`.
        unsafe {
            let ptr = sys_mmap(
                0,
                N,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS,
                -1,
                0,
            );
            &mut *(ptr as *mut [u8; N])
        }
    }

    /// Pair of 2-byte buffers allocated contiguously via `mmap`.
    #[repr(C)]
    pub struct DualBuf {
        pub out: [u8; 2],
        pub err: [u8; 2],
    }

    /// Minimal `mmap` allocator for a `DualBuf` (4 bytes total).
    #[inline(always)]
    pub fn mmap_alloc_dual() -> &'static mut DualBuf {
        // SAFETY: `DualBuf` has size 4 and alignment 1; `sys_mmap` maps 4 fresh bytes at `mmapBase`.
        unsafe {
            let ptr = sys_mmap(
                0,
                core::mem::size_of::<DualBuf>(),
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS,
                -1,
                0,
            );
            &mut *(ptr as *mut DualBuf)
        }
    }
}

/// Verified safe Rust application functions (`#[forbid(unsafe_code)]`) exercising
/// `brk`/`sbrk`, `mmap`, `write` (to both `stdout` and `stderr`), `exit`, and `exit_group`.
#[forbid(unsafe_code)]
pub mod app {
    use super::sys::{exit, exit_group, mmap_alloc, mmap_alloc_dual, sbrk_alloc, write_stderr, write_stdout};

    /// 1. Allocates a 4-byte buffer using the minimal `brk`/`sbrk` bump allocator,
    ///    populates `['O', 'K', ':', tag]` in safe Rust, and writes it to `stdout` (`fd = 1`).
    #[inline(never)]
    pub fn brk_alloc_and_write(tag: u8) -> usize {
        let buf = sbrk_alloc::<4>();
        buf[0] = b'O';
        buf[1] = b'K';
        buf[2] = b':';
        buf[3] = tag;
        write_stdout(buf)
    }

    /// 2. Allocates a 4-byte `DualBuf` via `mmap`, formats `[a, b]` for `stdout` (`fd = 1`)
    ///    and `[a + b, a ^ b]` for `stderr` (`fd = 2`), writes both streams, and returns
    ///    the total byte count written (`4`).
    #[inline(never)]
    pub fn mmap_alloc_and_log_dual(a: u8, b: u8) -> usize {
        let buf = mmap_alloc_dual();
        buf.out[0] = a;
        buf.out[1] = b;
        buf.err[0] = a.wrapping_add(b);
        buf.err[1] = a ^ b;
        let n_out = write_stdout(&buf.out);
        let n_err = write_stderr(&buf.err);
        n_out.wrapping_add(n_err)
    }

    /// 3. Allocates a 2-byte buffer via `sbrk`, writes `[val, val + 1]` to `stdout`,
    ///    and terminates the process with exit code `0` via `exit` (`SYS_EXIT = 93`).
    #[inline(never)]
    pub fn alloc_write_and_exit(val: u8) -> ! {
        let buf = sbrk_alloc::<2>();
        buf[0] = val;
        buf[1] = val.wrapping_add(1);
        let _ = write_stdout(buf);
        exit(0)
    }

    /// 4. Allocates a 2-byte buffer via `mmap`, writes `['!', err_byte]` to `stderr`,
    ///    and terminates the process group with `code` via `exit_group` (`SYS_EXIT_GROUP = 94`).
    #[inline(never)]
    pub fn mmap_stderr_and_exit_group(err_byte: u8, code: u64) -> ! {
        let buf = mmap_alloc::<2>();
        buf[0] = b'!';
        buf[1] = err_byte;
        let _ = write_stderr(buf);
        exit_group(code)
    }

    /// 5. Divides `a` by `b` in safe Rust (`assert!(b != 0); a / b`), returning `a / b`
    ///    when `b != 0` and aborting via `panic!` (process exit code `101`) when `b == 0`.
    #[inline(never)]
    pub fn checked_div_or_panic(a: u64, b: u64) -> u64 {
        assert!(b != 0);
        a / b
    }

    /// 6. Indexes `s[idx]` in safe Rust, returning the `u64` element at `idx` when
    ///    `idx < s.len()` and aborting via `panic!` (process exit code `101`) when `idx >= s.len()`.
    #[inline(never)]
    pub fn slice_get_or_panic(s: &[u64], idx: usize) -> u64 {
        s[idx]
    }
}

pub use app::*;
