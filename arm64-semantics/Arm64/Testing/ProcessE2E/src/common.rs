// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Shared runtime support for `#![no_main]` static `aarch64-unknown-linux-musl` process e2e binaries.
//!
//! Provides:
//! 1. `BrkMmapAlloc`: a `#[global_allocator]` backed exclusively by `SYS_brk` (`214`), anonymous
//!    private RW `SYS_mmap` (`222`), and `SYS_munmap` (`215`), avoiding musl `mallocng`'s
//!    `mmap(..., PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED)` guard-page call.
//! 2. `read_args` / `read_envp`: safe wrappers around `argc`, `argv`, and musl's `environ`.
//! 3. `open_read_no_cloexec` / `open_write_trunc_no_cloexec`: `std::fs::File` constructors calling
//!    `SYS_openat` (`56`) without `O_CLOEXEC` so musl's `open()` wrapper never emits `SYS_fcntl`
//!    (`F_SETFD`), allowing `std::fs::File` (`fstat`, `read`, `write`, `close`) to run cleanly.

#![allow(dead_code)]

use core::alloc::{GlobalAlloc, Layout};
use core::arch::asm;
use core::ffi::{CStr, c_char, c_int};
use core::ptr;
use core::sync::atomic::{AtomicUsize, Ordering};
use std::fs::File;
use std::io;
use std::os::fd::FromRawFd;

pub const SYS_OPENAT: usize = 56;
pub const SYS_GETRANDOM: usize = 278;
pub const SYS_BRK: usize = 214;
pub const SYS_MUNMAP: usize = 215;
pub const SYS_MMAP: usize = 222;

pub const AT_FDCWD: isize = -100;
pub const O_RDONLY: usize = 0;
pub const O_WRONLY: usize = 1;
pub const O_CREAT: usize = 0x40;
pub const O_TRUNC: usize = 0x200;
pub const O_LARGEFILE: usize = 0x20000;

const PAGE_SIZE: usize = 4096;
const BRK_CHUNK: usize = 64 * 1024;
const MMAP_THRESHOLD: usize = 16 * 1024;
const PROT_RW: usize = 0x3;
const MAP_PRIVATE_ANON: usize = 0x22;

#[inline(always)]
pub unsafe fn syscall1(nr: usize, a0: usize) -> isize {
    let ret: isize;
    unsafe {
        asm!(
            "svc #0",
            in("x8") nr,
            inout("x0") a0 => ret,
            options(nostack)
        );
    }
    ret
}

#[inline(always)]
pub unsafe fn syscall2(nr: usize, a0: usize, a1: usize) -> isize {
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
pub unsafe fn syscall3(nr: usize, a0: usize, a1: usize, a2: usize) -> isize {
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
pub unsafe fn syscall4(nr: usize, a0: usize, a1: usize, a2: usize, a3: usize) -> isize {
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
pub unsafe fn syscall6(
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

#[inline]
const fn align_up(x: usize, align: usize) -> usize {
    (x + (align - 1)) & !(align - 1)
}

/// Single-threaded process allocator:
/// - Small allocations (`<= 16 KiB` with `align <= 4096`) bump-allocate out of `SYS_brk` chunks,
///   falling back to anonymous `SYS_mmap` if `brk` is declined.
/// - Large allocations (`> 16 KiB` or `align > 4096`) map anonymous private RW pages via
///   `SYS_mmap` and release them via `SYS_munmap` on `dealloc`.
pub struct BrkMmapAlloc {
    cur: AtomicUsize,
    end: AtomicUsize,
}

impl BrkMmapAlloc {
    pub const fn new() -> Self {
        Self {
            cur: AtomicUsize::new(0),
            end: AtomicUsize::new(0),
        }
    }

    unsafe fn mmap_anon(bytes: usize) -> *mut u8 {
        let len = align_up(bytes.max(PAGE_SIZE), PAGE_SIZE);
        let ret = unsafe {
            syscall6(
                SYS_MMAP,
                0,
                len,
                PROT_RW,
                MAP_PRIVATE_ANON,
                usize::MAX,
                0,
            )
        };
        if ret <= 0 && ret > -4096 {
            ptr::null_mut()
        } else {
            ret as usize as *mut u8
        }
    }
}

unsafe impl GlobalAlloc for BrkMmapAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let size = layout.size().max(1);
        let align = layout.align().max(8);
        if size > MMAP_THRESHOLD || align > PAGE_SIZE {
            if align > PAGE_SIZE {
                return ptr::null_mut();
            }
            return unsafe { Self::mmap_anon(size) };
        }
        let mut cur = self.cur.load(Ordering::Relaxed);
        let mut end = self.end.load(Ordering::Relaxed);
        if cur == 0 {
            let base = unsafe { syscall1(SYS_BRK, 0) } as usize;
            cur = base;
            end = base;
            self.cur.store(cur, Ordering::Relaxed);
            self.end.store(end, Ordering::Relaxed);
        }
        let aligned = align_up(cur, align);
        let Some(next) = aligned.checked_add(size) else {
            return ptr::null_mut();
        };
        if next <= end {
            self.cur.store(next, Ordering::Relaxed);
            return aligned as *mut u8;
        }
        let grow = align_up(next - end, BRK_CHUNK);
        if let Some(target_end) = end.checked_add(grow) {
            let got = unsafe { syscall1(SYS_BRK, target_end) } as usize;
            if got >= target_end {
                self.cur.store(next, Ordering::Relaxed);
                self.end.store(got, Ordering::Relaxed);
                return aligned as *mut u8;
            }
        }
        unsafe { Self::mmap_anon(size) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let size = layout.size().max(1);
        let align = layout.align().max(8);
        if (size > MMAP_THRESHOLD || align > PAGE_SIZE)
            && (ptr as usize).is_multiple_of(PAGE_SIZE)
        {
            let len = align_up(size.max(PAGE_SIZE), PAGE_SIZE);
            let _ = unsafe { syscall2(SYS_MUNMAP, ptr as usize, len) };
        }
    }
}

unsafe extern "C" {
    static environ: *const *const c_char;
}

/// Collect `argv[0..argc]` as byte slices without NUL terminators.
pub unsafe fn read_args(argc: c_int, argv: *const *const c_char) -> Vec<&'static [u8]> {
    let n = argc.max(0) as usize;
    let mut out = Vec::with_capacity(n);
    for i in 0..n {
        let p = unsafe { *argv.add(i) };
        if !p.is_null() {
            out.push(unsafe { CStr::from_ptr(p) }.to_bytes());
        }
    }
    out
}

/// Collect `environ` entries until the trailing NULL pointer.
pub unsafe fn read_envp() -> Vec<&'static [u8]> {
    let mut out = Vec::new();
    let mut cur = unsafe { environ };
    if cur.is_null() {
        return out;
    }
    while unsafe { !(*cur).is_null() } {
        let p = unsafe { *cur };
        out.push(unsafe { CStr::from_ptr(p) }.to_bytes());
        cur = unsafe { cur.add(1) };
    }
    out
}

fn c_path(path: &str) -> io::Result<Vec<u8>> {
    if path.as_bytes().contains(&0) {
        return Err(io::Error::from_raw_os_error(22));
    }
    let mut buf = Vec::with_capacity(path.len() + 1);
    buf.extend_from_slice(path.as_bytes());
    buf.push(0);
    Ok(buf)
}

/// Open `path` relative to `AT_FDCWD` for reading WITHOUT `O_CLOEXEC` (avoiding musl `fcntl`).
pub fn open_read_no_cloexec(path: &str) -> io::Result<File> {
    let raw = c_path(path)?;
    let rc = unsafe {
        syscall4(
            SYS_OPENAT,
            AT_FDCWD as usize,
            raw.as_ptr() as usize,
            O_RDONLY | O_LARGEFILE,
            0,
        )
    };
    if rc < 0 {
        Err(io::Error::from_raw_os_error((-rc) as i32))
    } else {
        Ok(unsafe { File::from_raw_fd(rc as i32) })
    }
}

/// Open/create/truncate `path` relative to `AT_FDCWD` for writing WITHOUT `O_CLOEXEC`.
pub fn open_write_trunc_no_cloexec(path: &str) -> io::Result<File> {
    let raw = c_path(path)?;
    let rc = unsafe {
        syscall4(
            SYS_OPENAT,
            AT_FDCWD as usize,
            raw.as_ptr() as usize,
            O_WRONLY | O_CREAT | O_TRUNC | O_LARGEFILE,
            0o666,
        )
    };
    if rc < 0 {
        Err(io::Error::from_raw_os_error((-rc) as i32))
    } else {
        Ok(unsafe { File::from_raw_fd(rc as i32) })
    }
}
