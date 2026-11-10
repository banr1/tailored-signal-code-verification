// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `nostd_minimal`: zero-libc `#![no_std]` static AArch64 ELF binary with custom `_start`.
//!
//! Reads `argc`, `argv`, `envp` directly from the Linux initial stack frame (`SP`), probes
//! `SYS_brk`, optionally reads `stdin` and writes to `stdout` / `stderr`, and exits via
//! `SYS_exit_group`. Compact enough (~4 KiB) to run quickly under the unaccelerated reference
//! `Arm64.Process.runElf` (`runSteps Program.pureMem`) as well as `runElfByteArrayFast` and QEMU.

#![no_std]
#![no_main]

use core::arch::{asm, global_asm};
use core::panic::PanicInfo;

const SYS_READ: usize = 63;
const SYS_WRITE: usize = 64;
const SYS_EXIT_GROUP: usize = 94;
const SYS_BRK: usize = 214;

global_asm!(
    ".global _start",
    "_start:",
    "mov x0, sp",
    "bl rust_entry",
    "brk #0",
);

#[inline(always)]
unsafe fn sys1(nr: usize, a0: usize) -> isize {
    let ret: isize;
    unsafe {
        asm!("svc #0", in("x8") nr, inout("x0") a0 => ret, options(nostack));
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

unsafe fn exit_group(code: i32) -> ! {
    let _ = unsafe { sys1(SYS_EXIT_GROUP, code as usize) };
    loop {
        unsafe { asm!("udf #0", options(nomem, nostack)) };
    }
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

unsafe fn cstr_slice(p: *const u8) -> &'static [u8] {
    let mut len = 0usize;
    while unsafe { *p.add(len) } != 0 {
        len += 1;
    }
    unsafe { core::slice::from_raw_parts(p, len) }
}

fn push_usize_dec(out: &mut [u8; 32], mut v: usize) -> &[u8] {
    if v == 0 {
        out[31] = b'0';
        return &out[31..32];
    }
    let mut pos = 32;
    while v > 0 {
        pos -= 1;
        out[pos] = b'0' + (v % 10) as u8;
        v /= 10;
    }
    &out[pos..32]
}

#[unsafe(no_mangle)]
extern "C" fn rust_entry(sp: *const usize) -> ! {
    let argc = unsafe { *sp };
    let argv = unsafe { sp.add(1) as *const *const u8 };
    let envp = unsafe { sp.add(1 + argc + 1) as *const *const u8 };
    let mut envc = 0usize;
    while unsafe { !(*envp.add(envc)).is_null() } {
        envc += 1;
    }

    let mode: &[u8] = if argc >= 2 {
        unsafe { cstr_slice(*argv.add(1)) }
    } else {
        b"echo"
    };

    if mode == b"exit7" {
        unsafe { exit_group(7) };
    }
    if mode == b"stderr" {
        write_all_fd(1, b"nostd-out\n");
        write_all_fd(2, b"nostd-err\n");
        unsafe { exit_group(2) };
    }
    if mode == b"meta" {
        let mut scratch = [0u8; 32];
        write_all_fd(1, b"argc=");
        write_all_fd(1, push_usize_dec(&mut scratch, argc));
        write_all_fd(1, b" envc=");
        write_all_fd(1, push_usize_dec(&mut scratch, envc));
        write_all_fd(1, b"\n");
        unsafe { exit_group(0) };
    }

    // Default `"echo"`: grow `brk` by one page, copy `stdin` through heap memory to `stdout`.
    let base = unsafe { sys1(SYS_BRK, 0) } as usize;
    let grown = unsafe { sys1(SYS_BRK, base + 4096) } as usize;
    if grown < base + 4096 {
        unsafe { exit_group(99) };
    }
    let heap_buf = unsafe { core::slice::from_raw_parts_mut(base as *mut u8, 4096) };
    loop {
        let n = unsafe { sys3(SYS_READ, 0, heap_buf.as_mut_ptr() as usize, heap_buf.len()) };
        if n <= 0 {
            break;
        }
        write_all_fd(1, &heap_buf[..n as usize]);
    }
    unsafe { exit_group(0) };
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
pub extern "C" fn rust_eh_personality() {}

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    unsafe { asm!("udf #0", options(noreturn)) }
}
