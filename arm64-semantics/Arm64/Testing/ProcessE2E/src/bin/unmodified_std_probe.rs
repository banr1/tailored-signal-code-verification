// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `unmodified_std_probe`: `#![no_main]` Rust `std` on stock static musl with ZERO allocator or
//! syscall shims, isolating each exact trap or divergence encountered by unmodified `std` code:
//! - `"fs"`     -> `std::fs::File::open("coins")` + `Read::read` + `std::fs::File::create("out")` +
//!                 `Write::write_all` on a stack buffer with zero custom allocator/shims (exercises
//!                 `SYS_openat(..., O_CLOEXEC)` + `SYS_fcntl(fd, F_SETFD, FD_CLOEXEC)` + `SYS_read` +
//!                 `SYS_write` + `SYS_close` end-to-end).
//! - `"malloc"` -> `Vec::<u8>::with_capacity(64)` using stock musl `mallocng` (traps at `SYS_mmap = 222`
//!                 with `PROT_NONE = 0` and `MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED = 0x32`).
//! - `"panic"`  -> `panic!("boom from process e2e probe")` (QEMU writes panic message & dies with
//!                 `SIGABRT`; Lean traps at `SYS_gettid = 178` before writing `stderr`).
//! - `"abort"`  -> `std::process::abort()` (QEMU dies with `SIGABRT`; Lean traps at
//!                 `SYS_rt_sigprocmask = 135`).
//! - `"udf"`    -> `asm!("udf #0")` (`core::intrinsics::abort`: QEMU `SIGILL`; Lean `decode 0 = none` -> `.Halted`).
//! - `"udf1"`   -> `asm!("udf #1")` (non-zero `UDF #imm16`: QEMU `SIGILL`; Lean `.Exception "udf"`).
//! - `"brk1"`   -> `asm!("brk #1")` (DIVERGENCE: QEMU dies with `SIGTRAP`; Lean cleanly exits `101`!).
//! - `"brk0"`   -> `asm!("brk #0")` (QEMU dies with `SIGTRAP`; Lean transitions to `.Halted`).

#![no_main]

use core::arch::asm;
use core::ffi::{CStr, c_char, c_int};
use core::hint::black_box;

#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let mode: &[u8] = if argc >= 2 {
        unsafe { CStr::from_ptr(*argv.add(1)) }.to_bytes()
    } else {
        b"fs"
    };

    match mode {
        b"fs" => {
            use std::io::{Read, Write};
            let mut buf = [0u8; 64];
            let Ok(mut in_file) = std::fs::File::open("coins") else {
                return 2;
            };
            let Ok(n) = in_file.read(&mut buf) else {
                return 2;
            };
            let Ok(mut out_file) = std::fs::File::create("out") else {
                return 2;
            };
            if out_file.write_all(&buf[..n]).is_err() {
                return 2;
            }
            0
        }
        b"malloc" => {
            let mut v: Vec<u8> = Vec::with_capacity(64);
            v.extend_from_slice(b"hello mallocng");
            black_box(&v);
            0
        }
        b"panic" => {
            panic!("boom from process e2e probe");
        }
        b"abort" => {
            std::process::abort();
        }
        b"udf" => unsafe {
            asm!("udf #0", options(noreturn));
        },
        b"udf1" => unsafe {
            asm!("udf #1", options(noreturn));
        },
        b"brk1" => unsafe {
            asm!("brk #1", options(noreturn));
        },
        b"brk0" => unsafe {
            asm!("brk #0", options(noreturn));
        },
        _ => 2,
    }
}
