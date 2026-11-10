// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `getrandom_use`: `#![no_main]` Rust `std` on static musl testing `SYS_getrandom` (`278`):
//! - `"check"` mode validates return values across valid flags (`0`, `GRND_NONBLOCK`), zero-length
//!   reads, invalid flag bits (`-EINVAL`), mutually exclusive `GRND_RANDOM | GRND_INSECURE`
//!   (`-EINVAL`), and unmapped pointer (`-EFAULT`), producing 100% deterministic output.
//! - `"raw-hex"` mode prints 16 bytes returned by `getrandom` in hex, demonstrating host kernel
//!   entropy on Linux/QEMU vs deterministic `Oracle.getrandom` bytes in Lean `runElf`.

#![no_main]

#[path = "../common.rs"]
mod common;

use common::{BrkMmapAlloc, SYS_GETRANDOM, read_args, syscall3};
use std::ffi::{c_char, c_int};
use std::io::{self, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

const GRND_NONBLOCK: usize = 0x0001;
const GRND_RANDOM: usize = 0x0002;
const GRND_INSECURE: usize = 0x0004;

#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let args = unsafe { read_args(argc, argv) };
    let mode = args.get(1).copied().unwrap_or(b"check");
    let mut out = io::stdout();

    if mode == b"raw-hex" {
        let mut buf = [0u8; 16];
        let rc = unsafe { syscall3(SYS_GETRANDOM, buf.as_mut_ptr() as usize, buf.len(), 0) };
        if rc != 16 {
            return 2;
        }
        for b in buf {
            let _ = write!(out, "{b:02x}");
        }
        let _ = writeln!(out);
        let _ = out.flush();
        return 0;
    }

    let mut buf = [0xa5u8; 32];
    let r_full = unsafe { syscall3(SYS_GETRANDOM, buf.as_mut_ptr() as usize, 32, 0) };
    let r_nb = unsafe { syscall3(SYS_GETRANDOM, buf.as_mut_ptr() as usize, 16, GRND_NONBLOCK) };
    let r_zero = unsafe { syscall3(SYS_GETRANDOM, buf.as_mut_ptr() as usize, 0, 0) };
    let r_bad_flags = unsafe { syscall3(SYS_GETRANDOM, buf.as_mut_ptr() as usize, 16, 0xdead) };
    let r_excl_flags = unsafe {
        syscall3(
            SYS_GETRANDOM,
            buf.as_mut_ptr() as usize,
            16,
            GRND_RANDOM | GRND_INSECURE,
        )
    };
    let r_efault = unsafe { syscall3(SYS_GETRANDOM, 0, 16, 0) };

    let _ = writeln!(
        out,
        "full={r_full} nonblock={r_nb} zero={r_zero} bad_flags={r_bad_flags} excl_flags={r_excl_flags} efault={r_efault}"
    );
    let _ = out.flush();
    if r_full == 32
        && r_nb == 16
        && r_zero == 0
        && r_bad_flags == -22
        && r_excl_flags == -22
        && r_efault == -14
    {
        0
    } else {
        1
    }
}
