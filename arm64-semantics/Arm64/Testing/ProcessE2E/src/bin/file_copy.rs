// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `file_copy`: `#![no_main]` Rust `std` on static musl copying regular files in `cwd` with stock
//! `std::fs` (`openat` + `fcntl(F_SETFD)` + `fstat` + `read` / `write` + `close`).
//!
//! - `file_copy cp SRC DST`: `fs::read(SRC)`, `fs::write(DST)`, then re-open `DST` with
//!   `File::open` + `read_to_end` and verify the bytes match.
//! - `file_copy upper SRC DST`: as `cp`, but ASCII-uppercases the contents.
//! - `file_copy cat FILE...`: print each file with a `==> FILE (N bytes) <==` header; a missing file
//!   reports the `io::Error` on `stderr`, continues, and exits `1`.

#![no_main]

#[path = "../common.rs"]
mod common;

use common::{BrkMmapAlloc, read_args};
use std::ffi::{c_char, c_int};
use std::fs::{self, File};
use std::io::{self, Read, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

fn fnv1a(data: &[u8]) -> u64 {
    data.iter().fold(0xcbf29ce484222325u64, |h, &b| {
        (h ^ b as u64).wrapping_mul(0x100000001b3)
    })
}

fn copy(src: &str, dst: &str, upper: bool) -> io::Result<String> {
    let mut data = fs::read(src)?;
    if upper {
        data.make_ascii_uppercase();
    }
    fs::write(dst, &data)?;
    let mut back = Vec::new();
    File::open(dst)?.read_to_end(&mut back)?;
    if back != data {
        return Err(io::Error::other("read-back mismatch"));
    }
    Ok(format!(
        "{src} -> {dst}: {} bytes fnv1a=0x{:016x}\n",
        data.len(),
        fnv1a(&back)
    ))
}

#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let args = unsafe { read_args(argc, argv) };
    let strs: Vec<String> = args
        .iter()
        .map(|a| String::from_utf8_lossy(a).into_owned())
        .collect();
    let mut out = io::stdout();
    let mut err = io::stderr();
    let code = match strs
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .as_slice()
    {
        [_, mode @ ("cp" | "upper"), src, dst] => match copy(src, dst, *mode == "upper") {
            Ok(line) => {
                let _ = out.write_all(line.as_bytes());
                0
            }
            Err(e) => {
                let _ = writeln!(err, "file_copy: {src} -> {dst}: {e}");
                1
            }
        },
        [_, "cat", files @ ..] if !files.is_empty() => {
            let mut code = 0;
            for f in files {
                match fs::read(f) {
                    Ok(data) => {
                        let _ = writeln!(out, "==> {f} ({} bytes) <==", data.len());
                        let _ = out.write_all(&data);
                    }
                    Err(e) => {
                        let _ = out.flush();
                        let _ = writeln!(err, "file_copy: {f}: {e}");
                        code = 1;
                    }
                }
            }
            code
        }
        _ => {
            let _ = writeln!(err, "usage: file_copy cp|upper SRC DST | cat FILE...");
            2
        }
    };
    if out.flush().is_err() {
        return 2;
    }
    code
}
