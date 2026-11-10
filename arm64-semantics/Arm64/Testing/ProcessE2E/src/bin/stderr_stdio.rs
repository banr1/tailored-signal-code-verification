// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `stderr_stdio`: `#![no_main]` Rust `std` on static musl interleaving writes to `stdout` (`fd 1`)
//! and `stderr` (`fd 2`).

#![no_main]

#[path = "../common.rs"]
mod common;

use common::{BrkMmapAlloc, read_args};
use std::ffi::{c_char, c_int};
use std::io::{self, Read, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let args = unsafe { read_args(argc, argv) };
    let mode = args.get(1).copied().unwrap_or(b"interleave");
    let mut input = Vec::new();
    let _ = io::stdin().read_to_end(&mut input);

    let mut out = io::stdout();
    let mut err = io::stderr();

    if mode == b"fail-stderr" {
        let _ = writeln!(err, "fatal: rejected payload of {} bytes", input.len());
        let _ = err.flush();
        return 1;
    }
    if mode == b"panic-fmt" {
        let mut heap_tag = String::from("alpha");
        heap_tag.push_str("-heap");
        panic!("formatted panic: len={} tag={}", input.len(), heap_tag);
    }
    if mode == b"abort-flush" {
        let _ = out.write_all(b"before-abort\n");
        let _ = out.flush();
        std::process::abort();
    }

    for (idx, line) in input.split(|&b| b == b'\n').enumerate() {
        if line.is_empty() {
            continue;
        }
        if idx % 2 == 0 {
            let _ = out.write_all(b"out:");
            let _ = out.write_all(line);
            let _ = out.write_all(b"\n");
            let _ = out.flush();
        } else {
            let _ = err.write_all(b"err:");
            let _ = err.write_all(line);
            let _ = err.write_all(b"\n");
            let _ = err.flush();
        }
    }
    0
}
