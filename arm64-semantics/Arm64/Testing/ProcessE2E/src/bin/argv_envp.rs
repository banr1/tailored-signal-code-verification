// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `argv_envp`: `#![no_main]` Rust `std` on static musl printing `argc`, `argv[i]`, `envc`,
//! and musl `environ[j]` in order.

#![no_main]

#[path = "../common.rs"]
mod common;

use common::{BrkMmapAlloc, read_args, read_envp};
use std::ffi::{c_char, c_int};
use std::io::{self, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let args = unsafe { read_args(argc, argv) };
    let envs = unsafe { read_envp() };
    let mut out = io::stdout();
    if writeln!(out, "argc={}", args.len()).is_err() {
        return 2;
    }
    for (i, a) in args.iter().enumerate() {
        if write!(out, "argv[{i}]=").is_err()
            || out.write_all(a).is_err()
            || out.write_all(b"\n").is_err()
        {
            return 2;
        }
    }
    if writeln!(out, "envc={}", envs.len()).is_err() {
        return 2;
    }
    for (j, e) in envs.iter().enumerate() {
        if write!(out, "env[{j}]=").is_err()
            || out.write_all(e).is_err()
            || out.write_all(b"\n").is_err()
        {
            return 2;
        }
    }
    if out.flush().is_err() {
        return 2;
    }
    0
}
