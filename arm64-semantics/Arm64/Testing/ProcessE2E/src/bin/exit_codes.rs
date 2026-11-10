// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `exit_codes`: `#![no_main]` Rust `std` on static `aarch64-unknown-linux-musl` testing exit codes.

#![no_main]

#[path = "../common.rs"]
mod common;

use common::{BrkMmapAlloc, read_args};
use std::ffi::{c_char, c_int};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let args = unsafe { read_args(argc, argv) };
    match args.get(1).copied() {
        Some(b"ok") => 0,
        Some(b"reject") => 1,
        Some(b"bad-args") | None => 2,
        Some(b"code") => args
            .get(2)
            .and_then(|s| core::str::from_utf8(s).ok())
            .and_then(|s| s.parse::<i32>().ok())
            .unwrap_or(2),
        _ => 2,
    }
}
