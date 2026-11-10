// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `echo_cat`: `#![no_main]` Rust `std` on static musl echoing all of `stdin` to `stdout`.

#![no_main]

#[path = "../common.rs"]
mod common;

use common::BrkMmapAlloc;
use std::ffi::{c_char, c_int};
use std::io::{self, Read, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

#[unsafe(no_mangle)]
extern "C" fn main(_argc: c_int, _argv: *const *const c_char) -> c_int {
    let mut buf = Vec::new();
    if io::stdin().read_to_end(&mut buf).is_err() {
        return 2;
    }
    let mut out = io::stdout();
    if out.write_all(&buf).and_then(|()| out.flush()).is_err() {
        return 2;
    }
    0
}
