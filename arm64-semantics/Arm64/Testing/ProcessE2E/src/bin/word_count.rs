// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `word_count`: `#![no_main]` Rust `std` on static musl counting lines, ASCII words, and bytes.

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
    let mut input = Vec::new();
    if io::stdin().read_to_end(&mut input).is_err() {
        return 2;
    }
    let lines = input.iter().filter(|&&b| b == b'\n').count();
    let mut words = 0usize;
    let mut in_word = false;
    for &b in &input {
        if b.is_ascii_whitespace() {
            in_word = false;
        } else if !in_word {
            in_word = true;
            words += 1;
        }
    }
    let bytes = input.len();
    let mut out = io::stdout();
    if writeln!(out, "{lines} {words} {bytes}")
        .and_then(|()| out.flush())
        .is_err()
    {
        return 2;
    }
    0
}
