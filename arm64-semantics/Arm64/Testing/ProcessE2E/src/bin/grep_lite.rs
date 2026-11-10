// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `grep_lite`: `#![no_main]` Rust `std` on static musl implementing fixed-string `grep`.
//!
//! `grep_lite [-i] [-v] [-n] [-c] PATTERN < input` filters `stdin` lines containing `PATTERN`
//! (`-i`: ASCII case-insensitive, `-v`: invert, `-n`: `lineno:` prefix, `-c`: print count only).
//! Exit status follows POSIX `grep`: `0` if any line was selected, `1` if none, `2` on usage error.

#![no_main]

#[path = "../common.rs"]
mod common;

use common::{BrkMmapAlloc, read_args};
use std::ffi::{c_char, c_int};
use std::io::{self, Read, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

fn contains(hay: &[u8], needle: &[u8], fold: bool) -> bool {
    if needle.is_empty() {
        return true;
    }
    hay.windows(needle.len()).any(|w| {
        if fold {
            w.eq_ignore_ascii_case(needle)
        } else {
            w == needle
        }
    })
}

#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let args = unsafe { read_args(argc, argv) };
    let (mut fold, mut invert, mut number, mut count) = (false, false, false, false);
    let mut pattern: Option<&[u8]> = None;
    let mut usage_error = false;
    for a in args.iter().skip(1) {
        match (*a, pattern) {
            (b"-i", None) => fold = true,
            (b"-v", None) => invert = true,
            (b"-n", None) => number = true,
            (b"-c", None) => count = true,
            (p, None) if !p.starts_with(b"-") => pattern = Some(p),
            _ => usage_error = true,
        }
    }
    let Some(pattern) = pattern.filter(|_| !usage_error) else {
        let _ = io::stderr().write_all(b"usage: grep_lite [-i] [-v] [-n] [-c] PATTERN < input\n");
        return 2;
    };
    let mut input = Vec::new();
    if io::stdin().read_to_end(&mut input).is_err() {
        return 2;
    }
    let body = input.strip_suffix(b"\n").unwrap_or(&input);
    let mut text = Vec::new();
    let mut selected = 0usize;
    if !input.is_empty() {
        for (i, line) in body.split(|&b| b == b'\n').enumerate() {
            if contains(line, pattern, fold) != invert {
                selected += 1;
                if !count {
                    if number {
                        let _ = write!(text, "{}:", i + 1);
                    }
                    text.extend_from_slice(line);
                    text.push(b'\n');
                }
            }
        }
    }
    if count {
        let _ = writeln!(text, "{selected}");
    }
    let mut out = io::stdout();
    if out.write_all(&text).and_then(|()| out.flush()).is_err() {
        return 2;
    }
    if selected > 0 { 0 } else { 1 }
}
