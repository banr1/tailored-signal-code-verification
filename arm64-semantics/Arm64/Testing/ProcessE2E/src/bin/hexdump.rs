// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `hexdump`: `#![no_main]` Rust `std` on static musl reproducing `hexdump -C` canonical output.
//!
//! Prints 16-byte rows (`%08x` offset, two 8-byte hex groups, `|ascii|` gutter), collapses runs of
//! identical rows into a single `*` line (disabled by `-v`), and ends with the total length.

#![no_main]

#[path = "../common.rs"]
mod common;

use common::{BrkMmapAlloc, read_args};
use std::ffi::{c_char, c_int};
use std::fmt::Write as _;
use std::io::{self, Read, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

fn render(input: &[u8], squeeze: bool) -> String {
    let mut out = String::with_capacity(input.len() * 5 + 16);
    let mut prev: Option<&[u8]> = None;
    let mut starred = false;
    for (row, chunk) in input.chunks(16).enumerate() {
        let off = row * 16;
        if squeeze && chunk.len() == 16 && prev == Some(chunk) {
            if !starred {
                out.push_str("*\n");
                starred = true;
            }
            continue;
        }
        starred = false;
        prev = Some(chunk);
        let _ = write!(out, "{off:08x} ");
        for i in 0..16 {
            if i == 8 {
                out.push(' ');
            }
            match chunk.get(i) {
                Some(b) => {
                    let _ = write!(out, " {b:02x}");
                }
                None => out.push_str("   "),
            }
        }
        out.push_str("  |");
        for &b in chunk {
            out.push(if (0x20..0x7f).contains(&b) {
                b as char
            } else {
                '.'
            });
        }
        out.push_str("|\n");
    }
    if !input.is_empty() {
        let _ = writeln!(out, "{:08x}", input.len());
    }
    out
}

#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let args = unsafe { read_args(argc, argv) };
    let mut squeeze = true;
    for a in args.iter().skip(1) {
        if *a == b"-v" {
            squeeze = false;
        } else {
            let mut err = io::stderr();
            let _ = err.write_all(b"hexdump: unknown option '");
            let _ = err.write_all(a);
            let _ = err.write_all(b"'\n");
            return 2;
        }
    }
    let mut input = Vec::new();
    if io::stdin().read_to_end(&mut input).is_err() {
        return 2;
    }
    let text = render(&input, squeeze);
    let mut out = io::stdout();
    if out
        .write_all(text.as_bytes())
        .and_then(|()| out.flush())
        .is_err()
    {
        return 2;
    }
    0
}
