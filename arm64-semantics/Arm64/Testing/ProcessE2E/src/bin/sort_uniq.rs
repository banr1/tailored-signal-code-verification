// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `sort_uniq`: `#![no_main]` Rust `std` on static musl emulating `sort | uniq -c`.
//!
//! Reads `stdin` lines (a missing trailing newline is tolerated), sorts them bytewise via
//! `slice::sort_unstable`, and prints `%7d <line>` per distinct line. `-r` reverses the order,
//! `-n` orders by descending count (ties broken bytewise), and `-d` prints only duplicated lines.

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
    let (mut reverse, mut by_count, mut dups_only) = (false, false, false);
    for a in args.iter().skip(1) {
        match *a {
            b"-r" => reverse = true,
            b"-n" => by_count = true,
            b"-d" => dups_only = true,
            _ => {
                let _ = io::stderr().write_all(b"usage: sort_uniq [-r] [-n] [-d] < input\n");
                return 2;
            }
        }
    }
    let mut input = Vec::new();
    if io::stdin().read_to_end(&mut input).is_err() {
        return 2;
    }
    let body = input.strip_suffix(b"\n").unwrap_or(&input);
    let mut lines: Vec<&[u8]> = if input.is_empty() {
        Vec::new()
    } else {
        body.split(|&b| b == b'\n').collect()
    };
    lines.sort_unstable();

    let mut groups: Vec<(usize, &[u8])> = Vec::new();
    for line in lines {
        match groups.last_mut() {
            Some((n, prev)) if *prev == line => *n += 1,
            _ => groups.push((1, line)),
        }
    }
    if by_count {
        groups.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(b.1)));
    }
    if reverse {
        groups.reverse();
    }

    let mut text = Vec::new();
    for (n, line) in groups.iter().filter(|g| !dups_only || g.0 > 1) {
        let _ = write!(text, "{n:7} ");
        text.extend_from_slice(line);
        text.push(b'\n');
    }
    let mut out = io::stdout();
    if out.write_all(&text).and_then(|()| out.flush()).is_err() {
        return 2;
    }
    0
}
