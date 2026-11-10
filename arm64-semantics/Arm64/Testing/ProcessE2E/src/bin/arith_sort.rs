// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `arith_sort`: `#![no_main]` Rust `std` on static musl parsing signed `i64` integers from
//! `stdin`, sorting via `slice::sort`, computing 64/128-bit sums & FNV-1a digest, and reporting
//! malformed input on `stderr` with exit code `2`.

#![no_main]

#[path = "../common.rs"]
mod common;

use common::BrkMmapAlloc;
use std::ffi::{c_char, c_int};
use std::io::{self, Read, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

fn fnv1a_i64s(xs: &[i64]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for &x in xs {
        for b in x.to_le_bytes() {
            h ^= b as u64;
            h = h.wrapping_mul(0x100000001b3);
        }
    }
    h
}

#[unsafe(no_mangle)]
extern "C" fn main(_argc: c_int, _argv: *const *const c_char) -> c_int {
    let mut raw = Vec::new();
    if io::stdin().read_to_end(&mut raw).is_err() {
        return 2;
    }
    let Ok(text) = core::str::from_utf8(&raw) else {
        let _ = io::stderr().write_all(b"error: invalid utf-8 input\n");
        let _ = io::stderr().flush();
        return 2;
    };
    let mut nums: Vec<i64> = Vec::new();
    for tok in text.split_ascii_whitespace() {
        match tok.parse::<i64>() {
            Ok(v) => nums.push(v),
            Err(_) => {
                let mut err = io::stderr();
                let _ = writeln!(err, "error: invalid integer '{tok}'");
                let _ = err.flush();
                return 2;
            }
        }
    }
    nums.sort();
    let wrap_sum: i64 = nums.iter().copied().fold(0i64, i64::wrapping_add);
    let wide_sum: i128 = nums.iter().map(|&x| x as i128).sum();
    let digest = fnv1a_i64s(&nums);

    let mut out = io::stdout();
    let _ = writeln!(
        out,
        "count={} wrap_sum={wrap_sum} wide_sum={wide_sum} fnv1a=0x{digest:016x}",
        nums.len()
    );
    let _ = write!(out, "sorted=[");
    for (i, &x) in nums.iter().enumerate() {
        if i > 0 {
            let _ = write!(out, ",");
        }
        let _ = write!(out, "{x}");
    }
    let _ = writeln!(out, "]");
    if out.flush().is_err() {
        return 2;
    }
    0
}
