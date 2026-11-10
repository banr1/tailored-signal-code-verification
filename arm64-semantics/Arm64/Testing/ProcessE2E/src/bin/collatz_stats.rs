// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `collatz_stats`: `#![no_main]` Rust `std` on static musl computing Collatz (`3n + 1`) chain
//! statistics over `[LO, HI]` from `argv` (`1 <= LO <= HI <= 100000`).
//!
//! Walks every chain with `u64::checked_mul` / `checked_add` (overflow exits `1`) and prints the
//! longest chain, the highest peak, the total step count, the median length (sorted `Vec<u32>`),
//! and a `BTreeMap` histogram of chain lengths bucketed by 25. Invalid ranges exit `2`.

#![no_main]

#[path = "../common.rs"]
mod common;

use common::{BrkMmapAlloc, read_args};
use std::collections::BTreeMap;
use std::ffi::{c_char, c_int};
use std::fmt::Write as _;
use std::io::{self, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

fn parse(a: Option<&&[u8]>) -> Option<u64> {
    core::str::from_utf8(a?).ok()?.parse().ok()
}

/// Returns `(steps, peak)` for the chain starting at `n`, or `None` on `u64` overflow.
fn chain(n: u64) -> Option<(u32, u64)> {
    let mut x = n;
    let mut steps = 0u32;
    let mut peak = n;
    while x != 1 {
        x = if x % 2 == 0 {
            x / 2
        } else {
            x.checked_mul(3)?.checked_add(1)?
        };
        peak = peak.max(x);
        steps += 1;
    }
    Some((steps, peak))
}

#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let args = unsafe { read_args(argc, argv) };
    let (Some(lo), Some(hi)) = (parse(args.get(1)), parse(args.get(2))) else {
        let _ = writeln!(io::stderr(), "usage: collatz_stats LO HI");
        return 2;
    };
    if lo == 0 || lo > hi || hi > 100_000 {
        let _ = writeln!(
            io::stderr(),
            "collatz_stats: need 1 <= LO <= HI <= 100000, got [{lo}, {hi}]"
        );
        return 2;
    }
    let mut lens: Vec<u32> = Vec::with_capacity((hi - lo + 1) as usize);
    let (mut best_n, mut best_len) = (lo, 0u32);
    let (mut peak_n, mut peak) = (lo, 0u64);
    let mut total: u64 = 0;
    let mut hist: BTreeMap<u32, u32> = BTreeMap::new();
    for n in lo..=hi {
        let Some((len, pk)) = chain(n) else {
            let _ = writeln!(io::stderr(), "collatz_stats: u64 overflow at n={n}");
            return 1;
        };
        if len > best_len {
            (best_n, best_len) = (n, len);
        }
        if pk > peak {
            (peak_n, peak) = (n, pk);
        }
        total += len as u64;
        lens.push(len);
        *hist.entry(len / 25 * 25).or_default() += 1;
    }
    lens.sort_unstable();
    let median = lens[lens.len() / 2];
    let mut text = String::new();
    let _ = writeln!(
        text,
        "range=[{lo},{hi}] longest={best_n}:{best_len} peak={peak_n}:{peak} total_steps={total} median={median}"
    );
    for (bucket, count) in &hist {
        let _ = writeln!(text, "{:>4}-{:<4} {count}", bucket, bucket + 24);
    }
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
