// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `matrix_mul`: `#![no_main]` Rust `std` on static musl multiplying two deterministic `N x N`
//! `i64` matrices (`N` from `argv[1]`, `1..=48`; seed from `argv[2]`, default `1`).
//!
//! Entries come from a 64-bit LCG reduced to `-1000..=1000`; the product uses wrapping
//! multiply-accumulate. Prints the trace, an FNV-1a checksum over all product entries, the first
//! product row (up to 8 entries), and checks `A * I == A`. Invalid arguments exit `2`.

#![no_main]

#[path = "../common.rs"]
mod common;

use common::{BrkMmapAlloc, read_args};
use std::ffi::{c_char, c_int};
use std::fmt::Write as _;
use std::io::{self, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> i64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((self.0 >> 33) % 2001) as i64 - 1000
    }
}

fn matmul(a: &[i64], b: &[i64], n: usize) -> Vec<i64> {
    let mut c = vec![0i64; n * n];
    for i in 0..n {
        for k in 0..n {
            let aik = a[i * n + k];
            for j in 0..n {
                c[i * n + j] = c[i * n + j].wrapping_add(aik.wrapping_mul(b[k * n + j]));
            }
        }
    }
    c
}

fn parse_arg(a: Option<&&[u8]>, default: u64) -> Option<u64> {
    match a {
        None => Some(default),
        Some(s) => core::str::from_utf8(s).ok()?.parse().ok(),
    }
}

#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let args = unsafe { read_args(argc, argv) };
    let (Some(n), Some(seed)) = (
        parse_arg(args.get(1), 8).filter(|n| (1..=48).contains(n)),
        parse_arg(args.get(2), 1),
    ) else {
        let _ = writeln!(io::stderr(), "usage: matrix_mul [N in 1..=48] [SEED]");
        return 2;
    };
    let n = n as usize;
    let mut rng = Lcg(seed);
    let a: Vec<i64> = (0..n * n).map(|_| rng.next()).collect();
    let b: Vec<i64> = (0..n * n).map(|_| rng.next()).collect();
    let c = matmul(&a, &b, n);
    let ident: Vec<i64> = (0..n * n)
        .map(|idx| i64::from(idx / n == idx % n))
        .collect();
    let identity_ok = matmul(&a, &ident, n) == a;

    let trace = (0..n).fold(0i64, |t, i| t.wrapping_add(c[i * n + i]));
    let mut h: u64 = 0xcbf29ce484222325;
    for v in &c {
        for byte in v.to_le_bytes() {
            h = (h ^ byte as u64).wrapping_mul(0x100000001b3);
        }
    }
    let mut text = String::new();
    let _ = writeln!(text, "n={n} seed={seed} trace={trace} fnv1a=0x{h:016x}");
    let row: Vec<String> = c[..n.min(8)].iter().map(i64::to_string).collect();
    let _ = writeln!(text, "row0=[{}]", row.join(","));
    let _ = writeln!(
        text,
        "identity={}",
        if identity_ok { "ok" } else { "MISMATCH" }
    );
    let mut out = io::stdout();
    if out
        .write_all(text.as_bytes())
        .and_then(|()| out.flush())
        .is_err()
    {
        return 2;
    }
    if identity_ok { 0 } else { 1 }
}
