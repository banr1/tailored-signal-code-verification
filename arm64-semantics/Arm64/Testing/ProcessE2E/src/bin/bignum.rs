// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `bignum`: `#![no_main]` Rust `std` on static musl computing arbitrary-precision naturals as
//! little-endian base-`10^9` `Vec<u32>` limbs (`u64` carries, `udiv`-heavy decimal printing).
//!
//! `bignum fact N`, `bignum fib N`, or `bignum pow2 N` (`N <= 2000`) prints the full decimal value
//! followed by `digits=<count> digit_sum=<sum>`. Missing, non-numeric, or out-of-range `N` reports
//! the error on `stderr` (`exit 2`).

#![no_main]

#[path = "../common.rs"]
mod common;

use common::{BrkMmapAlloc, read_args};
use std::ffi::{c_char, c_int};
use std::io::{self, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

const BASE: u64 = 1_000_000_000;

fn mul_small(a: &mut Vec<u32>, m: u32) {
    let mut carry: u64 = 0;
    for limb in a.iter_mut() {
        let v = (*limb as u64) * (m as u64) + carry;
        *limb = (v % BASE) as u32;
        carry = v / BASE;
    }
    while carry > 0 {
        a.push((carry % BASE) as u32);
        carry /= BASE;
    }
}

fn add(a: &[u32], b: &[u32]) -> Vec<u32> {
    let mut out = Vec::with_capacity(a.len().max(b.len()) + 1);
    let mut carry: u64 = 0;
    for i in 0..a.len().max(b.len()) {
        let v = *a.get(i).unwrap_or(&0) as u64 + *b.get(i).unwrap_or(&0) as u64 + carry;
        out.push((v % BASE) as u32);
        carry = v / BASE;
    }
    if carry > 0 {
        out.push(carry as u32);
    }
    out
}

fn to_decimal(a: &[u32]) -> String {
    let mut s = String::new();
    let mut limbs = a.iter().rev();
    if let Some(top) = limbs.next() {
        s.push_str(&top.to_string());
    }
    for limb in limbs {
        s.push_str(&format!("{limb:09}"));
    }
    s
}

fn compute(op: &[u8], n: u32) -> Option<Vec<u32>> {
    match op {
        b"fact" => {
            let mut acc = vec![1u32];
            for k in 2..=n {
                mul_small(&mut acc, k);
            }
            Some(acc)
        }
        b"fib" => {
            let (mut a, mut b) = (vec![0u32], vec![1u32]);
            for _ in 0..n {
                let c = add(&a, &b);
                a = core::mem::replace(&mut b, c);
            }
            Some(a)
        }
        b"pow2" => {
            let mut acc = vec![1u32];
            for _ in 0..n {
                mul_small(&mut acc, 2);
            }
            Some(acc)
        }
        _ => None,
    }
}

#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let args = unsafe { read_args(argc, argv) };
    let mut err = io::stderr();
    let (Some(op), Some(n_raw)) = (args.get(1), args.get(2)) else {
        let _ = writeln!(err, "usage: bignum fact|fib|pow2 N");
        return 2;
    };
    let n = match core::str::from_utf8(n_raw)
        .ok()
        .and_then(|s| s.parse::<u32>().ok())
    {
        Some(n) if n <= 2000 => n,
        _ => {
            let _ = writeln!(
                err,
                "bignum: N must be an integer in 0..=2000, got '{}'",
                String::from_utf8_lossy(n_raw)
            );
            return 2;
        }
    };
    let Some(value) = compute(op, n) else {
        let _ = writeln!(
            err,
            "bignum: unknown operation '{}'",
            String::from_utf8_lossy(op)
        );
        return 2;
    };
    let dec = to_decimal(&value);
    let digit_sum: u32 = dec.bytes().map(|b| (b - b'0') as u32).sum();
    let mut out = io::stdout();
    let text = format!("{dec}\ndigits={} digit_sum={digit_sum}\n", dec.len());
    if out
        .write_all(text.as_bytes())
        .and_then(|()| out.flush())
        .is_err()
    {
        return 2;
    }
    0
}
