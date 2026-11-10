// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `rpn_calc`: `#![no_main]` Rust `std` on static musl evaluating one reverse-Polish `i64`
//! expression per `stdin` line.
//!
//! Supports `+ - * / %` (checked arithmetic), `neg`, `dup`, `swap`, `drop`, and `sum` (fold the
//! whole stack). Each non-blank line must leave exactly one value, printed as `<line>: <value>`.
//! The first error (stack underflow, division by zero, overflow, unknown token, or a leftover
//! stack) is reported on `stderr` with its line number after flushing earlier results (`exit 1`).

#![no_main]

#[path = "../common.rs"]
mod common;

use common::BrkMmapAlloc;
use std::ffi::{c_char, c_int};
use std::io::{self, Read, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

fn pop2(st: &mut Vec<i64>, op: &str) -> Result<(i64, i64), String> {
    let b = st
        .pop()
        .ok_or_else(|| format!("stack underflow at '{op}'"))?;
    let a = st
        .pop()
        .ok_or_else(|| format!("stack underflow at '{op}'"))?;
    Ok((a, b))
}

fn eval_line(line: &str) -> Result<i64, String> {
    let mut st: Vec<i64> = Vec::new();
    for tok in line.split_ascii_whitespace() {
        let overflow = || format!("overflow at '{tok}'");
        match tok {
            "+" | "-" | "*" | "/" | "%" => {
                let (a, b) = pop2(&mut st, tok)?;
                if (tok == "/" || tok == "%") && b == 0 {
                    return Err(format!("division by zero at '{tok}'"));
                }
                let r = match tok {
                    "+" => a.checked_add(b),
                    "-" => a.checked_sub(b),
                    "*" => a.checked_mul(b),
                    "/" => a.checked_div(b),
                    _ => a.checked_rem(b),
                };
                st.push(r.ok_or_else(overflow)?);
            }
            "neg" => {
                let a = st.pop().ok_or("stack underflow at 'neg'")?;
                st.push(a.checked_neg().ok_or_else(overflow)?);
            }
            "dup" => {
                let a = *st.last().ok_or("stack underflow at 'dup'")?;
                st.push(a);
            }
            "swap" => {
                let (a, b) = pop2(&mut st, tok)?;
                st.push(b);
                st.push(a);
            }
            "drop" => {
                st.pop().ok_or("stack underflow at 'drop'")?;
            }
            "sum" => {
                let mut acc: i64 = 0;
                for v in st.drain(..) {
                    acc = acc.checked_add(v).ok_or_else(overflow)?;
                }
                st.push(acc);
            }
            _ => {
                let v = tok
                    .parse::<i64>()
                    .map_err(|_| format!("unknown token '{tok}'"))?;
                st.push(v);
            }
        }
    }
    match st.as_slice() {
        [v] => Ok(*v),
        [] => Err("empty stack".into()),
        _ => Err(format!("{} values left on stack", st.len())),
    }
}

#[unsafe(no_mangle)]
extern "C" fn main(_argc: c_int, _argv: *const *const c_char) -> c_int {
    let mut raw = String::new();
    if io::stdin().read_to_string(&mut raw).is_err() {
        let _ = io::stderr().write_all(b"rpn_calc: invalid utf-8 input\n");
        return 2;
    }
    let mut out = io::stdout();
    let mut text = String::new();
    let mut code = 0;
    for (i, line) in raw.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        match eval_line(line) {
            Ok(v) => text.push_str(&format!("{}: {v}\n", i + 1)),
            Err(e) => {
                let _ = out.write_all(text.as_bytes()).and_then(|()| out.flush());
                text.clear();
                let _ = writeln!(io::stderr(), "rpn_calc: line {}: {e}", i + 1);
                code = 1;
                break;
            }
        }
    }
    if out
        .write_all(text.as_bytes())
        .and_then(|()| out.flush())
        .is_err()
    {
        return 2;
    }
    code
}
