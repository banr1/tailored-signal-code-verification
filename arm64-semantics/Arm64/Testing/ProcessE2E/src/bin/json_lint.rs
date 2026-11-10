// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `json_lint`: `#![no_main]` Rust `std` on static musl tokenizing JSON from `stdin` with an
//! explicit bracket stack (no recursion).
//!
//! Validates bracket nesting, string escapes (`\" \\ \/ \b \f \n \r \t \uXXXX`), number syntax,
//! and the literals `true` / `false` / `null`, then prints token-class counts and the maximum
//! nesting depth. The first lexical or nesting error is reported with its byte offset on `stderr`
//! (`exit 1`).

#![no_main]

#[path = "../common.rs"]
mod common;

use common::BrkMmapAlloc;
use std::ffi::{c_char, c_int};
use std::io::{self, Read, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

#[derive(Default)]
struct Stats {
    objects: usize,
    arrays: usize,
    strings: usize,
    numbers: usize,
    literals: usize,
    max_depth: usize,
}

fn lex_string(s: &[u8], mut i: usize) -> Result<usize, (usize, &'static str)> {
    // `s[i] == b'"'`; returns the index after the closing quote.
    let start = i;
    i += 1;
    loop {
        match s.get(i) {
            None => return Err((start, "unterminated string")),
            Some(b'"') => return Ok(i + 1),
            Some(b'\\') => match s.get(i + 1) {
                Some(b'"' | b'\\' | b'/' | b'b' | b'f' | b'n' | b'r' | b't') => i += 2,
                Some(b'u') => {
                    let hex = s.get(i + 2..i + 6).ok_or((i, "truncated \\u escape"))?;
                    if !hex.iter().all(u8::is_ascii_hexdigit) {
                        return Err((i, "invalid \\u escape"));
                    }
                    i += 6;
                }
                _ => return Err((i, "invalid escape")),
            },
            Some(&c) if c < 0x20 => return Err((i, "control character in string")),
            Some(_) => i += 1,
        }
    }
}

fn lex_number(s: &[u8], mut i: usize) -> Result<usize, (usize, &'static str)> {
    let start = i;
    let digits = |s: &[u8], mut j: usize| {
        let k = j;
        while s.get(j).is_some_and(u8::is_ascii_digit) {
            j += 1;
        }
        (j, j > k)
    };
    if s.get(i) == Some(&b'-') {
        i += 1;
    }
    if s.get(i) == Some(&b'0') {
        i += 1;
    } else {
        let (j, any) = digits(s, i);
        if !any {
            return Err((start, "invalid number"));
        }
        i = j;
    }
    if s.get(i) == Some(&b'.') {
        let (j, any) = digits(s, i + 1);
        if !any {
            return Err((start, "invalid fraction"));
        }
        i = j;
    }
    if matches!(s.get(i), Some(b'e' | b'E')) {
        i += 1;
        if matches!(s.get(i), Some(b'+' | b'-')) {
            i += 1;
        }
        let (j, any) = digits(s, i);
        if !any {
            return Err((start, "invalid exponent"));
        }
        i = j;
    }
    Ok(i)
}

fn lint(s: &[u8]) -> Result<Stats, (usize, String)> {
    let mut st = Stats::default();
    let mut stack: Vec<(u8, usize)> = Vec::new();
    let mut i = 0;
    let mut values = 0usize;
    while i < s.len() {
        let c = s[i];
        match c {
            b' ' | b'\t' | b'\n' | b'\r' | b',' | b':' => i += 1,
            b'{' | b'[' => {
                if c == b'{' {
                    st.objects += 1;
                } else {
                    st.arrays += 1;
                }
                stack.push((c, i));
                st.max_depth = st.max_depth.max(stack.len());
                i += 1;
            }
            b'}' | b']' => {
                let want = if c == b'}' { b'{' } else { b'[' };
                match stack.pop() {
                    Some((open, _)) if open == want => {}
                    Some((open, at)) => {
                        return Err((
                            i,
                            format!(
                                "mismatched '{}' closes '{}' opened at offset {at}",
                                c as char, open as char
                            ),
                        ));
                    }
                    None => return Err((i, format!("unbalanced '{}'", c as char))),
                }
                if stack.is_empty() {
                    values += 1;
                }
                i += 1;
            }
            b'"' => {
                i = lex_string(s, i).map_err(|(o, m)| (o, m.to_owned()))?;
                st.strings += 1;
            }
            b'-' | b'0'..=b'9' => {
                i = lex_number(s, i).map_err(|(o, m)| (o, m.to_owned()))?;
                st.numbers += 1;
            }
            _ => {
                let lit = [&b"true"[..], b"false", b"null"]
                    .into_iter()
                    .find(|l| s[i..].starts_with(l));
                let Some(lit) = lit else {
                    return Err((i, format!("unexpected byte 0x{c:02x}")));
                };
                st.literals += 1;
                i += lit.len();
            }
        }
        if stack.is_empty() && matches!(c, b'"' | b'-' | b'0'..=b'9' | b't' | b'f' | b'n') {
            values += 1;
        }
    }
    if let Some((open, at)) = stack.last() {
        return Err((
            s.len(),
            format!("unclosed '{}' opened at offset {at}", *open as char),
        ));
    }
    if values != 1 {
        return Err((
            s.len(),
            format!("expected exactly 1 top-level value, found {values}"),
        ));
    }
    Ok(st)
}

#[unsafe(no_mangle)]
extern "C" fn main(_argc: c_int, _argv: *const *const c_char) -> c_int {
    let mut input = Vec::new();
    if io::stdin().read_to_end(&mut input).is_err() {
        return 2;
    }
    match lint(&input) {
        Ok(st) => {
            let mut out = io::stdout();
            let _ = writeln!(
                out,
                "ok objects={} arrays={} strings={} numbers={} literals={} max_depth={}",
                st.objects, st.arrays, st.strings, st.numbers, st.literals, st.max_depth
            );
            if out.flush().is_err() {
                return 2;
            }
            0
        }
        Err((off, msg)) => {
            let _ = writeln!(io::stderr(), "json_lint: offset {off}: {msg}");
            1
        }
    }
}
