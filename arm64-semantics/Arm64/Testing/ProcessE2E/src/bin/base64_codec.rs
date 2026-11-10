// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `base64_codec`: `#![no_main]` Rust `std` on static musl implementing RFC 4648 base64.
//!
//! - `base64_codec enc`: encodes `stdin`, wrapping output at 76 columns (MIME style).
//! - `base64_codec dec`: decodes `stdin`, ignoring ASCII whitespace; reports the byte offset of
//!   the first invalid character, misplaced padding, or truncated quantum on `stderr` (`exit 1`).
//! - Missing or unknown mode: usage on `stderr` (`exit 2`).

#![no_main]

#[path = "../common.rs"]
mod common;

use common::{BrkMmapAlloc, read_args};
use std::ffi::{c_char, c_int};
use std::io::{self, Read, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

fn encode(input: &[u8]) -> Vec<u8> {
    let mut raw = Vec::with_capacity(input.len().div_ceil(3) * 4);
    for chunk in input.chunks(3) {
        let b0 = chunk[0] as u32;
        let b1 = chunk.get(1).copied().unwrap_or(0) as u32;
        let b2 = chunk.get(2).copied().unwrap_or(0) as u32;
        let n = (b0 << 16) | (b1 << 8) | b2;
        raw.push(ALPHABET[(n >> 18) as usize & 63]);
        raw.push(ALPHABET[(n >> 12) as usize & 63]);
        raw.push(if chunk.len() > 1 {
            ALPHABET[(n >> 6) as usize & 63]
        } else {
            b'='
        });
        raw.push(if chunk.len() > 2 {
            ALPHABET[n as usize & 63]
        } else {
            b'='
        });
    }
    let mut out = Vec::with_capacity(raw.len() + raw.len() / 76 + 1);
    for line in raw.chunks(76) {
        out.extend_from_slice(line);
        out.push(b'\n');
    }
    out
}

fn sextet(c: u8) -> Option<u32> {
    match c {
        b'A'..=b'Z' => Some((c - b'A') as u32),
        b'a'..=b'z' => Some((c - b'a' + 26) as u32),
        b'0'..=b'9' => Some((c - b'0' + 52) as u32),
        b'+' => Some(62),
        b'/' => Some(63),
        _ => None,
    }
}

fn decode(input: &[u8]) -> Result<Vec<u8>, String> {
    let mut out = Vec::with_capacity(input.len() / 4 * 3);
    let mut acc: u32 = 0;
    let mut nbits_in_quad = 0usize;
    let mut pad = 0usize;
    for (off, &c) in input.iter().enumerate() {
        if c.is_ascii_whitespace() {
            continue;
        }
        if c == b'=' {
            if nbits_in_quad < 2 {
                return Err(format!("misplaced padding at offset {off}"));
            }
            pad += 1;
            nbits_in_quad += 1;
            if nbits_in_quad == 4 {
                // Flush 1 or 2 bytes from a padded quantum.
                acc <<= 6 * pad as u32;
                let bytes = [(acc >> 16) as u8, (acc >> 8) as u8];
                out.extend_from_slice(&bytes[..3 - pad]);
                nbits_in_quad = 0;
                acc = 0;
            }
            continue;
        }
        if pad > 0 {
            return Err(format!("data after padding at offset {off}"));
        }
        let Some(v) = sextet(c) else {
            return Err(format!("invalid character 0x{c:02x} at offset {off}"));
        };
        acc = (acc << 6) | v;
        nbits_in_quad += 1;
        if nbits_in_quad == 4 {
            out.extend_from_slice(&[(acc >> 16) as u8, (acc >> 8) as u8, acc as u8]);
            nbits_in_quad = 0;
            acc = 0;
        }
    }
    if nbits_in_quad != 0 {
        return Err(format!("truncated quantum ({nbits_in_quad} of 4 symbols)"));
    }
    Ok(out)
}

fn fail(msg: &str, code: c_int) -> c_int {
    let mut err = io::stderr();
    let _ = writeln!(err, "base64_codec: {msg}");
    let _ = err.flush();
    code
}

#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let args = unsafe { read_args(argc, argv) };
    let mode = args.get(1).copied().unwrap_or(b"");
    if mode != b"enc" && mode != b"dec" {
        return fail("usage: base64_codec enc|dec < input", 2);
    }
    let mut input = Vec::new();
    if io::stdin().read_to_end(&mut input).is_err() {
        return fail("read error", 2);
    }
    let output = if mode == b"enc" {
        encode(&input)
    } else {
        match decode(&input) {
            Ok(v) => v,
            Err(e) => return fail(&e, 1),
        }
    };
    let mut out = io::stdout();
    if out.write_all(&output).and_then(|()| out.flush()).is_err() {
        return 2;
    }
    0
}
