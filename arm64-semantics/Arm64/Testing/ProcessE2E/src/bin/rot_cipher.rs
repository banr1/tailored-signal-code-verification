// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `rot_cipher`: `#![no_main]` Rust `std` on static musl applying classical substitution ciphers
//! to `stdin`, selected by `argv`.
//!
//! - `rot_cipher rot13`: ROT13 over ASCII letters.
//! - `rot_cipher caesar K`: shift letters by signed `K` (reduced mod 26); `caesar -K` inverts it.
//! - `rot_cipher atbash`: mirror the alphabet (`a <-> z`).
//! - `rot_cipher freq`: print the 26 letter counts (case-folded) and the most frequent letter.
//!
//! Non-letters (including non-ASCII bytes) pass through unchanged. Bad mode or shift: `exit 2`.

#![no_main]

#[path = "../common.rs"]
mod common;

use common::{BrkMmapAlloc, read_args};
use std::ffi::{c_char, c_int};
use std::io::{self, Read, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

fn map_letters(input: &mut [u8], f: impl Fn(u8) -> u8) {
    for b in input.iter_mut() {
        let base = match *b {
            b'a'..=b'z' => b'a',
            b'A'..=b'Z' => b'A',
            _ => continue,
        };
        *b = base + f(*b - base);
    }
}

#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let args = unsafe { read_args(argc, argv) };
    let shift: Option<u8> = match args.get(1..).unwrap_or(&[]) {
        [m] if *m == b"rot13" => Some(13),
        [m] if *m == b"atbash" || *m == b"freq" => None,
        [m, k] if *m == b"caesar" => {
            match core::str::from_utf8(k)
                .ok()
                .and_then(|s| s.parse::<i64>().ok())
            {
                Some(k) => Some(k.rem_euclid(26) as u8),
                None => {
                    let _ = writeln!(
                        io::stderr(),
                        "rot_cipher: invalid shift '{}'",
                        String::from_utf8_lossy(k)
                    );
                    return 2;
                }
            }
        }
        _ => {
            let _ =
                io::stderr().write_all(b"usage: rot_cipher rot13|atbash|freq|caesar K < input\n");
            return 2;
        }
    };
    let mut input = Vec::new();
    if io::stdin().read_to_end(&mut input).is_err() {
        return 2;
    }
    let mut out = io::stdout();
    if args[1] == b"freq" {
        let mut counts = [0usize; 26];
        for b in &input {
            if b.is_ascii_alphabetic() {
                counts[(b.to_ascii_lowercase() - b'a') as usize] += 1;
            }
        }
        let mut text = String::new();
        for (i, c) in counts.iter().enumerate() {
            text.push_str(&format!(
                "{}={c}{}",
                (b'a' + i as u8) as char,
                if i % 13 == 12 { "\n" } else { " " }
            ));
        }
        // `max_by_key` returns the last maximum; iterate in reverse so ties pick the earliest letter.
        let (top, n) = counts
            .iter()
            .enumerate()
            .rev()
            .max_by_key(|&(_, c)| *c)
            .unwrap();
        text.push_str(&format!("top={} ({n})\n", (b'a' + top as u8) as char));
        let _ = out.write_all(text.as_bytes());
    } else {
        match shift {
            Some(k) => map_letters(&mut input, |x| (x + k) % 26),
            None => map_letters(&mut input, |x| 25 - x),
        }
        let _ = out.write_all(&input);
    }
    if out.flush().is_err() {
        return 2;
    }
    0
}
