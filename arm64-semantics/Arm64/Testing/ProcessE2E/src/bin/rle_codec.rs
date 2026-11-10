// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `rle_codec`: `#![no_main]` Rust `std` on static musl implementing byte-level run-length coding
//! as `(count: u8 in 1..=255, byte)` pairs.
//!
//! - `rle_codec c`: compress `stdin` to binary `stdout`.
//! - `rle_codec d`: decompress `stdin`; odd length or a zero count reports the pair offset on
//!   `stderr` (`exit 1`).
//! - `rle_codec rt`: compress, decompress, verify the roundtrip in memory, and print sizes, run
//!   count, and an FNV-1a digest of the compressed form.

#![no_main]

#[path = "../common.rs"]
mod common;

use common::{BrkMmapAlloc, read_args};
use std::ffi::{c_char, c_int};
use std::io::{self, Read, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

fn compress(input: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < input.len() {
        let b = input[i];
        let mut run = 1usize;
        while i + run < input.len() && input[i + run] == b && run < 255 {
            run += 1;
        }
        out.push(run as u8);
        out.push(b);
        i += run;
    }
    out
}

fn decompress(input: &[u8]) -> Result<Vec<u8>, String> {
    if !input.len().is_multiple_of(2) {
        return Err(format!("odd input length {}", input.len()));
    }
    let mut out = Vec::new();
    for (pair, chunk) in input.chunks_exact(2).enumerate() {
        if chunk[0] == 0 {
            return Err(format!("zero run count in pair {pair}"));
        }
        out.extend(core::iter::repeat_n(chunk[1], chunk[0] as usize));
    }
    Ok(out)
}

fn fnv1a(data: &[u8]) -> u64 {
    data.iter().fold(0xcbf29ce484222325u64, |h, &b| {
        (h ^ b as u64).wrapping_mul(0x100000001b3)
    })
}

#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let args = unsafe { read_args(argc, argv) };
    let mode = args.get(1).copied().unwrap_or(b"");
    let mut input = Vec::new();
    if io::stdin().read_to_end(&mut input).is_err() {
        return 2;
    }
    let mut out = io::stdout();
    let mut err = io::stderr();
    let code = match mode {
        b"c" => {
            let _ = out.write_all(&compress(&input));
            0
        }
        b"d" => match decompress(&input) {
            Ok(v) => {
                let _ = out.write_all(&v);
                0
            }
            Err(e) => {
                let _ = writeln!(err, "rle_codec: corrupt stream: {e}");
                1
            }
        },
        b"rt" => {
            let packed = compress(&input);
            let ok = decompress(&packed).is_ok_and(|v| v == input);
            let _ = writeln!(
                out,
                "in={} packed={} runs={} fnv1a=0x{:016x} roundtrip={}",
                input.len(),
                packed.len(),
                packed.len() / 2,
                fnv1a(&packed),
                if ok { "ok" } else { "MISMATCH" }
            );
            if ok { 0 } else { 1 }
        }
        _ => {
            let _ = writeln!(err, "usage: rle_codec c|d|rt < input");
            2
        }
    };
    if out.flush().is_err() {
        return 2;
    }
    code
}
