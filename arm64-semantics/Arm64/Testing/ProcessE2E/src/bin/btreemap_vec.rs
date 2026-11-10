// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! `btreemap_vec`: `#![no_main]` Rust `std` on static musl exercising hashbrown-free
//! `BTreeMap<String, Vec<u8>>` mutations, `Vec` growth over `SYS_brk`, and multi-page scratch
//! allocation + deallocation via anonymous `SYS_mmap` + `SYS_munmap`.

#![no_main]

#[path = "../common.rs"]
mod common;

use common::{BrkMmapAlloc, read_args};
use std::collections::BTreeMap;
use std::ffi::{c_char, c_int};
use std::io::{self, Write};

#[global_allocator]
static ALLOC: BrkMmapAlloc = BrkMmapAlloc::new();

#[unsafe(no_mangle)]
extern "C" fn main(argc: c_int, argv: *const *const c_char) -> c_int {
    let args = unsafe { read_args(argc, argv) };
    let count: usize = args
        .get(1)
        .and_then(|s| core::str::from_utf8(s).ok())
        .and_then(|s| s.parse().ok())
        .unwrap_or(24);
    let use_large_mmap = args.get(2).copied() == Some(b"mmap");

    let mut mmap_digest: u64 = 0;
    if use_large_mmap {
        // 32 KiB exceeds `BrkMmapAlloc`'s 16 KiB threshold, triggering `SYS_mmap` on alloc and
        // `SYS_munmap` when `scratch` drops at the end of this block.
        let mut scratch = vec![0u8; 32 * 1024];
        for (idx, slot) in scratch.iter_mut().enumerate() {
            *slot = ((idx * 131 + 17) & 0xff) as u8;
        }
        for &b in &scratch {
            mmap_digest = mmap_digest.wrapping_mul(1099511628211).wrapping_add(b as u64);
        }
    }

    let mut map: BTreeMap<String, Vec<u8>> = BTreeMap::new();
    for i in 0..count {
        let key = format!("entry-{:04}", (i * 37 + 11) % 97);
        let mut payload = Vec::with_capacity((i % 19) + 4);
        for j in 0..((i % 19) + 4) {
            payload.push(((i * 7 + j * 13) & 0xff) as u8);
        }
        map.insert(key, payload);
    }
    // Remove every key whose trailing decimal digit is divisible by 3.
    let to_remove: Vec<String> = map
        .keys()
        .enumerate()
        .filter_map(|(idx, k)| if idx % 3 == 0 { Some(k.clone()) } else { None })
        .collect();
    for k in &to_remove {
        map.remove(k);
    }

    let mut rolling: u64 = 0x9e3779b97f4a7c15;
    for (k, v) in map.range(String::from("entry-0010")..=String::from("entry-0090")) {
        for &b in k.as_bytes().iter().chain(v.iter()) {
            rolling = rolling.rotate_left(5) ^ (b as u64);
        }
    }

    let first_key = map.keys().next().map(String::as_str).unwrap_or("none");
    let last_key = map.keys().next_back().map(String::as_str).unwrap_or("none");
    let mut out = io::stdout();
    let _ = writeln!(
        out,
        "len={} removed={} first={first_key} last={last_key} range_hash=0x{rolling:016x} mmap_digest=0x{mmap_digest:016x}",
        map.len(),
        to_remove.len()
    );
    if out.flush().is_err() {
        return 2;
    }
    0
}
