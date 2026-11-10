// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Static `aarch64-unknown-linux-musl` Rust binary with `PT_TLS` (`.tdata` + `.tbss`),
//! `PT_GNU_RELRO`, `.rodata`, `.data`, and a multi-page 64 KiB `.bss` section.

use std::cell::Cell;
use std::hint::black_box;

#[used]
static RO_BANNER: [u8; 32] = *b"ARM64-ELF-LOADER-DIFF-RUST-MUSL!";

#[used]
static mut RW_WORDS: [u64; 8] = [
    0x1111_2222_3333_4444,
    0x5555_6666_7777_8888,
    0x9999_aaaa_bbbb_cccc,
    0xdddd_eeee_ffff_0000,
    0x0123_4567_89ab_cdef,
    0xfedc_ba98_7654_3210,
    0xcafe_babe_dead_beef,
    0x0f1e_2d3c_4b5a_6978,
];

#[used]
static mut LARGE_BSS: [u8; 65536] = [0u8; 65536];

std::thread_local! {
    static TLS_INIT: Cell<[u64; 4]> = const {
        Cell::new([
            0xa1a2_a3a4_a5a6_a7a8,
            0xb1b2_b3b4_b5b6_b7b8,
            0xc1c2_c3c4_c5c6_c7c8,
            0xd1d2_d3d4_d5d6_d7d8,
        ])
    };
    static TLS_ZERO: Cell<[u8; 256]> = const { Cell::new([0u8; 256]) };
}

fn main() {
    let mut sum = RO_BANNER[0] as u64;
    TLS_INIT.with(|c| {
        let mut arr = c.get();
        sum ^= arr[0];
        arr[1] = sum;
        c.set(arr);
    });
    TLS_ZERO.with(|z| {
        let mut buf = z.get();
        buf[0] = (sum & 0xff) as u8;
        z.set(buf);
    });
    unsafe {
        let ptr = &raw mut LARGE_BSS;
        (*ptr)[0] = 1;
        (*ptr)[32768] = 2;
        (*ptr)[65535] = 3;
        let rw = &raw mut RW_WORDS;
        (*rw)[0] ^= sum;
        black_box(ptr);
        black_box(rw);
    }
}
