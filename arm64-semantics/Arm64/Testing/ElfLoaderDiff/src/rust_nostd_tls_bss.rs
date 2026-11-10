// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Minimal `#![no_std]` static `aarch64-unknown-linux-musl` Rust release binary with
//! explicit `.tdata` / `.tbss` (`PT_TLS`), `.rodata`, `.data`, and a 64 KiB `.bss` array.
#![no_std]
#![no_main]

use core::arch::asm;
use core::panic::PanicInfo;

#[used]
#[unsafe(link_section = ".rodata")]
static RO_MAGIC: [u64; 4] = [
    0x0102_0304_0506_0708,
    0x1122_3344_5566_7788,
    0x99aa_bbcc_ddee_ff00,
    0xdead_beef_cafe_babe,
];

#[used]
#[unsafe(link_section = ".data")]
static mut RW_DATA: [u64; 4] = [
    0xaaaa_bbbb_cccc_dddd,
    0x1234_5678_9abc_def0,
    0x0fed_cba9_8765_4321,
    0x1357_9bdf_2468_ace0,
];

#[used]
#[unsafe(link_section = ".bss")]
static mut BIG_BSS: [u8; 65536] = [0u8; 65536];

#[used]
#[unsafe(link_section = ".tdata")]
static mut TLS_TDATA: [u64; 4] = [
    0xf1f2_f3f4_f5f6_f7f8,
    0xe1e2_e3e4_e5e6_e7e8,
    0xd1d2_d3d4_d5d6_d7d8,
    0xc1c2_c3c4_c5c6_c7c8,
];

#[used]
#[unsafe(link_section = ".tbss")]
static mut TLS_TBSS: [u8; 128] = [0u8; 128];

#[unsafe(no_mangle)]
pub unsafe extern "C" fn _start() -> ! {
    unsafe {
        let p_bss = &raw mut BIG_BSS;
        (*p_bss)[0] = (RO_MAGIC[0] & 0xff) as u8;
        (*p_bss)[65535] = ((*(&raw const TLS_TDATA))[0] & 0xff) as u8;
        let p_rw = &raw mut RW_DATA;
        (*p_rw)[0] ^= (*(&raw const TLS_TBSS))[0] as u64;
        asm!(
            "mov x0, #0",
            "mov x8, #94",
            "svc #0",
            options(noreturn)
        );
    }
}

#[panic_handler]
fn panic(_info: &PanicInfo<'_>) -> ! {
    unsafe {
        asm!(
            "mov x0, #1",
            "mov x8, #94",
            "svc #0",
            options(noreturn)
        );
    }
}
