// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Small illustrative Rust programs for the Spec Adequacy Tour
//! (`Arm64/Testing/Tours/SpecAdequacyTour.lean`).
//!
//! Each function is compiled through the standard `rustc` AArch64 release pipeline
//! (`opt-level = 2`) via `rust-obj2lean` and verified (or proved to reach an unsafe
//! state) directly against the operational semantics in `Arm64/Trusted/`.

#![no_std]
#![deny(unsafe_op_in_unsafe_fn)]

use core::arch::asm;

pub const SYS_EXIT_GROUP: usize = 94;
pub const SYS_MMAP: usize = 222;
pub const SYS_GETRANDOM: usize = 278;

pub const PROT_READ: usize = 0x1;
pub const PROT_WRITE: usize = 0x2;
pub const MAP_PRIVATE: usize = 0x02;
pub const MAP_ANONYMOUS: usize = 0x20;
pub const PAGE_SIZE: usize = 4096;

/// Fixed address used by [`read_fixed_addr`] to illustrate that guessing an
/// unmapped virtual address faults under our conservative memory model.
pub const FIXED_ADDR: usize = 0xdead_beef_0000;

/// Expected 32-bit little-endian AArch64 instruction encoding of `nop` (`0xd503201f`).
pub const NOP_INSN_WORD: u32 = 0xd503_201f;

#[cfg(not(test))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo<'_>) -> ! {
    exit_group(101)
}

/// Raw Linux AArch64 `exit_group(code)` system call (`svc #0`, `x8 = 94`).
#[inline(always)]
pub fn exit_group(code: u64) -> ! {
    // SAFETY: Terminates the process group via Linux AArch64 `exit_group` (`x8 = 94`).
    unsafe {
        asm!(
            "svc #0",
            in("x8") SYS_EXIT_GROUP,
            in("x0") code,
            options(noreturn, nostack)
        )
    }
}

/// Raw Linux AArch64 `getrandom(buf, 1, 0)` system call (`svc #0`, `x8 = 278`),
/// filling a single byte on the stack and returning it.
#[inline(always)]
pub fn getrandom_u8() -> u8 {
    let mut byte: u8 = 0;
    let ptr = core::ptr::addr_of_mut!(byte);
    // SAFETY: `ptr` points to a valid 1-byte stack slot `byte`.
    unsafe {
        let _ret: usize;
        asm!(
            "svc #0",
            in("x8") SYS_GETRANDOM,
            inlateout("x0") ptr => _ret,
            in("x1") 1usize,
            in("x2") 0usize,
            options(preserves_flags)
        );
        core::ptr::read_volatile(ptr)
    }
}

/// Raw Linux AArch64 anonymous `mmap(0, PAGE_SIZE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0)`
/// system call (`svc #0`, `x8 = 222`).
#[inline(always)]
pub fn mmap_one_page() -> *mut u64 {
    let ret: usize;
    // SAFETY: Invokes the modeled Linux AArch64 anonymous `mmap` syscall (`x8 = 222`).
    unsafe {
        asm!(
            "svc #0",
            in("x8") SYS_MMAP,
            inlateout("x0") 0usize => ret,
            in("x1") PAGE_SIZE,
            in("x2") PROT_READ | PROT_WRITE,
            in("x3") MAP_PRIVATE | MAP_ANONYMOUS,
            in("x4") (-1isize) as usize,
            in("x5") 0usize,
            options(nostack, preserves_flags)
        );
    }
    ret as *mut u64
}

/// **Example 2:** `assert!(getrandom() > 5)` is unsafe — relies on the `SYS_GETRANDOM`
/// syscall model (`s₀.oracle.getrandom`) and panics whenever the oracle byte is `<= 5`.
#[inline(never)]
pub fn assert_getrandom_gt_5() {
    let r = getrandom_u8();
    assert!(r > 5);
}

/// **Example 3:** Maps a fresh 4096-byte page via `mmap`, checks that the newly mapped
/// page is initially zero, writes `x + 7` to the page, reads it back, and asserts that
/// the round-tripped word equals `x + 7`.
#[inline(never)]
pub fn mmap_write_and_verify(x: u64) -> u64 {
    let page = mmap_one_page();
    // SAFETY: When `mmap` succeeds in the model, `page` points to a freshly mapped,
    // zero-initialized 4096-byte `Perm.rw` region.
    let v0 = unsafe { core::ptr::read_volatile(page) };
    let expected = x.wrapping_add(7);
    unsafe {
        core::ptr::write_volatile(page, expected.wrapping_add(v0));
    }
    let v1 = unsafe { core::ptr::read_volatile(page) };
    assert!(v1 == expected);
    v1
}

/// **Example 4:** Non-trivial process exit with status `1`: exits with status `0` if
/// `x == 0`, and exits the whole process with status `1` whenever `x != 0`.
#[inline(never)]
pub fn nonzero_exit_one(x: u64) -> ! {
    let code = if x == 0 { 0 } else { 1 };
    exit_group(code)
}

/// **Example 5:** Reads a 64-bit word from the fixed address `0xdead_beef_0000`
/// via inline assembly. Faults with `.Exception "permission fault"` whenever that
/// address is unmapped.
#[inline(never)]
pub fn read_fixed_addr() -> u64 {
    let val: u64;
    // SAFETY (intentionally unsafe when `FIXED_ADDR` is unmapped):
    // Reads 8 bytes from the hardcoded address `0xdead_beef_0000`.
    unsafe {
        asm!(
            "ldr {val}, [{addr}]",
            addr = in(reg) FIXED_ADDR,
            val = lateout(reg) val,
            options(nostack, preserves_flags)
        );
    }
    val
}

/// **Example 6:** Reads its own code bytes via PC-relative `adr` + `ldr` and asserts
/// that the instruction word at label `2:` equals the AArch64 encoding of `nop`
/// (`0xd503201f`). Proved safe until return under `Program.CodeLoaded` alone.
#[inline(never)]
pub fn verify_own_code_bytes() {
    let insn_word: u32;
    // SAFETY: `adr` computes the runtime address of label `2:` inside this function's
    // own `.text` section, and `ldr` reads that 4-byte instruction word (`Perm.rx`).
    unsafe {
        asm!(
            "adr {tmp}, 2f",
            "2:",
            "nop",
            "ldr {w:w}, [{tmp}]",
            tmp = out(reg) _,
            w = out(reg) insn_word,
            options(nostack, preserves_flags)
        );
    }
    assert!(insn_word == NOP_INSN_WORD);
}

/// **Example 7:** Attempts to overwrite its own `nop` instruction via PC-relative
/// `adr` + `str` (self-modifying code). Always faults with `.Exception "permission fault"`
/// under `Program.CodeLoaded` because executable code is mapped `Perm.rx` (`writable = false`).
#[inline(never)]
pub fn write_own_code_bytes() {
    // SAFETY (intentionally faults under W^X): attempts to store a 32-bit word into
    // this function's own `.text` section (`Perm.rx`).
    unsafe {
        asm!(
            "adr {tmp}, 2f",
            "str {val:w}, [{tmp}]",
            "2:",
            "nop",
            tmp = out(reg) _,
            val = in(reg) NOP_INSN_WORD,
            options(nostack, preserves_flags)
        );
    }
}

/// **Example 8:** Spills `x + 1` to a stack slot via volatile store/load and asserts
/// the round-trip value. Safe until return when `SP` is 16-byte aligned and the stack
/// slot is writable, and faults immediately with `.Exception "SP alignment fault"`
/// when `SP` is misaligned (`sp &&& 0xF != 0`).
#[inline(never)]
pub fn stack_spill_verify(x: u64) -> u64 {
    let mut slot: u64 = 0;
    let ptr = core::ptr::addr_of_mut!(slot);
    let expected = x.wrapping_add(1);
    // SAFETY: `ptr` points to the 8-byte stack slot `slot`.
    let loaded = unsafe {
        core::ptr::write_volatile(ptr, expected);
        core::ptr::read_volatile(ptr)
    };
    assert!(loaded == expected);
    loaded
}
