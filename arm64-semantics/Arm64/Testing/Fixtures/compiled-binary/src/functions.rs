// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Rust and inline-assembly implementations of the benchmark/utility functions compiled to AArch64
//! (`cargo build --release --target aarch64-unknown-linux-gnu`)
//! and exported to `Arm64/Testing/Generators/CompiledBinaryFixture.lean`
//! for verification in `Arm64/Testing/Tours/Demo.lean` and `SpecAdequacyTour.lean`.

#[derive(Copy, Clone)]
pub struct Pair {
    pub a: u64,
    pub b: u64,
}

/// Inline-assembly microbenchmark functions (`xor_swap`, `arith_shift`, `control_flow`,
/// `move_2_regs_to_heap`, `reg_offset`, and `decoder_bug_regressions`).
pub mod asm {
    use core::arch::naked_asm;

    /// Register swap of `x2` and `x3` using 3 `eor` instructions.
    #[unsafe(no_mangle)]
    #[unsafe(naked)]
    pub unsafe extern "C" fn xor_swap() {
        naked_asm!(
            "eor x3, x3, x2",
            "eor x2, x2, x3",
            "eor x3, x3, x2",
            "ret",
        )
    }

    /// Multi-instruction arithmetic and shift pipeline: `((x0 - 17) << 3) + x1`.
    #[unsafe(no_mangle)]
    #[unsafe(naked)]
    pub unsafe extern "C" fn arith_shift() {
        naked_asm!(
            "sub x4, x0, #17",
            "lsl x5, x4, #3",
            "add x0, x5, x1",
            "ret",
        )
    }

    /// Untaken conditional branch (`mov x2, #0`, `cbnz x2, .+8`, `mov x0, #99`).
    #[unsafe(no_mangle)]
    #[unsafe(naked)]
    pub unsafe extern "C" fn control_flow() {
        naked_asm!(
            "mov x2, #0",
            "cbnz x2, 2f",
            "mov x0, #99",
            "2:",
            "ret",
        )
    }

    /// Storing `x3`, `x4` to `[x0, #8]` and `[x0]` and reloading them swapped into `x1`, `x2`.
    #[unsafe(no_mangle)]
    #[unsafe(naked)]
    pub unsafe extern "C" fn move_2_regs_to_heap() {
        naked_asm!(
            "str x3, [x0, #8]",
            "str x4, [x0]",
            "ldr x1, [x0]",
            "ldr x2, [x0, #8]",
            "ret",
        )
    }

    /// Memory store and load with shifted register offset `[x0, x1, lsl #3]` and increment.
    #[unsafe(no_mangle)]
    #[unsafe(naked)]
    pub unsafe extern "C" fn reg_offset() {
        naked_asm!(
            "mov x2, #0x1234",
            "str x2, [x0, x1, lsl #3]",
            "ldr x4, [x0, x1, lsl #3]",
            "add x0, x4, #1",
            "ret",
        )
    }

    /// Decoder/semantics regression (`cmp x1, #1`, `cset x0, eq`, `neg x2, x1, lsl #3`, `ngc x3, x1`).
    #[unsafe(no_mangle)]
    #[unsafe(naked)]
    pub unsafe extern "C" fn decoder_bug_regressions() {
        naked_asm!(
            "cmp x1, #1",
            "cset x0, eq",
            "neg x2, x1, lsl #3",
            "ngc x3, x1",
            "ret",
        )
    }
}

/// 1. Arithmetic and shift pipeline: `(x + 42) * 3`.
#[inline(never)]
pub fn arith_shift(x: u64) -> u64 {
    (x.wrapping_add(42)).wrapping_mul(3)
}

/// 2. Unsigned 64-bit maximum (`cmp` + `csel hi`).
#[inline(never)]
pub fn max_u64(a: u64, b: u64) -> u64 {
    if a > b { a } else { b }
}

/// 3. Unsigned 64-bit clamp to `[lo, hi]` (`cmp` + `csel` chain).
#[inline(never)]
pub fn clamp_u64(x: u64, lo: u64, hi: u64) -> u64 {
    let m = if x >= lo { x } else { lo };
    if m <= hi { m } else { hi }
}

/// 4. Unsigned 64-bit absolute difference `|a - b|` (`subs` + `cneg`).
#[inline(never)]
pub fn abs_diff_u64(a: u64, b: u64) -> u64 {
    a.abs_diff(b)
}

/// 5. Unsigned 64-bit saturating addition (`adds` + `csinv`).
#[inline(never)]
pub fn saturating_add_u64(a: u64, b: u64) -> u64 {
    a.saturating_add(b)
}

/// 6. Bitfield extraction and insertion (`((x >> 8) & 0xffff) | ((x & 0xff) << 16)`).
#[inline(never)]
pub fn extract_bitfield(x: u64) -> u64 {
    ((x >> 8) & 0xffff) | ((x & 0xff) << 16)
}

/// 7. Bitwise manipulation with `bic`, `orr`, and rotated `eor` (`ror #17`).
#[inline(never)]
pub fn bit_tricks(x: u64, y: u64) -> u64 {
    (x & !y) ^ ((x | y).rotate_right(17))
}

/// 8. 64x64 -> 128-bit widening unsigned multiplication (`mul` + `umulh`).
#[inline(never)]
pub fn widening_mul_u64(a: u64, b: u64) -> Pair {
    let prod = (a as u128) * (b as u128);
    Pair {
        a: prod as u64,
        b: (prod >> 64) as u64,
    }
}

/// 9. 64-bit slice indexing (`ldr x0, [x0, x1, lsl #3]`).
#[inline(never)]
pub unsafe fn slice_index(ptr: *const u64, idx: usize) -> u64 {
    unsafe { *ptr.add(idx) }
}

/// 10. In-place 64-bit memory swap (`ldr` + `str`).
#[inline(never)]
pub fn mem_swap(a: &mut u64, b: &mut u64) {
    core::mem::swap(a, b);
}

/// 11a. 128-bit struct copy (`ldp` + `stp`).
#[inline(never)]
pub fn pair_copy(src: &Pair, dst: &mut Pair) {
    *dst = *src;
}

/// 11b. 128-bit struct sum and difference transform (`ldp`, `add`, `sub`, `stp`).
#[inline(never)]
pub fn pair_sum_diff(src: &Pair, dst: &mut Pair) {
    let a = src.a;
    let b = src.b;
    dst.a = a.wrapping_add(b);
    dst.b = a.wrapping_sub(b);
}

/// 12. Arbitrary-`N` XOR-shift countdown loop (`cbz`, `eor ... lsr #1`, `subs`, `b.ne`).
#[inline(never)]
pub fn countdown_loop(mut acc: u64, mut n: u64) -> u64 {
    while n != 0 {
        acc ^= acc >> 1;
        n -= 1;
    }
    acc
}

/// 13. Unsigned 64-bit checked addition (`Option<u64>` returned as ScalarPair in `(W0, X1)`).
#[inline(never)]
pub fn checked_add_u64(a: u64, b: u64) -> Option<u64> {
    a.checked_add(b)
}

/// 14. Asserts `x == 0`, panicking for any non-zero input (`assert!(x == 0)`).
#[inline(never)]
pub fn bad(x: u64) {
    assert!(x == 0)
}
