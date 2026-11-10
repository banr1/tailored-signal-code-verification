// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! AArch64 assembly subroutines for `Arm64/Testing/Regression/FunctionalCorrectness.lean`
//! (`Arm64/Testing/Generators/CompiledBinaryFixture.lean`).

use core::arch::naked_asm;

/// 1. Unsigned division & remainder (`UDIV` + `MSUB`).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn divmod_u64() {
    naked_asm!(
        "udiv x2, x0, x1",
        "msub x1, x2, x1, x0",
        "mov x0, x2",
        "ret",
    )
}

/// 2. 64-bit endianness byte swap, leading zero count, bit reversal & bitfields.
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn bswap_and_clz_u64() {
    naked_asm!(
        "rev x0, x0",
        "clz x1, x0",
        "rbit x2, x0",
        "ubfx x3, x0, #8, #16",
        "sbfx x4, x0, #8, #8",
        "ret",
    )
}

/// 3. 128-bit multi-word addition with carry (`ADDS` + `ADC`).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn add128_u64() {
    naked_asm!(
        "adds x0, x0, x2",
        "adc x1, x1, x3",
        "ret",
    )
}

/// 4. Signed 32-to-64 sign-extending multiply-accumulate & signed division (`SMADDL` + `SDIV` + `CSINC` + `CSINV`).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn smaddl_sdiv_i64() {
    naked_asm!(
        "smaddl x4, w0, w1, x2",
        "sdiv x0, x4, x3",
        "cmp x4, #0",
        "csinc x1, x0, x0, ge",
        "csinv x2, x4, x4, ge",
        "ret",
    )
}

/// 5. Stack frame spill/reload & struct update subroutine (`STP`/`LDP` with 32-byte frame).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn stack_spill_struct_update() {
    naked_asm!(
        "stp x29, x30, [sp, #-32]!",
        "stp x19, x20, [sp, #16]",
        "ldp x19, x20, [x0]",
        "add x19, x19, x1",
        "sub x20, x20, x1",
        "stp x19, x20, [x0]",
        "add x0, x19, x20",
        "ldp x19, x20, [sp, #16]",
        "ldp x29, x30, [sp], #32",
        "ret",
    )
}
