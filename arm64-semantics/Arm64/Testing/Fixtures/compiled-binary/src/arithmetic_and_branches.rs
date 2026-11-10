// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! AArch64 assembly subroutines for `Arm64/Testing/Generators/CompiledBinaryFixture.lean`
//! (`Arm64/Testing/Generators/CompiledBinary.lean`).

use core::arch::naked_asm;

/// 1. Shifted arithmetic subroutine: `(x + (y << 3)) - 1`.
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn shift_add_sub(x: u64, y: u64) -> u64 {
    naked_asm!(
        "add x0, x0, x1, lsl #3",
        "sub x0, x0, #1",
        "ret",
    )
}

/// 2. Branchless unsigned maximum (`max_u64(x, y)` via `CMP` + `CSEL`).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn max_u64_csel(x: u64, y: u64) -> u64 {
    naked_asm!(
        "cmp x0, x1",
        "csel x0, x0, x1, cs",
        "ret",
    )
}

/// 3. Branchless signed absolute value (`abs_i64(x)` via `CMP` + `CSNEG`).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn abs_i64_csneg(x: i64) -> i64 {
    naked_asm!(
        "cmp x0, #0",
        "csneg x0, x0, x0, ge",
        "ret",
    )
}

/// 4. Branching unsigned maximum (`max_u64(x, y)` via `CMP` + `B.CS` + `MOV`).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn max_u64_branch(x: u64, y: u64) -> u64 {
    naked_asm!(
        "cmp x0, x1",
        "b.cs 2f",
        "mov x0, x1",
        "2:",
        "ret",
    )
}

/// 5. Compare-and-branch-on-zero (`CBZ` default fallback).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn cbz_fallback(x: u64) -> u64 {
    naked_asm!(
        "cbz x0, 2f",
        "sub x0, x0, #1",
        "ret",
        "2:",
        "mov x0, #42",
        "ret",
    )
}
