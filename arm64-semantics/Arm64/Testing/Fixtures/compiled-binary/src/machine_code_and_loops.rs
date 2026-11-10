// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! AArch64 assembly subroutines for `Arm64/Testing/Generators/CompiledBinaryFixture.lean`
//! (`Arm64/Testing/Generators/CompiledBinary.lean`).

use core::arch::naked_asm;

/// 1. Unsigned 64-bit maximum (`CMP` + `CSEL`).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn machine_code_max(x: u64, y: u64) -> u64 {
    naked_asm!(
        "cmp x0, x1",
        "csel x0, x0, x1, cs",
        "ret",
    )
}

/// 2. Byte-reverse and logical shift right (`rev64(x) >> 8`).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn machine_code_rev_shift(x: u64) -> u64 {
    naked_asm!(
        "rev x0, x0",
        "lsr x0, x0, #8",
        "ret",
    )
}

/// 3. Iterative accumulation loop (`while (x1 != 0) { x0 += 1; x1 -= 1; }`).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn countdown_add_loop(acc: u64, n: u64) -> u64 {
    naked_asm!(
        "2:",
        "cbz x1, 3f",
        "add x0, x0, #1",
        "sub x1, x1, #1",
        "b 2b",
        "3:",
        "ret",
    )
}
