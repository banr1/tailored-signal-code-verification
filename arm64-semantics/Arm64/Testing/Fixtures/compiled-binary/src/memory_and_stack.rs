// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! AArch64 assembly subroutines for `Arm64/Testing/Generators/CompiledBinaryFixture.lean`
//! (`Arm64/Testing/Generators/CompiledBinary.lean`).

use core::arch::naked_asm;

/// 1. In-place 64-bit memory pointer swap (`swap_mem64(uint64_t *p, uint64_t *q)`).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn swap_mem64(p: *mut u64, q: *mut u64) {
    naked_asm!(
        "ldr x2, [x0]",
        "ldr x3, [x1]",
        "str x3, [x0]",
        "str x2, [x1]",
        "ret",
    )
}

/// 2. AAPCS64 stack frame prologue & epilogue (`STP` pre-index / `LDP` post-index).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn stack_frame(x: u64) -> u64 {
    naked_asm!(
        "stp x29, x30, [sp, #-16]!",
        "mov x29, sp",
        "add x0, x0, #42",
        "ldp x29, x30, [sp], #16",
        "ret",
    )
}
