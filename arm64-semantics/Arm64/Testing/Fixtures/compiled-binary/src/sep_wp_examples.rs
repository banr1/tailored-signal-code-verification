// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! AArch64 assembly subroutines for `Arm64/Testing/Generators/CompiledBinaryFixture.lean`
//! (`Arm64/Testing/Generators/CompiledBinary.lean`).

use core::arch::{global_asm, naked_asm};

/// 1. `tiered_fee_schedule` (3-tier piecewise fee + priority surcharge diamond).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn tiered_fee_schedule() {
    naked_asm!(
        "ldp x2, x3, [x0]",
        "cmp x2, #100",
        "b.hs 2f",
        "mov x4, #5",
        "b 4f",
        "2:",
        "cmp x2, #500",
        "b.hs 3f",
        "lsr x4, x2, #3",
        "add x4, x4, #10",
        "b 4f",
        "3:",
        "lsr x4, x2, #2",
        "add x4, x4, #25",
        "4:",
        "cbz x3, 5f",
        "add x4, x4, #15",
        "5:",
        "add x5, x2, x4",
        "stp x4, x5, [x1]",
        "add x0, x4, #0",
        "ret",
    )
}

/// 2. `sort3_in_place` (3-element in-place sorting network in memory).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn sort3_in_place() {
    naked_asm!(
        "ldr x1, [x0]",
        "ldr x2, [x0, #8]",
        "ldr x3, [x0, #16]",
        "cmp x1, x2",
        "b.ls 2f",
        "add x4, x1, #0",
        "add x1, x2, #0",
        "add x2, x4, #0",
        "2:",
        "cmp x2, x3",
        "b.ls 3f",
        "add x4, x2, #0",
        "add x2, x3, #0",
        "add x3, x4, #0",
        "3:",
        "cmp x1, x2",
        "b.ls 4f",
        "add x4, x1, #0",
        "add x1, x2, #0",
        "add x2, x4, #0",
        "4:",
        "str x1, [x0]",
        "str x2, [x0, #8]",
        "str x3, [x0, #16]",
        "add x0, x2, #0",
        "ret",
    )
}

/// 3. `validate_packet_header` (multi-stage header validator with early-exit branches).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn validate_packet_header() {
    naked_asm!(
        "ldr x3, [x0]",
        "ldr x4, [x0, #8]",
        "ldr x5, [x0, #16]",
        "cbz x3, 2f",
        "cbz x4, 3f",
        "cmp x4, x1",
        "b.hi 4f",
        "mov x6, #0",
        "eor x7, x3, x4",
        "add x7, x7, x5",
        "eor x7, x7, x4, lsl #2",
        "b 5f",
        "2:",
        "mov x6, #1",
        "mov x7, #0",
        "b 5f",
        "3:",
        "mov x6, #2",
        "mov x7, #0",
        "b 5f",
        "4:",
        "mov x6, #3",
        "mov x7, #0",
        "5:",
        "stp x6, x7, [x2]",
        "add x0, x6, #0",
        "ret",
    )
}

/// 5. `transfer_balance` (cross-account atomic transfer with audit counter).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn transfer_balance() {
    naked_asm!(
        "ldr x4, [x0]",
        "cmp x4, x2",
        "b.lo 2f",
        "sub x4, x4, x2",
        "ldr x5, [x0, #8]",
        "add x5, x5, #1",
        "stp x4, x5, [x0]",
        "ldp x6, x7, [x1]",
        "add x6, x6, x2",
        "add x7, x7, #1",
        "stp x6, x7, [x1]",
        "mov x0, #1",
        "ret",
        "2:",
        "ldr x5, [x3]",
        "add x5, x5, #1",
        "str x5, [x3]",
        "mov x0, #0",
        "ret",
    )
}

// 4. `swap_and_accumulate` and 6. `rotate_and_commit_ctx`.
global_asm!(
    ".section .text.sep_wp_examples,\"ax\",@progbits",
    ".balign 4",

    ".globl swap_and_accumulate",
    ".type swap_and_accumulate, @function",
    "swap_and_accumulate:",
    ".Lswap_and_accumulate:",
    "ldr x3, [x0]",
    "ldr x4, [x1]",
    "str x4, [x0]",
    "str x3, [x1]",
    "ldr x5, [x2]",
    "eor x6, x3, x4",
    "add x5, x5, x6",
    "str x5, [x2]",
    "add x0, x5, #0",
    "ret",
    ".size swap_and_accumulate, .-swap_and_accumulate",

    ".globl rotate_and_commit_ctx",
    ".type rotate_and_commit_ctx, @function",
    "rotate_and_commit_ctx:",
    "stp x19, x30, [sp, #-32]!",
    "stp x20, x21, [sp, #16]",
    "add x19, x0, #0",
    "add x20, x1, #0",
    "add x21, x2, #0",
    "bl .Lswap_and_accumulate",
    "ldr x1, [x19]",
    "bl mix_step",
    "str x0, [x21, #8]",
    "ldp x20, x21, [sp, #16]",
    "ldp x19, x30, [sp], #32",
    "ret",
    ".size rotate_and_commit_ctx, .-rotate_and_commit_ctx",
);
