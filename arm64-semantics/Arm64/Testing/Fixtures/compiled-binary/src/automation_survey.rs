// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! AArch64 assembly subroutines for `Arm64/Testing/Generators/CompiledBinaryFixture.lean`
//! (`Arm64/Testing/Generators/CompiledBinary.lean`).

use core::arch::{global_asm, naked_asm};

/// 1. Benchmark 1: `clamp_and_store` (control-flow diamond + memory framing).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn clamp_and_store() {
    naked_asm!(
        "ldr x4, [x0]",
        "cmp x4, x2",
        "b.hs 2f",
        "add x4, x2, #0",
        "b 3f",
        "2:",
        "cmp x3, x4",
        "b.hs 3f",
        "add x4, x3, #0",
        "3:",
        "str x4, [x1]",
        "add x0, x4, #0",
        "ret",
    )
}

/// 3. Benchmark 3: `mem_countdown_loop` (pre-loop load + loop invariant + post-loop store).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn mem_countdown_loop() {
    naked_asm!(
        "ldr x3, [x0]",
        "2:",
        "cbz x1, 3f",
        "add x3, x3, #1",
        "sub x1, x1, #1",
        "b 2b",
        "3:",
        "str x3, [x0]",
        "add x0, x3, #0",
        "ret",
    )
}

// Benchmarks 2 (`mix_step`, `tag_finalize`, `hash_pair_and_store`) and 4 (`auth_counter_send`).
global_asm!(
    ".section .text.automation_survey,\"ax\",@progbits",
    ".balign 4",

    ".globl mix_step",
    ".type mix_step, @function",
    "mix_step:",
    ".Lmix_step:",
    "eor x0, x0, x1",
    "add x0, x0, #7",
    "ret",
    ".size mix_step, .-mix_step",

    ".globl tag_finalize",
    ".type tag_finalize, @function",
    "tag_finalize:",
    ".Ltag_finalize:",
    "add x0, x0, #42",
    "ret",
    ".size tag_finalize, .-tag_finalize",

    ".globl hash_pair_and_store",
    ".type hash_pair_and_store, @function",
    "hash_pair_and_store:",
    "stp x19, x30, [sp, #-16]!",
    "add x19, x0, #0",
    "ldr x0, [x19]",
    "bl .Lmix_step",
    "ldr x1, [x19, #8]",
    "bl .Lmix_step",
    "bl .Ltag_finalize",
    "str x0, [x19, #16]",
    "ldp x19, x30, [sp], #16",
    "ret",
    ".size hash_pair_and_store, .-hash_pair_and_store",

    ".globl auth_counter_send",
    ".type auth_counter_send, @function",
    "auth_counter_send:",
    "stp x19, x30, [sp, #-16]!",
    "add x19, x1, #0",
    "ldr x3, [x0]",
    "add x4, x3, #1",
    "str x4, [x0]",
    "str x3, [x19]",
    "ldr x1, [x0, #8]",
    "eor x0, x2, x3",
    "bl .Lmix_step",
    "cbnz x0, 2f",
    "mov x0, #1",
    "2:",
    "str x0, [x19, #8]",
    "ldp x19, x30, [sp], #16",
    "ret",
    ".size auth_counter_send, .-auth_counter_send",
);
