// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! AArch64 assembly subroutines for `Arm64/Testing/Generators/CompiledBinaryFixture.lean`
//! (`Arm64/Testing/Generators/CompiledBinary.lean`).

use core::arch::global_asm;

global_asm!(
    ".section .text.compositional_calls,\"ax\",@progbits",
    ".balign 4",

    ".globl foo",
    ".type foo, @function",
    "foo:",
    ".Lfoo:",
    "add x0, x0, #1",
    "ret",
    ".size foo, .-foo",

    ".globl baz",
    ".type baz, @function",
    "baz:",
    ".Lbaz:",
    "add x0, x0, #42",
    "ret",
    ".size baz, .-baz",

    ".globl bar",
    ".type bar, @function",
    "bar:",
    ".Lbar:",
    "stp x19, x30, [sp, #-16]!",
    "add x19, x0, #0",
    "bl .Lfoo",
    "add x0, x0, x19",
    "ldp x19, x30, [sp], #16",
    "ret",
    ".size bar, .-bar",

    ".globl twoCalls",
    ".type twoCalls, @function",
    "twoCalls:",
    "stp x19, x30, [sp, #-16]!",
    "bl .Lfoo",
    "add x19, x0, #0",
    "bl .Lbaz",
    "add x0, x0, x19",
    "ldp x19, x30, [sp], #16",
    "ret",
    ".size twoCalls, .-twoCalls",

    ".globl outer",
    ".type outer, @function",
    "outer:",
    "stp x19, x30, [sp, #-16]!",
    "add x19, x0, #0",
    "bl .Lbar",
    "add x0, x0, x19",
    "ldp x19, x30, [sp], #16",
    "ret",
    ".size outer, .-outer",

    ".globl leafTailCall",
    ".type leafTailCall, @function",
    "leafTailCall:",
    "add x0, x0, #10",
    "b .Lfoo",
    ".size leafTailCall, .-leafTailCall",

    ".globl callThenTailCall",
    ".type callThenTailCall, @function",
    "callThenTailCall:",
    "stp x19, x30, [sp, #-16]!",
    "add x19, x0, #0",
    "bl .Lfoo",
    "add x0, x0, x19",
    "ldp x19, x30, [sp], #16",
    "b .Lbaz",
    ".size callThenTailCall, .-callThenTailCall",
);
