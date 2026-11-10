// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! AArch64 assembly subroutines for `Arm64/Testing/Generators/CompiledBinaryFixture.lean`
//! (`Arm64/Testing/Generators/CompiledBinary.lean`).

use core::arch::naked_asm;

/// 1. Unscaled `STUR` / `LDUR` round-trip through negative stack offsets.
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn stur_ldur() {
    naked_asm!(
        "stur x0, [sp, #-8]",
        "ldur x1, [sp, #-8]",
        "ret",
    )
}

/// 2. Unscaled accesses at byte, halfword, word and doubleword widths.
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn stur_ldur_sizes() {
    naked_asm!(
        "sturb w0, [x1, #-1]",
        "ldurb w2, [x1, #-1]",
        "sturh w0, [x1, #-2]",
        "ldurh w3, [x1, #-2]",
        "stur w0, [x1, #-4]",
        "ldur w4, [x1, #-4]",
        "stur x0, [x1, #-8]",
        "ldur x5, [x1, #-8]",
        "ret",
    )
}

/// 3. Unscaled stores framed by separation (`stur` + `ldr`).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn stur_disjoint() {
    naked_asm!(
        "stur x0, [x1, #-8]",
        "ldr x2, [x3]",
        "ret",
    )
}

/// 4. Release/acquire publication (`STLR` / `DMB ISH` / `LDAR`).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn publish() {
    naked_asm!(
        "stlr x1, [x0]",
        "dmb ish",
        "ldar x2, [x0]",
        "ret",
    )
}

/// 5. 128-bit `STR q0` / `LDR q1` spill-reload.
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn q_spill() {
    naked_asm!(
        "str q0, [x0]",
        "ldr q1, [x0]",
        "ret",
    )
}

/// 6. Vector `EOR` XOR-swap of two `Q` registers.
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn vec_swap() {
    naked_asm!(
        "eor v0.16b, v0.16b, v1.16b",
        "eor v1.16b, v1.16b, v0.16b",
        "eor v0.16b, v0.16b, v1.16b",
        "ret",
    )
}

/// 7. `DUP` / `UMOV` lane round-trip.
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn dup_umov() {
    naked_asm!(
        "dup v0.2d, x0",
        "umov x1, v0.d[1]",
        "ret",
    )
}

/// 8. `FMOV` GPR <-> vector round-trip.
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn fmov() {
    naked_asm!(
        "fmov x0, d0",
        "fmov d1, x0",
        "ret",
    )
}

/// 9. System registers (`TPIDR_EL0`) and SIMD pair access (`STP`/`LDP`).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn sys_and_simd_pair() {
    naked_asm!(
        "msr tpidr_el0, x0",
        "mrs x9, tpidr_el0",
        "stp d0, d1, [x1]",
        "ldp d2, d3, [x1]",
        "ret",
    )
}

/// 10. `INS` and the vector ALU (`AND`, `ORR`, `ADD`).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn vec_alu() {
    naked_asm!(
        "ins v4.d[0], x0",
        "and v5.16b, v0.16b, v1.16b",
        "orr v6.16b, v0.16b, v1.16b",
        "add v7.4s, v0.4s, v1.4s",
        "ret",
    )
}

/// 11. Single-round AES encryption (`AESE`).
#[unsafe(no_mangle)]
#[unsafe(naked)]
pub unsafe extern "C" fn aes() {
    naked_asm!(
        ".arch_extension aes",
        "aese v0.16b, v1.16b",
        "ret",
    )
}
