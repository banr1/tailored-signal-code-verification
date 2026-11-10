/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Testing.Harness.TestCase

/-!
# Hand-Written Multi-Instruction Differential Vectors

Defines hand-written multi-instruction `IsaTestCase` suites (`cAlgorithmicSubroutineCases`,
`isaSurfaceAndScalarFpCases`, `extendedFpSimdAtomicsAndBoundaryCases`, and their union
`handWrittenVectorCases`) covering integer loops, memory/atomic instructions, AdvSIMD/crypto,
system registers, and scalar IEEE-754 floating-point boundary behavior.
-/

@[expose] public section

namespace Testing.Generators

open Arm64
open Testing.Harness

/-- Hand-written C-style algorithmic loop subroutines (Euclidean GCD, Fibonacci, popcount). -/
def cAlgorithmicSubroutineCases : Array IsaTestCase := #[
  makeAsmTestCase
    "C_Subroutine/Euclidean_GCD_u64(1071, 462) == 21"
    "loop:\ncbz x1, done\nudiv x2, x0, x1\nmsub x2, x2, x1, x0\nmov x0, x1\nmov x1, x2\nb loop\ndone:\nnop"
    (regs := [(0, 1071#64), (1, 462#64)]),

  makeAsmTestCase
    "C_Subroutine/Fibonacci_Iter(15) == 610"
    "mov x1, #0\nmov x2, #1\ncbz x0, done\nloop:\nadd x3, x1, x2\nmov x1, x2\nmov x2, x3\nsub x0, x0, #1\ncbnz x0, loop\ndone:\nmov x0, x1"
    (regs := [(0, 15#64)]),

  makeAsmTestCase
    "C_Subroutine/Bit_Twiddling_Popcount(0xF0F00F0F12345678)"
    "mov x1, #0\nloop:\ncbz x0, done\nsub x2, x0, #1\nand x0, x0, x2\nadd x1, x1, #1\nb loop\ndone:\nmov x0, x1"
    (regs := [(0, 0xf0f00f0f12345678#64)])
]

/-- Hand-written ISA surface, AdvSIMD, AES, `TPIDR_EL0`, and scalar IEEE-754 FP vectors. -/
def isaSurfaceAndScalarFpCases : Array IsaTestCase := #[
  makeAsmTestCase
    "IsaSurface/LdurStur_AlignedAndUnaligned"
    "stur x0, [x10, #8]\nldur x2, [x10, #8]\nsturb w1, [x10, #16]\nldurb w3, [x10, #16]\nstur x0, [x10, #-8]\nldur x4, [x10, #-8]"
    (regs := [(0, 0x1122334455667788#64), (1, 0xaabbccdd#64), (10, dataBase + 64#64)])
    (memWatchU64 := [dataBase + 56#64, dataBase + 72#64, dataBase + 80#64]),

  makeAsmTestCase
    "IsaSurface/LdarStlr_And_Dmb"
    "stlr x0, [x10]\ndmb ish\nldar x2, [x10]\nadd x11, x10, #8\nstlrb w1, [x11]\ndmb ish\nldarb w3, [x11]"
    (regs := [(0, 0xcafebabe12345678#64), (1, 0x000000ab#64), (10, dataBase)])
    (memWatchU64 := [dataBase, dataBase + 8#64]),

  makeAsmTestCase
    "IsaSurface/SimdLoadStore_VectorArith_Permute_Ext"
    "stp x0, x1, [x10]\nldr q0, [x10]\ndup v1.16b, w2\neor v2.16b, v0.16b, v1.16b\nrev64 v3.16b, v2.16b\next v4.16b, v2.16b, v3.16b, #8\nuzp1 v5.16b, v2.16b, v3.16b\nzip1 v6.16b, v2.16b, v3.16b\nstr q4, [x10, #16]\nstr q5, [x10, #32]\nstr q6, [x10, #48]\nfmov x3, d4\nfmov x4, v4.d[1]"
    (regs := [(0, 0x0102030405060708#64), (1, 0x1112131415161718#64), (2, 0x5a#64), (10, dataBase)])
    (memWatchU64 := [dataBase + 16#64, dataBase + 24#64, dataBase + 32#64, dataBase + 40#64, dataBase + 48#64, dataBase + 56#64]),

  makeAsmTestCase
    "IsaSurface/AES_SingleRound_And_MixColumns"
    "stp x0, x1, [x10]\nstp x2, x3, [x10, #16]\nldr q0, [x10]\nldr q1, [x10, #16]\naese v0.16b, v1.16b\naesmc v0.16b, v0.16b\nstr q0, [x10, #32]\nfmov x4, d0\nfmov x5, v0.d[1]"
    (regs := [
      (0, 0x0011223344556677#64),
      (1, 0x8899aabbccddeeff#64),
      (2, 0x0001020304050607#64),
      (3, 0x08090a0b0c0d0e0f#64),
      (10, dataBase)
    ])
    (memWatchU64 := [dataBase + 32#64, dataBase + 40#64]),

  makeAsmTestCase
    "IsaSurface/SimdCompare_Umaxv_Shifts_St1Post"
    "stp x0, x1, [x10]\nldr q0, [x10]\ncmeq v1.16b, v0.16b, #0\ncmlt v2.16b, v0.16b, #0\numaxv b3, v0.16b\nfmov w4, s3\nshl v5.2d, v0.2d, #4\nushll v6.8h, v0.8b, #0\nushll2 v7.8h, v0.16b, #0\nstr q5, [x10, #16]\nstr q6, [x10, #32]\nstr q7, [x10, #48]\nadd x12, x10, #64\nst1 { v0.b }[15], [x12], #1"
    (regs := [(0, 0x80007f0100ff1234#64), (1, 0xfe0055aa10203040#64), (10, dataBase)])
    (memWatchU64 := [dataBase + 16#64, dataBase + 24#64, dataBase + 32#64, dataBase + 40#64, dataBase + 48#64, dataBase + 56#64, dataBase + 64#64]),

  -- ASL: `SSHL` with a negative shift count is an arithmetic right shift
  -- (`RShr(SInt(elem), -shift)`), `USHL` a logical one; `|shift| >= esize` saturates.
  makeAsmTestCase
    "AslAudit/SimdSshlUshl_NegativePositiveAndSaturatedShifts"
    "stp x0, x1, [x10]\nstp x2, x3, [x10, #16]\nldr q0, [x10]\nldr q1, [x10, #16]\nsshl v2.4s, v0.4s, v1.4s\nushl v3.4s, v0.4s, v1.4s\nsshl v4.16b, v0.16b, v1.16b\nushl v5.8h, v0.8h, v1.8h\nsshl v6.8h, v0.8h, v1.8h\nstr q2, [x10, #32]\nstr q3, [x10, #48]\nstr q4, [x10, #64]\nstr q5, [x10, #80]\nstr q6, [x10, #96]"
    (regs := [
      (0, 0x8000000000000080#64),
      (1, 0x80ff7f01ffffffff#64),
      (2, 0xfffffffcffffffff#64),
      (3, 0x000000fee0000003#64),
      (10, dataBase)
    ])
    (memWatchU64 := [dataBase + 32#64, dataBase + 40#64, dataBase + 48#64, dataBase + 56#64,
                     dataBase + 64#64, dataBase + 72#64, dataBase + 80#64, dataBase + 88#64,
                     dataBase + 96#64, dataBase + 104#64]),

  makeAsmTestCase
    "IsaSurface/SysReg_Mrs_Msr_TpidrEl0"
    "msr tpidr_el0, x0\nmrs x1, tpidr_el0\nadd x2, x1, #1\nmsr tpidr_el0, x2\nmrs x3, tpidr_el0\nmsr tpidr_el0, xzr\nmrs x4, tpidr_el0"
    (regs := [(0, 0x1122334455667788#64)]),

  makeAsmTestCase
    "ScalarFP/FabsFnegFsqrt_F64_And_F32"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov d3, x3\nfmov d4, x4\nfmov d5, x5\nfabs d6, d1\nfneg d7, d0\nfsqrt d8, d0\nfsqrt d9, d1\nfsqrt d10, d2\nfsqrt d11, d3\nfsqrt d12, d4\nfabs d13, d5\nfneg d14, d5\nfsqrt d15, d5\nfmov x10, d6\nfmov x11, d7\nfmov x12, d8\nfmov x13, d9\nfmov x14, d10\nfmov x15, d11\nfmov x16, d12\nfmov x17, d13\nfmov x18, d14\nfmov x19, d15\nfmov s20, w6\nfabs s21, s20\nfneg s22, s20\nfsqrt s23, s20\nfmov s24, w7\nfsqrt s25, s24\nfmov w20, s21\nfmov w21, s22\nfmov w22, s23\nfmov w23, s25"
    (regs := [
      (0, 0x4002000000000000#64), -- +2.25
      (1, 0xc002000000000000#64), -- -2.25
      (2, 0x8000000000000000#64), -- -0.0
      (3, 0x7ff0000000000000#64), -- +Inf
      (4, 0x0000000000000001#64), -- min subnormal f64
      (5, 0xfff0000000000005#64), -- negative sNaN f64
      (6, 0x41100000#64),         -- +9.0f32
      (7, 0x7f800003#64)          -- sNaN f32
    ]),

  makeAsmTestCase
    "ScalarFP/Frint_AllModes_F64_And_F32"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov d3, x3\nfrintn d4, d0\nfrintn d5, d1\nfrinta d6, d0\nfrinta d7, d2\nfrintp d8, d0\nfrintp d9, d2\nfrintm d10, d0\nfrintm d11, d2\nfrintz d12, d1\nfrintz d13, d2\nfrintx d14, d0\nfrinti d15, d1\nfrintn d16, d3\nfmov x10, d4\nfmov x11, d5\nfmov x12, d6\nfmov x13, d7\nfmov x14, d8\nfmov x15, d9\nfmov x16, d10\nfmov x17, d11\nfmov x18, d12\nfmov x19, d13\nfmov x20, d14\nfmov x21, d15\nfmov x22, d16\nfmov s0, w4\nfrintn s1, s0\nfrinta s2, s0\nfrintp s3, s0\nfrintm s4, s0\nfrintz s5, s0\nfmov w23, s1\nfmov w24, s2\nfmov w25, s3\nfmov w26, s4\nfmov w27, s5"
    (regs := [
      (0, 0x3ff8000000000000#64), -- +1.5
      (1, 0x4004000000000000#64), -- +2.5
      (2, 0xbff8000000000000#64), -- -1.5
      (3, 0xbfd0000000000000#64), -- -0.25 (rounds to -0.0 under RNE/RTN/RTZ/RNA)
      (4, 0xc0200000#64)          -- -2.5f32
    ]),

  makeAsmTestCase
    "ScalarFP/FaddFsub_NormalSubnormalInfNaN_F64_And_F32"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov d3, x3\nfmov d4, x4\nfmov d5, x5\nfmov d6, x6\nfmov d7, x7\nfadd d8, d0, d1\nfsub d9, d0, d1\nfsub d10, d0, d0\nfadd d11, d2, d2\nfadd d12, d3, d4\nfadd d13, d5, d5\nfsub d14, d6, d6\nfsub d15, d0, d7\nfmov x10, d8\nfmov x11, d9\nfmov x12, d10\nfmov x13, d11\nfmov x14, d12\nfmov x15, d13\nfmov x16, d14\nfmov x17, d15\nfmov s0, w8\nfmov s1, w9\nfadd s2, s0, s1\nfsub s3, s0, s1\nfmov w18, s2\nfmov w19, s3"
    (regs := [
      (0, 0x3ff8000000000000#64), -- 1.5
      (1, 0x4002000000000000#64), -- 2.25
      (2, 0x8000000000000000#64), -- -0.0
      (3, 0x000fffffffffffff#64), -- max subnormal f64
      (4, 0x0000000000000001#64), -- min subnormal f64
      (5, 0x7fefffffffffffff#64), -- max normal f64
      (6, 0x7ff0000000000000#64), -- +Inf
      (7, 0x7ff8000000000abc#64), -- +qNaN (fsub(1.5, qNaN) preserves +qNaN sign)
      (8, 0x3fc00000#64),         -- 1.5f32
      (9, 0xc0100000#64)          -- -2.25f32
    ]),

  makeAsmTestCase
    "ScalarFP/FmulFnmulFdiv_F64_And_F32"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov d3, x3\nfmov d4, x4\nfmov d5, x5\nfmov d6, x6\nfmul d7, d0, d1\nfnmul d8, d0, d1\nfdiv d9, d0, d1\nfdiv d10, d0, d2\nfmul d11, d3, d5\nfdiv d12, d1, d3\nfmul d13, d4, d0\nfnmul d14, d0, d6\nfdiv d15, d3, d3\nfmov x10, d7\nfmov x11, d8\nfmov x12, d9\nfmov x13, d10\nfmov x14, d11\nfmov x15, d12\nfmov x16, d13\nfmov x17, d14\nfmov x18, d15\nfmov s0, w7\nfmov s1, w8\nfmul s2, s0, s1\nfnmul s3, s0, s1\nfdiv s4, s0, s1\nfmov w19, s2\nfmov w20, s3\nfmov w21, s4"
    (regs := [
      (0, 0x3ff0000000000000#64), -- 1.0
      (1, 0x4008000000000000#64), -- 3.0
      (2, 0x4004000000000000#64), -- 2.5
      (3, 0x8000000000000000#64), -- -0.0
      (4, 0x0010000000000000#64), -- min normal f64
      (5, 0x7ff0000000000000#64), -- +Inf
      (6, 0x7ff8000000000011#64), -- +qNaN
      (7, 0x40400000#64),         -- 3.0f32
      (8, 0x40e00000#64)          -- 7.0f32
    ]),

  makeAsmTestCase
    "ScalarFP/FmaxFminFmaxnmFminnm_F64_And_F32"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov d3, x3\nfmov d4, x4\nfmov d5, x5\nfmax d6, d0, d1\nfmin d7, d0, d1\nfmax d8, d2, d3\nfmin d9, d2, d3\nfmax d10, d0, d4\nfmaxnm d11, d0, d4\nfminnm d12, d4, d1\nfmaxnm d13, d0, d5\nfmov x10, d6\nfmov x11, d7\nfmov x12, d8\nfmov x13, d9\nfmov x14, d10\nfmov x15, d11\nfmov x16, d12\nfmov x17, d13\nfmov s0, w6\nfmov s1, w7\nfmax s2, s0, s1\nfmin s3, s0, s1\nfmaxnm s4, s0, s1\nfminnm s5, s0, s1\nfmov w18, s2\nfmov w19, s3\nfmov w20, s4\nfmov w21, s5"
    (regs := [
      (0, 0x3ff8000000000000#64), -- 1.5
      (1, 0xc004000000000000#64), -- -2.5
      (2, 0x0000000000000000#64), -- +0.0
      (3, 0x8000000000000000#64), -- -0.0
      (4, 0x7ff8000000000022#64), -- qNaN
      (5, 0x7ff0000000000033#64), -- sNaN
      (6, 0x3fc00000#64),         -- 1.5f32
      (7, 0x7fc00005#64)          -- qNaN f32
    ]),

  makeAsmTestCase
    "ScalarFP/FmaddFmsubFnmaddFnmsub_SingleRounding_F64_And_F32"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov d3, x3\nfmov d4, x4\nfmadd d5, d0, d1, d2\nfmsub d6, d0, d1, d2\nfnmadd d7, d0, d1, d2\nfnmsub d8, d0, d1, d2\nfmsub d9, d3, d3, d4\nfmov x10, d5\nfmov x11, d6\nfmov x12, d7\nfmov x13, d8\nfmov x14, d9\nfmov s0, w5\nfmov s1, w6\nfmov s2, w7\nfmadd s3, s0, s1, s2\nfmsub s4, s0, s1, s2\nfnmadd s5, s0, s1, s2\nfnmsub s6, s0, s1, s2\nfmov w15, s3\nfmov w16, s4\nfmov w17, s5\nfmov w18, s6"
    (regs := [
      (0, 0x4000000000000000#64), -- 2.0
      (1, 0x4008000000000000#64), -- 3.0
      (2, 0x4010000000000000#64), -- 4.0
      (3, 0x3ff0000000000001#64), -- 1.0 + 2^-52 (single-rounding FMA)
      (4, 0xbff0000000000000#64), -- -1.0 (so d4 - d3*d3 or d3*d3 - 1.0)
      (5, 0x40000000#64),         -- 2.0f32
      (6, 0x40400000#64),         -- 3.0f32
      (7, 0x40800000#64)          -- 4.0f32
    ]),

  makeAsmTestCase
    "ScalarFP/FcmpFcmpeFccmpFcsel_F64_And_F32"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov d3, x3\nfmov d4, x4\nfcmp d0, d1\ncset x10, mi\ncset x11, lt\ncset x12, gt\ncset x13, ge\nfcmp d2, #0.0\ncset x14, eq\ncset x15, le\nfcmpe d0, d4\ncset x16, vs\ncset x17, hi\ncset x18, lt\nfcsel d5, d0, d1, vs\nfcsel d6, d0, d1, vc\nfmov x19, d5\nfmov x20, d6\nfcmp d0, d1\nfccmp d1, d0, #0, mi\ncset x21, gt\nfccmp d1, d0, #4, gt\nmov x22, #0\nfmov s0, w5\nfmov s1, w6\nfcmp s0, s1\n"
    (regs := [
      (0, 0x3ff8000000000000#64), -- 1.5
      (1, 0x4004000000000000#64), -- 2.5
      (2, 0x8000000000000000#64), -- -0.0
      (3, 0x0000000000000000#64), -- +0.0
      (4, 0x7ff8000000000001#64), -- qNaN
      (5, 0xc0400000#64),         -- -3.0f32
      (6, 0x40000000#64)          -- +2.0f32
    ]),

  makeAsmTestCase
    "ScalarFP/Fcvt_IntConv_And_FixedPoint"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov s3, w3\nfcvt s4, d0\nfcvt d5, s3\nfmov w10, s4\nfmov x11, d5\nfcvtns x12, d0\nfcvtnu x13, d0\nfcvtps x14, d0\nfcvtpu x15, d0\nfcvtms x16, d0\nfcvtmu x17, d1\nfcvtas x18, d0\nfcvtau x19, d0\nfcvtzs x20, d1\nfcvtzu x21, d2\nscvtf d6, x4\nucvtf d7, x5\nscvtf s8, w6\nucvtf s9, w7\nfmov x22, d6\nfmov x23, d7\nfmov w24, s8\nfmov w25, s9\nscvtf d10, x4, #4\nucvtf d11, x5, #8\nfcvtzs x26, d0, #4\nfcvtzu w27, s3, #3\nfmov x28, d10"
    (regs := [
      (0, 0x4004000000000000#64), -- +2.5
      (1, 0xc004000000000000#64), -- -2.5
      (2, 0x7ff8000000000001#64), -- qNaN (-> 0 for integer conversions)
      (3, 0x40300000#64),         -- +2.75f32
      (4, 0xffffffffffffffec#64), -- -20 (signed 64-bit)
      (5, 0x0000000000000190#64), -- 400 (unsigned 64-bit)
      (6, 0xffffffce#64),         -- -50 (signed 32-bit)
      (7, 0x000000fa#64)          -- 250 (unsigned 32-bit)
    ]),

  makeAsmTestCase
    "ScalarFP/FmaddNaN_And_InfZero_EdgeCases"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov d3, x3\nfmov d4, x4\nfmov d5, x5\nfmadd d6, d0, d1, d3\nfmadd d7, d1, d0, d3\nfmadd d8, d2, d2, d3\nfmsub d9, d2, d2, d3\nfnmadd d10, d2, d2, d3\nfnmsub d11, d2, d2, d3\nfmadd d12, d2, d4, d3\nfmadd d13, d5, d2, d3\nfmov x10, d6\nfmov x11, d7\nfmov x12, d8\nfmov x13, d9\nfmov x14, d10\nfmov x15, d11\nfmov x16, d12\nfmov x17, d13"
    (regs := [
      (0, 0x0000000000000000#64), -- +0.0
      (1, 0x7ff0000000000000#64), -- +Inf
      (2, 0x3ff0000000000000#64), -- 1.0
      (3, 0x7ff8000000000011#64), -- qNaN in Ra
      (4, 0x7ff8000000000022#64), -- qNaN in Rm
      (5, 0x7ff0000000000033#64)  -- sNaN in Rn (takes precedence over qNaN in Ra)
    ]),

  makeAsmTestCase
    "ScalarFP/IntSaturation_And_SubnormalFcvt_EdgeCases"
    "fmov d0, x0\nfmov d1, x1\nfmov s2, w2\nfmov d3, x3\nfcvtzs x10, d0\nfcvtzu x11, d0\nfcvtzs x12, d1\nfcvtzu x13, d1\nfcvtzs w14, d0\nfcvtzu w15, d0\nfcvtzs w16, d1\nfcvtzu w17, d1\nscvtf d4, x4\nucvtf d5, x5\nscvtf s6, x4\nucvtf s7, x5\nfcvt d8, s2\nfcvt s9, d3\nfmov x18, d4\nfmov x19, d5\nfmov w20, s6\nfmov w21, s7\nfmov x22, d8\nfmov w23, s9"
    (regs := [
      (0, 0x7ff0000000000000#64), -- +Inf (saturates to INT_MAX / UINT_MAX)
      (1, 0xfff0000000000000#64), -- -Inf (saturates to INT_MIN / 0)
      (2, 0x00000001#64),         -- min subnormal f32 (widens to normal f64)
      (3, 0x36a0000000000000#64), -- 2^-149 in f64 (narrows to min subnormal f32)
      (4, 0x8000000000000000#64), -- INT64_MIN (-2^63)
      (5, 0xffffffffffffffff#64)  -- UINT64_MAX (2^64 - 1, rounds up to 2^64)
    ])
]

/-- Extended scalar FP, AdvSIMD, crypto, LSE atomics, RCpc, CRC32, and integer/SIMD boundary vectors. -/
def extendedFpSimdAtomicsAndBoundaryCases : Array IsaTestCase := #[
  makeAsmTestCase
    "ScalarFP/FP1_Double_FmovFabsFnegFsqrtFcvt"
    "fmov d0, x0\nfmov d1, d0\nfabs d2, d1\nfneg d3, d2\nfsqrt d4, d2\nfmov d5, x1\nfsqrt d5, d5\nfmov d6, x2\nfsqrt d6, d6\nfmov d7, x3\nfsqrt d7, d7\nfcvt s16, d2\nfcvt d17, s16\nfmov d18, x4\nfcvt s19, d18\nfcvt d20, s19\nfmov x10, d1\nfmov x11, d2\nfmov x12, d3\nfmov x13, d4\nfmov x14, d5\nfmov x15, d6\nfmov x16, d7\nfmov w17, s16\nfmov x18, d17\nfmov w19, s19\nfmov x20, d20"
    (regs := [
      (0, 0xc022000000000000#64), -- -9.0
      (1, 0x4000000000000000#64), -- 2.0
      (2, 0x8000000000000000#64), -- -0.0
      (3, 0xc010000000000000#64), -- -4.0 (sqrt -> default NaN)
      (4, 0x7ff000123456789a#64)  -- SNaN
    ]),

  makeAsmTestCase
    "ScalarFP/FP1_Single_FmovFabsFnegFsqrt"
    "fmov s0, w0\nfmov s1, s0\nfabs s2, s1\nfneg s3, s2\nfsqrt s4, s2\nfmov s5, w1\nfsqrt s5, s5\nfmov s6, w2\nfsqrt s6, s6\nfmov s7, w3\nfsqrt s7, s7\nfmov w10, s1\nfmov w11, s2\nfmov w12, s3\nfmov w13, s4\nfmov w14, s5\nfmov w15, s6\nfmov w16, s7"
    (regs := [
      (0, 0xc1c80000#64), -- -25.0f
      (1, 0x40400000#64), -- 3.0f
      (2, 0x80000000#64), -- -0.0f
      (3, 0xbf800000#64)  -- -1.0f
    ]),

  makeAsmTestCase
    "ScalarFP/FP1_Double_Frint_AllModes"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov d3, x3\nfrintn d10, d0\nfrintn d11, d1\nfrintn d12, d2\nfrintp d13, d0\nfrintp d14, d2\nfrintm d15, d0\nfrintm d16, d2\nfrintz d17, d1\nfrintz d18, d2\nfrintz d19, d3\nfrinta d20, d0\nfrinta d21, d2\nfrintx d22, d0\nfrinti d23, d1\nfmov x10, d10\nfmov x11, d11\nfmov x12, d12\nfmov x13, d13\nfmov x14, d14\nfmov x15, d15\nfmov x16, d16\nfmov x17, d17\nfmov x18, d18\nfmov x19, d19\nfmov x20, d20\nfmov x21, d21\nfmov x22, d22\nfmov x23, d23"
    (regs := [
      (0, 0x4004000000000000#64), -- 2.5
      (1, 0x400c000000000000#64), -- 3.5
      (2, 0xc004000000000000#64), -- -2.5
      (3, 0xbfd0000000000000#64)  -- -0.25 (rounds to -0.0)
    ]),

  makeAsmTestCase
    "ScalarFP/FP1_Single_Frint_AllModes"
    "fmov s0, w0\nfmov s1, w1\nfmov s2, w2\nfmov s3, w3\nfrintn s10, s0\nfrintn s11, s1\nfrintp s12, s0\nfrintp s13, s2\nfrintm s14, s0\nfrintm s15, s2\nfrintz s16, s1\nfrintz s17, s3\nfrinta s18, s0\nfrinta s19, s2\nfrintx s20, s0\nfrinti s21, s1\nfmov w10, s10\nfmov w11, s11\nfmov w12, s12\nfmov w13, s13\nfmov w14, s14\nfmov w15, s15\nfmov w16, s16\nfmov w17, s17\nfmov w18, s18\nfmov w19, s19\nfmov w20, s20\nfmov w21, s21"
    (regs := [
      (0, 0x40200000#64), -- 2.5f
      (1, 0x40600000#64), -- 3.5f
      (2, 0xc0200000#64), -- -2.5f
      (3, 0xbe800000#64)  -- -0.25f
    ]),

  makeAsmTestCase
    "ScalarFP/FP2_Double_AddSubMulDivFnmul_NormalAndSubnormal"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov d3, x3\nfadd d10, d0, d1\nfsub d11, d0, d1\nfmul d12, d0, d1\nfdiv d13, d0, d1\nfnmul d14, d0, d1\nfadd d15, d2, d3\nfsub d16, d3, d2\nfmul d17, d2, d1\nfdiv d18, d3, d1\nfsub d19, d0, d0\nfmov x10, d10\nfmov x11, d11\nfmov x12, d12\nfmov x13, d13\nfmov x14, d14\nfmov x15, d15\nfmov x16, d16\nfmov x17, d17\nfmov x18, d18\nfmov x19, d19"
    (regs := [
      (0, 0x400921fb54442d18#64), -- pi
      (1, 0xc005bf0a8b145769#64), -- -e
      (2, 0x0000000000000001#64), -- min subnormal
      (3, 0x000fffffffffffff#64)  -- max subnormal
    ]),

  makeAsmTestCase
    "ScalarFP/FP2_Single_AddSubMulDivFnmul_NormalAndSubnormal"
    "fmov s0, w0\nfmov s1, w1\nfmov s2, w2\nfmov s3, w3\nfadd s10, s0, s1\nfsub s11, s0, s1\nfmul s12, s0, s1\nfdiv s13, s0, s1\nfnmul s14, s0, s1\nfadd s15, s2, s3\nfsub s16, s3, s2\nfdiv s17, s3, s1\nfmov w10, s10\nfmov w11, s11\nfmov w12, s12\nfmov w13, s13\nfmov w14, s14\nfmov w15, s15\nfmov w16, s16\nfmov w17, s17"
    (regs := [
      (0, 0x40490fdb#64), -- pi_f32
      (1, 0xc02df854#64), -- -e_f32
      (2, 0x00000001#64), -- min subnormal f32
      (3, 0x007fffff#64)  -- max subnormal f32
    ]),

  makeAsmTestCase
    "ScalarFP/FP2_Double_Special_ZeroInfNaN"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov d3, x3\nfmov d4, x4\nfmov d5, x5\nfadd d10, d0, d1\nfadd d11, d1, d1\nfadd d12, d2, d3\nfmul d13, d0, d2\nfdiv d14, d0, d1\nfdiv d15, d2, d3\nfadd d16, d4, d2\nfadd d17, d4, d5\nfnmul d18, d1, d2\nfmov x10, d10\nfmov x11, d11\nfmov x12, d12\nfmov x13, d13\nfmov x14, d14\nfmov x15, d15\nfmov x16, d16\nfmov x17, d17\nfmov x18, d18"
    (regs := [
      (0, 0x0000000000000000#64), -- +0.0
      (1, 0x8000000000000000#64), -- -0.0
      (2, 0x7ff0000000000000#64), -- +inf
      (3, 0xfff0000000000000#64), -- -inf
      (4, 0x7ff80000000000aa#64), -- QNaN
      (5, 0xfff0000000000055#64)  -- negative SNaN
    ]),

  makeAsmTestCase
    "ScalarFP/FP2_Double_MaxMin_And_MaxMinNum"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov d3, x3\nfmov d4, x4\nfmov d5, x5\nfmax d10, d0, d1\nfmin d11, d0, d1\nfmax d12, d2, d3\nfmin d13, d2, d3\nfmax d14, d4, d0\nfmaxnm d15, d4, d0\nfminnm d16, d0, d4\nfmaxnm d17, d5, d0\nfminnm d18, d0, d5\nfmov x10, d10\nfmov x11, d11\nfmov x12, d12\nfmov x13, d13\nfmov x14, d14\nfmov x15, d15\nfmov x16, d16\nfmov x17, d17\nfmov x18, d18"
    (regs := [
      (0, 0x3ff8000000000000#64), -- 1.5
      (1, 0xc004000000000000#64), -- -2.5
      (2, 0x0000000000000000#64), -- +0.0
      (3, 0x8000000000000000#64), -- -0.0
      (4, 0x7ff8000000000011#64), -- QNaN
      (5, 0x7ff0000000000022#64)  -- SNaN
    ]),

  makeAsmTestCase
    "ScalarFP/FP2_Single_MaxMin_And_Special"
    "fmov s0, w0\nfmov s1, w1\nfmov s2, w2\nfmov s3, w3\nfmov s4, w4\nfmov s5, w5\nfmax s10, s0, s1\nfmin s11, s0, s1\nfmax s12, s2, s3\nfmin s13, s2, s3\nfmax s14, s4, s0\nfmaxnm s15, s4, s0\nfminnm s16, s0, s4\nfmaxnm s17, s5, s0\nfmov w10, s10\nfmov w11, s11\nfmov w12, s12\nfmov w13, s13\nfmov w14, s14\nfmov w15, s15\nfmov w16, s16\nfmov w17, s17"
    (regs := [
      (0, 0x3fc00000#64), -- 1.5f
      (1, 0xc0200000#64), -- -2.5f
      (2, 0x00000000#64), -- +0.0f
      (3, 0x80000000#64), -- -0.0f
      (4, 0x7fc00011#64), -- QNaN f32
      (5, 0x7f800022#64)  -- SNaN f32
    ]),

  makeAsmTestCase
    "ScalarFP/FP3_Double_FmaddFmsubFnmaddFnmsub"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov d3, x3\nfmov d4, x4\nfmadd d10, d0, d1, d2\nfmsub d11, d0, d1, d2\nfnmadd d12, d0, d1, d2\nfnmsub d13, d0, d1, d2\nfmsub d14, d3, d4, d2\nfmov x10, d10\nfmov x11, d11\nfmov x12, d12\nfmov x13, d13\nfmov x14, d14"
    (regs := [
      (0, 0x4008000000000000#64), -- 3.0
      (1, 0x4010000000000000#64), -- 4.0
      (2, 0x3ff0000000000000#64), -- 1.0
      (3, 0x3ff0000000000001#64), -- 1.0 + 2^-52
      (4, 0x3fefffffffffffff#64)  -- 1.0 - 2^-53
    ]),

  makeAsmTestCase
    "ScalarFP/FP3_Single_FmaddFmsubFnmaddFnmsub"
    "fmov s0, w0\nfmov s1, w1\nfmov s2, w2\nfmadd s10, s0, s1, s2\nfmsub s11, s0, s1, s2\nfnmadd s12, s0, s1, s2\nfnmsub s13, s0, s1, s2\nfmov w10, s10\nfmov w11, s11\nfmov w12, s12\nfmov w13, s13"
    (regs := [
      (0, 0x40400000#64), -- 3.0f
      (1, 0x40800000#64), -- 4.0f
      (2, 0x3f800000#64)  -- 1.0f
    ]),

  makeAsmTestCase
    "ScalarFP/FPCompare_And_FCsel_Double"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov d3, x3\nfcmp d0, d2\ncset x10, eq\nfcsel d10, d0, d1, eq\nfcmp d1, d0\ncset x11, mi\nfcsel d11, d0, d1, lt\nfcmpe d0, d1\ncset x12, gt\nfccmp d0, d1, #0, gt\ncset x13, gt\nfccmpe d0, d1, #4, eq\ncset x14, eq\nfcmp d2, #0.0\ncset x15, eq\nfcmp d0, d3\ncset x16, vs\nfmov x17, d10\nfmov x18, d11"
    (regs := [
      (0, 0x4008000000000000#64), -- 3.0
      (1, 0xc000000000000000#64), -- -2.0
      (2, 0x8000000000000000#64), -- -0.0
      (3, 0x7ff8000000000001#64)  -- QNaN (leaves final NZCV = 0b0011 = 3)
    ]),

  makeAsmTestCase
    "ScalarFP/FPCompare_And_FCsel_Single"
    "fmov s0, w0\nfmov s1, w1\nfmov s2, w2\nfmov s3, w3\nfcmp s0, s0\ncset x10, eq\nfcsel s10, s0, s1, eq\nfcmp s1, s0\ncset x11, lt\nfcsel s11, s0, s1, gt\nfcmpe s0, s1\ncset x12, gt\nfccmp s0, s1, #2, gt\ncset x13, gt\nfccmpe s0, s3, #0, ne\ncset x14, vs\nfcmp s2, #0.0\ncset x15, eq\nfmov w16, s10\nfmov w17, s11"
    (regs := [
      (0, 0x40400000#64), -- 3.0f
      (1, 0xc0000000#64), -- -2.0f
      (2, 0x80000000#64), -- -0.0f
      (3, 0x7fc00001#64)  -- QNaN f32
    ]),

  makeAsmTestCase
    "ScalarFP/FPImm_And_IntToFp_ScvtfUcvtf"
    "fmov d0, #1.0\nfmov d1, #-2.5\nfmov s2, #0.125\nfmov s3, #31.0\nscvtf s4, w0\nucvtf s5, w1\nscvtf s6, x2\nucvtf s7, x3\nscvtf d8, w0\nucvtf d9, w1\nscvtf d10, x2\nucvtf d11, x3\nfmov x10, d0\nfmov x11, d1\nfmov w12, s2\nfmov w13, s3\nfmov w14, s4\nfmov w15, s5\nfmov w16, s6\nfmov w17, s7\nfmov x18, d8\nfmov x19, d9\nfmov x20, d10\nfmov x21, d11"
    (regs := [
      (0, 0xffffffd6#64),         -- -42 (i32)
      (1, 0xffffffff#64),         -- UINT32_MAX
      (2, 0x8000000000000000#64), -- INT64_MIN
      (3, 0xffffffffffffffff#64)  -- UINT64_MAX
    ]),

  makeAsmTestCase
    "ScalarFP/FpToInt_FcvtzsFcvtzu_SaturationAndNaN"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov d3, x3\nfmov d4, x4\nfmov s5, w5\nfmov s6, w6\nfcvtzs w10, d0\nfcvtzu w11, d0\nfcvtzs x12, d1\nfcvtzu x13, d1\nfcvtzs w14, d2\nfcvtzu w15, d2\nfcvtzs x16, d2\nfcvtzu x17, d2\nfcvtzs w18, d3\nfcvtzu w19, d3\nfcvtzs x20, d3\nfcvtzu x21, d3\nfcvtzs x22, d4\nfcvtzu x23, d4\nfcvtzs w24, s5\nfcvtzu x25, s6"
    (regs := [
      (0, 0x400f333333333333#64), -- 3.9
      (1, 0xc00f333333333333#64), -- -3.9
      (2, 0x46293e5939a08cea#64), -- ~1e30 (saturates max)
      (3, 0xc6293e5939a08cea#64), -- ~-1e30 (saturates min / 0)
      (4, 0x7ff8000000000001#64), -- QNaN -> 0
      (5, 0xc22b0000#64),         -- -42.75f
      (6, 0x42fe0000#64)          -- 127.0f
    ]),

  makeAsmTestCase
    "SimdExtra/AES_Decrypt_And_InvMixColumns"
    "stp x0, x1, [x10]\nstp x2, x3, [x10, #16]\nldr q0, [x10]\nldr q1, [x10, #16]\naese v0.16b, v1.16b\naesmc v0.16b, v0.16b\naesimc v2.16b, v0.16b\naesd v2.16b, v1.16b\nfmov x11, d0\nfmov x12, v0.d[1]\nfmov x13, d2\nfmov x14, v2.d[1]"
    (regs := [
      (0, 0x0011223344556677#64),
      (1, 0x8899aabbccddeeff#64),
      (2, 0x0001020304050607#64),
      (3, 0x08090a0b0c0d0e0f#64),
      (10, dataBase)
    ]),

  makeAsmTestCase
    "SimdExtra/MoviMvni_InsUmov_Dup"
    "movi v0.16b, #0x3c\nmovi v1.8h, #0x42, lsl #8\nmovi v2.4s, #0xa5, lsl #16\nmovi v3.2d, #0x0000ff00ff0000ff\nmvn v4.16b, v0.16b\nins v3.b[3], w0\nins v3.h[2], w1\nins v3.s[1], w2\nins v3.d[1], x3\nins v3.b[15], v0.b[0]\numov w10, v3.b[3]\numov w11, v3.h[2]\numov w12, v3.s[1]\numov x13, v3.d[0]\numov x14, v3.d[1]\numov x15, v1.d[0]\numov x16, v2.d[0]\numov x17, v4.d[0]"
    (regs := [
      (0, 0x77#64),
      (1, 0x1234#64),
      (2, 0xdeadbeef#64),
      (3, 0x0123456789abcdef#64)
    ]),

  makeAsmTestCase
    "SimdExtra/Ushl_Comparisons_Rev32_Permutes"
    "stp x0, x1, [x10]\nstp x2, x3, [x10, #16]\nldr q0, [x10]\nldr q1, [x10, #16]\nushl v2.16b, v0.16b, v1.16b\ncmgt v3.16b, v0.16b, v1.16b\ncmge v4.16b, v0.16b, v1.16b\ncmgt v5.16b, v0.16b, #0\ncmge v6.16b, v0.16b, #0\ncmle v7.16b, v0.16b, #0\nrev32 v8.16b, v0.16b\nrev32 x11, x0\nuzp2 v9.16b, v0.16b, v1.16b\nzip2 v16.16b, v0.16b, v1.16b\nfmov x12, d2\nfmov x13, v2.d[1]\nfmov x14, d3\nfmov x15, d4\nfmov x16, d5\nfmov x17, d6\nfmov x18, d7\nfmov x19, d8\nfmov x20, d9\nfmov x21, d16"
    (regs := [
      (0, 0x80ff7f000102fe81#64),
      (1, 0x1020304050607080#64),
      (2, 0x01ff02fe0004fc03#64),
      (3, 0xfffefdfcfbfa0102#64),
      (10, dataBase)
    ]),

  makeAsmTestCase
    "IntExtra/CCMN_RegAndImm_32And64"
    "cmp x0, x0\nccmn x0, x1, #0, eq\ncset x10, eq\ncset x11, cs\nccmn x0, #5, #0, ne\ncset x12, eq\nccmn w2, w3, #2, eq\ncset x13, mi\nccmn w2, #1, #4, eq"
    (regs := [
      (0, 5#64),
      (1, 0xfffffffffffffffb#64), -- -5 (5 + (-5) == 0 -> Z=1, C=1)
      (2, 0x7fffffff#64),
      (3, 1#64)
    ]),

  makeAsmTestCase
    "IntExtra/LDPSW_OffsetPrePost"
    "ldpsw x1, x2, [x0]\nldpsw x3, x4, [x0, #8]!\nldpsw x5, x6, [x0], #8"
    (regs := [(0, dataBase)])
    (memInitU64 := [
      (dataBase, 0x0000002affffff80#64),      -- w_lo = -128, w_hi = 42
      (dataBase + 8#64, 0x800000007fffffff#64) -- w_lo = INT32_MAX, w_hi = INT32_MIN
    ]),

  makeAsmTestCase
    "SimdExtra/LoadStore_B_H_S_D_Q_AllModes"
    "ldr b0, [x0]\nldr h1, [x0, #2]\nldr s2, [x0, #4]\nldr d3, [x0, #8]\nldr q4, [x0, #16]\nldp s5, s6, [x0, #8]\nldp d7, d8, [x0, #16]\nldp q9, q10, [x0]\nstr b0, [x1]\nstr h1, [x1, #2]\nstr s2, [x1, #4]\nstr d3, [x1, #8]\nstr q4, [x1, #16]\nstp s5, s6, [x1, #32]\nstp d7, d8, [x1, #40]\nstp q9, q10, [x1, #64]\nfmov w10, s0\nfmov w11, s1\nfmov w12, s2\nfmov x13, d3\nfmov x14, d4\nfmov x15, v4.d[1]\nfmov w16, s5\nfmov w17, s6\nfmov x18, d7\nfmov x19, d8\nfmov x20, d9\nfmov x21, v10.d[1]"
    (regs := [(0, dataBase), (1, dataBase + 0x100#64)])
    (memInitU64 := [
      (dataBase, 0x1122334455667788#64),
      (dataBase + 8#64, 0x99aabbccddeeff00#64),
      (dataBase + 16#64, 0x0123456789abcdef#64),
      (dataBase + 24#64, 0xfedcba9876543210#64)
    ])
    (memWatchU64 := [
      dataBase + 0x100#64,
      dataBase + 0x108#64,
      dataBase + 0x110#64,
      dataBase + 0x118#64,
      dataBase + 0x120#64,
      dataBase + 0x128#64,
      dataBase + 0x130#64,
      dataBase + 0x140#64,
      dataBase + 0x148#64,
      dataBase + 0x150#64,
      dataBase + 0x158#64
    ]),

  -- Sequential atomics, LSE, RCpc, CRC32, hints, and C++/Go runtime vector ops.
  makeAsmTestCase
    "Atomics/LdxrStxr_LdxpStxp_SequentialSuccess"
    "ldxr x2, [x10]\nadd x2, x2, #1\nstxr w3, x2, [x10]\nldaxrb w4, [x10]\nstlxrb w5, w1, [x10]\nldxp x6, x7, [x11]\nstlxp w8, x7, x6, [x11]\nldaxp w12, w13, [x11]\nstxp w14, w13, w12, [x11]\nclrex"
    (regs := [(1, 0x5a#64), (10, dataBase), (11, dataBase + 16#64)])
    (memInitU64 := [(dataBase, 0x00000000000000ff#64), (dataBase + 16#64, 0x1111111122222222#64),
      (dataBase + 24#64, 0x3333333344444444#64)])
    (memWatchU64 := [dataBase, dataBase + 16#64, dataBase + 24#64]),

  makeAsmTestCase
    "Atomics/Cas_CasP_SuccessAndFailure"
    "mov x2, x0\ncas x2, x1, [x10]\nmov x3, #7\ncasal x3, x1, [x10]\nmov w4, #0x44\ncasb w4, w1, [x10]\nmov x5, x10\nadd x5, x5, #16\nldp x6, x7, [x5]\nmov x8, x6\nmov x9, x7\ncaspal x8, x9, x0, x1, [x5]\nmov x12, #0\nmov x13, #0\ncasp x12, x13, x0, x1, [x5]"
    (regs := [(0, 0x0123456789abcdef#64), (1, 0xfedcba9876543210#64), (10, dataBase)])
    (memInitU64 := [(dataBase, 0x0123456789abcdef#64), (dataBase + 16#64, 0xaaaaaaaaaaaaaaaa#64),
      (dataBase + 24#64, 0xbbbbbbbbbbbbbbbb#64)])
    (memWatchU64 := [dataBase, dataBase + 16#64, dataBase + 24#64]),

  makeAsmTestCase
    "Atomics/LseRmw_AllOps_AllWidths"
    "ldadd x0, x2, [x10]\nldclral x1, x3, [x10]\nldeora w0, w4, [x10]\nldsetl w1, w5, [x10]\nldsmaxb w15, w6, [x11]\nldsminh w15, w7, [x11]\nldumax x0, x8, [x12]\nldumin x1, x9, [x12]\nswpal x0, x13, [x12]\nswpb w15, w14, [x11]\nstadd x0, [x10]\nstsmaxl w15, [x11]"
    -- Sub-word and W-size `LDSMAX`/`LDSMIN` use non-negative operands: Unicorn 2.1.3 zero-extends
    -- the memory operand there (an oracle bug; Sail agrees with Lean); the 64-bit forms use
    -- arbitrary values.
    (regs := [(0, 0x8000000000000081#64), (1, 0x00000000000000f0#64), (10, dataBase),
      (11, dataBase + 8#64), (12, dataBase + 16#64), (15, 0x10#64)])
    (memInitU64 := [(dataBase, 0x00ff00ff00ff00ff#64), (dataBase + 8#64, 0x7f7f7f7f7f7f7f7f#64),
      (dataBase + 16#64, 0x4000000000000000#64)])
    (memWatchU64 := [dataBase, dataBase + 8#64, dataBase + 16#64]),

  makeAsmTestCase
    "Atomics/Ldapr_Ldapur_Stlur"
    "ldapr x2, [x10]\nldaprb w3, [x10]\nldaprh w4, [x10]\nldapur w5, [x10, #4]\nldapursb x6, [x10, #7]\nldapursh w7, [x10, #6]\nldapursw x8, [x10, #4]\nstlur x0, [x10, #16]\nstlurb w0, [x10, #-1]\nstlurh w0, [x10, #24]"
    (regs := [(0, 0x1122334455667788#64), (10, dataBase + 8#64)])
    (memInitU64 := [(dataBase, 0#64), (dataBase + 8#64, 0x80f1e2d3c4b5a697#64)])
    (memWatchU64 := [dataBase, dataBase + 8#64, dataBase + 24#64, dataBase + 32#64]),

  makeAsmTestCase
    "System/Hints_Prfm_Nzcv"
    "yield\nsevl\nhint #0x22\nprfm pldl1keep, [x10]\nprfm pstl2strm, [x10, #64]\nprfum pldl3keep, [x10, #-3]\nprfm plil1keep, [x10, x1, lsl #3]\ncmp x1, x1\nmrs x2, nzcv\nmov x3, #0x60000000\nmsr nzcv, x3\ncset x4, eq\ncset x5, cs"
    (regs := [(1, 2#64), (10, dataBase)]),

  -- Sail's model configuration reports `DCZID_EL0 = 0x18` (DZP=1, DC ZVA prohibited) and traps
  -- `DC ZVA` to EL1, whereas Linux user space (which `Eval.lean` models) has DZP=0, BS=4.
  { (makeAsmTestCase
    "System/Dczid_DcZva_LinuxUserspace"
    "mrs x6, dczid_el0\nadd x7, x10, #0x45\ndc zva, x7"
    (regs := [(10, dataBase)])
    (memInitU64 := [(dataBase + 64#64, 0x1111111111111111#64), (dataBase + 120#64, 0x2222222222222222#64),
      (dataBase + 128#64, 0x3333333333333333#64)])
    (memWatchU64 := [dataBase + 64#64, dataBase + 120#64, dataBase + 128#64])) with
    skipSail := some "Sail config has DCZID_EL0.DZP=1 and traps DC ZVA (Linux EL0 has DZP=0)" },

  makeAsmTestCase
    "IntExtra/Crc32_Crc32c_AllWidths"
    "mov w2, #0xffffffff\ncrc32b w3, w2, w0\ncrc32h w4, w2, w0\ncrc32w w5, w2, w0\ncrc32x w6, w2, x1\ncrc32cb w7, w2, w0\ncrc32ch w8, w2, w0\ncrc32cw w9, w2, w0\ncrc32cx w11, w2, x1\ncrc32x w12, wzr, x1"
    (regs := [(0, 0x31323334#64), (1, 0x3132333435363738#64)]),

  makeAsmTestCase
    "LoadStore/Ldnp_Stnp_GprAndSimd"
    "ldnp x2, x3, [x10]\nldnp w4, w5, [x10, #8]\nstnp x3, x2, [x10, #32]\nstnp w5, w4, [x10, #48]\nldnp q0, q1, [x10]\nstnp q1, q0, [x10, #64]\nldnp d2, d3, [x10, #-16]\nstnp s3, s2, [x10, #96]\nfmov x6, d2\nfmov x7, d3"
    (regs := [(10, dataBase + 16#64)])
    (memInitU64 := [(dataBase, 0xa0a0a0a0a0a0a0a0#64), (dataBase + 8#64, 0xb0b0b0b0b0b0b0b0#64),
      (dataBase + 16#64, 0x0102030405060708#64), (dataBase + 24#64, 0x1112131415161718#64),
      (dataBase + 32#64, 0x2122232425262728#64), (dataBase + 40#64, 0x3132333435363738#64)])
    (memWatchU64 := [dataBase + 48#64, dataBase + 56#64, dataBase + 64#64, dataBase + 72#64,
      dataBase + 80#64, dataBase + 88#64, dataBase + 96#64, dataBase + 104#64, dataBase + 112#64]),

  makeAsmTestCase
    "SimdExtra/Popcount_Cnt_Uaddlv_Addv_Addp"
    "fmov d0, x0\ncnt v0.8b, v0.8b\nuaddlv h0, v0.8b\nfmov w2, s0\nfmov d1, x1\nmov v1.d[1], x0\ncnt v1.16b, v1.16b\naddv h3, v1.8h\nfmov w3, s3\nsaddlv s4, v1.8h\nfmov w4, s4\nmov v5.d[0], x0\nmov v5.d[1], x1\naddp d6, v5.2d\nfmov x6, d6\naddp v7.4s, v5.4s, v1.4s\nfmov x7, d7\nfmov x8, v7.d[1]\nsminv h9, v5.8h\numov w9, v9.h[0]"
    (regs := [(0, 0xf0f0ff0012345678#64), (1, 0x8000000000000001#64)]),

  -- Sail (sail-arm v9.4-a C model) hits an internal assertion on byte-lane `ADDV` (`.8b`/`.16b`).
  { (makeAsmTestCase
    "SimdExtra/Addv_ByteLanes"
    "fmov d1, x1\nmov v1.d[1], x0\ncnt v2.16b, v1.16b\naddv b3, v2.16b\nfmov w3, s3\naddv b4, v1.8b\nfmov w4, s4\naddv b5, v1.16b\nfmov w5, s5"
    (regs := [(0, 0xf0f0ff0012345678#64), (1, 0x8000000000000001#64)])) with
    skipSail := some "Sail C model assertion failure on byte-lane ADDV" },

  makeAsmTestCase
    "SimdExtra/Tbl_Tbx_Trn_Sri_Sli"
    "mov v0.d[0], x0\nmov v0.d[1], x1\nmov v1.d[0], x2\nmov v1.d[1], x3\nmov v2.d[0], x4\nmov v2.d[1], x4\ntbl v3.16b, {v0.16b}, v2.16b\ntbl v4.8b, {v0.16b, v1.16b}, v2.8b\nmov v5.16b, v1.16b\ntbx v5.16b, {v0.16b}, v2.16b\ntrn1 v6.8h, v0.8h, v1.8h\ntrn2 v7.4s, v0.4s, v1.4s\nmov v8.16b, v1.16b\nsri v8.4s, v0.4s, #12\nmov v9.16b, v1.16b\nsli v9.2d, v0.2d, #20\nfmov x10, d3\nfmov x11, v3.d[1]\nfmov x12, d4\nfmov x13, v5.d[1]\nfmov x14, d6\nfmov x15, v7.d[1]\nfmov x16, d8\nfmov x17, v9.d[1]"
    (regs := [(0, 0x0706050403020100#64), (1, 0x0f0e0d0c0b0a0908#64), (2, 0x1716151413121110#64),
      (3, 0x1f1e1d1c1b1a1918#64), (4, 0x40001f10ff0e0503#64)]),

  makeAsmTestCase
    "SimdExtra/Ld1St1Multi_Ld1r_LdrLiteral"
    "ld1 {v0.16b, v1.16b}, [x10]\nld1 {v2.4s}, [x10], #16\nld1 {v3.2d, v4.2d, v5.2d}, [x10], x1\nst1 {v0.8h, v1.8h}, [x11]\nst1 {v2.2s}, [x11]\nadd x12, x11, #64\nst1 {v3.16b, v4.16b, v5.16b, v6.16b}, [x12], #64\nld1r {v7.4s}, [x10]\nld1r {v8.8b}, [x10], #1\nldr q9, lit\nldr d10, lit\nfmov x13, d7\nfmov x14, d8\nfmov x15, v9.d[1]\nfmov x16, d10\nb done\n.p2align 4\nlit:\n.word 0xd503201f\n.word 0xd503203f\n.word 0xd503205f\n.word 0xd503209f\ndone:\nnop"
    (regs := [(1, 16#64), (10, dataBase), (11, dataBase + 0x100#64)])
    (memInitU64 := [(dataBase, 0x0102030405060708#64), (dataBase + 8#64, 0x1112131415161718#64),
      (dataBase + 16#64, 0x2122232425262728#64), (dataBase + 24#64, 0x3132333435363738#64),
      (dataBase + 32#64, 0x4142434445464748#64), (dataBase + 40#64, 0x5152535455565758#64),
      (dataBase + 48#64, 0x6162636465666768#64), (dataBase + 56#64, 0x7172737475767778#64),
      (dataBase + 64#64, 0x8182838485868788#64)])
    (memWatchU64 := [dataBase + 0x100#64, dataBase + 0x108#64, dataBase + 0x110#64, dataBase + 0x118#64,
      dataBase + 0x140#64, dataBase + 0x148#64, dataBase + 0x170#64, dataBase + 0x178#64]),

  -- 128-bit V0..V31 vector register differential check via `vregs`
  makeAsmTestCase
    "SimdFp/VRegs128_FullRegisterCheck"
    "eor v2.16b, v0.16b, v1.16b\nadd v3.2d, v0.2d, v1.2d\nfadd s4, s0, s1\nshl v5.2d, v0.2d, #7\nushr v6.4s, v1.4s, #3\ndup v7.2d, v0.d[1]\next v8.16b, v0.16b, v1.16b, #5\nzip1 v9.4s, v0.4s, v1.4s\nuzp2 v10.8h, v0.8h, v1.8h\nrev64 v11.16b, v0.16b"
    (vregs := [(0, 0xfedcba98765432100123456789abcdef#128), (1, 0x00112233445566778899aabbccddeeff#128)]),

  -- AdvSIMD shifts, narrowing/widening shifts, modified immediates, SMOV, REV16, CLZ/CLS/RBIT
  makeAsmTestCase
    "Simd/FamilyA_Shifts_ModImm_Smov_Rev16"
    "sshr v2.16b, v0.16b, #3\nsshll v3.8h, v0.8b, #4\nsshll2 v4.4s, v1.8h, #7\nusra v2.4s, v0.4s, #5\nssra v3.2d, v1.2d, #11\nurshr v5.8h, v0.8h, #1\nsrshr v6.4s, v1.4s, #1\nursra v5.4s, v0.4s, #2\nsrsra v6.2d, v1.2d, #3\nshrn v7.8b, v0.8h, #4\nshrn2 v7.16b, v1.8h, #4\nrshrn v8.4h, v0.4s, #8\nrshrn2 v8.8h, v1.4s, #8\nsqshrn v9.8b, v0.8h, #2\nuqshrn2 v9.16b, v1.8h, #2\nsqshrun v10.4h, v0.4s, #3\nsqrshrun2 v10.8h, v1.4s, #3\nsqrshrn v11.2s, v0.2d, #5\nuqrshrn2 v11.4s, v1.2d, #5\nsqshl v12.8h, v0.8h, #4\nuqshl v13.4s, v1.4s, #4\nsqshlu v14.8h, v0.8h, #3\nmovi v15.4s, #0xa5, msl #8\nmvni v16.2s, #0xa5, msl #16\norr v15.4s, #0x03, lsl #8\nbic v16.8h, #0x0f, lsl #8\nfmov v17.4s, #1.0\nfmov v18.2d, #1.0\nrev16 v19.16b, v0.16b\nrbit v20.16b, v1.16b\nclz v21.4s, v0.4s\ncls v22.8h, v1.8h\nsrshl v23.8h, v0.8h, v1.8h\nurshl v24.4s, v0.4s, v1.4s\nsqshl v25.8b, v0.8b, v1.8b\nuqshl v26.8h, v0.8h, v1.8h\nsqrshl v27.4s, v0.4s, v1.4s\nuqrshl v28.2d, v0.2d, v1.2d\nsmov w3, v0.b[3]\nsmov x4, v1.h[5]\nsmov x5, v0.s[2]"
    (vregs := [(0, 0x80017fff0000ffff_fedcba9876543210#128), (1, 0x0102fffe0003fffd_001122338899aabb#128)]),

  -- Integer AdvSIMD: BIT/BIF, halving/saturating add/sub, min/max/pairwise, ABD/ABA, MUL/MLA/MLS/PMUL, SQDMULH, ADDLP/ADALP, SUQADD/USQADD, ABS/NEG/SQABS/SQNEG, XTN/SQXTN/UQXTN/SQXTUN
  makeAsmTestCase
    "Simd/FamilyC_Tier1_IntegerAdvSimd"
    "mov v2.16b, v0.16b\nbit v2.16b, v1.16b, v0.16b\nmov v3.16b, v0.16b\nbif v3.16b, v1.16b, v0.16b\nshadd v4.16b, v0.16b, v1.16b\nuhadd v5.8h, v0.8h, v1.8h\nsrhadd v6.4s, v0.4s, v1.4s\nurhadd v7.16b, v0.16b, v1.16b\nshsub v8.8h, v0.8h, v1.8h\nuhsub v9.4s, v0.4s, v1.4s\nsqadd v10.16b, v0.16b, v1.16b\nuqadd v11.2d, v0.2d, v1.2d\nsqsub v12.8h, v0.8h, v1.8h\nuqsub v13.4s, v0.4s, v1.4s\nsmax v14.16b, v0.16b, v1.16b\numax v15.8h, v0.8h, v1.8h\nsmin v16.4s, v0.4s, v1.4s\numin v17.16b, v0.16b, v1.16b\nsmaxp v18.8h, v0.8h, v1.8h\numinp v19.4s, v0.4s, v1.4s\nsabd v20.16b, v0.16b, v1.16b\nuabd v21.8h, v0.8h, v1.8h\nsaba v20.16b, v1.16b, v0.16b\nuaba v21.8h, v1.8h, v0.8h\nmul v22.4s, v0.4s, v1.4s\nmla v22.4s, v0.4s, v1.4s\nmls v22.8h, v0.8h, v1.8h\npmul v23.16b, v0.16b, v1.16b\nsqdmulh v24.4s, v0.4s, v1.4s\nsqrdmulh v25.8h, v0.8h, v1.8h\nsaddlp v26.8h, v0.16b\nuaddlp v27.4s, v1.8h\nsadalp v26.8h, v1.16b\nuadalp v27.4s, v0.8h\nsuqadd v26.8h, v0.8h\nusqadd v27.4s, v1.4s\nabs v28.4s, v0.4s\nneg v29.2d, v1.2d\nsqabs v30.8h, v0.8h\nsqneg v31.16b, v1.16b\nxtn v2.8b, v0.8h\nxtn2 v2.16b, v1.8h\nsqxtn v3.4h, v0.4s\nsqxtn2 v3.8h, v1.4s\nuqxtn v4.2s, v0.2d\nuqxtn2 v4.4s, v1.2d\nsqxtun v5.8b, v0.8h\nsqxtun2 v5.16b, v1.8h"
    (vregs := [(0, 0x80007fff80000001_fedcba9876543210#128), (1, 0x7fff8000ffffffff_001122338899aabb#128)]),

  -- Crypto: SHA-1, SHA-256, SHA-512, SHA-3, PMULL/PMULL2
  makeAsmTestCase
    "Crypto/Sha1_Sha256_Sha512_Sha3_Pmull"
    "pmull v3.8h, v0.8b, v1.8b\npmull2 v4.8h, v0.16b, v1.16b\npmull v5.1q, v0.1d, v1.1d\npmull2 v6.1q, v0.2d, v1.2d\nsha1h s7, s0\nmov v8.16b, v0.16b\nsha1su0 v8.4s, v1.4s, v2.4s\nsha1su1 v8.4s, v2.4s\nmov v9.16b, v0.16b\nsha1c q9, s1, v2.4s\nmov v10.16b, v0.16b\nsha1p q10, s1, v2.4s\nmov v11.16b, v0.16b\nsha1m q11, s1, v2.4s\nmov v12.16b, v0.16b\nsha256su0 v12.4s, v1.4s\nsha256su1 v12.4s, v1.4s, v2.4s\nmov v13.16b, v0.16b\nsha256h q13, q1, v2.4s\nmov v14.16b, v1.16b\nsha256h2 q14, q0, v2.4s\nmov v15.16b, v0.16b\nsha512su0 v15.2d, v1.2d\nsha512su1 v15.2d, v1.2d, v2.2d\nmov v16.16b, v0.16b\nsha512h q16, q1, v2.2d\nmov v17.16b, v1.16b\nsha512h2 q17, q0, v2.2d\neor3 v18.16b, v0.16b, v1.16b, v2.16b\nbcax v19.16b, v0.16b, v1.16b, v2.16b\nrax1 v20.2d, v0.2d, v1.2d\nxar v21.2d, v0.2d, v1.2d, #17"
    (vregs := [
      (0, 0x1032547698badcfe_efcdab8967452301#128),
      (1, 0x5be0cd191f83d9ab_9b05688c510e527f#128),
      (2, 0x0000001800000000_0000000061626380#128)
    ]),

  -- Scalar FP edge conversions, FMADD single-rounding, FRINT*, FMINNM/FMAXNM, FCMP/FCCMP
  makeAsmTestCase
    "ScalarFP/EdgeConversions_Fcvt_Fmadd_Frint_FixedPoint"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov d3, x3\nfmov s4, w4\nfmov s5, w5\nfcvtzs w6, s4\nfcvtzs w7, s5\nfcvtzu w8, s5\nfcvtzs x9, d0\nfcvtzu x10, d1\nfcvtas w11, d2\nfcvtps w12, d2\nfcvtms w13, d2\nfcvtns w14, d2\nfcvtzs x15, d3, #4\nucvtf d6, x4, #4\nscvtf d7, x5, #4\nfmadd d8, d2, d3, d0\nfmsub d9, d2, d3, d0\nfcvt s10, d2\nfcvt d11, s4\nfrintn d12, d2\nfrintp d13, d2\nfrintm d14, d2\nfrintz d15, d2\nfrinta d16, d2\nfminnm d17, d2, d3\nfmaxnm d18, d2, d3\nfcmp d2, d3\nfccmp d2, d2, #0, lt"
    (regs := [
      (0, 0x43e0000000000000#64), -- +2^63 (saturates signed 64-bit to INT64_MAX)
      (1, 0xc3e0000000000000#64), -- -2^63 (saturates unsigned to 0)
      (2, 0x4004000000000000#64), -- +2.5 (halfway tie-to-even -> 2, tie-away -> 3)
      (3, 0xc00c000000000000#64), -- -3.5 (halfway tie-to-even -> -4, tie-away -> -4)
      (4, 0x4f000000#64),         -- +2^31 in f32 (saturates signed 32-bit to INT32_MAX)
      (5, 0xcf000000#64)          -- -2^31 in f32 (exact INT32_MIN)
    ]),

  -- Integer boundary values: shift >= width, SDIV INT_MIN/-1 and /0, ADC/SBC carry chains, sign-ext loads
  makeAsmTestCase
    "IntBoundary/ShiftModWidth_SdivMin_AdcChain_SignExt"
    "lslv w4, w0, w1\nlsrv x5, x2, x3\nasrv x6, x2, x3\nrorv w7, w0, w1\nsdiv w8, w0, w9\nsdiv x11, x2, x12\nudiv x13, x2, xzr\nsdiv x14, x2, xzr\nadds x15, x2, x2\nadcs x16, x9, x9\nsbcs x17, xzr, xzr\nextr w18, w0, w1, #17\nsbfm x19, x0, #4, #19\nubfm x20, x2, #56, #63\nldrsb x21, [x10]\nldrsh x22, [x10, #2]\nldrsw x23, [x10, #4]\nldrsb w24, [x10]"
    (regs := [
      (0, 0x80000000#64),         -- INT32_MIN in W0
      (1, 37#64),                 -- shift amount >= 32 (37 mod 32 = 5)
      (2, 0x8000000000000000#64), -- INT64_MIN in X2
      (3, 127#64),                -- shift amount >= 64 (127 mod 64 = 63)
      (9, 0xffffffffffffffff#64), -- -1
      (10, dataBase),
      (12, 0xffffffffffffffff#64)
    ])
    (memInitU64 := [(dataBase, 0x800000018001ff80#64)]),

  -- Wrap-around BFM/SBFM/UBFM (imms < immr), EXTR lsb=0/63, CSINC/CSINV/CSNEG AL/NV, LDPSW pre-index
  makeAsmTestCase
    "IntBoundary/BitfieldWrap_ExtrLsb0_CsincAlNv_LdpswPre"
    "bfm x4, x0, #48, #15\nsbfm x5, x1, #56, #7\nubfm w6, w0, #24, #7\nextr x7, x0, x1, #0\nextr w8, w0, w1, #0\nextr x9, x0, x1, #63\ncsinc x11, x0, x0, al\ncsinv x12, x1, x1, nv\ncsneg w13, w0, w0, al\nclz w14, wzr\ncls w15, w1\nrbit x16, x0\nrev16 x17, x0\nrev32 x18, x0\nldpsw x19, x20, [x10, #8]!"
    (regs := [
      (0, 0x123456789abcdef0#64),
      (1, 0xfedcba9876543281#64),
      (4, 0xaaaaaaaaaaaaaaaa#64),
      (10, dataBase)
    ])
    (memInitU64 := [
      (dataBase, 0x1111111122222222#64),
      (dataBase + 8#64, 0x80000005fffffffe#64)
    ]),

  -- SIMD/FP boundary values: SADDLP/UADDLP 2S (1D <- 2S) & SADDLV/UADDLV 4S, FMOV D[1] upper-lane move, LD1 V31->V0 wrap-around, LD1R post-index
  makeAsmTestCase
    "SimdFpBoundary/Saddlp2S_Saddlv4S_FmovD1_Ld1WrapV31_Ld1rPost"
    "saddlp v2.1d, v0.2s\nuaddlp v3.1d, v0.2s\nsaddlv d7, v0.4s\nuaddlv d8, v0.4s\nfmov x4, v0.d[1]\nfmov v5.d[1], x0\nld1 {v31.2d, v0.2d}, [x10]\nld1r {v6.4s}, [x10], #4"
    (regs := [
      (0, 0xdeadbeefcafebabe#64),
      (10, dataBase)
    ])
    (vregs := [
      (0, 0x1122334455667788_80000000ffffffff#128),
      (5, 0x0000000000000000_0102030405060708#128)
    ])
    (memInitU64 := [
      (dataBase, 0xa1a2a3a4a5a6a7a8#64),
      (dataBase + 8#64, 0xb1b2b3b4b5b6b7b8#64),
      (dataBase + 16#64, 0xc1c2c3c4c5c6c7c8#64),
      (dataBase + 24#64, 0xd1d2d3d4d5d6d7d8#64)
    ]),

  -- Single-instruction pre-encoded test case (`adds x2, x0, #1` at INT64_MAX -> INT64_MIN, NZCV = N|V = 9)
  { name := "SingleInsn/Adds64_CarryOverflow_SingleStep"
    basePC := codeBase
    startPC := codeBase
    exitPC := codeBase + 4#64
    maxSteps := 1
    words := #[0xb1000402#32]
    regs := initRegArray [(0, 0x7fffffffffffffff#64)]
    nzcv := 0 },

  -- Exact IEEE-754 RNE halfway tie-to-even in `roundDyadic` (`FADD`, `FCVT`, `SCVTF` with even vs odd LSB)
  makeAsmTestCase
    "ScalarFP/RoundDyadic_HalfwayTieToEven_F64_And_F32"
    "fmov d0, x0\nfmov d1, x1\nfmov d2, x2\nfmov d3, x3\nfadd d10, d0, d2\nfadd d11, d1, d2\nfcvt s14, d3\nscvtf s15, x4\nscvtf s16, x5\nfmov x10, d10\nfmov x11, d11\nfmov w14, s14\nfmov w15, s15\nfmov w16, s16\nfmov s0, w6\nfmov s1, w7\nfmov s2, w8\nfadd s12, s0, s2\nfadd s13, s1, s2\nfmov w12, s12\nfmov w13, s13"
    (regs := [
      (0, 0x3ff0000000000000#64), -- 1.0 (even LSB = 0)
      (1, 0x3ff0000000000001#64), -- 1.0 + 2^-52 (odd LSB = 1)
      (2, 0x3ca0000000000000#64), -- 2^-53 (half-ULP at [1.0, 2.0): 1.0 + 2^-53 ties to even 1.0)
      (3, 0x3ff0000010000000#64), -- 1.0 + 2^-24 (f64->f32 halfway tie to even 1.0f32)
      (4, 0x0000000001000001#64), -- 2^24 + 1 (scvtf halfway tie to even 2^24)
      (5, 0x0000000001000003#64), -- 2^24 + 3 (scvtf halfway tie to even 2^24 + 4)
      (6, 0x3f800000#64),         -- 1.0f32 (even LSB = 0)
      (7, 0x3f800001#64),         -- 1.0f32 + 2^-23 (odd LSB = 1)
      (8, 0x33800000#64)          -- 2^-24f32 (half-ULP at [1.0f32, 2.0f32))
    ]),

  -- FPSR sticky IEEE-754 exception flags (IOC, DZC, IXC), FPSR.QC saturation,
  -- MRS/MSR FPSR/FPCR, and musl fenv.s patterns (fetestexcept, feclearexcept, FRINTN vs FRINTX)
  makeAsmTestCase
    "ScalarFP/FpsrFpcr_StickyFlags_Qc_And_MuslFenv"
    "msr fpsr, xzr\nmrs x10, fpcr\nmsr fpcr, xzr\nfmov d0, x0\nfmov d1, x1\nfmov d2, xzr\nfmov d3, x2\nfdiv d4, d0, d1\nmrs x11, fpsr\nfdiv d5, d0, d2\nfadd d6, d0, d0\nmrs x12, fpsr\nbic x12, x12, #0x10\nmsr fpsr, x12\nmrs x13, fpsr\nfdiv d7, d2, d2\nfrintn d8, d3\nmrs x14, fpsr\nfrintx d9, d3\nsqadd v16.4s, v17.4s, v18.4s\nmrs x15, fpsr\nmsr fpsr, xzr\nmrs x16, fpsr"
    (regs := [
      (0, 0x3ff0000000000000#64), -- 1.0
      (1, 0x4008000000000000#64), -- 3.0 (1.0 / 3.0 -> IXC)
      (2, 0x3ff8000000000000#64)  -- 1.5 (FRINTN vs FRINTX)
    ])
    (vregs := [
      (17, 0x0000000000000000_000000017fffffff#128),
      (18, 0x0000000000000000_0000000100000001#128)
    ]),

  -- LD1/ST1 single-structure lane load/store, LD2/LD3/LD4/ST2/ST3/ST4 multiple structures, and scalar DUP element
  makeAsmTestCase
    "SimdFpBoundary/Ld1St1SingleLane_Ld2Ld3Ld4St2St3St4Multi_DupScalar"
    "ld1 {v0.b}[3], [x10]\nld1 {v1.h}[2], [x10], #2\nld1 {v2.s}[1], [x10], x11\nld1 {v3.d}[1], [x10]\nst1 {v3.d}[1], [x26]\nst1 {v2.s}[1], [x13]\nst1 {v1.h}[2], [x21]\nst1 {v0.b}[3], [x22]\nst1 {v3.d}[1], [x12], #8\nst1 {v0.b}[3], [x12], #1\ndup b20, v0.b[3]\ndup h21, v1.h[2]\ndup s22, v2.s[1]\ndup d23, v3.d[1]\nld2 {v4.8b, v5.8b}, [x14]\nst2 {v4.8b, v5.8b}, [x23]\nld2 {v6.4s, v7.4s}, [x14], #32\nst2 {v6.4s, v7.4s}, [x15]\nld2 {v24.2d, v25.2d}, [x18]\nst2 {v24.2d, v25.2d}, [x24]\nld3 {v8.4h, v9.4h, v10.4h}, [x16]\nst3 {v8.4h, v9.4h, v10.4h}, [x17], #24\nld4 {v12.8b, v13.8b, v14.8b, v15.8b}, [x18]\nst4 {v12.8b, v13.8b, v14.8b, v15.8b}, [x25]\nld4 {v16.16b, v17.16b, v18.16b, v19.16b}, [x18]\nst4 {v16.16b, v17.16b, v18.16b, v19.16b}, [x19], x20"
    (regs := [
      (10, dataBase),
      (11, 4#64),
      (12, dataBase + 64#64),
      (13, dataBase + 80#64),
      (14, dataBase),
      (15, dataBase + 96#64),
      (16, dataBase),
      (17, dataBase + 128#64),
      (18, dataBase),
      (19, dataBase + 160#64),
      (20, 64#64),
      (21, dataBase + 88#64),
      (22, dataBase + 92#64),
      (23, dataBase + 224#64),
      (24, dataBase + 240#64),
      (25, dataBase + 272#64),
      (26, dataBase + 304#64)
    ])
    (vregs := [
      (0, 0x1111111111111111_2222222222222222#128),
      (1, 0x3333333333333333_4444444444444444#128),
      (2, 0x5555555555555555_6666666666666666#128),
      (3, 0x7777777777777777_8888888888888888#128),
      (20, 0xffffffffffffffff_ffffffffffffffff#128),
      (21, 0xffffffffffffffff_ffffffffffffffff#128),
      (22, 0xffffffffffffffff_ffffffffffffffff#128),
      (23, 0xffffffffffffffff_ffffffffffffffff#128)
    ])
    (memInitU64 := [
      (dataBase, 0x0807060504030201#64),
      (dataBase + 8#64, 0x100f0e0d0c0b0a09#64),
      (dataBase + 16#64, 0x1817161514131211#64),
      (dataBase + 24#64, 0x201f1e1d1c1b1a19#64),
      (dataBase + 32#64, 0x2827262524232221#64),
      (dataBase + 40#64, 0x302f2e2d2c2b2a29#64),
      (dataBase + 48#64, 0x3837363534333231#64),
      (dataBase + 56#64, 0x403f3e3d3c3b3a39#64)
    ])
    (memWatchU64 := [
      dataBase + 64#64, dataBase + 72#64, dataBase + 80#64, dataBase + 88#64,
      dataBase + 96#64, dataBase + 104#64, dataBase + 112#64, dataBase + 120#64,
      dataBase + 128#64, dataBase + 136#64, dataBase + 144#64,
      dataBase + 160#64, dataBase + 168#64, dataBase + 176#64, dataBase + 184#64,
      dataBase + 192#64, dataBase + 200#64, dataBase + 208#64, dataBase + 216#64,
      dataBase + 224#64, dataBase + 232#64,
      dataBase + 240#64, dataBase + 248#64, dataBase + 256#64, dataBase + 264#64,
      dataBase + 272#64, dataBase + 280#64, dataBase + 288#64, dataBase + 296#64,
      dataBase + 304#64
    ]),

  -- AdvSIMD three-register different (SMULL/UMULL/SMLAL/UMLAL/SMLSL/UMLSL/ADDHN/SUBHN/RADDHN/RSUBHN/SADDL/UADDL/SADDW/UADDW/SSUBL/USUBL/SSUBW/USUBW/SABAL/UABAL/SABDL/UABDL/PMULL) and vector FABS/FNEG
  makeAsmTestCase
    "SimdFpBoundary/ThreeDiff_Smull_Umull_Smlal_Addhn_Subhn_Addw_Abal"
    "smull v4.8h, v0.8b, v1.8b\nsmull2 v5.8h, v0.16b, v1.16b\nsmull v6.4s, v0.4h, v1.4h\nsmull2 v7.4s, v0.8h, v1.8h\nsmull v8.2d, v0.2s, v1.2s\nsmull2 v9.2d, v0.4s, v1.4s\numull v10.8h, v0.8b, v1.8b\numull2 v11.4s, v0.8h, v1.8h\numull v12.2d, v0.2s, v1.2s\numull2 v13.2d, v0.4s, v1.4s\nsmlal v4.4s, v0.4h, v1.4h\nsmlal2 v5.4s, v0.8h, v1.8h\numlal v6.2d, v0.2s, v1.2s\numlal2 v7.2d, v0.4s, v1.4s\nsmlsl v8.4s, v0.4h, v1.4h\nsmlsl2 v8.4s, v0.8h, v1.8h\numlsl v9.2d, v0.2s, v1.2s\numlsl2 v9.2d, v0.4s, v1.4s\naddhn v14.8b, v2.8h, v3.8h\naddhn2 v14.16b, v0.8h, v1.8h\nraddhn v15.4h, v2.4s, v3.4s\nraddhn2 v15.8h, v0.4s, v1.4s\nsubhn v16.2s, v2.2d, v3.2d\nsubhn2 v16.4s, v0.2d, v1.2d\nrsubhn v17.4h, v2.4s, v3.4s\nrsubhn2 v17.8h, v0.4s, v1.4s\nsaddl v18.8h, v0.8b, v1.8b\nsaddl2 v18.4s, v0.8h, v1.8h\nuaddl v19.8h, v0.8b, v1.8b\nuaddl2 v19.4s, v0.8h, v1.8h\nsaddw v20.4s, v2.4s, v0.4h\nsaddw2 v20.4s, v20.4s, v0.8h\nuaddw v21.2d, v3.2d, v1.2s\nuaddw2 v21.2d, v21.2d, v1.4s\nssubl v22.8h, v0.8b, v1.8b\nssubl2 v22.4s, v0.8h, v1.8h\nusubl v23.8h, v0.8b, v1.8b\nusubl2 v23.4s, v0.8h, v1.8h\nssubw v24.4s, v2.4s, v0.4h\nssubw2 v24.4s, v24.4s, v0.8h\nusubw v25.2d, v3.2d, v1.2s\nusubw2 v25.2d, v25.2d, v1.4s\nsabal v26.4s, v0.4h, v1.4h\nsabal2 v26.4s, v0.8h, v1.8h\nuabal v27.4s, v0.4h, v1.4h\nuabal2 v27.4s, v0.8h, v1.8h\nsabdl v28.8h, v0.8b, v1.8b\nsabdl2 v28.8h, v0.16b, v1.16b\nuabdl v29.8h, v0.8b, v1.8b\nuabdl2 v29.8h, v0.16b, v1.16b\npmull v10.1q, v0.1d, v1.1d\npmull2 v11.1q, v0.2d, v1.2d\nfabs v12.2s, v0.2s\nfneg v13.2s, v1.2s\nfneg v30.2d, v2.2d\nfabs v31.4s, v0.4s"
    (vregs := [
      (0, 0x80007fff_fffe0003_80010002_ff807f01#128),
      (1, 0x7fff8000_0005fffd_ffff0004_0280ff03#128),
      (2, 0x12345678_9abcdef0_fedcba98_76543210#128),
      (3, 0x01020304_05060708_11223344_55667788#128),
      (26, 0x00000001_00000002_00000003_00000004#128),
      (27, 0x00000010_00000020_00000030_00000040#128)
    ])
]

/-- All hand-written multi-instruction differential test vectors. -/
def handWrittenVectorCases : Array IsaTestCase :=
  cAlgorithmicSubroutineCases ++ isaSurfaceAndScalarFpCases ++ extendedFpSimdAtomicsAndBoundaryCases

end Testing.Generators
