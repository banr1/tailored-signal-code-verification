/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Exec
public import Arm64.Testing.Harness.Encode
public import Arm64.Testing.Harness.TestCase
public import Arm64.Testing.Generators.CompiledBinary
public import Arm64.Testing.Generators.SyscallTraces
public import Arm64.Testing.Generators.TrustedSuite
public import Arm64.Testing.Conformance.IsaConformance
public import Arm64.Testing.Regression.FunctionalCorrectness
public import Arm64.Testing.Regression.Process
public import Arm64.Testing.Regression.ProcessE2E
public import Arm64.Testing.Regression.ElfLoaderDiff
public import Arm64.Testing.Regression.SyscallDiff
meta import ProofLib.TestFiles

/-!
# ARM64 Unit and Regression Tests

Deterministic unit and regression test suite (`runTestSuite`) covering `Arm64.decode` and
`Arm64.encode` round-trips, instruction/FP/SIMD/syscall execution, compiled fixture execution,
and re-exported ISA conformance and differential trace helpers.
-/

@[expose] public section

namespace Testing

open Arm64
open ProofLib

export Testing.Harness (
  UnitTestCase TestCase runTestSuite
  runProgram runProgramRaw runWords runWordsRaw
  testOracle dataBase rwState withMem64
)

export Testing.Generators (
  fixtureProg fixtureWords codecMismatches
  runExportedProg reportRustExportCodec
  dumpFsDiffTrace dumpMmapDiffTrace dumpSigaltstackDiffTrace
)

set_option compiler.extract_closed false in
def allTestsPart1 (_ : Unit := ()) : List TestCase := [
  -- Binary decoder tests
  { name := "decode: ADD X0, X1, #42"
    check := decode 0x9100a820#32 == some (.addSubImm .W64 .ADD .x0 .x1 42#12 false) },
  { name := "decode: SUBS XZR, X0, X1 (CMP X0, X1)"
    check := decode 0xeb01001f#32 == some (.addSubShift .W64 .SUBS .xzr .x0 .x1 .LSL 0) },
  { name := "decode: CSEL X0, X0, X1, CS"
    check := decode 0x9a812000#32 == some (.condSelect .W64 .CSEL .x0 .x0 .x1 .CS) },
  { name := "decode: CSNEG X0, X0, X0, GE"
    check := decode 0xda80a400#32 == some (.condSelect .W64 .CSNEG .x0 .x0 .x0 .GE) },
  { name := "decode: REV X0, X0"
    check := decode 0xdac00c00#32 == some (.dataProc1 .W64 .REV .x0 .x0) },
  { name := "decode: CLZ X0, X1"
    check := decode 0xdac01020#32 == some (.dataProc1 .W64 .CLZ .x0 .x1) },
  { name := "decode: RBIT X0, X1"
    check := decode 0xdac00020#32 == some (.dataProc1 .W64 .RBIT .x0 .x1) },
  { name := "decode: UBFM X0, X0, #8, #63 (LSR X0, X0, #8)"
    check := decode 0xd348fc00#32 == some (.bitfield .W64 .UBFM .x0 .x0 8 63) },
  { name := "decode: STP X29, X30, [SP, #-16]!"
    check := decode 0xa9bf7bfd#32 == some (.stp .W64 .x29 .x30 (.PreIndex .sp (-16#64))) },
  { name := "decode: LDP X29, X30, [SP], #16"
    check := decode 0xa8c17bfd#32 == some (.ldp .W64 false .x29 .x30 (.PostIndex .sp 16#64)) },
  { name := "decode: RET"
    check := decode 0xd65f03c0#32 == some (.ret .x30) },

  -- AddWithCarry and NZCV flag semantics
  { name := "AddWithCarry64: signed overflow INT64_MAX + 1 sets N=1, Z=0, C=0, V=1"
    check :=
      let (_, ps) := AddWithCarry64 0x7fffffffffffffff#64 1#64 false
      ps.n == true && ps.z == false && ps.c == false && ps.v == true },
  { name := "AddWithCarry64: unsigned carry UINT64_MAX + 1 sets N=0, Z=1, C=1, V=0"
    check :=
      let (res, ps) := AddWithCarry64 0xffffffffffffffff#64 1#64 false
      res == 0#64 && ps.n == false && ps.z == true && ps.c == true && ps.v == false },
  { name := "AddWithCarry64: CMP 5, 10 sets N=1, Z=0, C=0, V=0"
    check :=
      let (_, ps) := AddWithCarry64 5#64 (~~~10#64) true
      ps.n == true && ps.z == false && ps.c == false && ps.v == false },
  { name := "AddWithCarry64: CMP 10, 5 sets N=0, Z=0, C=1, V=0"
    check :=
      let (_, ps) := AddWithCarry64 10#64 (~~~5#64) true
      ps.n == false && ps.z == false && ps.c == true && ps.v == false },

  -- Execution of decoded machine code subroutines
  { name := "execWords: max_u64(100, 250) == 250"
    check :=
      let s0 := ({} : State).writeReg64 .x0 100#64 |>.writeReg64 .x1 250#64
      let sf := runWords [0xeb01001f#32, 0x9a812000#32, 0xd65f03c0#32] s0
      sf.readReg64 .x0 == 250#64 },
  { name := "execWords: abs_i64(-42) == 42"
    check :=
      let s0 := ({} : State).writeReg64 .x0 (-42#64)
      let sf := runWords [0xf100001f#32, 0xda80a400#32, 0xd65f03c0#32] s0
      sf.readReg64 .x0 == 42#64 },
  { name := "execWords: rev64(0x0102030405060708) >> 8 == 0x0008070605040302"
    check :=
      let s0 := ({} : State).writeReg64 .x0 0x0102030405060708#64
      let sf := runWords [0xdac00c00#32, 0xd348fc00#32, 0xd65f03c0#32] s0
      sf.readReg64 .x0 == 0x0008070605040302#64 },
  { name := "execWords: stack frame prologue/epilogue preserves FP, LR, SP and adds 42 to X0"
    check :=
      let s0 := ({} : State).writeReg64 .x0 10#64 |>.writeReg64 .fp 0x11223344#64 |>.writeReg64 .lr 0xdead0000#64 |>.writeReg64 .sp 0x80000#64
      let sf := runWords [0xa9bf7bfd#32, 0x910003fd#32, 0x9100a800#32, 0xa8c17bfd#32, 0xd65f03c0#32] s0
      sf.readReg64 .x0 == 52#64 && sf.readReg64 .fp == 0x11223344#64 && sf.sp == 0x80000#64 },
  { name := "execWords: countdown accumulation loop (10 + 25 == 35)"
    check :=
      let s0 := ({} : State).writeReg64 .x0 10#64 |>.writeReg64 .x1 25#64
      let sf := runWords [0xb4000081#32, 0x91000400#32, 0xd1000421#32, 0x17fffffd#32, 0xd65f03c0#32] s0
      sf.readReg64 .x0 == 35#64 && sf.readReg64 .x1 == 0#64 },
  { name := "execWords: ChaCha20 quarter round RFC 8439 §2.1.1 test vector"
    check :=
      let s0 := ({} : State).writeReg32 .x0 0x11111111#32
                            |>.writeReg32 .x1 0x01020304#32
                            |>.writeReg32 .x2 0x9b8d6f43#32
                            |>.writeReg32 .x3 0x01234567#32
      let sf := runWords [
        0x0b010000#32, 0x4a000063#32, 0x13834063#32,
        0x0b030042#32, 0x4a020021#32, 0x13815021#32,
        0x0b010000#32, 0x4a000063#32, 0x13836063#32,
        0x0b030042#32, 0x4a020021#32, 0x13816421#32,
        0xd65f03c0#32
      ] s0
      sf.readReg32 .x0 == 0xea2a92f4#32 &&
      sf.readReg32 .x1 == 0xcb1cf8ce#32 &&
      sf.readReg32 .x2 == 0x4581472e#32 &&
      sf.readReg32 .x3 == 0x5881c4bb#32 },
  { name := "execWords: SipHash SipRound permutation matches pure spec"
    check :=
      let v0 := 0x736f6d6570736575#64
      let v1 := 0x646f72616e646f6d#64
      let v2 := 0x6c7967656e657261#64
      let v3 := 0x7465646279746573#64
      let v0_1 := v0 + v1
      let v1_1 := (v1.rotateLeft 13) ^^^ v0_1
      let v0_2 := v0_1.rotateLeft 32
      let v2_1 := v2 + v3
      let v3_1 := (v3.rotateLeft 16) ^^^ v2_1
      let e0 := v0_2 + v3_1
      let e3 := (v3_1.rotateLeft 21) ^^^ e0
      let v2_2 := v2_1 + v1_1
      let e1 := (v1_1.rotateLeft 17) ^^^ v2_2
      let e2 := v2_2.rotateLeft 32
      let s0 := ({} : State).writeReg64 .x0 v0 |>.writeReg64 .x1 v1 |>.writeReg64 .x2 v2 |>.writeReg64 .x3 v3
      let sf := runWords [
        0x8b010000#32, 0xcac1cc01#32, 0x93c08000#32,
        0x8b030042#32, 0xcac3c043#32, 0x8b030000#32,
        0xcac3ac03#32, 0x8b010042#32, 0xcac1bc41#32,
        0x93c28042#32, 0xd65f03c0#32
      ] s0
      sf.readReg64 .x0 == e0 && sf.readReg64 .x1 == e1 && sf.readReg64 .x2 == e2 && sf.readReg64 .x3 == e3 },
  { name := "ubfiz_width_eq_lsb_regression"
    check :=
      -- ubfiz w7, w2, #8, #8 (0x53181c47): N=32, immr=24, imms=7 (imms + 1 == N - immr == 8)
      -- ubfiz x3, x1, #16, #16 (0xd3703c23): N=64, immr=48, imms=15 (imms + 1 == N - immr == 16)
      let s0 := ({} : State).writeReg64 .x1 0xfedcba9887654321#64 |>.writeReg64 .x2 0x0000000000119c0f#64
      let sf := runWords [0x53181c47#32, 0xd3703c23#32, 0xd65f03c0#32] s0
      sf.readReg64 .x7 == 0x0000000000000f00#64 && sf.readReg64 .x3 == 0x0000000043210000#64 },
  { name := "decode_undefined_encodings_rejected"
    check :=
      -- LogicalImm sf=0, N=1 (0x12400000); MoveWide sf=0, hw=32 (0x52c00000); AddSubReg ROR (0x8bc00000)
      decode 0x12400000#32 == none && decode 0x52c00000#32 == none && decode 0x8b000000#32 != none && decode 0x8bc00000#32 == none },
  { name := "fetch_decode_countdown_loop_words"
    check :=
      let words : List (BitVec 32) := [0xb4000081#32, 0xca400400#32, 0xf1000421#32, 0x54ffffc1#32, 0xd65f03c0#32]
      let p := Program.ofWords 0x1000#64 words
      (List.range words.length).all fun i =>
        p.fetch (0x1000#64 + BitVec.ofNat 64 (i * 4)) == decode words[i]! },
  { name := "execWords_decoder_bug_regressions"
    check :=
      -- Regression test for subs xzr (cmp), shifted neg, and ngc
      let sf := runWords [
        0xf100043f#32, -- subs xzr, x1, #1
        0x9a9f17e0#32, -- cset x0, eq
        0xcb010fe2#32, -- neg x2, x1, lsl #3
        0xda0103e3#32, -- ngc x3, x1
        0xd65f03c0#32  -- ret
      ] (({} : State).writeReg64 .x1 1#64)
      sf.pc == 0xdead0000#64 && sf.readReg64 .x0 == 1#64 && sf.readReg64 .x2 == (-8#64) && sf.readReg64 .x3 == (-1#64) },

  -- AST-to-binary encoder and hex-string round-trip tests (`encode` / `decode`)
  { name := "codec hex: ADD X0, X1, #42 == 0x9100a820"
    check :=
      let inst : Instr := .addSubImm .W64 .ADD .x0 .x1 42#12 false
      encodeHex inst == some "0x9100a820" &&
      roundTripWordHex 0x9100a820#32 == some ("0x9100a820", "0x9100a820") },
  { name := "codec hex: SUBS XZR, X0, X1 == 0xeb01001f"
    check :=
      let inst : Instr := .addSubShift .W64 .SUBS .xzr .x0 .x1 .LSL 0
      encodeHex inst == some "0xeb01001f" &&
      roundTripWordHex 0xeb01001f#32 == some ("0xeb01001f", "0xeb01001f") },
  { name := "codec hex: CSEL / CSNEG / REV64 / CLZ / RBIT / UBFM / STP / LDP / RET"
    check :=
      let hexWords := [
        "0x9a812000", "0xda80a400", "0xdac00c00", "0xdac01020",
        "0xdac00020", "0xd348fc00", "0xa9bf7bfd", "0xa8c17bfd", "0xd65f03c0"
      ]
      let words : List (BitVec 32) := [
        0x9a812000#32, 0xda80a400#32, 0xdac00c00#32, 0xdac01020#32,
        0xdac00020#32, 0xd348fc00#32, 0xa9bf7bfd#32, 0xa8c17bfd#32, 0xd65f03c0#32
      ]
      (words.filterMap decode |> encodeProgHex) == some hexWords },
  { name := "codec hex: LogicalImm bitmask encoding (esize 2, 4, 8, 16, 32, 64 & wrap-around)"
    check :=
      let testMasks : List (Instr × String) := [
        (.logicalImm .W64 .AND  .x0 .x1 0x5555555555555555#64, "0x9200f020"),
        (.logicalImm .W64 .ORR  .x0 .x1 0x3333333333333333#64, "0xb200e420"),
        (.logicalImm .W64 .EOR  .x0 .x1 0x0f0f0f0f0f0f0f0f#64, "0xd200cc20"),
        (.logicalImm .W64 .ANDS .x0 .x1 0x00ff00ff00ff00ff#64, "0xf2009c20"),
        (.logicalImm .W64 .AND  .x0 .x1 0x00000000ffffffff#64, "0x92407c20"),
        (.logicalImm .W64 .AND  .x0 .x1 0x800000000000000f#64, "0x92411020"),
        (.logicalImm .W32 .AND  .x0 .x1 0x000000ff000000ff#64, "0x12001c20")
      ]
      testMasks.all fun (inst, expectedHex) =>
        encodeHex inst == some expectedHex &&
        (encode inst >>= decode) == some inst },
  { name := "codec hex: ChaCha20 & SipHash full machine-code hex round-trip"
    check :=
      let words : List (BitVec 32) := [
        0x0b010000#32, 0x4a000063#32, 0x13834063#32,
        0x0b030042#32, 0x4a020021#32, 0x13815021#32,
        0x0b010000#32, 0x4a000063#32, 0x13836063#32,
        0x0b030042#32, 0x4a020021#32, 0x13816421#32,
        0x8b010000#32, 0xcac1cc01#32, 0x93c08000#32,
        0x8b030042#32, 0xcac3c043#32, 0x8b030000#32,
        0xcac3ac03#32, 0x8b010042#32, 0xcac1bc41#32,
        0x93c28042#32, 0xd65f03c0#32
      ]
      let inHex := wordsToHex words
      let outHex := (decodeProg words >>= encodeProgHex).getD []
      inHex == outHex },
  { name := "codec hex: every instruction class round-trips AST -> hex -> AST -> hex"
    check :=
      let insts : List Instr := [
        .nop,
        .system false 0#16,
        .system true 1#16,
        .adr false .x0 16#64,
        .adr true .x1 0x2000#64,
        .addSubImm .W64 .ADD .x0 .sp 16#12 false,
        .addSubImm .W64 .SUB .x2 .x3 5#12 true,
        .logicalImm .W64 .ORR .x0 .xzr 0x0000ffff0000ffff#64,
        .moveWide .W64 .MOVZ .x0 0x1234#16 16,
        .moveWide .W32 .MOVK .x1 0xabcd#16 0,
        .bitfield .W64 .UBFM .x0 .x1 8 63,
        .extr .W64 .x0 .x1 .x2 12,
        .b (-12#64),
        .bl 64#64,
        .cbz .W64 true .x1 16#64,
        .tbz .W64 false .x2 37 (-8#64),
        .bCond .NE (-16#64),
        .br .x8,
        .blr .x9,
        .ret .x30,
        .logicalShift .W64 .BIC .x0 .x1 .x2 .LSR 5,
        .addSubShift .W64 .ADDS .xzr .x0 .x1 .ASR 3,
        .addSubExt .W64 .ADD .sp .sp .x1 .UXTW 2,
        .addSubCarry .W64 .SUB .x0 .x1 .x2,
        .condCompareImm .W64 true .x0 7#5 4#4 .EQ,
        .condCompareReg .W64 false .x0 .x1 2#4 .NE,
        .condSelect .W64 .CSINC .x0 .x1 .x2 .LT,
        .dataProc1 .W64 .CLZ .x0 .x1,
        .dataProc2 .W64 .UDIV .x0 .x1 .x2,
        .dataProc3 .W64 .MADD .x0 .x1 .x2 .x3,
        .ldp .W64 false .x29 .x30 (.PreIndex .sp (-16#64)),
        .stp .W64 .x0 .x1 (.Offset .sp 16#64),
        .ldr .W64 .X64 false .x0 (.Offset .x1 24#64),
        .ldr .W64 .X64 false .x0 (.UnscaledOffset .x1 (-8#64)),
        .str .W32 .x2 (.RegOffset .x0 .x1 .UXTW 2),
        .ldrLit .W64 false .x0 32#64,
        .ldarStlr .B8 true .x0 .x8,
        .ldarStlr .X64 false .x0 .x8,
        .ldxr .X64 false .x10 .x8,
        .ldxr .B8 true .sp .xzr,
        .stxr .X64 false .x12 .x10 .x11,
        .stxr .H16 true .xzr .sp .x1,
        .sysReg true 0x5e82#15 .x8,
        .barrier 0b1011#4 5#3,
        .ldpSimd .Q128 0#5 1#5 (.Offset .sp 32#64),
        .stpSimd .D64 2#5 3#5 (.PreIndex .sp (-16#64)),
        .ldrSimd .Q128 4#5 (.Offset .x0 16#64),
        .strSimd .Q128 5#5 (.UnscaledOffset .x0 (-16#64)),
        .st1SinglePost true 31#5 0#3 true 3#2 .x12 0#5,
        .aes .AESE 0#5 1#5,
        .aes .AESMC 0#5 0#5,
        .fmovGprVec true 1#2 0#2 7#3 8#5 0#5,
        .simdImmShift true false 0#4 0#3 0b11100#5 0#5 0#5,
        .simdInsDup true false 1#5 1#4 8#5 0#5,
        .simdInsDup true true 0b01011#5 0b0000#4 0#5 2#5,
        .simdThreeSame true true 0#2 1#5 3#5 0#5 0#5,
        .simdTwoRegMisc true false 0#2 0#5 0#5 0#5,
        .simdAcrossLanes true true 0#2 10#5 0#5 0#5,
        .simdPermute true 0#2 1#5 1#3 0#5 0#5,
        .simdExt true 1#5 8#4 0#5 0#5,
        .fpDataProc1 1#2 0#6 3#5 0#5,
        .fpDataProc1 1#2 0xb#6 0#5 1#5,
        .fpDataProc2 1#2 1#5 3#4 0#5 1#5,
        .fpDataProc2 1#2 2#5 0#4 1#5 1#5,
        .fpCompare 1#2 1#5 0#2 0#5 0#5,
        .fpImm 1#2 0x70#8 0#5,
        .fpCondCompare 1#2 1#5 0#4 0#5 false 4#4,
        .fpCondSelect 1#2 2#5 0#4 1#5 0#5,
        .fpDataProc3 1#2 false 2#5 false 3#5 1#5 0#5,
        .fpFixedConv true 1#2 3#2 0#3 0x30#6 0#5 0#5
      ]
      insts.all fun p =>
        match roundTripInstHex p with
        | some (h1, h2, eqP) => h1 == h2 && eqP
        | none => false },
  { name := "codec: scalar FP instructions (fmov, frintz, fsub, fmul, fcvtzu, fcmp, fmov #imm, fccmp, fcsel, fmadd, fixed-point fcvtzs) decode and round-trip"
    check :=
      decode 0x1e604060#32 == some (.fpDataProc1 1#2 0#6 3#5 0#5) &&
      decode 0x1e65c001#32 == some (.fpDataProc1 1#2 0xb#6 0#5 1#5) &&
      decode 0x1e613801#32 == some (.fpDataProc2 1#2 1#5 3#4 0#5 1#5) &&
      decode 0x1e620821#32 == some (.fpDataProc2 1#2 2#5 0#4 1#5 1#5) &&
      decode 0x9e790008#32 == some (.fmovGprVec true 1#2 3#2 1#3 0#5 8#5) &&
      decode 0x1e790029#32 == some (.fmovGprVec false 1#2 3#2 1#3 1#5 9#5) &&
      decode 0x1e612000#32 == some (.fpCompare 1#2 1#5 0#2 0#5 0#5) &&
      decode 0x1e602008#32 == some (.fpCompare 1#2 0#5 0#2 0#5 8#5) &&
      decode 0x1e6e1000#32 == some (.fpImm 1#2 0x70#8 0#5) &&
      decode 0x1e610404#32 == some (.fpCondCompare 1#2 1#5 0#4 0#5 false 4#4) &&
      decode 0x1e620c20#32 == some (.fpCondSelect 1#2 2#5 0#4 1#5 0#5) &&
      decode 0x1f420c20#32 == some (.fpDataProc3 1#2 false 2#5 false 3#5 1#5 0#5) &&
      decode 0x9e58c000#32 == some (.fpFixedConv true 1#2 3#2 0#3 0x30#6 0#5 0#5) &&
      [0x1e604060#32, 0x1e65c001#32, 0x1e613801#32, 0x1e620821#32, 0x9e790008#32,
       0x1e790029#32, 0x1e612000#32, 0x1e602008#32, 0x1e6e1000#32, 0x1e610404#32,
       0x1e620c20#32, 0x1f420c20#32, 0x9e58c000#32].all fun w =>
        (decode w >>= encode) == some w },

  -- Unscaled, acquire/release, SIMD, AES, and system-register execution tests
  { name := "execWords: LDUR/STUR unscaled offsets (positive, negative, byte, halfword)"
    check :=
      -- stur x0,[x10,#8]; ldur x2,[x10,#8]; stur x1,[x10,#-8]; ldur x3,[x10,#-8]
      -- sturb w0,[x10,#17]; ldurb w4,[x10,#17]; sturh w1,[x10,#-3]; ldurh w5,[x10,#-3]
      let s0 := (({} : State).writeReg64 .x0 0x1122334455667788#64
                            |>.writeReg64 .x1 0xfedcba9876543210#64
                            |>.writeReg64 .x10 (dataBase + 64#64))
      let sf := runWords [
        0xf8008140#32, 0xf8408142#32, 0xf81f8141#32, 0xf85f8143#32,
        0x38011140#32, 0x38411144#32, 0x781fd141#32, 0x785fd145#32,
        0xd65f03c0#32
      ] s0
      sf.readReg64 .x2 == 0x1122334455667788#64 &&
      sf.readReg64 .x3 == 0xfedcba9876543210#64 &&
      sf.readReg64 .x4 == 0x88#64 &&
      sf.readReg64 .x5 == 0x3210#64 &&
      sf.mem.read64 (dataBase + 72#64) == 0x1122334455667788#64 &&
      -- the unaligned `sturh` at `dataBase + 61` overlaps the `stur` at `dataBase + 56`
      sf.mem.read64 (dataBase + 56#64) == 0xfe32109876543210#64 },
  { name := "execWords: LDAR/STLR at byte, halfword, word and doubleword widths"
    check :=
      -- stlr x0,[x10]; ldar x2,[x10]; stlrb w1,[x10+8]; ldarb w3; stlrh w1,[x10+16]; ldarh w4
      -- stlr w1,[x10+24]; ldar w5,[x10+24]
      let s0 := (({} : State).writeReg64 .x0 0xcafebabe12345678#64
                            |>.writeReg64 .x1 0xdeadbeef#64
                            |>.writeReg64 .x10 dataBase)
      let sf := runWords [
        0xc89ffd40#32, 0xc8dffd42#32, 0x9100214b#32, 0x089ffd61#32,
        0x08dffd63#32, 0x9100414c#32, 0x489ffd81#32, 0x48dffd84#32,
        0x9100614d#32, 0x889ffda1#32, 0x88dffda5#32, 0xd65f03c0#32
      ] s0
      sf.readReg64 .x2 == 0xcafebabe12345678#64 &&
      sf.readReg64 .x3 == 0xef#64 &&
      sf.readReg64 .x4 == 0xbeef#64 &&
      sf.readReg64 .x5 == 0xdeadbeef#64 &&
      sf.mem.read64 dataBase == 0xcafebabe12345678#64 &&
      sf.mem.readSized .B8 false (dataBase + 8#64) == 0xef#64 &&
      sf.mem.readSized .H16 false (dataBase + 16#64) == 0xbeef#64 &&
      sf.mem.readSized .W32 false (dataBase + 24#64) == 0xdeadbeef#64 },
  { name := "decode: LDXR/STXR words (ldxr x8,[x10] = 0xc85f7d48; stxr w12,x11,[x10] = 0xc80c7d4b)"
    check :=
      decode 0xc85f7d48#32 == some (.ldxr .X64 false .x10 .x8) &&
      decode 0xc80c7d4b#32 == some (.stxr .X64 false .x12 .x10 .x11) &&
      decode 0x885f7d09#32 == some (.ldxr .W32 false .x8 .x9) &&
      decode 0x880afd09#32 == some (.stxr .W32 true .x10 .x8 .x9) &&
      decode 0x085ffc20#32 == some (.ldxr .B8 true .x1 .x0) &&
      decode 0x48027fe1#32 == some (.stxr .H16 false .x2 .sp .x1) &&
      encode (.ldxr .X64 false .x10 .x8) == some 0xc85f7d48#32 &&
      encode (.stxr .X64 false .x12 .x10 .x11) == some 0xc80c7d4b#32 },
  { name := "decode: STXR CONSTRAINED UNPREDICTABLE overlaps and non-SBO LDXR fields are rejected"
    check :=
      decode 0xc8087d48#32 == none &&  -- stxr w8, x8, [x10]  (Rs == Rt)
      decode 0xc80a7d48#32 == none &&  -- stxr w10, x8, [x10] (Rs == Rn)
      decode 0xc85f7948#32 == none &&  -- ldxr, Rt2 != 11111
      decode 0xc85e7d48#32 == none &&  -- ldxr, Rs != 11111
      -- stxr w0, x1, [sp]: Rn = 31 is SP, so `Rs == Rn` overlap does not apply
      decode 0xc8007fe1#32 == some (.stxr .X64 false .x0 .sp .x1) },
  { name := "execWords: LDXR/STXR exclusive pairs succeed when exclFails = [] (status := 0) at all widths"
    check :=
      -- mov w9,#7; mov w12,#7; ldxr x2,[x10]; stxr w9,x0,[x10]; ldaxr w3,[x10];
      -- stlxr w12,w1,[x10]; ldxrb w4,[x10]; stxrh w13,w0,[x10]; ldaxrh w5,[x10]
      let s0 := (({} : State).writeReg64 .x0 0xcafebabe12345678#64
                            |>.writeReg64 .x1 0xdeadbeef#64
                            |>.writeReg64 .x13 0xffffffffffffffff#64
                            |>.writeReg64 .x10 dataBase)
      let sf := runWords [
        0x528000e9#32, 0x528000ec#32, 0xc85f7d42#32, 0xc8097d40#32,
        0x885ffd43#32, 0x880cfd41#32, 0x085f7d44#32, 0x480d7d40#32,
        0x485ffd45#32, 0xd65f03c0#32
      ] s0
      sf.readReg64 .x2 == 0#64 &&
      sf.readReg64 .x3 == 0x12345678#64 &&
      sf.readReg64 .x4 == 0xef#64 &&
      sf.readReg64 .x5 == 0x5678#64 &&
      sf.readReg64 .x9 == 0#64 &&
      sf.readReg64 .x12 == 0#64 &&
      sf.readReg64 .x13 == 0#64 &&
      sf.mem.read64 dataBase == 0xcafebabedead5678#64 },
  { name := "execInst: STXR and STXP spurious-failure oracle sets Ws := 1 without writing memory on true, then Ws := 0 and writes memory on false"
    check :=
      let s0 := (({ rwState with exclFails := [true, false, true] } : State)
        |>.writeReg64 .x0 0x1122334455667788#64
        |>.writeReg64 .x1 0x99aabbccddeeff00#64
        |>.writeReg64 .x10 dataBase)
      -- 1st STXR fails spuriously (exclFails head = true): x9 := 1, memory unchanged
      let s1 := execInst (.stxr .X64 false .x9 .x10 .x0) s0
      -- 2nd STXR succeeds (exclFails head = false): x9 := 0, memory updated
      let s2 := execInst (.stxr .X64 false .x9 .x10 .x0) s1
      -- 3rd store-exclusive (STXP, exclFails head = true) fails spuriously: x9 := 1, memory unchanged
      let s3 := execInst (.stxp .W64 false .x9 .x10 .x0 .x1) s2
      -- 4th store-exclusive (STXP, exclFails = [] defaults to false) succeeds: x9 := 0, 16B written
      let s4 := execInst (.stxp .W64 false .x9 .x10 .x0 .x1) s3
      s1.readReg64 .x9 == 1#64 && s1.mem.read64 dataBase == 0#64 && s1.exclFails == [false, true] &&
      s2.readReg64 .x9 == 0#64 && s2.mem.read64 dataBase == 0x1122334455667788#64 && s2.exclFails == [true] &&
      s3.readReg64 .x9 == 1#64 && s3.mem.read64 (dataBase + 8#64) == 0#64 && s3.exclFails == [] &&
      s4.readReg64 .x9 == 0#64 && s4.mem.read64 (dataBase + 8#64) == 0x99aabbccddeeff00#64 && s4.exclFails == [] },
  { name := "execWords: DMB ISH / DSB ISH / ISB are PC-advancing no-ops"
    check :=
      -- add x1,x0,#1; dmb ish; add x2,x1,#1; dsb ish; isb; add x3,x2,#1
      let s0 := ({} : State).writeReg64 .x0 41#64
      let sf := runWords [
        0x91000401#32, 0xd5033bbf#32, 0x91000422#32,
        0xd5033b9f#32, 0xd5033fdf#32, 0x91000443#32, 0xd65f03c0#32
      ] s0
      sf.pc == 0xdead0000#64 &&
      sf.readReg64 .x1 == 42#64 && sf.readReg64 .x2 == 43#64 && sf.readReg64 .x3 == 44#64 },
  { name := "execWords: MSR/MRS tpidr_el0 round-trips through the thread pointer"
    check :=
      -- msr tpidr_el0,x0; mrs x1,tpidr_el0; add x2,x1,#1; msr tpidr_el0,x2; mrs x3,tpidr_el0
      let s0 := ({} : State).writeReg64 .x0 0x1122334455667788#64
      let sf := runWords [
        0xd51bd040#32, 0xd53bd041#32, 0x91000422#32,
        0xd51bd042#32, 0xd53bd043#32, 0xd65f03c0#32
      ] s0
      sf.readReg64 .x1 == 0x1122334455667788#64 &&
      sf.readReg64 .x2 == 0x1122334455667789#64 &&
      sf.readReg64 .x3 == 0x1122334455667789#64 &&
      sf.tpidrEl0 == 0x1122334455667789#64 },
  { name := "execWords: SIMD LDR/STR at q, d and s widths (plus unscaled LDUR q)"
    check :=
      -- stp x0,x1,[x10]; ldr q0,[x10]; ldr d1,[x10,#8]; ldr s2,[x10,#4]
      -- str q0,[x10,#16]; str d1,[x10,#32]; str s2,[x10,#40]; ldur q3,[x10,#-16]
      let s0 := withMem64
        (({} : State).writeReg64 .x0 0x0807060504030201#64
                    |>.writeReg64 .x1 0x100f0e0d0c0b0a09#64
                    |>.writeReg64 .x10 dataBase)
        [(dataBase - 16#64, 0xaaaabbbbccccdddd#64), (dataBase - 8#64, 0x1111222233334444#64)]
      let sf := runWords [
        0xa9000540#32, 0x3dc00140#32, 0xfd400541#32, 0xbd400542#32,
        0x3d800540#32, 0xfd001141#32, 0xbd002942#32, 0x3cdf0143#32,
        0xd65f03c0#32
      ] s0
      sf.readVReg128 0#5 == 0x100f0e0d0c0b0a090807060504030201#128 &&
      sf.readVReg128 1#5 == 0x100f0e0d0c0b0a09#128 &&
      sf.readVReg128 2#5 == 0x08070605#128 &&
      sf.readVReg128 3#5 == 0x1111222233334444aaaabbbbccccdddd#128 &&
      sf.mem.read128 (dataBase + 16#64) == 0x100f0e0d0c0b0a090807060504030201#128 &&
      sf.mem.read64 (dataBase + 32#64) == 0x100f0e0d0c0b0a09#64 &&
      sf.mem.read32 (dataBase + 40#64) == 0x08070605#32 },
  { name := "execWords: SIMD LDP/STP (q pair and d pair)"
    check :=
      -- stp x0,x1,[x10]; stp x2,x3,[x10,#16]; ldp q0,q1,[x10]; stp q1,q0,[x10,#32]; ldp d2,d3,[x10,#8]
      let s0 := (({} : State).writeReg64 .x0 0x0807060504030201#64
                            |>.writeReg64 .x1 0x100f0e0d0c0b0a09#64
                            |>.writeReg64 .x2 0x1817161514131211#64
                            |>.writeReg64 .x3 0x201f1e1d1c1b1a19#64
                            |>.writeReg64 .x10 dataBase)
      let sf := runWords [
        0xa9000540#32, 0xa9010d42#32, 0xad400540#32,
        0xad010141#32, 0x6d408d42#32, 0xd65f03c0#32
      ] s0
      sf.readVReg128 0#5 == 0x100f0e0d0c0b0a090807060504030201#128 &&
      sf.readVReg128 1#5 == 0x201f1e1d1c1b1a191817161514131211#128 &&
      sf.readVReg128 2#5 == 0x100f0e0d0c0b0a09#128 &&
      sf.readVReg128 3#5 == 0x1817161514131211#128 &&
      sf.mem.read128 (dataBase + 32#64) == 0x201f1e1d1c1b1a191817161514131211#128 &&
      sf.mem.read128 (dataBase + 48#64) == 0x100f0e0d0c0b0a090807060504030201#128 },
  { name := "execWords: FMOV GPR <-> vector (s, d, and the high d[1] lane)"
    check :=
      -- fmov d0,x0; fmov x1,d0; fmov s1,w2; fmov w3,s1; fmov v0.d[1],x4; fmov x5,v0.d[1]
      let s0 := (({} : State).writeReg64 .x0 0x0123456789abcdef#64
                            |>.writeReg64 .x2 0xffffffffcafebabe#64
                            |>.writeReg64 .x4 0x1122334455667788#64)
      let sf := runWords [
        0x9e670000#32, 0x9e660001#32, 0x1e270041#32,
        0x1e260023#32, 0x9eaf0080#32, 0x9eae0005#32, 0xd65f03c0#32
      ] s0
      sf.readReg64 .x1 == 0x0123456789abcdef#64 &&
      sf.readReg64 .x3 == 0xcafebabe#64 &&
      sf.readReg64 .x5 == 0x1122334455667788#64 &&
      sf.readVReg128 0#5 == 0x11223344556677880123456789abcdef#128 &&
      sf.readVReg128 1#5 == 0xcafebabe#128 },
  { name := "execWords: scalar FP instructions (fmov d0, d3; frintz d1, d0; fsub d1, d0, d1; fmul d1, d1, d2; fcvtzu x8, d0; fcvtzu w9, d1; fmov d4, #1.0; fcsel; fcmp; fmadd)"
    check :=
      let d3Val : BitVec 64 := 0x3ff8000000000000#64
      let d2Val : BitVec 64 := 0x41cdcd6500000000#64
      let s0 := (({} : State).writeVReg128 0#5 0xffffffffffffffffffffffffffffffff#128
                            |>.writeVReg64 2#5 d2Val
                            |>.writeVReg64 3#5 d3Val
                            |>.setPState { n := false, z := true, c := false, v := false })
      let sf := runWords [
        0x1e604060#32, -- fmov d0, d3
        0x1e65c001#32, -- frintz d1, d0
        0x1e613801#32, -- fsub d1, d0, d1
        0x1e620821#32, -- fmul d1, d1, d2
        0x9e790008#32, -- fcvtzu x8, d0
        0x1e790029#32, -- fcvtzu w9, d1
        0x1e6e1004#32, -- fmov d4, #1.0 (0x3ff0000000000000)
        0x1e620c05#32, -- fcsel d5, d0, d2, eq (z=true -> d0)
        0x1e621c06#32, -- fcsel d6, d0, d2, ne (z=true -> d2)
        0x1f420c27#32, -- fmadd d7, d1, d2, d3
        0x1e622000#32, -- fcmp d0, d2
        0xd65f03c0#32  -- ret
      ] s0
      let expRint := evalFp1Op64 0xb#6 d3Val
      let expSub := evalFp2Op64 0x3#4 d3Val expRint
      let expMul := evalFp2Op64 0x0#4 expSub d2Val
      let expX8 := evalFpToInt64_64 true 0b11#2 d3Val
      let expW9 := evalFpToInt32_64 true 0b11#2 expMul
      let expFmadd := evalFp3Op64 false false expMul d2Val d3Val
      let expPs := evalFpCmp64 false d3Val d2Val
      expRint == 0x3ff0000000000000#64 &&
      expSub == 0x3fe0000000000000#64 &&
      expMul == 0x41bdcd6500000000#64 &&
      expX8 == 1#64 &&
      expW9 == 500000000#32 &&
      expFmadd == 0x439bc16d674ec800#64 &&
      expPs == { n := true, z := false, c := false, v := false } &&
      sf.status == .Running &&
      sf.pc == 0xdead0000#64 &&
      sf.readVReg128 0#5 == d3Val.zeroExtend 128 &&
      sf.readVReg64 1#5 == expMul &&
      sf.readReg64 .x8 == expX8 &&
      sf.readReg32 .x9 == expW9 &&
      sf.readVReg64 4#5 == 0x3ff0000000000000#64 &&
      sf.readVReg64 5#5 == d3Val &&
      sf.readVReg64 6#5 == d2Val &&
      sf.readVReg64 7#5 == expFmadd &&
      sf.pstate == expPs },
  { name := "execWords: concrete IEEE-754 32/64-bit arithmetic, rounding conversions, and fixed-point"
    check :=
      let s0 := (({} : State).writeVReg64 0#5 0x4004000000000000#64  -- 2.5
                            |>.writeVReg64 1#5 0xbff8000000000000#64 -- -1.5
                            |>.writeReg64 .x0 0x00028000#64          -- 2.5 in Q48.16
                            |>.writeReg32 .x1 0xffffffec#32)         -- -20 in Q24.8 -> -0.078125
      let sf := runWords [
        0x1e612802#32, -- fadd d2, d0, d1        -> 1.0 (0x3ff0000000000000)
        0x1e611803#32, -- fdiv d3, d0, d1        -> -5/3 (0xbffaaaaaaaaaaaab)
        0x1e60c044#32, -- fsqrt d4, d2           -> 1.0 (0x3ff0000000000000)
        0x1e618805#32, -- fnmul d5, d0, d1       -> 3.75 (0x400e000000000000)
        0x9e600002#32, -- fcvtns x2, d0          -> 2 (ties to even: 2.5 -> 2)
        0x9e640003#32, -- fcvtas x3, d0          -> 3 (ties away: 2.5 -> 3)
        0x9e680024#32, -- fcvtps x4, d1          -> -1 (ceil(-1.5) = -1)
        0x9e700025#32, -- fcvtms x5, d1          -> -2 (floor(-1.5) = -2)
        0x9e42c006#32, -- scvtf d6, x0, #16      -> 2.5 (0x4004000000000000)
        0x9e58c0c6#32, -- fcvtzs x6, d6, #16     -> 0x00028000
        0x1e02e027#32, -- scvtf s7, w1, #8       -> -0.078125 (0xbda00000)
        0x1e22c0e8#32, -- fcvt d8, s7            -> -0.078125 (0xbfb4000000000000)
        0x1e6240a9#32, -- fcvt s9, d5            -> 3.75f (0x40700000)
        0xd65f03c0#32  -- ret
      ] s0
      sf.status == .Running &&
      sf.readVReg64 2#5 == 0x3ff0000000000000#64 &&
      sf.readVReg64 3#5 == 0xbffaaaaaaaaaaaab#64 &&
      sf.readVReg64 4#5 == 0x3ff0000000000000#64 &&
      sf.readVReg64 5#5 == 0x400e000000000000#64 &&
      sf.readReg64 .x2 == 2#64 &&
      sf.readReg64 .x3 == 3#64 &&
      sf.readReg64 .x4 == 0xffffffffffffffff#64 &&
      sf.readReg64 .x5 == 0xfffffffffffffffe#64 &&
      sf.readVReg64 6#5 == 0x4004000000000000#64 &&
      sf.readReg64 .x6 == 0x00028000#64 &&
      sf.readVReg32 7#5 == 0xbda00000#32 &&
      sf.readVReg64 8#5 == 0xbfb4000000000000#64 &&
      sf.readVReg32 9#5 == 0x40700000#32 },
  { name := "execWords: DUP / INS / UMOV element moves"
    check :=
      -- dup v0.16b,w0; dup v1.2d,x1; ins v1.d[0],x2; umov x3,v1.d[1]; umov w4,v0.b[3]; ins v2.b[5],v0.b[0]
      let s0 := (({} : State).writeReg64 .x0 0x5a#64
                            |>.writeReg64 .x1 0x1122334455667788#64
                            |>.writeReg64 .x2 0xaabbccddeeff0011#64)
      let sf := runWords [
        0x4e010c00#32, 0x4e080c21#32, 0x4e081c41#32,
        0x4e183c23#32, 0x0e073c04#32, 0x6e0b0402#32, 0xd65f03c0#32
      ] s0
      sf.readReg64 .x3 == 0x1122334455667788#64 &&
      sf.readReg64 .x4 == 0x5a#64 &&
      sf.readVReg128 0#5 == 0x5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a#128 &&
      sf.readVReg128 1#5 == 0x1122334455667788aabbccddeeff0011#128 &&
      sf.readVReg128 2#5 == 0x00005a0000000000#128 },
  { name := "execWords: SIMD three-same EOR / ADD.4s / SUB.8h / CMEQ.16b"
    check :=
      -- ldr q0,[x10]; ldr q1,[x10,#16]; eor v2.16b; add v3.4s; sub v4.8h; cmeq v5.16b
      let s0 := withMem64 (({} : State).writeReg64 .x10 dataBase)
        [(dataBase, 0x0807060504030201#64), (dataBase + 8#64, 0x100f0e0d0c0b0a09#64),
         (dataBase + 16#64, 0x0807060504030201#64), (dataBase + 24#64, 0xf0f0f0f0f0f0f0f0#64)]
      let sf := runWords [
        0x3dc00140#32, 0x3dc00541#32, 0x6e211c02#32,
        0x4ea18403#32, 0x6e618404#32, 0x6e218c05#32, 0xd65f03c0#32
      ] s0
      sf.readVReg128 2#5 == 0xe0fffefdfcfbfaf90000000000000000#128 &&
      sf.readVReg128 3#5 == 0x00fffefdfcfbfaf9100e0c0a08060402#128 &&
      sf.readVReg128 4#5 == 0x1f1f1d1d1b1b19190000000000000000#128 &&
      sf.readVReg128 5#5 == 0x0000000000000000ffffffffffffffff#128 },
  { name := "execWords: SIMD REV64 (.16b/.8h/.4s) and REV32 (.16b)"
    check :=
      let s0 := withMem64 (({} : State).writeReg64 .x10 dataBase)
        [(dataBase, 0x0807060504030201#64), (dataBase + 8#64, 0x100f0e0d0c0b0a09#64)]
      let sf := runWords [
        0x3dc00140#32, 0x4e200801#32, 0x4e600802#32,
        0x4ea00803#32, 0x6e200804#32, 0xd65f03c0#32
      ] s0
      sf.readVReg128 1#5 == 0x090a0b0c0d0e0f100102030405060708#128 &&
      sf.readVReg128 2#5 == 0x0a090c0b0e0d100f0201040306050807#128 &&
      sf.readVReg128 3#5 == 0x0c0b0a09100f0e0d0403020108070605#128 &&
      sf.readVReg128 4#5 == 0x0d0e0f10090a0b0c0506070801020304#128 },
  { name := "execWords: SIMD CMEQ #0 (.16b/.4s) and CMLT #0 (.16b)"
    check :=
      let s0 := withMem64 (({} : State).writeReg64 .x10 dataBase)
        [(dataBase, 0x00ff008000000001#64), (dataBase + 8#64, 0x0000000080000000#64)]
      let sf := runWords [
        0x3dc00140#32, 0x4e209801#32, 0x4ea09802#32, 0x4e20a803#32, 0xd65f03c0#32
      ] s0
      sf.readVReg128 1#5 == 0xffffffff00ffffffff00ff00ffffff00#128 &&
      sf.readVReg128 2#5 == 0xffffffff000000000000000000000000#128 &&
      sf.readVReg128 3#5 == 0x00000000ff00000000ff00ff00000000#128 },
  { name := "execWords: SIMD CMGT #0, CMGE #0 and CMLE #0 (.16b)"
    check :=
      -- ldr q0,[x10]; cmgt v1.16b,v0.16b,#0; cmge v2.16b,v0.16b,#0; cmle v3.16b,v0.16b,#0
      let s0 := withMem64 (({} : State).writeReg64 .x10 dataBase)
        [(dataBase, 0x00ff008000000001#64), (dataBase + 8#64, 0x0000000080000000#64)]
      let sf := runWords [
        0x3dc00140#32, 0x4e208801#32, 0x6e208802#32, 0x6e209803#32, 0xd65f03c0#32
      ] s0
      sf.readVReg128 1#5 == 0x000000000000000000000000000000ff#128 &&
      sf.readVReg128 2#5 == 0xffffffff00ffffffff00ff00ffffffff#128 &&
      sf.readVReg128 3#5 == 0xffffffffffffffffffffffffffffff00#128 },
  { name := "execWords: SIMD UMAXV across .16b and .8h lanes"
    check :=
      -- ldr q0,[x10]; umaxv b1,v0.16b; fmov w0,s1; umaxv h2,v0.8h; fmov w1,s2
      let s0 := withMem64 (({} : State).writeReg64 .x10 dataBase)
        [(dataBase, 0x0102037f04050607#64), (dataBase + 8#64, 0x08090a0b0c0dfe0f#64)]
      let sf := runWords [
        0x3dc00140#32, 0x6e30a801#32, 0x1e260020#32,
        0x6e70a802#32, 0x1e260041#32, 0xd65f03c0#32
      ] s0
      sf.readReg64 .x0 == 0xfe#64 &&
      sf.readReg64 .x1 == 0xfe0f#64 &&
      sf.readVReg128 1#5 == 0xfe#128 &&
      sf.readVReg128 2#5 == 0xfe0f#128 },
  { name := "execWords: SIMD ZIP1/ZIP2 and UZP1/UZP2 permutes"
    check :=
      let s0 := withMem64 (({} : State).writeReg64 .x10 dataBase)
        [(dataBase, 0x0807060504030201#64), (dataBase + 8#64, 0x100f0e0d0c0b0a09#64),
         (dataBase + 16#64, 0x2827262524232221#64), (dataBase + 24#64, 0x302f2e2d2c2b2a29#64)]
      let sf := runWords [
        0x3dc00140#32, 0x3dc00541#32, 0x4e013802#32, 0x4e011803#32,
        0x4e017804#32, 0x4e015805#32, 0x4ec13806#32, 0xd65f03c0#32
      ] s0
      sf.readVReg128 2#5 == 0x28082707260625052404230322022101#128 &&
      sf.readVReg128 3#5 == 0x2f2d2b29272523210f0d0b0907050301#128 &&
      sf.readVReg128 4#5 == 0x30102f0f2e0e2d0d2c0c2b0b2a0a2909#128 &&
      sf.readVReg128 5#5 == 0x302e2c2a28262422100e0c0a08060402#128 &&
      sf.readVReg128 6#5 == 0x28272625242322210807060504030201#128 },
  { name := "execWords: SIMD EXT (.16b #8, .16b #1, .8b #3)"
    check :=
      let s0 := withMem64 (({} : State).writeReg64 .x10 dataBase)
        [(dataBase, 0x0807060504030201#64), (dataBase + 8#64, 0x100f0e0d0c0b0a09#64),
         (dataBase + 16#64, 0x2827262524232221#64), (dataBase + 24#64, 0x302f2e2d2c2b2a29#64)]
      let sf := runWords [
        0x3dc00140#32, 0x3dc00541#32, 0x6e014002#32,
        0x6e010803#32, 0x2e011804#32, 0xd65f03c0#32
      ] s0
      sf.readVReg128 2#5 == 0x2827262524232221100f0e0d0c0b0a09#128 &&
      sf.readVReg128 3#5 == 0x21100f0e0d0c0b0a0908070605040302#128 &&
      sf.readVReg128 4#5 == 0x2322210807060504#128 },
  { name := "execWords: SIMD MOVI / SHL / USHLL / USHLL2"
    check :=
      -- movi v0.16b,#0x5a; ldr q1,[x10]; shl v2.2d,#4; shl v3.16b,#1; ushll v4.8h,#0; ushll2 v5.8h,#2
      let s0 := withMem64 (({} : State).writeReg64 .x10 dataBase)
        [(dataBase, 0x0807060504030201#64), (dataBase + 8#64, 0x100f0e0d0c0b0a09#64)]
      let sf := runWords [
        0x4f02e740#32, 0x3dc00141#32, 0x4f445422#32,
        0x4f095423#32, 0x2f08a424#32, 0x6f0aa425#32, 0xd65f03c0#32
      ] s0
      sf.readVReg128 0#5 == 0x5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a#128 &&
      sf.readVReg128 2#5 == 0x00f0e0d0c0b0a0908070605040302010#128 &&
      sf.readVReg128 3#5 == 0x201e1c1a18161412100e0c0a08060402#128 &&
      sf.readVReg128 4#5 == 0x00080007000600050004000300020001#128 &&
      sf.readVReg128 5#5 == 0x0040003c003800340030002c00280024#128 },
  { name := "execWords: ST1 single-lane post-indexed (b/h/s/d) writes back the base"
    check :=
      -- ldr q0,[x10]; add x11,x10,#64
      -- st1 {v0.b}[15],[x11],#1; st1 {v0.h}[3],[x11],#2; st1 {v0.s}[2],[x11],#4; st1 {v0.d}[1],[x11],#8
      let s0 := withMem64 (({} : State).writeReg64 .x10 dataBase)
        [(dataBase, 0x0807060504030201#64), (dataBase + 8#64, 0x100f0e0d0c0b0a09#64)]
      let sf := runWords [
        0x3dc00140#32, 0x9101014b#32, 0x4d9f1d60#32,
        0x0d9f5960#32, 0x4d9f8160#32, 0x4d9f8560#32, 0xd65f03c0#32
      ] s0
      sf.readReg64 .x11 == dataBase + 79#64 &&
      sf.mem.readSized .B8 false (dataBase + 64#64) == 0x10#64 &&
      sf.mem.readSized .H16 false (dataBase + 65#64) == 0x0807#64 &&
      sf.mem.readSized .W32 false (dataBase + 67#64) == 0x0c0b0a09#64 &&
      sf.mem.read64 (dataBase + 71#64) == 0x100f0e0d0c0b0a09#64 },
  { name := "execWords: AESE + AESMC match the FIPS-197 AES-128 round-1 known answer"
    check :=
      -- FIPS-197 Appendix C.1 (AES-128, plaintext 00112233445566778899aabbccddeeff,
      -- cipher key 000102030405060708090a0b0c0d0e0f):
      --   AESE  v0.16b, v1.16b  = ShiftRows(SubBytes(state XOR rk0)) = 6353e08c0960e104cd70b751bacad0e7
      --   AESMC v0.16b, v0.16b  = MixColumns(...)                    = 5f72641557f5bc92f7be3b291db9f91a
      -- (byte strings above are in memory order, i.e. bit-reversed vs. the 128-bit literals)
      let s0 := withMem64 (({} : State).writeReg64 .x10 dataBase)
        [(dataBase, 0x7766554433221100#64), (dataBase + 8#64, 0xffeeddccbbaa9988#64),
         (dataBase + 16#64, 0x0706050403020100#64), (dataBase + 24#64, 0x0f0e0d0c0b0a0908#64)]
      let sf := runWords [
        0x3dc00140#32, 0x3dc00541#32, 0x4e284820#32,
        0x3d800940#32, 0x4e286800#32, 0x3d800d40#32, 0xd65f03c0#32
      ] s0
      sf.mem.read128 (dataBase + 32#64) == 0xe7d0caba51b770cd04e160098ce05363#128 &&
      sf.mem.read128 (dataBase + 48#64) == 0x1af9b91d293bbef792bcf5571564725f#128 &&
      sf.readVReg128 0#5 == 0x1af9b91d293bbef792bcf5571564725f#128 },
  { name := "execWords: unaligned 17-byte ServiceId copy (STRB at +0 + STUR q0 at +1) and 20-byte UuidBuilder stack spill (STUR w0 at -32 + STUR q0 at -28)"
    check :=
      let src := dataBase
      let dst := dataBase + 64#64
      let tag8 : BitVec 8 := 0x01#8
      let uuid : BitVec 128 := 0x100f0e0d0c0b0a090807060504030201#128
      let trail : BitVec 8 := 0xaa#8
      let m0 := (((Memory.empty.write8 src tag8).write128 (src + 1#64) uuid).write8 (dst + 17#64) trail)
      let sCopy0 := ({ mem := m0 } : State).writeReg64 .x0 src |>.writeReg64 .x8 dst
      let sfCopy := runWords [
        0x39400009#32, 0x3cc01000#32, 0x39000109#32, 0x3c801100#32, 0xd65f03c0#32
      ] sCopy0
      let sSpill0 := ({} : State).writeReg32 .x0 0x12345678#32 |>.writeVReg128 0#5 uuid |>.writeReg64 .sp (dataBase + 256#64)
      let sfSpill := runWords [
        0xb81e03e0#32, 0x3c9e43e0#32, 0xb85e03e1#32, 0x3cde43e1#32, 0x385e63e2#32, 0xd65f03c0#32
      ] sSpill0
      sfCopy.mem.read8 dst == tag8 &&
      sfCopy.mem.read128 (dst + 1#64) == uuid &&
      sfCopy.mem.read8 (dst + 17#64) == trail &&
      sfSpill.readReg32 .x1 == 0x12345678#32 &&
      sfSpill.readVReg128 1#5 == uuid &&
      sfSpill.readReg64 .x2 == 0x03#64 },

  -- Exported Rust machine code (`Arm64/Testing/Generators/CompiledBinaryFixture.lean`, placed via `Obj.PlacedLib.program`)
  { name := "rust-export image: the loaded `examples` image is non-empty"
    check := fixtureWords.length > 0 },
  { name := "rust-export image: every exported word decodes (`decode w ≠ none`)"
    check := fixtureWords.all (fun w => (decode w).isSome) },
  { name := "rust-export image: every exported word re-encodes identically (`encode i = some w`)"
    check := codecMismatches fixtureWords == [] },
  { name := "rust-export exec: max_u64(100, 250) == 250 and clamp_u64(500, 10, 200) == 200"
    check :=
      let s0 := ({} : State).writeReg64 .x0 100#64 |>.writeReg64 .x1 250#64
      let s1 := ({} : State).writeReg64 .x0 500#64 |>.writeReg64 .x1 10#64 |>.writeReg64 .x2 200#64
      (runExportedProg fixtureProg (fixtureProg.fnAddr "examples::functions::max_u64") s0).readReg64 .x0 == 250#64 &&
      (runExportedProg fixtureProg (fixtureProg.fnAddr "examples::functions::clamp_u64") s1).readReg64 .x0 == 200#64 },
  { name := "rust-export exec: gcd_u64(1071, 462) == 21 and pow_u64(3, 13) == 1594323"
    check :=
      let s0 := ({} : State).writeReg64 .x0 1071#64 |>.writeReg64 .x1 462#64
      let s1 := ({} : State).writeReg64 .x0 3#64 |>.writeReg64 .x1 13#64
      (runExportedProg fixtureProg (fixtureProg.fnAddr "examples::algorithms::gcd_u64") s0).readReg64 .x0 == 21#64 &&
      (runExportedProg fixtureProg (fixtureProg.fnAddr "examples::algorithms::pow_u64") s1).readReg64 .x0 == 1594323#64 },
  { name := "rust-export exec: safe Rust syscalls (brk_alloc_and_write, mmap_alloc_and_log_dual, alloc_write_and_exit, mmap_stderr_and_exit_group)"
    check :=
      let s0 := (({ brk := 0x50000#64, oracle := testOracle 0x90000#64, physMemAvail := 0x10000 } : State).writeReg64 .x0 0x37#64)
      let sf1 := runProgramRaw fixtureProg
        (fixtureProg.fnAddr "examples::syscalls::app::brk_alloc_and_write") s0
      let sDual0 := (({ brk := 0x50000#64, oracle := testOracle 0x90000#64, physMemAvail := 0x10000 } : State).writeReg64 .x0 0x10#64 |>.writeReg64 .x1 0x22#64)
      let sf2 := runProgramRaw fixtureProg
        (fixtureProg.fnAddr "examples::syscalls::app::mmap_alloc_and_log_dual") sDual0
      let sExit0 := (({ brk := 0x50000#64, oracle := testOracle 0x90000#64, physMemAvail := 0x10000 } : State).writeReg64 .x0 0x41#64)
      let sf3 := runProgramRaw fixtureProg
        (fixtureProg.fnAddr "examples::syscalls::app::alloc_write_and_exit") sExit0
      let sExitGrp0 := (({ brk := 0x50000#64, oracle := testOracle 0x90000#64, physMemAvail := 0x10000 } : State).writeReg64 .x0 0x45#64 |>.writeReg64 .x1 99#64)
      let sf4 := runProgramRaw fixtureProg
        (fixtureProg.fnAddr "examples::syscalls::app::mmap_stderr_and_exit_group") sExitGrp0
      sf1.readReg64 .x0 == 4#64 &&
      sf1.brk == 0x50004#64 &&
      sf1.stdoutBytes == [0x4f#8, 0x4b#8, 0x3a#8, 0x37#8] &&
      sf1.stderrBytes == [] &&
      sf2.readReg64 .x0 == 4#64 &&
      sf2.oracleIdx == 1 &&
      sf2.mem.readBytes 0x90000#64 4 == [0x10#8, 0x22#8, 0x32#8, 0x32#8] &&
      sf2.stdoutBytes == [0x10#8, 0x22#8] &&
      sf2.stderrBytes == [0x32#8, 0x32#8] &&
      sf3.status == .Exited 0#64 &&
      sf3.brk == 0x50002#64 &&
      sf3.stdoutBytes == [0x41#8, 0x42#8] &&
      sf4.status == .Exited 99#64 &&
      sf4.oracleIdx == 1 &&
      sf4.mem.readBytes 0x90000#64 2 == [0x21#8, 0x45#8] &&
      sf4.stderrBytes == [0x21#8, 0x45#8] },
  { name := "TrustedSuite: buildTrustedSuite contains VIXL, Unicorn, RandomFuzz, ScalarFP, and RustExport vectors"
    check :=
      let suite := Testing.TrustedSuite.buildTrustedSuite
      let preEncoded := suite.filter (fun tc => !tc.words.isEmpty)
      suite.size == 226 && preEncoded.size == 15 &&
      preEncoded.all Testing.TrustedSuite.checkPreEncodedCase },

  -- Exception transitions for unmodeled syscalls (`SVC`), system registers, and SIMD opcodes
  { name := "execWords: SVC #0 with unmodeled syscalls (socket = 198, clone = 220, execve = 221) and flags traps to Exception"
    check :=
      let syscallNums : List (BitVec 64) := [198#64, 220#64, 221#64]
      let okUnmodSys := syscallNums.all fun sysno =>
        let s0 := ({} : State).writeReg64 .x8 sysno |>.writeReg64 .x0 123#64
        -- svc #0 (0xd4000001); add x0, x0, #42 (0x9100a800); ret (0xd65f03c0)
        let sf := runWords [0xd4000001#32, 0x9100a800#32, 0xd65f03c0#32] s0
        sf.status == .Exception "unmodeled syscall (svc)" &&
        sf.pc == 0x1000#64 &&
        sf.readReg64 .x0 == 123#64
      -- Unmodeled openat flags (O_SYNC = 0x101000), unmodeled newfstatat syscall (79),
      -- and unmodeled clock_gettime clock id (99) fail closed with .Exception:
      let sOpenFlag := runWords [0xd4000001#32]
        (({} : State).writeReg64 .x8 56#64 |>.writeReg64 .x0 (-100#64) |>.writeReg64 .x2 0x101000#64)
      let sStatFlag := runWords [0xd4000001#32]
        (({} : State).writeReg64 .x8 79#64 |>.writeReg64 .x0 (-100#64) |>.writeReg64 .x3 0x2000#64)
      let sClockFlag := runWords [0xd4000001#32]
        (({} : State).writeReg64 .x8 113#64 |>.writeReg64 .x0 99#64)
      okUnmodSys &&
      sOpenFlag.status == .Exception "unmodeled openat flags" &&
      sStatFlag.status == .Exception "unmodeled syscall (svc)" &&
      sClockFlag.status == .Exception "unmodeled clock_gettime clockid" },
  { name := "execWords: SVC #0 file-system syscalls (openat, read, pread64, write, lseek, fstat, close, ioctl, clock_gettime)"
    check :=
      -- Map path buffer [0x2000..0x2020), I/O scratch [0x2100..0x2200), stat/clock scratch [0x2200..0x2300)
      let pathA : List (BitVec 8) := [0x61#8, 0x00#8] -- "a\0"
      let pathB : List (BitVec 8) := [0x62#8, 0x00#8] -- "b\0"
      let fileA : List (BitVec 8) := [0x41#8, 0x42#8, 0x43#8, 0x44#8, 0x45#8, 0x46#8, 0x47#8] -- "ABCDEFG" (7B)
      let mem0 := Memory.empty.mapZero 0x2000#64 0x300
        |>.writeBytes 0x2000#64 pathA
        |>.writeBytes 0x2010#64 pathB
        |>.writeBytes 0x2180#64 [0x78#8, 0x79#8, 0x7a#8, 0x21#8]
      let fs0 := (({} : FsState).setFile "a" (some (.file fileA)))
        |>.setFile "d" (some .dir)
        |>.setFd 9#64 (some { kind := .custom 1, path := "", accMode := .rdwr })
      let s0 : State := { mem := mem0, fs := fs0 }
      let callSvc (s : State) (sysno a0 a1 a2 a3 : BitVec 64) : State :=
        runWordsRaw [0xd4000001#32, 0xd65f03c0#32]
          (s |>.writeReg64 .x8 sysno |>.writeReg64 .x0 a0 |>.writeReg64 .x1 a1
             |>.writeReg64 .x2 a2 |>.writeReg64 .x3 a3)
      -- 1. clock_gettime(1, 0x2280) -> 0; openat(AT_FDCWD, "b", O_RDONLY, 0) -> -ENOENT (-2)
      let sClk := callSvc s0 113#64 1#64 0x2280#64 0#64 0#64
      let sNoent := callSvc sClk 56#64 (-100#64) 0x2010#64 0#64 0#64
      -- 2. openat(AT_FDCWD, "a", O_RDONLY, 0) -> fd 3; ioctl(3, TCGETS, ...) -> -ENOTTY (-25);
      --    fstat(3, 0x2200) -> st_mode=0x81a4, st_size=7
      let sOpenA := callSvc sNoent 56#64 (-100#64) 0x2000#64 0#64 0#64
      let sIoctl := callSvc sOpenA 29#64 3#64 0x5401#64 0x2100#64 0#64
      let sStatA := callSvc sIoctl 80#64 3#64 0x2200#64 0#64 0#64
      -- 4. pread64(3, 0x2100, 4, 2) -> 4 ("CDEF") without advancing offset (still 0)
      let sPread := callSvc sStatA 67#64 3#64 0x2100#64 4#64 2#64
      -- 5. read(3, 0x2110, 5) -> 5 ("ABCDE"), read(3, 0x2120, 5) -> 2 ("FG"), read(3, 0x2130, 5) -> 0 (EOF)
      let sRead1 := callSvc sPread 63#64 3#64 0x2110#64 5#64 0#64
      let sRead2 := callSvc sRead1 63#64 3#64 0x2120#64 5#64 0#64
      let sRead3 := callSvc sRead2 63#64 3#64 0x2130#64 5#64 0#64
      -- 6. lseek(3, -2, SEEK_END=2) -> 5; close(3) -> 0; read(3, ...) -> -EBADF (-9)
      let sSeek := callSvc sRead3 62#64 3#64 (-2#64) 2#64 0#64
      let sClose := callSvc sSeek 57#64 3#64 0#64 0#64 0#64
      let sBadf := callSvc sClose 63#64 3#64 0x2100#64 1#64 0#64
      -- 7. openat(AT_FDCWD, "b", O_WRONLY|O_CREAT|O_TRUNC=0x241, 0644) -> 3; write(3, 0x2180, 4) -> 4;
      --    openat(AT_FDCWD, "b", O_WRONLY|O_CREAT|O_EXCL=0xc1, 0644) -> -EEXIST (-17); fstat(3) -> size 4
      let sCreateB := callSvc sBadf 56#64 (-100#64) 0x2010#64 0x241#64 0x1a4#64
      let sWriteB := callSvc sCreateB 64#64 3#64 0x2180#64 4#64 0#64
      let sExclB := callSvc sWriteB 56#64 (-100#64) 0x2010#64 0xc1#64 0x1a4#64
      let sNstatB := callSvc sExclB 80#64 3#64 0x2200#64 0#64 0#64
      let sCustomFd := callSvc sNstatB 63#64 9#64 0x2100#64 1#64 0#64
      sIoctl.readReg64 .x0 == (-25#64) &&
      sClk.readReg64 .x0 == 0#64 &&
      sClk.oracleIdx == 1 &&
      sClk.mem.read64 0x2280#64 == 0#64 &&
      sClk.mem.read64 0x2288#64 == 0#64 &&
      sNoent.readReg64 .x0 == (-2#64) &&
      sOpenA.readReg64 .x0 == 3#64 &&
      sStatA.readReg64 .x0 == 0#64 &&
      sStatA.mem.read32 0x2210#64 == 0x81a4#32 &&
      sStatA.mem.read64 0x2230#64 == 7#64 &&
      sPread.readReg64 .x0 == 4#64 &&
      sPread.mem.readBytes 0x2100#64 4 == [0x43#8, 0x44#8, 0x45#8, 0x46#8] &&
      sRead1.readReg64 .x0 == 5#64 &&
      sRead1.mem.readBytes 0x2110#64 5 == [0x41#8, 0x42#8, 0x43#8, 0x44#8, 0x45#8] &&
      sRead2.readReg64 .x0 == 2#64 &&
      sRead2.mem.readBytes 0x2120#64 2 == [0x46#8, 0x47#8] &&
      sRead3.readReg64 .x0 == 0#64 &&
      sSeek.readReg64 .x0 == 5#64 &&
      sClose.readReg64 .x0 == 0#64 &&
      sBadf.readReg64 .x0 == (-9#64) &&
      sCreateB.readReg64 .x0 == 3#64 &&
      sWriteB.readReg64 .x0 == 4#64 &&
      sExclB.readReg64 .x0 == (-17#64) &&
      sNstatB.readReg64 .x0 == 0#64 &&
      sNstatB.mem.read64 0x2230#64 == 4#64 &&
      sCustomFd.status == .Exception "unmodeled non-file fd" },
  { name := "execWords: SVC #0 modeled syscalls (write, brk/sbrk, mmap, getrandom, exit, exit_group)"
    check :=
      -- 1. write(1, 0x2000, 2) -> stdout [0x4f, 0x4b]; write(2, 0x2002, 1) -> stderr [0x21]
      let mem0 := ((Memory.empty.mapZero 0x2000#64 3).writeBytes 0x2000#64 [0x4f#8, 0x4b#8, 0x21#8]).mapZero
        0x3000#64 3
      let sWrite0 : State :=
        ({ mem := mem0, brk := 0x40000#64, oracle := testOracle 0x80000#64, physMemAvail := 0x10000 } : State)
        |>.writeReg64 .x8 64#64
        |>.writeReg64 .x0 1#64
        |>.writeReg64 .x1 0x2000#64
        |>.writeReg64 .x2 2#64
      let sWrite1 := runWordsRaw [0xd4000001#32, 0xd65f03c0#32] sWrite0
      let sWrite2 := runWordsRaw [0xd4000001#32, 0xd65f03c0#32]
        (sWrite1 |>.writeReg64 .x8 64#64 |>.writeReg64 .x0 2#64 |>.writeReg64 .x1 0x2002#64 |>.writeReg64 .x2 1#64)
      -- 2. brk(0) -> 0x40000; brk(0x40020) -> 0x40020 (consumes oracle 0, maps [0x40000, 0x41000))
      let sBrk0 := sWrite2 |>.writeReg64 .x8 214#64 |>.writeReg64 .x0 0#64
      let sBrk1 := runWordsRaw [0xd4000001#32, 0xd65f03c0#32] sBrk0
      let sBrk2 := runWordsRaw [0xd4000001#32, 0xd65f03c0#32]
        (sBrk1 |>.writeReg64 .x8 214#64 |>.writeReg64 .x0 (sBrk1.readReg64 .x0 + 0x20#64))
      -- 3. mmap(0, 0x1000, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0) ->
      --    oracle query 0 (0x80000), oracleIdx = 1
      let mmapArgs (s : State) (len : BitVec 64) : State :=
        s |>.writeReg64 .x8 222#64 |>.writeReg64 .x0 0#64 |>.writeReg64 .x1 len
          |>.writeReg64 .x2 3#64 |>.writeReg64 .x3 0x22#64 |>.writeReg64 .x4 (-1#64)
          |>.writeReg64 .x5 0#64
      let sMmap := runWordsRaw [0xd4000001#32, 0xd65f03c0#32]
        (mmapArgs { sBrk2 with oracleIdx := 0 } 0x1000#64)
      -- 3b. mmap of 1 byte rounds up to a zero-filled page at oracle query 1 (0x90000)
      let sMmap1 := runWordsRaw [0xd4000001#32, 0xd65f03c0#32] (mmapArgs sMmap 1#64)
      -- 3c. mmap when oracle returns an already-mapped page -> sanitized fallback at MMAP_MIN_ADDR (0x10000);
      --     VA-space exhaustion (2^48) -> .OutOfMemory; length 0 -> -EINVAL; other flags trap
      let sMmapSanitized := runWordsRaw [0xd4000001#32, 0xd65f03c0#32]
        (mmapArgs { sMmap1 with oracleIdx := 0 } 0x1000#64)
      let sNoMem := runWordsRaw [0xd4000001#32, 0xd65f03c0#32]
        (mmapArgs { sMmap1 with oracleIdx := 0 } 0x0001000000000000#64)
      let sInval := runWordsRaw [0xd4000001#32, 0xd65f03c0#32] (mmapArgs sMmap1 0#64)
      let sShared := runWordsRaw [0xd4000001#32, 0xd65f03c0#32]
        (mmapArgs sMmap1 0x1000#64 |>.writeReg64 .x3 0x21#64)
      -- 3d. getrandom(0x3000, 3, 0) fills bytes from oracle query 2 and returns 3;
      --     valid flags (GRND_NONBLOCK=1, GRND_RANDOM=2, GRND_INSECURE=4, GRND_NONBLOCK|GRND_RANDOM=3,
      --     GRND_NONBLOCK|GRND_INSECURE=5, and ignored upper 32 bits of X2) succeed, while unknown flags,
      --     GRND_RANDOM|GRND_INSECURE (6 or 7), or count > MAX_RW_COUNT (0x7ffff000) return -EINVAL (-22)
      --     without writing the buffer or advancing oracleIdx.
      let callGetrandom (s : State) (buf count flags64 : BitVec 64) : State :=
        runWordsRaw [0xd4000001#32, 0xd65f03c0#32]
          (s |>.writeReg64 .x8 278#64 |>.writeReg64 .x0 buf |>.writeReg64 .x1 count
             |>.writeReg64 .x2 flags64)
      let sRand := callGetrandom sMmap1 0x3000#64 3#64 0#64
      let sRandUpperW2 := callGetrandom sRand 0x3000#64 1#64 0xdeadbeef_00000005#64
      let sRandBadFlag := callGetrandom sRandUpperW2 0x3000#64 1#64 0x8#64
      let sRandMutExcl6 := callGetrandom sRandUpperW2 0x3000#64 1#64 0x6#64
      let sRandMutExcl7 := callGetrandom sRandUpperW2 0x3000#64 1#64 0x7#64
      let sRandTooBig := callGetrandom sRandUpperW2 0x3000#64 0x7ffff001#64 0#64
      -- 4. exit(0) and exit_group(7)
      let sExit := runWordsRaw [0xd4000001#32, 0xd65f03c0#32]
        (sMmap |>.writeReg64 .x8 93#64 |>.writeReg64 .x0 0#64)
      let sExitGroup := runWordsRaw [0xd4000001#32, 0xd65f03c0#32]
        (sMmap |>.writeReg64 .x8 94#64 |>.writeReg64 .x0 7#64)
      sWrite1.readReg64 .x0 == 2#64 &&
      sWrite2.trace == [.writeByte .stdout 0x4f#8, .writeByte .stdout 0x4b#8, .writeByte .stderr 0x21#8] &&
      sWrite2.stdoutBytes == [0x4f#8, 0x4b#8] &&
      sWrite2.stderrBytes == [0x21#8] &&
      sBrk1.readReg64 .x0 == 0x40000#64 &&
      sBrk2.readReg64 .x0 == 0x40020#64 &&
      sBrk2.brk == 0x40020#64 &&
      sMmap.readReg64 .x0 == 0x80000#64 &&
      sMmap.oracleIdx == 1 &&
      sMmap1.readReg64 .x0 == 0x90000#64 &&
      sMmap1.oracleIdx == 2 &&
      sMmap1.mem.read8 0x90000#64 == 0#8 &&
      sMmap1.mem.read8 0x90fff#64 == 0#8 &&
      sMmapSanitized.status == .Running &&
      sMmapSanitized.readReg64 .x0 == 0x10000#64 &&
      sMmapSanitized.oracleIdx == 1 &&
      sNoMem.status == .OutOfMemory &&
      sNoMem.oracleIdx == 0 &&
      sInval.readReg64 .x0 == -22#64 &&
      (match sShared.status with | .Exception _ => true | _ => false) &&
      sRand.readReg64 .x0 == 3#64 &&
      sRand.mem.readBytes 0x3000#64 3 == [0x20#8, 0x21#8, 0x22#8] &&
      sRand.oracleIdx == 3 &&
      sRandUpperW2.readReg64 .x0 == 1#64 &&
      sRandUpperW2.mem.read8 0x3000#64 == 0x30#8 &&
      sRandUpperW2.oracleIdx == 4 &&
      sRandBadFlag.readReg64 .x0 == -22#64 &&
      sRandBadFlag.mem.read8 0x3000#64 == 0x30#8 &&
      sRandBadFlag.oracleIdx == 4 &&
      sRandMutExcl6.readReg64 .x0 == -22#64 &&
      sRandMutExcl6.oracleIdx == 4 &&
      sRandMutExcl7.readReg64 .x0 == -22#64 &&
      sRandMutExcl7.oracleIdx == 4 &&
      sRandTooBig.readReg64 .x0 == -22#64 &&
      sRandTooBig.mem.read8 0x3000#64 == 0x30#8 &&
      sRandTooBig.oracleIdx == 4 &&
      sExit.status == .Exited 0#64 &&
      sExitGroup.status == .Exited 7#64 },
  { name := "execWords: SVC #0 nondeterministic clock_gettime (oracle query, non-monotonic successive calls, EFAULT and unmodeled clock ID preserve oracleIdx)"
    check :=
      let mem0 := Memory.empty.mapZero 0x3000#64 32
      let oracle0 : Oracle := {
        clockGettime := fun n =>
          if n == 0 then { sec := 0x0102030405060708#64, nsec := ⟨999999999, by decide⟩ }
          else { sec := 0xfffffffffffffffe#64, nsec := ⟨123456789, by decide⟩ }
      }
      let s0 : State := { mem := mem0, oracle := oracle0 }
      let callClk (s : State) (clk tp : BitVec 64) : State :=
        runWordsRaw [0xd4000001#32, 0xd65f03c0#32]
          (s |>.writeReg64 .x8 113#64 |>.writeReg64 .x0 clk |>.writeReg64 .x1 tp)
      let s1 := callClk s0 0#64 0x3000#64
      let sEfault := callClk s1 1#64 0x4000#64
      let sBadClk := callClk s1 8#64 0x3000#64
      let s2 := callClk sEfault 7#64 0x3010#64
      s1.readReg64 .x0 == 0#64 &&
      s1.oracleIdx == 1 &&
      s1.mem.read64 0x3000#64 == 0x0102030405060708#64 &&
      s1.mem.read64 0x3008#64 == 999999999#64 &&
      sEfault.readReg64 .x0 == (-14#64) &&
      sEfault.oracleIdx == 1 &&
      sBadClk.status == .Exception "unmodeled clock_gettime clockid" &&
      sBadClk.oracleIdx == 1 &&
      s2.readReg64 .x0 == 0#64 &&
      s2.oracleIdx == 2 &&
      s2.mem.read64 0x3010#64 == 0xfffffffffffffffe#64 &&
      s2.mem.read64 0x3018#64 == 123456789#64 },
  { name := "execWords: SVC #0 fail-closed brk (brk(0) query, page-granular grow/shrink, overlap failure, below-brkStart failure, TASK_SIZE_64 bound, physMemAvail OOM)"
    check :=
      let callBrk (s : State) (addr : BitVec 64) : State :=
        runWordsRaw [0xd4000001#32, 0xd65f03c0#32]
          (s |>.writeReg64 .x8 214#64 |>.writeReg64 .x0 addr)
      -- Initial state: brkStart = brk = 0x40000, obstacle page mapped at [0x142000, 0x143000) with 0x77#8
      -- (so 1 MiB guard gap [0x42000, 0x142000) allows growing to 0x41008 -> newPage=0x42000,
      --  while growing to 0x42001 -> newPage=0x43000 collides with the guard gap at 0x142000)
      let mem0 := (Memory.empty.mapZero 0x142000#64 0x1000).write8 0x142000#64 0x77#8
      let s0 : State := { mem := mem0, brkStart := 0x40000#64, brk := 0x40000#64, physMemAvail := 0x2000 }
      -- 1. brk(0) queries current break without consuming oracle or changing memory
      let sQuery := callBrk s0 0#64
      -- 2. Grow ok: brk(0x40004) maps page [0x40000, 0x41000) zero-filled RW (page granularity)
      let sGrow1 := callBrk sQuery 0x40004#64
      -- Write 0xab#8 at 0x40000, then sub-page grow brk(0x40100) within the same page preserves 0x40000
      let sSeed := sGrow1.setMem (sGrow1.mem.write8 0x40000#64 0xab#8)
      let sGrowSub := callBrk sSeed 0x40100#64
      -- Grow by a second page: brk(0x41008) maps [0x41000, 0x42000)
      let sGrow2 := callBrk sGrowSub 0x41008#64
      -- 3. Grow into 1 MiB guard gap before [0x142000, 0x143000): brk(0x42001) fails, returns old brk (0x41008),
      --    leaves memory at 0x142000 (0x77#8) and 0x40000 (0xab#8) unchanged
      let sOverlap := callBrk sGrow2 0x42001#64
      -- 4. Shrink below brkStart (0x40000): brk(0x3ffff) fails, returns old brk (0x41008), memory unchanged
      let sBelow := callBrk sOverlap 0x3ffff#64
      -- 5. Above TASK_SIZE_64 (2^48): brk(0x0001_0000_0000_0001) fails, returns old brk (0x41008)
      let sAbove := callBrk sBelow 0x0001000000000001#64
      -- 6. Shrink within [brkStart, brk): brk(0x40010) shrinks newPage to 0x41000, unmapping [0x41000, 0x42000)
      --    while keeping [0x40000, 0x41000) mapped with 0xab#8 at 0x40000; then brk(0x40000) unmaps [0x40000, 0x41000)
      let sShrink1 := callBrk sAbove 0x40010#64
      let sShrink0 := callBrk sShrink1 0x40000#64
      -- 7. Physical memory exhaustion: when physMemAvail < 0x1000, brk(0x40004) transitions to .OutOfMemory
      let sOomFail := callBrk
        { sShrink0 with physMemAvail := 0xffe, oracleIdx := 5 } 0x40004#64
      sQuery.readReg64 .x0 == 0x40000#64 &&
      sQuery.brk == 0x40000#64 &&
      sQuery.oracleIdx == 0 &&
      sQuery.mem.perm 0x40000#64 == none &&
      sGrow1.readReg64 .x0 == 0x40004#64 &&
      sGrow1.brk == 0x40004#64 &&
      sGrow1.oracleIdx == 0 &&
      sGrow1.physMemAvail == 0x1000 &&
      sGrow1.mem.perm 0x40000#64 == some .rw &&
      sGrow1.mem.read8 0x40000#64 == 0#8 &&
      sGrow1.mem.perm 0x40fff#64 == some .rw &&
      sGrow1.mem.read8 0x40fff#64 == 0#8 &&
      sGrow1.mem.perm 0x41000#64 == none &&
      sGrowSub.readReg64 .x0 == 0x40100#64 &&
      sGrowSub.brk == 0x40100#64 &&
      sGrowSub.oracleIdx == 0 &&
      sGrowSub.physMemAvail == 0x1000 &&
      sGrowSub.mem.read8 0x40000#64 == 0xab#8 &&
      sGrow2.readReg64 .x0 == 0x41008#64 &&
      sGrow2.brk == 0x41008#64 &&
      sGrow2.physMemAvail == 0 &&
      sGrow2.mem.perm 0x41000#64 == some .rw &&
      sGrow2.mem.perm 0x41fff#64 == some .rw &&
      sOverlap.readReg64 .x0 == 0x41008#64 &&
      sOverlap.brk == 0x41008#64 &&
      sOverlap.oracleIdx == 0 &&
      sOverlap.physMemAvail == 0 &&
      sOverlap.mem.read8 0x142000#64 == 0x77#8 &&
      sOverlap.mem.read8 0x40000#64 == 0xab#8 &&
      sBelow.readReg64 .x0 == 0x41008#64 &&
      sBelow.brk == 0x41008#64 &&
      sBelow.mem.perm 0x40000#64 == some .rw &&
      sAbove.readReg64 .x0 == 0x41008#64 &&
      sAbove.brk == 0x41008#64 &&
      sShrink1.readReg64 .x0 == 0x40010#64 &&
      sShrink1.brk == 0x40010#64 &&
      sShrink1.physMemAvail == 0x1000 &&
      sShrink1.mem.perm 0x40000#64 == some .rw &&
      sShrink1.mem.read8 0x40000#64 == 0xab#8 &&
      sShrink1.mem.perm 0x41000#64 == none &&
      sShrink0.readReg64 .x0 == 0x40000#64 &&
      sShrink0.brk == 0x40000#64 &&
      sShrink0.physMemAvail == 0x2000 &&
      sShrink0.mem.perm 0x40000#64 == none &&
      sOomFail.status == .OutOfMemory &&
      sOomFail.brk == 0x40000#64 &&
      sOomFail.oracleIdx == 5 &&
      sOomFail.mem.perm 0x40000#64 == none },
  { name := "execWords: SVC #0 munmap, mprotect (PROT_NONE <-> PROT_RW), and madvise (MADV_DONTNEED zero-fill, hints, fail-closed errors)"
    check :=
      let callSvc (s : State) (nr x0 x1 x2 : BitVec 64) : State :=
        runWordsRaw [0xd4000001#32, 0xd65f03c0#32]
          (s |>.writeReg64 .x8 nr |>.writeReg64 .x0 x0 |>.writeReg64 .x1 x1 |>.writeReg64 .x2 x2)
      -- Initial memory: two RW pages [0x50000, 0x52000) seeded with non-zero bytes, plus one frozen RO page [0x60000, 0x61000)
      let mem0 := (((Memory.empty.mapZero 0x50000#64 0x2000).write8 0x50000#64 0x41#8).write8
        0x51000#64 0x42#8).mapFresh 0x60000#64 0x1000 .ro
      -- Raw write8 on unmapped address 0x70000 leaves perm = none (not some .protNone)
      let memRawWrite := Memory.empty.write8 0x70000#64 0x99#8
      let s0 : State := { mem := mem0, physMemAvail := 0x1000 }
      -- 1. mprotect(0x50000, 0x1000, PROT_NONE=0): marks first page some .protNone, preserves byte 0x41#8, keeps mapped=true
      let sProtNone := callSvc s0 226#64 0x50000#64 0x1000#64 0#64
      -- Load (ldr w0, [x1]) from a PROT_NONE page faults with .Exception
      let sFaultLoad := runWordsRaw [0xb9400020#32, 0xd65f03c0#32]
        (sProtNone.writeReg64 .x1 0x50000#64)
      -- 2. mprotect(0x50000, 0x2000, PROT_READ|PROT_WRITE=3) across mixed [some .protNone, some .rw] restores some .rw on both pages
      let sProtRw := callSvc sProtNone 226#64 0x50000#64 0x2000#64 3#64
      -- mprotect error cases: unaligned -> -EINVAL, len=0 -> 0, unmapped -> -ENOMEM, partial -> Exception, past 2^48 -> Exception, frozen -> Exception, PROT_READ(1) -> Exception
      let sProtEinval := callSvc sProtRw 226#64 0x50001#64 0x1000#64 3#64
      let sProtZero := callSvc sProtRw 226#64 0x50000#64 0#64 3#64
      let sProtEnomem := callSvc sProtRw 226#64 0x52000#64 0x1000#64 3#64
      let sProtPartial := callSvc sProtRw 226#64 0x51000#64 0x2000#64 0#64
      let sProtAbove := callSvc sProtRw 226#64 0x0001000000000000#64 0x1000#64 3#64
      let sProtFrozen := callSvc sProtRw 226#64 0x60000#64 0x1000#64 3#64
      let sProtBad := callSvc sProtRw 226#64 0x50000#64 0x1000#64 1#64
      -- 3. madvise: MADV_DONTDUMP(16) is a no-op returning 0; MADV_DONTNEED(4) zero-fills [0x50000, 0x51000) while keeping 0x51000=0x42#8
      let sAdvNoop := callSvc sProtRw 233#64 0x50000#64 0x1000#64 16#64
      let sAdvDontneed := callSvc sAdvNoop 233#64 0x50000#64 0x1000#64 4#64
      let sAdvEinval := callSvc sAdvDontneed 233#64 0x50001#64 0x1000#64 4#64
      let sAdvEnomem := callSvc sAdvDontneed 233#64 0x52000#64 0x1000#64 4#64
      let sAdvPartial := callSvc sAdvDontneed 233#64 0x51000#64 0x2000#64 4#64
      let sAdvAbove := callSvc sAdvDontneed 233#64 0x0001000000000000#64 0x1000#64 4#64
      let sAdvFrozen := callSvc sAdvDontneed 233#64 0x60000#64 0x1000#64 4#64
      let sAdvFree := callSvc sAdvDontneed 233#64 0x50000#64 0x1000#64 8#64
      let sAdvBad := callSvc sAdvDontneed 233#64 0x50000#64 0x1000#64 9#64
      -- 4. munmap: make [0x51000, 0x52000) PROT_NONE first, then unmap [0x50000, 0x53000) mixing
      --    an RW page [0x50000, 0x51000), a PROT_NONE page [0x51000, 0x52000), and an already-unmapped
      --    page [0x52000, 0x53000); verify all three pages become unmapped (none) and canMap is true
      let sMixedBeforeUnmap := callSvc sAdvDontneed 226#64 0x51000#64 0x1000#64 0#64
      let sUnmapOk := callSvc sMixedBeforeUnmap 215#64 0x50000#64 0x3000#64 0#64
      let sUnmapEinvalAlign := callSvc sUnmapOk 215#64 0x50001#64 0x1000#64 0#64
      let sUnmapEinvalZero := callSvc sUnmapOk 215#64 0x50000#64 0#64 0#64
      let sUnmapFrozen := callSvc sUnmapOk 215#64 0x60000#64 0x1000#64 0#64
      memRawWrite.perm 0x70000#64 == none &&
      memRawWrite.read8 0x70000#64 == 0x99#8 &&
      sProtNone.readReg64 .x0 == 0#64 &&
      sProtNone.mem.perm 0x50000#64 == some .protNone &&
      !sProtNone.mem.canRead 0x50000#64 1 &&
      !sProtNone.mem.canWrite 0x50000#64 1 &&
      !sProtNone.mem.canMap 0x50000#64 0x1000 &&
      (match sFaultLoad.status with | .Exception _ => true | _ => false) &&
      sProtRw.readReg64 .x0 == 0#64 &&
      sProtRw.mem.perm 0x50000#64 == some .rw &&
      sProtRw.mem.read8 0x50000#64 == 0x41#8 &&
      sProtEinval.readReg64 .x0 == -22#64 &&
      sProtZero.readReg64 .x0 == 0#64 &&
      sProtEnomem.readReg64 .x0 == -12#64 &&
      sProtPartial.status == .Exception "mprotect on partially mapped range" &&
      sProtAbove.status == .Exception "mprotect range exceeds user VA space" &&
      (match sProtFrozen.status with | .Exception _ => true | _ => false) &&
      (match sProtBad.status with | .Exception _ => true | _ => false) &&
      sAdvNoop.readReg64 .x0 == 0#64 &&
      sAdvNoop.mem.read8 0x50000#64 == 0x41#8 &&
      sAdvDontneed.readReg64 .x0 == 0#64 &&
      sAdvDontneed.mem.read8 0x50000#64 == 0#8 &&
      sAdvDontneed.mem.perm 0x50000#64 == some .rw &&
      sAdvDontneed.mem.read8 0x51000#64 == 0x42#8 &&
      sAdvEinval.readReg64 .x0 == -22#64 &&
      sAdvEnomem.readReg64 .x0 == -12#64 &&
      sAdvPartial.status == .Exception "madvise on partially mapped range" &&
      sAdvAbove.status == .Exception "madvise range exceeds user VA space" &&
      (match sAdvFrozen.status with | .Exception _ => true | _ => false) &&
      sAdvFree.readReg64 .x0 == 0#64 &&
      sAdvFree.mem.isLazyFree 0x50000#64 &&
      !sAdvFree.mem.canRead 0x50000#64 1 &&
      (match sAdvBad.status with | .Exception _ => true | _ => false) &&
      sMixedBeforeUnmap.mem.perm 0x50000#64 == some .rw &&
      sMixedBeforeUnmap.mem.perm 0x51000#64 == some .protNone &&
      sMixedBeforeUnmap.mem.perm 0x52000#64 == none &&
      sUnmapOk.readReg64 .x0 == 0#64 &&
      sUnmapOk.mem.perm 0x50000#64 == none &&
      sUnmapOk.mem.perm 0x51000#64 == none &&
      sUnmapOk.mem.perm 0x51fff#64 == none &&
      sUnmapOk.mem.perm 0x52000#64 == none &&
      sUnmapOk.mem.canMap 0x50000#64 0x3000 &&
      sUnmapEinvalAlign.readReg64 .x0 == -22#64 &&
      sUnmapEinvalZero.readReg64 .x0 == -22#64 &&
      (match sUnmapFrozen.status with | .Exception _ => true | _ => false) }
]

set_option compiler.extract_closed false in
def allTestsPart2 (_ : Unit := ()) : List TestCase := [
  { name := "execInst / execWords: unmodeled MRS/MSR and nonzero MSR FPCR transition to ExecStatus.Exception"
    check :=
      let s0 := ({} : State).writeReg64 .x0 0x42#64
      -- mrs x0, cntvct_el0 (0xd53be040, sysreg = 0x5f02)
      -- msr cntvct_el0, x0 (0xd51be040, sysreg = 0x5f02)
      -- msr fpcr, x0 (0xd51b4400, sysreg = 0x5a20; x0 != 0 fails closed with unsupported FPCR value)
      -- msr dczid_el0, x0 (0xd51b00e0, sysreg = 0x5807; DCZID_EL0 is read-only)
      let sfRead := runWords [0xd53be040#32, 0x9100a800#32, 0xd65f03c0#32] s0
      let sfUnmodWrite := runWords [0xd51be040#32, 0x9100a800#32, 0xd65f03c0#32] s0
      let sfWrite := runWords [0xd51b4400#32, 0x9100a800#32, 0xd65f03c0#32] s0
      let sfDczidWrite := runWords [0xd51b00e0#32, 0x9100a800#32, 0xd65f03c0#32] s0
      sfRead.status == .Exception "unmodeled system register" &&
      sfRead.pc == 0x1000#64 &&
      sfRead.readReg64 .x0 == 0x42#64 &&
      sfUnmodWrite.status == .Exception "unmodeled system register" &&
      sfUnmodWrite.pc == 0x1000#64 &&
      sfWrite.status == .Exception "unsupported FPCR value" &&
      sfWrite.pc == 0x1000#64 &&
      sfWrite.readReg64 .x0 == 0x42#64 &&
      sfDczidWrite.status == .Exception "unmodeled system register" &&
      sfDczidWrite.pc == 0x1000#64 },
  { name := "execWords: MSR/MRS nzcv round-trips N/Z/C/V (RES0 bits dropped) and MRS dczid_el0 reads BS = 4"
    check :=
      -- msr nzcv, x0 (0xd51b4200); mrs x1, nzcv (0xd53b4201); mrs x2, dczid_el0 (0xd53b00e2); ret
      let s0 := ({} : State).writeReg64 .x0 0x6000000f#64
      let sf := runWords [0xd51b4200#32, 0xd53b4201#32, 0xd53b00e2#32, 0xd65f03c0#32] s0
      sf.pc == 0xdead0000#64 &&
      sf.readReg64 .x1 == 0x60000000#64 &&
      sf.readReg64 .x2 == 4#64 &&
      sf.pstate == { n := false, z := true, c := true, v := false } },
  { name := "execInst: unimplemented SIMD opcodes across all SIMD instruction classes transition to ExecStatus.Exception"
    check :=
      let s0 : State := {}
      let unimpInsts : List Instr := [
        .fmovGprVec true 0b11#2 0b00#2 0b110#3 0#5 0#5,
        .fmovGprVec true 0b11#2 0b00#2 0b111#3 0#5 0#5,
        .fmovGprVec true 0b11#2 0b00#2 0b000#3 0#5 0#5,
        .simdImmShift true true 0#4 0#3 0b00001#5 0#5 0#5,
        .simdImmShift true false 1#4 0#3 0b11111#5 0#5 0#5,
        .simdInsDup false false 8#5 0b0101#4 0#5 0#5,
        .simdThreeSame false false 0b11#2 0#5 0b10000#5 0#5 0#5,
        .simdThreeSame true false 0b00#2 0#5 0b11111#5 0#5 0#5,
        .simdTwoRegMisc true false 0b00#2 0b11111#5 0#5 0#5,
        .simdAcrossLanes true false 0b00#2 0b00000#5 0#5 0#5,
        -- ADDV with size:Q = 100 and UADDLV with size = 11 (reserved)
        .simdAcrossLanes false false 0b10#2 0b11011#5 0#5 0#5,
        .simdAcrossLanes true true 0b11#2 0b00011#5 0#5 0#5,
        .simdPermute true 0b00#2 0#5 0b000#3 0#5 0#5,
        .simdPermute true 0b00#2 0#5 0b100#3 0#5 0#5,
        -- TRN1 with size:Q = 110 (reserved)
        .simdPermute false 0b11#2 0#5 0b010#3 0#5 0#5,
        .fpDataProc1 0b11#2 0b000000#6 0#5 0#5,
        .fpDataProc1 0b01#2 0b111111#6 0#5 0#5,
        .fpDataProc2 0b11#2 0#5 0b0000#4 0#5 0#5,
        .fpDataProc2 0b01#2 0#5 0b1111#4 0#5 0#5,
        .fpCompare 0b11#2 0#5 0#2 0#5 0#5,
        .fpCompare 0b01#2 0#5 1#2 0#5 0#5,
        .fpImm 0b11#2 0x70#8 0#5,
        .fpCondCompare 0b11#2 0#5 0#4 0#5 false 0#4,
        .fpCondSelect 0b11#2 0#5 0#4 0#5 0#5,
        .fpDataProc3 0b11#2 false 0#5 false 0#5 0#5 0#5,
        .fpFixedConv true 0b11#2 0b11#2 0#3 0x30#6 0#5 0#5,
        .fpFixedConv false 0b01#2 0b11#2 0#3 0x10#6 0#5 0#5,
        .simdLdSt1Single true false false 0#5 0b100#3 true 0b01#2 .x0 0#5,
        .simdLdStMulti true false 0b11#2 2 .x0 false 0#5 0#5,
        .simdDupScalar 0b10000#5 0#5 0#5,
        .simdThreeDiff false false 0b11#2 0#5 0b0000#4 0#5 0#5,
        .simdThreeDiff false false 0b01#2 0#5 0b1001#4 0#5 0#5
      ]
      unimpInsts.all fun inst =>
        let sf := execInst inst s0
        match sf.status with
        | .Exception msg => !msg.isEmpty && sf.pc == s0.pc
        | _ => false },

  -- Functional correctness suite (`Arm64.Testing.Regression.FunctionalCorrectness`)
  { name := "FunctionalCorrectness: divmod_u64 (UDIV + MSUB) across normal, boundary, and divide-by-zero pairs"
    check :=
      let pairs : List (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) := [
        (100#64, 7#64, 14#64, 2#64),
        (42#64, 42#64, 1#64, 0#64),
        (15#64, 25#64, 0#64, 15#64),
        (0#64, 99#64, 0#64, 0#64),
        (0xffffffffffffffff#64, 10#64, 1844674407370955161#64, 5#64),
        (0xffffffffffffffff#64, 0xffffffffffffffff#64, 1#64, 0#64),
        (123456789#64, 0#64, 0#64, 123456789#64),
        (0#64, 0#64, 0#64, 0#64)
      ]
      pairs.all fun (a, b, expQ, expR) =>
        let s0 := ({} : State).writeReg64 .x0 a |>.writeReg64 .x1 b
        let sf1 := runProgram Testing.FunctionalCorrectness.divmodU64Prog 0x1000#64 s0
        let sf2 := runProgram Testing.FunctionalCorrectness.functionalCorrectnessLinkedProg Testing.FunctionalCorrectness.divmodU64_addr s0
        sf1.readReg64 .x0 == expQ && sf1.readReg64 .x1 == expR &&
        sf2.readReg64 .x0 == expQ && sf2.readReg64 .x1 == expR },
  { name := "FunctionalCorrectness: bswap_and_clz_u64 (REV + CLZ + RBIT + UBFX + SBFX) edge cases"
    check :=
      let inputs : List (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) := [
        -- x = 0x0102030405060708 -> swapped = 0x0807060504030201: clz = 4, ubfx[23:8] = 0x0302, sbfx[15:8] = 0x02
        (0x0102030405060708#64, 0x0807060504030201#64, 4#64, 0x0302#64, 0x02#64),
        -- x = 0x0080ff0000000000 -> swapped = 0x0000000000ff8000: clz = 40, ubfx[23:8] = 0xff80, sbfx[15:8] = -128 (0xffffffffffffff80)
        (0x0080ff0000000000#64, 0x0000000000ff8000#64, 40#64, 0xff80#64, 0xffffffffffffff80#64),
        -- x = 0 -> swapped = 0: clz = 64, ubfx = 0, sbfx = 0
        (0#64, 0#64, 64#64, 0#64, 0#64),
        -- x = UINT64_MAX -> swapped = UINT64_MAX: clz = 0, ubfx = 0xffff, sbfx = -1
        (0xffffffffffffffff#64, 0xffffffffffffffff#64, 0#64, 0xffff#64, 0xffffffffffffffff#64)
      ]
      inputs.all fun (x, expSwapped, expClz, expUbfx, expSbfx) =>
        let s0 := ({} : State).writeReg64 .x0 x
        let sf := runProgram Testing.FunctionalCorrectness.bswapAndClzU64Prog 0x1000#64 s0
        let sfLinked := runProgram Testing.FunctionalCorrectness.functionalCorrectnessLinkedProg Testing.FunctionalCorrectness.bswapAndClzU64_addr s0
        sf.readReg64 .x0 == expSwapped &&
        sf.readReg64 .x1 == expClz &&
        sf.readReg64 .x2 == reverseBits expSwapped &&
        sf.readReg64 .x3 == expUbfx &&
        sf.readReg64 .x4 == expSbfx &&
        sfLinked.readReg64 .x0 == expSwapped &&
        sfLinked.readReg64 .x1 == expClz &&
        sfLinked.readReg64 .x2 == reverseBits expSwapped &&
        sfLinked.readReg64 .x3 == expUbfx &&
        sfLinked.readReg64 .x4 == expSbfx },
  { name := "FunctionalCorrectness: add128_u64 (ADDS + ADC) 128-bit addition with carry overflow (0xffffffffffffffff + 1)"
    check :=
      let vectors : List (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) := [
        -- No carry from low word
        (0x1111222233334444#64, 0x0000000000000001#64, 0x5555666677778888#64, 0x0000000000000002#64,
         0x66668888aaaaccCC#64, 0x0000000000000003#64),
        -- Carry overflow: 0xffffffffffffffff + 1 = (hi = 1, lo = 0)
        (0xffffffffffffffff#64, 0#64, 1#64, 0#64, 0#64, 1#64),
        -- Carry overflow with non-zero high words: (0x123456789abcdef0 ++ 0xffffffffffffffff) + (1 ++ 0xffffffffffffffff)
        (0xffffffffffffffff#64, 0x123456789abcdef0#64, 0xffffffffffffffff#64, 1#64,
         0xfffffffffffffffe#64, 0x123456789abcdef2#64)
      ]
      vectors.all fun (lo_a, hi_a, lo_b, hi_b, expLo, expHi) =>
        let s0 := ({} : State).writeReg64 .x0 lo_a |>.writeReg64 .x1 hi_a |>.writeReg64 .x2 lo_b |>.writeReg64 .x3 hi_b
        let sf := runProgram Testing.FunctionalCorrectness.add128U64Prog 0x1000#64 s0
        let sfLinked := runProgram Testing.FunctionalCorrectness.functionalCorrectnessLinkedProg Testing.FunctionalCorrectness.add128U64_addr s0
        let sum128 : BitVec 128 := (hi_a ++ lo_a) + (hi_b ++ lo_b)
        sf.readReg64 .x0 == expLo &&
        sf.readReg64 .x1 == expHi &&
        (sf.readReg64 .x1 ++ sf.readReg64 .x0) == sum128 &&
        (sfLinked.readReg64 .x1 ++ sfLinked.readReg64 .x0) == sum128 },
  { name := "FunctionalCorrectness: smaddl_sdiv_i64 (SMADDL + SDIV + CMP + CSINC + CSINV) signed arithmetic"
    check :=
      let cases : List (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) := [
        -- prod = -8 + (-7) * 6 = -50 (< 0): quot = sdiv(-50, 5) = -10, csinc = -9, csinv = ~(-50) = 49
        (0xfffffffffffffff9#64, 6#64, (-8#64), 5#64, (-10#64), (-9#64), 49#64),
        -- prod = 500 + (-100000) * (-200000) = 20000000500 (>= 0): quot = 20000, csinc = 20000, csinv = 20000000500
        (0x00000000fffe7960#64, 0x00000000fffcf2c0#64, 500#64, 1000000#64, 20000#64, 20000#64, 20000000500#64),
        -- divide by zero (div = 0) with negative prod = 2 + (-3)*4 = -10: quot = 0, csinc = 1, csinv = ~(-10) = 9
        (0xfffffffffffffffd#64, 4#64, 2#64, 0#64, 0#64, 1#64, 9#64)
      ]
      cases.all fun (a, b, acc, div, expQuot, expCsinc, expCsinv) =>
        let s0 := ({} : State).writeReg64 .x0 a |>.writeReg64 .x1 b |>.writeReg64 .x2 acc |>.writeReg64 .x3 div
        let sf := runProgram Testing.FunctionalCorrectness.smaddlSdivI64Prog 0x1000#64 s0
        let sfLinked := runProgram Testing.FunctionalCorrectness.functionalCorrectnessLinkedProg Testing.FunctionalCorrectness.smaddlSdivI64_addr s0
        sf.readReg64 .x0 == expQuot && sf.readReg64 .x1 == expCsinc && sf.readReg64 .x2 == expCsinv &&
        sfLinked.readReg64 .x0 == expQuot && sfLinked.readReg64 .x1 == expCsinc && sfLinked.readReg64 .x2 == expCsinv },
  { name := "FunctionalCorrectness: stack_spill_struct_update updates struct fields and preserves caller stack above sp0 and callee-saved x19..x28, fp"
    check :=
      let sp0 : BitVec 64 := 0x90000#64
      let s0 := withMem64
        (({} : State).writeReg64 .x0 dataBase
                    |>.writeReg64 .x1 125#64
                    |>.writeReg64 .x19 0x1919191919191919#64
                    |>.writeReg64 .x20 0x2020202020202020#64
                    |>.writeReg64 .x21 0x2121212121212121#64
                    |>.writeReg64 .x22 0x2222222222222222#64
                    |>.writeReg64 .x23 0x2323232323232323#64
                    |>.writeReg64 .x24 0x2424242424242424#64
                    |>.writeReg64 .x25 0x2525252525252525#64
                    |>.writeReg64 .x26 0x2626262626262626#64
                    |>.writeReg64 .x27 0x2727272727272727#64
                    |>.writeReg64 .x28 0x2828282828282828#64
                    |>.writeReg64 .fp  0x2929292929292929#64
                    |>.writeReg64 .sp  sp0)
        [(dataBase, 1000#64),
         (dataBase + 8#64, 350#64),
         (sp0, 0xdeadbeefcafebabe#64),
         (sp0 + 8#64, 0x0123456789abcdef#64),
         (sp0 + 16#64, 0xfedcba9876543210#64)]
      let sf := runProgram Testing.FunctionalCorrectness.stackSpillStructUpdateProg 0x1000#64 s0
      let sfLinked := runProgram Testing.FunctionalCorrectness.functionalCorrectnessLinkedProg Testing.FunctionalCorrectness.stackSpillStructUpdate_addr s0
      let checkState (st : State) : Bool :=
        st.readReg64 .x0 == 1350#64 &&
        st.mem.read64 dataBase == 1125#64 &&
        st.mem.read64 (dataBase + 8#64) == 225#64 &&
        st.sp == sp0 &&
        st.readReg64 .x19 == 0x1919191919191919#64 &&
        st.readReg64 .x20 == 0x2020202020202020#64 &&
        st.readReg64 .x21 == 0x2121212121212121#64 &&
        st.readReg64 .x22 == 0x2222222222222222#64 &&
        st.readReg64 .x23 == 0x2323232323232323#64 &&
        st.readReg64 .x24 == 0x2424242424242424#64 &&
        st.readReg64 .x25 == 0x2525252525252525#64 &&
        st.readReg64 .x26 == 0x2626262626262626#64 &&
        st.readReg64 .x27 == 0x2727272727272727#64 &&
        st.readReg64 .x28 == 0x2828282828282828#64 &&
        st.readReg64 .fp  == 0x2929292929292929#64 &&
        st.mem.read64 sp0 == 0xdeadbeefcafebabe#64 &&
        st.mem.read64 (sp0 + 8#64) == 0x0123456789abcdef#64 &&
        st.mem.read64 (sp0 + 16#64) == 0xfedcba9876543210#64
      checkState sf && checkState sfLinked },

  -- Architectural alignment checks (SP 16-byte alignment and LDAR/STLR natural alignment)
  { name := "execInst: SP-based loads/stores fault with 'SP alignment fault' when SP is not 16-byte aligned, succeed when 16-byte aligned, and non-SP unaligned accesses succeed"
    check :=
      let sUnalignedSP : State := rwState.writeReg64 .sp 0x1008#64
      let spInsts : List Instr := [
        .ldr .W64 .X64 false .x0 (.Offset .sp 0#64),
        .str .X64 .x0 (.Offset .sp 0#64),
        .ldp .W64 false .x0 .x1 (.PreIndex .sp (-16#64)),
        .stp .W64 .x0 .x1 (.PostIndex .sp 16#64),
        .ldrSimd .Q128 0#5 (.UnscaledOffset .sp 0#64),
        .strSimd .Q128 0#5 (.Offset .sp 0#64),
        .ldpSimd .Q128 0#5 1#5 (.Offset .sp 0#64),
        .stpSimd .Q128 0#5 1#5 (.Offset .sp 0#64),
        .st1SinglePost true 31#5 0b100#3 false 0b01#2 .sp 0#5,
        .simdLdSt1Single true false false 0#5 0b000#3 false 0b00#2 .sp 0#5,
        .simdLdStMulti true false 0b00#2 2 .sp false 0#5 0#5,
        .ldarStlr .X64 true .sp .x0,
        .ldarStlr .X64 false .sp .x0
      ]
      let allFaultOnUnalignedSP := spInsts.all fun inst =>
        let sf := execInst inst sUnalignedSP
        sf.status == .Exception "SP alignment fault" && sf.pc == sUnalignedSP.pc
      let sAlignedSP : State :=
        withMem64 (rwState.writeReg64 .sp 0x1000#64 |>.writeReg64 .x0 0x1122334455667788#64)
          [(0x1000#64, 0xaabbccddeeff0011#64)]
      let sfAlignedStr := execInst (.str .X64 .x0 (.Offset .sp 8#64)) sAlignedSP
      let sfAlignedLdr := execInst (.ldr .W64 .X64 false .x1 (.Offset .sp 0#64)) sfAlignedStr
      let alignedSPSucceeds :=
        sfAlignedLdr.status == .Running &&
        sfAlignedLdr.mem.read64 0x1008#64 == 0x1122334455667788#64 &&
        sfAlignedLdr.readReg64 .x1 == 0xaabbccddeeff0011#64
      let sUnalignedGpr : State :=
        rwState.writeReg64 .sp 0x1008#64
                    |>.writeReg64 .x0 0x1003#64
                    |>.writeReg64 .x1 0xdeadbeefcafebabe#64
                    |>.writeReg64 .x2 0x0102030405060708#64
      let sGpr1 := execInst (.str .X64 .x1 (.Offset .x0 0#64)) sUnalignedGpr
      let sGpr2 := execInst (.ldr .W64 .X64 false .x3 (.Offset .x0 0#64)) sGpr1
      let sGpr3 := execInst (.stp .W64 .x1 .x2 (.Offset .x0 16#64)) sGpr2
      let sGpr4 := execInst (.ldp .W64 false .x4 .x5 (.Offset .x0 16#64)) sGpr3
      let unalignedGprSucceeds :=
        sGpr4.status == .Running &&
        sGpr4.readReg64 .x3 == 0xdeadbeefcafebabe#64 &&
        sGpr4.readReg64 .x4 == 0xdeadbeefcafebabe#64 &&
        sGpr4.readReg64 .x5 == 0x0102030405060708#64
      allFaultOnUnalignedSP && alignedSPSucceeds && unalignedGprSucceeds },
  { name := "execInst: LDAR/STLR and LDXR/STXR enforce natural alignment (X64 8B, W32 4B, H16 2B fault when unaligned; B8 and aligned accesses succeed)"
    check :=
      let s0 : State :=
        rwState.writeReg64 .x0 0x1004#64
                    |>.writeReg64 .x1 0x1002#64
                    |>.writeReg64 .x2 0x1001#64
                    |>.writeReg64 .x3 0x1000#64
                    |>.writeReg64 .x4 0xfeedfacecafebeef#64
      let unalignedCases : List (MemWidth × Bool × Reg) := [
        (.X64, true,  .x0),
        (.X64, false, .x0),
        (.W32, true,  .x1),
        (.W32, false, .x1),
        (.H16, true,  .x2),
        (.H16, false, .x2)
      ]
      let allUnalignedFault := unalignedCases.all fun (sz, isLoad, rn) =>
        let sf := execInst (.ldarStlr sz isLoad rn .x4) s0
        sf.status == .Exception "alignment fault" && sf.pc == s0.pc
      let sB8Stlr := execInst (.ldarStlr .B8 false .x2 .x4) s0
      let sB8Ldar := execInst (.ldarStlr .B8 true .x2 .x5) sB8Stlr
      let sX64Stlr := execInst (.ldarStlr .X64 false .x3 .x4) sB8Ldar
      let sX64Ldar := execInst (.ldarStlr .X64 true .x3 .x6) sX64Stlr
      let sW32Stlr := execInst (.ldarStlr .W32 false .x0 .x4) sX64Ldar
      let sW32Ldar := execInst (.ldarStlr .W32 true .x0 .x7) sW32Stlr
      let sH16Stlr := execInst (.ldarStlr .H16 false .x1 .x4) sW32Ldar
      let sH16Ldar := execInst (.ldarStlr .H16 true .x1 .x8) sH16Stlr
      let exclUnalignedFault := unalignedCases.all fun (sz, isLoad, rn) =>
        let sf := if isLoad then execInst (.ldxr sz false rn .x4) s0
                  else execInst (.stxr sz false .x9 rn .x4) s0
        sf.status == .Exception "alignment fault" && sf.pc == s0.pc
      allUnalignedFault && exclUnalignedFault &&
      sH16Ldar.status == .Running &&
      sH16Ldar.readReg64 .x5 == 0xef#64 &&
      sH16Ldar.readReg64 .x6 == 0xfeedfacecafebeef#64 &&
      sH16Ldar.readReg64 .x7 == 0xcafebeef#64 &&
      sH16Ldar.readReg64 .x8 == 0xbeef#64 },
  { name := "SymWPEval: wp_sym_steps / wp_steps verified subroutine matches concrete Arm64.execInst execution"
    check :=
      let words : List (BitVec 32) := [
        0xa900789d#32, 0x8b010000#32, 0xd2401c00#32, 0xd37cec22#32,
        0x8b020000#32, 0xf9000880#32, 0xf9400880#32, 0xa940789d#32,
        0xd65f03c0#32
      ]
      let pairs : List (BitVec 64 × BitVec 64) := [
        (0#64, 0#64),
        (42#64, 7#64),
        (0x123456789abcdef0#64, 0x0fedcba987654321#64),
        (0xffffffffffffffff#64, 1#64)
      ]
      pairs.all fun (a, b) =>
        let s0 := ({} : State).writeReg64 .x0 a
                              |>.writeReg64 .x1 b
                              |>.writeReg64 .x4 dataBase
                              |>.writeReg64 .x29 0x1111222233334444#64
        let sf := runWords words s0
        let exp := ((a + b) ^^^ 0xff#64) + (b <<< 4)
        sf.status == .Running &&
        sf.pc == 0xdead0000#64 &&
        sf.readReg64 .x0 == exp &&
        sf.readReg64 .x29 == 0x1111222233334444#64 &&
        sf.mem.read64 dataBase == 0x1111222233334444#64 &&
        sf.mem.read64 (dataBase + 8#64) == 0xdead0000#64 &&
        sf.mem.read64 (dataBase + 16#64) == exp },
  { name := "ASL Audit Regressions: decode rejects barrier unallocated op2, load/store CONSTRAINED UNPREDICTABLE overlaps, and SIMD reg-offset option[1]==0"
    check :=
      let invalidWords : List (BitVec 32) := [
        -- Barrier unallocated op2 in {0, 1, 3, 7}
        0xd503301f#32, 0xd503303f#32, 0xd503307f#32, 0xd50330ff#32,
        -- Scalar LDP/LDPSW Rt == Rt2 overlap (including XZR)
        0xa9400020#32, 0x69400020#32, 0xa9407fff#32,
        -- Scalar LDP/STP writeback overlap (Rt == Rn or Rt2 == Rn, Rn != 31)
        0xa9c10400#32, 0xa9810400#32,
        -- Scalar LDR/STR pre/post-index writeback overlap (Rt == Rn, Rn != 31)
        0xf8408400#32, 0xf8008c00#32,
        -- SIMD LDP Vt1 == Vt2 overlap (including V31)
        0x2d400000#32, 0xad407fff#32,
        -- SIMD LDR/STR register offset with option[1] == 0 (UXTB/UXTH/SXTB/SXTH)
        0x3c600800#32, 0xbc608800#32
      ]
      let validWords : List (BitVec 32) := [
        -- Valid barriers: CLREX, DSB, DMB, ISB
        0xd5033f5f#32, 0xd5033b9f#32, 0xd5033bbf#32, 0xd5033fdf#32,
        -- Non-writeback LDR X0, [X0] and STP X0, X0, [X1] and STP V0, V0, [X1] are valid
        0xf9400000#32, 0xa9000020#32, 0x2d000020#32,
        -- SIMD LDR register offset with UXTW (010), LSL (011), SXTW (110), SXTX (111)
        0xbc604800#32, 0xbc606800#32, 0xbc60c800#32, 0xbc60e800#32
      ]
      invalidWords.all (fun w => decode w == none) &&
      validWords.all (fun w => (decode w).isSome) },
  { name := "Stub sentinels: 0x00000000 and 0xffffffff never decode; UDF #imm16 (imm != 0) decodes and raises"
    check :=
      let sf := runWords [0x0000beef#32, 0xd65f03c0#32] {}
      decode 0x00000000#32 == none &&
      decode 0xffffffff#32 == none &&
      decode 0x0000beef#32 == some (.udf 0xbeef#16) &&
      decode 0x00000001#32 == some (.udf 1#16) &&
      sf.status == .Exception "udf" && sf.pc == 0x1000#64 },
  { name := "ASL Audit Regressions: execInst rejects UNDEFINED SIMD encodings and executes SSHL negative shift as signed arithmetic right shift"
    check :=
      let s0 := rwState.writeReg64 .x0 0x1000#64
                       |>.writeVReg128 0#5 0x80ff7f01_80000000_ffffffff_00000080#128
                       |>.writeVReg128 1#5 0xfffefffe_fffffffc_fffffff8_ffffffff#128
      let undefWords : List (BitVec 32) := [
        -- ST3 single structure & invalid ST1 single structure encodings
        0x0d9f2000#32, 0x0d9fc000#32, 0x0d9f4400#32, 0x0d9f9400#32,
        -- simdImmShift: MOVI o2==1 (0x4f00ec00), SHL/USHR immh[3]::Q=='10', USHLL immh[3]=='1'
        0x4f00ec00#32, 0x0f405400#32, 0x2f400400#32, 0x2f40a400#32,
        -- simdInsDup: imm5=='10000', DUP 64-bit Q==0, INS Q==0, UMOV invalid Q/esize
        0x4e100400#32, 0x0e080400#32, 0x0e081c00#32, 0x2e080400#32, 0x4e013c00#32, 0x0e083c00#32,
        -- simdThreeSame: size::Q == '110'
        0x0ee08400#32,
        -- simdTwoRegMisc: REV64 size==11, REV32 size>=2, CM* #0 size::Q=='110', NOT size==01, RBIT/CNT size>=10
        0x4ee00800#32, 0x6ea00800#32, 0x0ee09800#32, 0x0e605800#32, 0x2ea05800#32,
        -- simdAcrossLanes: UMAXV size::Q=='100' and size=='11'
        0x2ea0a800#32, 0x6ee0a800#32,
        -- simdPermute: size::Q=='110', simdExt: Q==0 && imm4[3]==1
        0x0ec01800#32, 0x2e004000#32
      ]
      let allUndefFault := undefWords.all fun w =>
        match decode w with
        | none => false
        | some inst => (execInst inst s0).status != .Running
      -- Verify SSHL v0.4s, v0.4s, v1.4s (0x4ea14400) performs signed arithmetic right shift on negative shift counts
      -- Lane 0: 0x00000080 >>s 1 = 0x00000040
      -- Lane 1: 0xffffffff (-1) >>s 8 = 0xffffffff (-1)
      -- Lane 2: 0x80000000 (-2^31) >>s 4 = 0xf8000000
      let sSshl := match decode 0x4ea14400#32 with
        | some inst => execInst inst s0
        | none => { s0 with status := .Exception "decode failed" }
      let vRes := sSshl.readVReg128 0#5
      allUndefFault &&
      sSshl.status == .Running &&
      vRes.extractLsb' 0 32 == 0x00000040#32 &&
      vRes.extractLsb' 32 32 == 0xffffffff#32 &&
      vRes.extractLsb' 64 32 == 0xf8000000#32 },
  { name := "SIMD PMULL / PMULL2: decode, encode round-trip, and GF(2)[x] carry-less multiplication (1Q <- 1D/2D and 8H <- 8B/16B)"
    check :=
      -- 1. Decode and encode round-trip for 1Q <- 1D, 1Q <- 2D, 8H <- 8B, 8H <- 16B, and reserved size in {01, 10}
      decode 0x0ee2e020#32 == some (.simdPmull false true 2#5 1#5 0#5) &&
      encode (.simdPmull false true 2#5 1#5 0#5) == some 0x0ee2e020#32 &&
      decode 0x4ee5e083#32 == some (.simdPmull true true 5#5 4#5 3#5) &&
      encode (.simdPmull true true 5#5 4#5 3#5) == some 0x4ee5e083#32 &&
      decode 0x0e28e0e6#32 == some (.simdPmull false false 8#5 7#5 6#5) &&
      encode (.simdPmull false false 8#5 7#5 6#5) == some 0x0e28e0e6#32 &&
      decode 0x4e2be149#32 == some (.simdPmull true false 11#5 10#5 9#5) &&
      encode (.simdPmull true false 11#5 10#5 9#5) == some 0x4e2be149#32 &&
      decode 0x0e62e020#32 == none &&
      decode 0x0ea2e020#32 == none &&
      decode 0x4e62e020#32 == none &&
      decode 0x4ea2e020#32 == none &&
      -- 2. GF(2)[x] carry-less products via evalPmull and execWords
      -- (x + 1) * (x + 1) = x^2 + 1 (3 * 3 = 5)
      evalPmull false true 3#128 3#128 == 5#128 &&
      -- (x^2 + x + 1) * (x + 1) = x^3 + 1 (7 * 3 = 9)
      evalPmull false true 7#128 3#128 == 9#128 &&
      -- 2^63 * 2^63 = 2^126
      evalPmull false true 0x8000000000000000#128 0x8000000000000000#128 ==
        0x4000000000000000_0000000000000000#128 &&
      -- (x^63 + ... + 1)^2 = x^126 + x^124 + ... + 1
      evalPmull false true 0xffffffffffffffff#128 0xffffffffffffffff#128 ==
        0x5555555555555555_5555555555555555#128 &&
      -- Concrete execution of PMULL (Q=0) and PMULL2 (Q=1) on 1D/2D and 8B/16B lanes
      let s0 := ({} : State)
        |>.writeVReg128 1#5 0xffffffffffffffff_0000000000000003#128
        |>.writeVReg128 2#5 0x0000000000000003_8000000000000001#128
        |>.writeVReg128 7#5 0xff80070302010003_ff80070302010003#128
        |>.writeVReg128 8#5 0x038003030201ff05_038003030201ff03#128
      -- pmull v0.1q, v1.1d, v2.1d; pmull2 v3.1q, v1.2d, v2.2d;
      -- pmull v6.8h, v7.8b, v8.8b; pmull2 v9.8h, v7.16b, v8.16b; ret
      let sf := runWords [
        0x0ee2e020#32, 0x4ee2e023#32, 0x0e28e0e6#32, 0x4e28e0e9#32, 0xd65f03c0#32
      ] s0
      sf.status == .Running &&
      sf.readVReg128 0#5 == 0x0000000000000001_8000000000000003#128 &&
      sf.readVReg128 3#5 == 0x0000000000000001_0000000000000001#128 &&
      sf.readVReg128 6#5 == 0x0101400000090005_0004000100000005#128 &&
      sf.readVReg128 9#5 == 0x0101400000090005_000400010000000f#128 },
  { name := "FS syscall guards: negative fd (-EBADF), unmodeled stdio trap, and non-localFile FdKind trap"
    check :=
      let sBase := rwState.setMem (rwState.mem.write8 0x1000#64 0#8) -- empty string "" at 0x1000
      let callSvc (s : State) (nr x0 x1 x2 x3 : BitVec 64) : State :=
        execSyscall (((((s.writeReg64 .x8 nr).writeReg64 .x0 x0).writeReg64 .x1 x1).writeReg64 .x2 x2).writeReg64 .x3 x3)
      -- 1. Negative 32-bit fd (-1 = 0xffffffff#64) returns -EBADF across all fd syscalls even when fds table is populated at 0xffffffff
      let sNeg := { sBase with fs := { sBase.fs with fds := fun k => if k == 0xffffffff#64 then some { path := "bogus", accMode := .rdwr } else none } }
      let negOk :=
        [SYS_IOCTL, SYS_CLOSE, SYS_LSEEK, SYS_READ, SYS_PREAD64, SYS_WRITE, SYS_FSTAT].all fun nr =>
          let s1 := callSvc sNeg nr 0xffffffff#64 0x1100#64 0#64 0#64
          s1.status == .Running && s1.readReg64 .x0 == -EBADF
      -- 2. Unmodeled stdio fd (0, 1, 2 with s.fs.fds = none) traps fail-closed on fcntl/ioctl/close/lseek/read/pread64/fstat and write(0)
      let stdioTrapOk :=
        [SYS_FCNTL, SYS_IOCTL, SYS_CLOSE, SYS_LSEEK, SYS_READ, SYS_PREAD64, SYS_FSTAT].all (fun nr =>
          (callSvc sBase nr 0#64 0x1100#64 4#64 0#64).status == .Exception "unmodeled stdio fd") &&
        (callSvc sBase SYS_WRITE 0#64 0x1100#64 4#64 0#64).status == .Exception "unmodeled stdio fd"
      -- 3. `.stdio` descriptor (`initFsState`) supports sequential `read(0)` from out-of-band `fs.stdin`
      --    without polluting the `openat` path namespace, while non-stream ops on `fd = 0` fail closed
      let cstrStdin : List (BitVec 8) := "<stdin>".toList.map (fun c => BitVec.ofNat 8 c.toNat) ++ [0#8]
      let sStdio :=
        { sBase with
            mem := sBase.mem.writeBytes 0x1080#64 cstrStdin
            fs  := Process.initFsState { stdin := [0x41#8, 0x42#8] } }
      let sRead0 := callSvc sStdio SYS_READ 0#64 0x1100#64 4#64 0#64
      let sOpenStdin := callSvc sStdio SYS_OPENAT (-100#64) 0x1080#64 0#64 0#64
      let stdioStreamOk :=
        sRead0.status == .Running &&
        sRead0.readReg64 .x0 == 2#64 &&
        sRead0.mem.read8 0x1100#64 == 0x41#8 &&
        sRead0.mem.read8 0x1101#64 == 0x42#8 &&
        sOpenStdin.status == .Running &&
        sOpenStdin.readReg64 .x0 == -ENOENT &&
        [SYS_FCNTL, SYS_IOCTL, SYS_CLOSE, SYS_LSEEK, SYS_PREAD64, SYS_WRITE, SYS_FSTAT].all (fun nr =>
          (callSvc sStdio nr 0#64 0x1100#64 4#64 0#64).status == .Exception "unmodeled non-file fd")
      -- 4. Non-.localFile descriptor (.custom) traps fail-closed across fcntl, ioctl, fstat, read, pread64, write, lseek, close
      let sCustom := { sBase with fs := sBase.fs.setFd 5#64 (some { kind := .custom 1, path := "sock", accMode := .rdwr }) }
      let customTrapOk :=
        [SYS_FCNTL, SYS_IOCTL, SYS_CLOSE, SYS_LSEEK, SYS_READ, SYS_PREAD64, SYS_WRITE, SYS_FSTAT].all (fun nr =>
          (callSvc sCustom nr 5#64 0x1100#64 4#64 0#64).status == .Exception "unmodeled non-file fd")
      -- 5. `.localDir` descriptor supports `fcntl` `F_GETFD` / `F_SETFD` while failing closed on other `fcntl` cmds
      let sLocalDir := { sBase with fs := sBase.fs.setFd 6#64 (some { kind := .localDir, path := "dir", accMode := .rdonly }) }
      let sDirGet0 := callSvc sLocalDir SYS_FCNTL 6#64 1#64 0#64 0#64
      let sDirSet1 := callSvc sLocalDir SYS_FCNTL 6#64 2#64 1#64 0#64
      let sDirGet1 := callSvc sDirSet1  SYS_FCNTL 6#64 1#64 0#64 0#64
      let sDirSet0 := callSvc sDirSet1  SYS_FCNTL 6#64 2#64 0#64 0#64
      let localDirFcntlOk :=
        sDirGet0.status == .Running && sDirGet0.readReg64 .x0 == 0#64 &&
        sDirSet1.status == .Running && sDirSet1.readReg64 .x0 == 0#64 &&
        sDirGet1.status == .Running && sDirGet1.readReg64 .x0 == 1#64 &&
        sDirSet0.status == .Running && sDirSet0.readReg64 .x0 == 0#64 &&
        sDirSet0.fs.fds 6#64 == some { kind := .localDir, path := "dir", accMode := .rdonly, cloexec := false } &&
        [0#64, 3#64, 4#64].all (fun cmd =>
          (callSvc sLocalDir SYS_FCNTL 6#64 cmd 0#64 0#64).status == .Exception "unmodeled fcntl cmd")
      negOk && stdioTrapOk && stdioStreamOk && customTrapOk && localDirFcntlOk },
  { name := "C / AAPCS64 integer & FP conversion corner cases (NaN->0, saturation at 2^31/2^63/2^64, halfway rounding, fixed-point fbits, sign/zero extension)"
    check :=
      -- 1. FP -> int: NaN converts to 0 in ARM64 (both signed and unsigned)
      let nanToZeroOk :=
        evalFpToIntRound32_32 false .RTZ 0 0x7fc00000#32 == 0#32 &&
        evalFpToIntRound32_32 true  .RTZ 0 0x7fc00000#32 == 0#32 &&
        evalFpToIntRound64_64 false .RTZ 0 0x7ff8000000000000#64 == 0#64 &&
        evalFpToIntRound64_64 true  .RTZ 0 0x7ff8000000000000#64 == 0#64
      -- 2. FP -> int: exact boundaries 2^31, -2^31, 2^63, -2^63, 2^64 and negative -> unsigned
      let boundsOk :=
        evalFpToIntRound32_32 false .RTZ 0 0x4f000000#32 == 0x7fffffff#32 &&   -- +2^31 saturates i32 to INT32_MAX
        evalFpToIntRound32_32 true  .RTZ 0 0x4f000000#32 == 0x80000000#32 &&   -- +2^31 is exact in u32
        evalFpToIntRound32_32 false .RTZ 0 0xcf000000#32 == 0x80000000#32 &&   -- -2^31 is exact INT32_MIN
        evalFpToIntRound32_32 false .RTZ 0 0xcf800000#32 == 0x80000000#32 &&   -- -2^32 saturates to INT32_MIN
        evalFpToIntRound32_32 true  .RTZ 0 0xbf800000#32 == 0#32 &&            -- -1.0f -> u32 saturates to 0
        evalFpToIntRound32_32 true  .RTP 0 0xbf000000#32 == 0#32 &&            -- -0.5f -> u32 with RTP rounds to 0
        evalFpToIntRound64_64 false .RTZ 0 0x43e0000000000000#64 == 0x7fffffffffffffff#64 &&  -- +2^63 saturates i64
        evalFpToIntRound64_64 true  .RTZ 0 0x43e0000000000000#64 == 0x8000000000000000#64 &&  -- +2^63 exact u64
        evalFpToIntRound64_64 false .RTZ 0 0xc3e0000000000000#64 == 0x8000000000000000#64 &&  -- -2^63 exact INT64_MIN
        evalFpToIntRound64_64 true  .RTZ 0 0x43f0000000000000#64 == 0xffffffffffffffff#64     -- +2^64 saturates u64
      -- 3. Halfway rounding modes: +0.5 (0x3f000000), +1.5 (0x3fc00000), -0.5 (0xbf000000), -1.5 (0xbfc00000)
      let roundingOk :=
        evalFpToIntRound32_32 false .RNE 0 0x3f000000#32 == 0#32 &&
        evalFpToIntRound32_32 false .RNE 0 0x3fc00000#32 == 2#32 &&
        evalFpToIntRound32_32 false .RNA 0 0x3f000000#32 == 1#32 &&
        evalFpToIntRound32_32 false .RNA 0 0xbf000000#32 == 0xffffffff#32 &&
        evalFpToIntRound32_32 false .RTN 0 0xbf000000#32 == 0xffffffff#32 &&
        evalFpToIntRound32_32 false .RTP 0 0x3f000000#32 == 1#32
      -- 4. Fixed-point fbits and int -> FP rounding (2^24 + 1 = 16777217 -> 0x4b800000 in f32 RNE)
      let fbitsAndIntToFpOk :=
        evalFpToIntRound32_32 false .RTZ 4 0x3fc00000#32 == 24#32 &&           -- 1.5 * 2^4 = 24
        evalFixedToFp32_32 false 4 24#32 == 0x3fc00000#32 &&                   -- 24 / 2^4 = 1.5f
        evalFixedToFp32_64 true 0 16777217#64 == 0x4b800000#32 &&              -- 2^24 + 1 ties-to-even -> 2^24
        evalFixedToFp32_64 true 0 16777219#64 == 0x4b800002#32 &&              -- 2^24 + 3 ties-to-even -> 2^24 + 4
        evalFpCvt32To64 0x7f800001#32 == 0x7ff8000020000000#64 &&              -- sNaN32 quietened + payload preserved in f64
        evalFpCvt64To32 0x7ff0000020000000#64 == 0x7fc00001#32                 -- sNaN64 quietened + payload preserved in f32
      -- 5. C / AAPCS64 narrow load/store sign/zero extension and 32-bit W-register write zero-extension
      let m := (((Memory.empty.write8 0x1000#64 0x80#8).write16 0x1002#64 0x8000#16).write32 0x1004#64 0x80000000#32)
      let sW := (({} : State).writeReg64 .x0 0xffffffffffffffff#64).writeReg32 .x0 0x80000000#32
      let extOk :=
        m.readSized .B8 false 0x1000#64 == 0x80#64 &&
        m.readSized .B8 true 0x1000#64 == 0xffffffffffffff80#64 &&
        m.readSized .H16 false 0x1002#64 == 0x8000#64 &&
        m.readSized .H16 true 0x1002#64 == 0xffffffffffff8000#64 &&
        m.readSized .W32 false 0x1004#64 == 0x80000000#64 &&
        m.readSized .W32 true 0x1004#64 == 0xffffffff80000000#64 &&
        sW.readReg64 .x0 == 0x0000000080000000#64
      nanToZeroOk && boundsOk && roundingOk && fbitsAndIntToFpOk && extOk },
  { name := "SIMD Family A (§2.4 shifts, permutes, modified-immediates, and lane moves)"
    check :=
      let s1 := (({} : State).writeVReg128 1#5 0x0000000080000001_000000000000ff80#128)
      (execInst (.simdInsDup false false 0b00001#5 0b0101#4 1#5 0#5) s1).readReg64 .x0 == 0x00000000ffffff80#64 &&
      (execInst (.simdInsDup true false 0b10100#5 0b0101#4 1#5 0#5) s1).readReg64 .x0 == 0xffffffff80000001#64 &&
      evalSimdModImmExt true false 0b101#3 (0b1100#4 ++ 0#1) 0b00101#5 0#128 ==
        .ok 0x0000a5ff0000a5ff_0000a5ff0000a5ff#128 &&
      evalSimdModImmExt false true 0b101#3 (0b1101#4 ++ 0#1) 0b00101#5 0#128 ==
        .ok 0x0000000000000000_ff5a0000ff5a0000#128 &&
      evalSimdModImmExt true false 0b000#3 (0b0001#4 ++ 0#1) 0b00011#5 0x1000000020000000_3000000040000000#128 ==
        .ok 0x1000000320000003_3000000340000003#128 &&
      evalSimdModImmExt true true 0b000#3 (0b0001#4 ++ 0#1) 0b00011#5 0xffffffffffffffff_ffffffffffffffff#128 ==
        .ok 0xfffffffcfffffffc_fffffffcfffffffc#128 &&
      evalSimdModImmExt true false 0b011#3 (0b1111#4 ++ 0#1) 0b10000#5 0#128 ==
        .ok 0x3f8000003f800000_3f8000003f800000#128 &&
      evalSimdModImmExt true true 0b011#3 (0b1111#4 ++ 0#1) 0b10000#5 0#128 ==
        .ok 0x3ff0000000000000_3ff0000000000000#128 &&
      evalSimdImmShiftNonZeroExt false false 0b0001#4 0b111#3 0b00000#5 0#128 0x00000000000080fe#128 ==
        .ok 0x000000000000c0ff#128 &&
      evalSimdImmShiftNonZeroExt false false 0b0001#4 0b111#3 0b00100#5 0#128 0x00000000000080ff#128 ==
        .ok 0x000000000000c000#128 &&
      evalSimdImmShiftNonZeroExt false false 0b0001#4 0b111#3 0b00010#5 0x0000000000000101#128 0x00000000000004fe#128 ==
        .ok 0x0000000000000300#128 &&
      evalSimdImmShiftNonZeroExt false false 0b0001#4 0b000#3 0b10100#5 0#128 0x000000000000807f#128 ==
        .ok 0x0000000000000000_00000000ff80007f#128 &&
      evalSimdImmShiftNonZeroExt true false 0b0001#4 0b100#3 0b10000#5 0x1122334455667788#128 0x00ab00cd_00ef0012_00340056_0078009a#128 ==
        .ok 0x0a0c0e0103050709_1122334455667788#128 &&
      evalSimdImmShiftNonZeroExt false false 0b0001#4 0b111#3 0b10010#5 0#128 0xff000200#128 ==
        .ok 0x000000000000807f#128 &&
      evalSimdImmShiftNonZeroExt false true 0b0001#4 0b111#3 0b10000#5 0#128 0xff000200#128 ==
        .ok 0x00000000000000ff#128 &&
      evalSimdImmShiftNonZeroExt false true 0b0001#4 0b001#3 0b01100#5 0#128 0x0000000000807f40#128 ==
        .ok 0x000000000000fe80#128 &&
      evalSimdImmShiftNonZeroExt false false 0b0001#4 0b001#3 0b01110#5 0#128 0x0000000000807f20#128 ==
        .ok 0x0000000000807f40#128 &&
      evalSimdTwoRegMiscExt false false 0b00#2 0b00001#5 0#128 0x0102030405060708#128 ==
        .ok 0x0201040306050807#128 &&
      evalSimdTwoRegMiscExt false true 0b01#2 0b00101#5 0#128 0x0000000000008001#128 ==
        .ok 0x0000000000000180#128 &&
      evalSimdTwoRegMiscExt false true 0b00#2 0b00100#5 0#128 0x0000000000800100#128 ==
        .ok 0x0808080808000708#128 &&
      evalSimdTwoRegMiscExt false false 0b00#2 0b00100#5 0#128 0x00000000ff807f00#128 ==
        .ok 0x0707070707000007#128 &&
      evalSimdTwoRegMiscExt false true 0b00#2 0b10011#5 0#128 0x0000000000001234#128 ==
        .ok 0x00000000_00000000_00000000_12003400#128 &&
      evalSimdThreeSameExt false false 0b00#2 0b01001#5 0#128 0x0000000000c05020#128 0x0000000000010101#128 ==
        .ok 0x0000000000807f40#128 &&
      evalSimdThreeSameExt false true 0b00#2 0b01010#5 0#128 0x0000000000000302#128 0x000000000000ffff#128 ==
        .ok 0x0000000000000201#128 },
  { name := "SIMD Family C (Tier 1 integer AdvSIMD: BIT/BIF, halving/saturating add/sub, min/max/pairwise, ABD/ABA, MUL/MLA/MLS/PMUL, SQDMULH, ADDLP/ADALP, SUQADD/USQADD, ABS/NEG/SQABS/SQNEG, XTN/SQXTN/UQXTN/SQXTUN, URECPE/URSQRTE)"
    check :=
      -- BIT & BIF
      evalSimdThreeSameExt false true 0b10#2 0b00011#5 0xaaaa#128 0x5555#128 0xff00#128 == .ok 0x55aa#128 &&
      evalSimdThreeSameExt false true 0b11#2 0b00011#5 0xaaaa#128 0x5555#128 0xff00#128 == .ok 0xaa55#128 &&
      -- SHADD, URHADD, SHSUB
      evalSimdThreeSameExt false false 0b00#2 0b00000#5 0#128 0x807f#128 0x8001#128 == .ok 0x8040#128 &&
      evalSimdThreeSameExt false true 0b00#2 0b00010#5 0#128 0x0301#128 0x0200#128 == .ok 0x0301#128 &&
      evalSimdThreeSameExt false false 0b00#2 0b00100#5 0#128 0x7f80#128 0x807f#128 == .ok 0x7f80#128 &&
      -- SQADD, UQSUB
      evalSimdThreeSameExt false false 0b00#2 0b00001#5 0#128 0x807f#128 0xff01#128 == .ok 0x807f#128 &&
      evalSimdThreeSameExt false true 0b00#2 0b00101#5 0#128 0x0502#128 0x0205#128 == .ok 0x0300#128 &&
      -- SMAX, UMIN
      evalSimdThreeSameExt false false 0b00#2 0b01100#5 0#128 0x807f#128 0xff00#128 == .ok 0xff7f#128 &&
      evalSimdThreeSameExt false true 0b00#2 0b01101#5 0#128 0x807f#128 0xff01#128 == .ok 0x8001#128 &&
      -- SABD, UABA
      evalSimdThreeSameExt false false 0b00#2 0b01110#5 0#128 0x807f#128 0x7f80#128 == .ok 0xffff#128 &&
      evalSimdThreeSameExt false true 0b00#2 0b01111#5 0x0101#128 0x0a02#128 0x0308#128 == .ok 0x0807#128 &&
      -- MUL, MLA, MLS, PMUL
      evalSimdThreeSameExt false false 0b00#2 0b10011#5 0#128 0x0302#128 0x0504#128 == .ok 0x0f08#128 &&
      evalSimdThreeSameExt false false 0b00#2 0b10010#5 0x1010#128 0x0302#128 0x0504#128 == .ok 0x1f18#128 &&
      evalSimdThreeSameExt false true 0b00#2 0b10010#5 0x1010#128 0x0302#128 0x0504#128 == .ok 0x0108#128 &&
      evalSimdThreeSameExt false true 0b00#2 0b10011#5 0#128 0x0703#128 0x0303#128 == .ok 0x0905#128 &&
      -- SMAXP on 4H, SQDMULH on 4H
      evalSimdThreeSameExt false false 0b01#2 0b10100#5 0#128 0x0005_fffe_0003_ffff#128 0x0010_0020_fff0_ff80#128 ==
        .ok 0x0020_fff0_0005_0003#128 &&
      evalSimdThreeSameExt false false 0b01#2 0b10110#5 0#128 0x8000_4000#128 0x8000_4000#128 ==
        .ok 0x7fff_2000#128 &&
      -- SADDLP, UADALP, SUQADD, USQADD, SQABS, SQNEG, ABS, NEG
      evalSimdTwoRegMiscExt false false 0b00#2 0b00010#5 0#128 0x0000_0000_0000_807f#128 == .ok 0xffff#128 &&
      evalSimdTwoRegMiscExt false true 0b00#2 0b00110#5 0x0010#128 0x0000_0000_0000_0203#128 == .ok 0x0015#128 &&
      evalSimdTwoRegMiscExt false false 0b00#2 0b00011#5 0x7f80#128 0x1080#128 == .ok 0x7f00#128 &&
      evalSimdTwoRegMiscExt false false 0b00#2 0b00111#5 0#128 0x80ff#128 == .ok 0x7f01#128 &&
      evalSimdTwoRegMiscExt false true 0b00#2 0b00111#5 0#128 0x8001#128 == .ok 0x7fff#128 &&
      evalSimdTwoRegMiscExt false false 0b00#2 0b01011#5 0#128 0x80ff#128 == .ok 0x8001#128 &&
      evalSimdTwoRegMiscExt false true 0b00#2 0b01011#5 0#128 0x8001#128 == .ok 0x80ff#128 &&
      -- XTN, SQXTUN, SQXTN, UQXTN
      evalSimdTwoRegMiscExt false false 0b00#2 0b10010#5 0#128 0x1234_5678#128 == .ok 0x3478#128 &&
      evalSimdTwoRegMiscExt false true 0b00#2 0b10010#5 0#128 0xff80_0100#128 == .ok 0x00ff#128 &&
      evalSimdTwoRegMiscExt false false 0b00#2 0b10100#5 0#128 0xff00_0100#128 == .ok 0x807f#128 &&
      evalSimdTwoRegMiscExt false true 0b00#2 0b10100#5 0#128 0x0100_0042#128 == .ok 0xff42#128 &&
      -- URECPE & URSQRTE on 2S
      evalSimdTwoRegMiscExt false false 0b10#2 0b11100#5 0#128 0x80000000_7fffffff#128 ==
        .ok 0xff800000_ffffffff#128 &&
      evalSimdTwoRegMiscExt false true 0b10#2 0b11100#5 0#128 0x40000000_3fffffff#128 ==
        .ok 0xff800000_ffffffff#128 },
  { name := "SIMD Family B (§2.6 Crypto: SHA-1 & SHA-256 FIPS 180-4 'abc' single-block vectors, SHA-512, and SHA-3 EOR3/BCAX/RAX1/XAR)"
    check :=
      let add4S (a b : BitVec 128) : BitVec 128 :=
        (a.extractLsb' 96 32 + b.extractLsb' 96 32) ++
        (a.extractLsb' 64 32 + b.extractLsb' 64 32) ++
        (a.extractLsb' 32 32 + b.extractLsb' 32 32) ++
        (a.extractLsb' 0 32 + b.extractLsb' 0 32)
      -- FIPS 180-4 single-block SHA-1 ("abc") driven through `SHA1C`/`SHA1P`/`SHA1M`/`SHA1H`/`SHA1SU0`/`SHA1SU1`
      let sha1Abc : BitVec 128 × BitVec 32 := Id.run do
        let mut ws : Array (BitVec 128) := #[
          0x00000000_00000000_00000000_61626380#128,
          0#128,
          0#128,
          0x00000018_00000000_00000000_00000000#128
        ]
        for i in [4:20] do
          let su0 := (evalCryptoSha3Reg 3#3 ws[i - 4]! ws[i - 3]! ws[i - 2]!).toOption.getD 0#128
          let su1 := (evalCryptoSha2Reg 1#5 su0 ws[i - 1]!).toOption.getD 0#128
          ws := ws.push su1
        let hInit : BitVec 128 := 0x10325476_98badcfe_efcdab89_67452301#128
        let eInit : BitVec 32 := 0xc3d2e1f0#32
        let mut abcd := hInit
        let mut e := eInit
        for i in [0:20] do
          let (opc, k) : BitVec 3 × BitVec 128 :=
            if i < 5 then (0#3, 0x5a827999_5a827999_5a827999_5a827999#128)
            else if i < 10 then (1#3, 0x6ed9eba1_6ed9eba1_6ed9eba1_6ed9eba1#128)
            else if i < 15 then (2#3, 0x8f1bbcdc_8f1bbcdc_8f1bbcdc_8f1bbcdc#128)
            else (1#3, 0xca62c1d6_ca62c1d6_ca62c1d6_ca62c1d6#128)
          let wk := add4S ws[i]! k
          let eNext := ((evalCryptoSha2Reg 0#5 0#128 abcd).toOption.getD 0#128).truncate 32
          abcd := (evalCryptoSha3Reg opc abcd (e.zeroExtend 128) wk).toOption.getD 0#128
          e := eNext
        return (add4S abcd hInit, e + eInit)
      -- FIPS 180-4 single-block SHA-256 ("abc") driven through `SHA256H`/`SHA256H2`/`SHA256SU0`/`SHA256SU1`
      let sha256Abc : BitVec 128 × BitVec 128 := Id.run do
        let mut ws : Array (BitVec 128) := #[
          0x00000000_00000000_00000000_61626380#128,
          0#128,
          0#128,
          0x00000018_00000000_00000000_00000000#128
        ]
        for i in [4:16] do
          let su0 := (evalCryptoSha2Reg 2#5 ws[i - 4]! ws[i - 3]!).toOption.getD 0#128
          let su1 := (evalCryptoSha3Reg 6#3 su0 ws[i - 2]! ws[i - 1]!).toOption.getD 0#128
          ws := ws.push su1
        let k256 : Array (BitVec 128) := #[
          0xe9b5dba5_b5c0fbcf_71374491_428a2f98#128,
          0xab1c5ed5_923f82a4_59f111f1_3956c25b#128,
          0x550c7dc3_243185be_12835b01_d807aa98#128,
          0xc19bf174_9bdc06a7_80deb1fe_72be5d74#128,
          0x240ca1cc_0fc19dc6_efbe4786_e49b69c1#128,
          0x76f988da_5cb0a9dc_4a7484aa_2de92c6f#128,
          0xbf597fc7_b00327c8_a831c66d_983e5152#128,
          0x14292967_06ca6351_d5a79147_c6e00bf3#128,
          0x53380d13_4d2c6dfc_2e1b2138_27b70a85#128,
          0x92722c85_81c2c92e_766a0abb_650a7354#128,
          0xc76c51a3_c24b8b70_a81a664b_a2bfe8a1#128,
          0x106aa070_f40e3585_d6990624_d192e819#128,
          0x34b0bcb5_2748774c_1e376c08_19a4c116#128,
          0x682e6ff3_5b9cca4f_4ed8aa4a_391c0cb3#128,
          0x8cc70208_84c87814_78a5636f_748f82ee#128,
          0xc67178f2_bef9a3f7_a4506ceb_90befffa#128
        ]
        let abcdInit : BitVec 128 := 0xa54ff53a_3c6ef372_bb67ae85_6a09e667#128
        let efghInit : BitVec 128 := 0x5be0cd19_1f83d9ab_9b05688c_510e527f#128
        let mut abcd := abcdInit
        let mut efgh := efghInit
        for i in [0:16] do
          let wk := add4S ws[i]! k256[i]!
          let abcdNext := (evalCryptoSha3Reg 4#3 abcd efgh wk).toOption.getD 0#128
          let efghNext := (evalCryptoSha3Reg 5#3 efgh abcd wk).toOption.getD 0#128
          abcd := abcdNext
          efgh := efghNext
        return (add4S abcd abcdInit, add4S efgh efghInit)
      sha1Abc == (0x7850c26c_ba3e2571_4706816a_a9993e36#128, 0x9cd0d89d#32) &&
      sha256Abc == (0x5dae2223_414140de_8f01cfea_ba7816bf#128, 0xf20015ad_b410ff61_96177a9c_b00361a3#128) &&
      -- SHA-512 (`SHA512SU0`, `SHA512SU1`, `SHA512H`, `SHA512H2`) and SHA-3 (`EOR3`, `BCAX`, `RAX1`, `XAR`)
      evalCryptoSha512Reg2 0#128 0#128 == 0#128 &&
      evalCryptoSha512Reg3 2#2 0x0000000000000001_0000000000000002#128 0#128 0x0000000000000003_0000000000000004#128 ==
        0x0000000000000004_0000000000000006#128 &&
      evalCryptoSha512Reg3 3#2 0#128 0x1111111111111111_2222222222222222#128 0x8000000000000000_0000000000000001#128 ==
        0x1111111111111110_2222222222222220#128 &&
      evalCryptoSha3FourReg false 0x1111#128 0x2222#128 0x4444#128 == 0x7777#128 &&
      evalCryptoSha3FourReg true 0x0f0f#128 0x00ff#128 0x0ff0#128 == 0x0f00#128 &&
      evalCryptoXar 4#6 0x0000000000000012_0000000000000034#128 0#128 ==
        0x2000000000000001_4000000000000003#128 &&
      decode 0x5e280820#32 == some (.cryptoSha2Reg 0#5 1#5 0#5) &&
      encode (.cryptoSha2Reg 0#5 1#5 0#5) == some 0x5e280820#32 &&
      decode 0x5e020020#32 == some (.cryptoSha3Reg 0#3 2#5 1#5 0#5) &&
      encode (.cryptoSha3Reg 0#3 2#5 1#5 0#5) == some 0x5e020020#32 &&
      decode 0xcec08020#32 == some (.cryptoSha512Reg2 1#5 0#5) &&
      encode (.cryptoSha512Reg2 1#5 0#5) == some 0xcec08020#32 &&
      decode 0xce628020#32 == some (.cryptoSha512Reg3 0#2 2#5 1#5 0#5) &&
      encode (.cryptoSha512Reg3 0#2 2#5 1#5 0#5) == some 0xce628020#32 &&
      decode 0xce020c20#32 == some (.cryptoSha3FourReg false 2#5 3#5 1#5 0#5) &&
      encode (.cryptoSha3FourReg false 2#5 3#5 1#5 0#5) == some 0xce020c20#32 &&
      decode 0xce824420#32 == some (.cryptoXar 2#5 17#6 1#5 0#5) &&
      encode (.cryptoXar 2#5 17#6 1#5 0#5) == some 0xce824420#32 },

  -- Unsupported out-of-scope AdvSIMD / FP opcodes
  { name := "Scope D: descriptive unsupported errors for vector-FP, fixed-point, and undecoded AdvSIMD classes"
    check :=
      let s0 : State := {}
      -- 1. Decoded vector-FP FADD V0.4S, V1.4S, V2.4S (0x4e22d420)
      (execInst (.simdThreeSame true false 0b00#2 2#5 0b11010#5 1#5 0#5) s0).status ==
        .Exception "unsupported AdvSIMD: simdThreeSame vector-FP FADD (q=1 u=0 size=0 opcode=26) — vector FP not modeled in Arm64/Trusted/ISA" &&
      -- 2. Decoded vector fixed-point SCVTF V0.4S, V1.4S, #32 (0x4f20e420)
      (execInst (.simdImmShift true false 0b0100#4 0b000#3 0b11100#5 1#5 0#5) s0).status ==
        .Exception "unsupported AdvSIMD: simdImmShift vector-FP fixed-point SCVTF (q=1 u=0 immh=4 immb=0 opcode=28) — vector FP not modeled in Arm64/Trusted/ISA" &&
      -- 3. Decoded vector-FP FSQRT V0.4S, V1.4S (0x6ea1f820)
      (execInst (.simdTwoRegMisc true true 0b10#2 0b11111#5 1#5 0#5) s0).status ==
        .Exception "unsupported AdvSIMD: simdTwoRegMisc vector-FP FSQRT (q=1 u=1 size=2 opcode=31) — vector FP not modeled in Arm64/Trusted/ISA" &&
      -- 3b. Vector FABS and FNEG (2S/4S/2D) execute bitwise sign manipulation
      (execInst (.simdTwoRegMisc true true 0b11#2 0b01111#5 0#5 25#5) s0).readVReg128 25#5 ==
        0x8000000000000000_8000000000000000#128 &&
      (execInst (.simdTwoRegMisc true false 0b10#2 0b01111#5 1#5 0#5)
        (s0.writeVReg128 1#5 0x80000001_ffffffff_7fffffff_80000000#128)).readVReg128 0#5 ==
        0x00000001_7fffffff_7fffffff_00000000#128 &&
      -- 4. Decoded vector-FP FMAXV S0, V1.4S (0x6e30f820)
      (execInst (.simdAcrossLanes true true 0b00#2 0b01111#5 1#5 0#5) s0).status ==
        .Exception "unsupported AdvSIMD: simdAcrossLanes vector-FP FMAXV (q=1 u=1 size=0 opcode=15) — vector FP not modeled in Arm64/Trusted/ISA" &&
      -- 5. Undecoded three-different UADDL V0.8H, V1.8B, V2.8B (0x2e220020)
      describeUnsupportedAt 0x1000#64 0x2e220020#32 ==
        "at 0x1000: unsupported AdvSIMD encoding class three-different UADDL/UADDL2 (insn 0x2e220020, q=0 u=1 size=0 opcode=0) — not modeled in Arm64/Trusted/ISA" &&
      -- 6. Undecoded scalar-three-same CMEQ D0, D1, D2 (0x7ee28c20)
      describeUnsupportedAt 0x1004#64 0x7ee28c20#32 ==
        "at 0x1004: unsupported AdvSIMD encoding class scalar-three-same CMEQ (insn 0x7ee28c20, u=1 size=3 opcode=17) — scalar SIMD not modeled in Arm64/Trusted/ISA" &&
      -- 7. Undecoded vector-by-element MUL V0.4S, V1.4S, V2.S[0] (0x4f828020)
      describeUnsupportedAt 0x1008#64 0x4f828020#32 ==
        "at 0x1008: unsupported AdvSIMD encoding class vector-by-element (insn 0x4f828020, q=1 u=0 size=2 opcode=8) — not modeled in Arm64/Trusted/ISA" &&
      -- 8. Undecoded multi-structure LD2 {V0.16B, V1.16B}, [X2] (0x4c408040)
      describeUnsupportedAt 0x100c#64 0x4c408040#32 ==
        "at 0x100c: unsupported AdvSIMD encoding class multi-structure LD2 (insn 0x4c408040, q=1 L=1 opcode=8 size=0) — multi-structure LD2-LD4/ST2-ST4 not modeled in Arm64/Trusted/ISA" },

  -- ISA vs ASL 1.0 audit regressions
  { name := "ASL 1.0 Audit: reserved, unallocated, canonical S=1 B8, and CONSTRAINED UNPREDICTABLE decode rejections"
    check :=
      let rejectedWords : List (BitVec 32) := [
        -- DecodeBitMasks: len=0 (N=0, imms=111111), 32-bit N=1, non-canonical immr >= esize (esize=16, immr=16)
        0x9200fc00#32, 0x12400000#32, 0x9210c000#32,
        -- MOVZ 32-bit hw >= 2; SBFM/BFM/UBFM 32-bit N=1, imms[5]=1, immr[5]=1
        0x52c00000#32, 0x33400000#32, 0x53008000#32, 0x53200000#32,
        -- EXTR 32-bit N=1, imms[5]=1, 64-bit N=0
        0x13c00000#32, 0x13808000#32, 0x93800000#32,
        -- B.cond o0=1 or o1=1; ADD/SUB shifted ROR (11) or 32-bit imm6 >= 32; ADD/SUB ext imm3 > 4
        0x54000010#32, 0x55000000#32, 0x8bc10000#32, 0x0b018000#32, 0x8b211400#32,
        -- CCMP o2=1 / o3=1; CSEL op2=10; 32-bit REV64; 64-bit CRC32B; 32-bit SMADDL
        0x7a410400#32, 0x7a410010#32, 0x9a810800#32, 0x5ac00c00#32, 0x9ac14000#32, 0x1b210000#32,
        -- LDNP Rt==Rt2 (GPR & SIMD); 8-bit reg-offset S=1 canonicalization (LDRB, STRB, LDRSB, SIMD LDR B)
        0xa8400020#32, 0x2c400020#32, 0x38627820#32, 0x38227820#32, 0x38a27820#32, 0x3c617800#32,
        -- Exclusive & atomic overlaps: LDXP Rt==Rt2, STXP Rs==Rt / Rs==Rt2 / Rs==Rn, STXR Rs==Rt / Rs==Rn
        0xc87f0020#32, 0xc8200420#32, 0xc8210020#32, 0xc8220840#32, 0xc8007c20#32, 0xc8017c20#32,
        -- CASP odd Rs or odd Rt; LDAPUR/STLUR reserved size:opc; PMULL reserved size=01
        0x48217c40#32, 0x48207c41#32, 0xd9800000#32, 0x99c00000#32, 0x0e62e020#32
      ]
      rejectedWords.all (fun w => decode w == none) },
  { name := "ASL 1.0 Audit: BLR X30 target-before-link order"
    check :=
      let sBlr0 : State := ({ pc := 0x1000#64 } : State).writeReg64 .x30 0x4000#64
      let sBlr1 := match decode 0xd63f03c0#32 with
        | some inst => execInst inst sBlr0
        | none => { sBlr0 with status := .Exception "decode failed" }
      sBlr1.status == .Running && sBlr1.pc == 0x4000#64 && sBlr1.readReg64 .x30 == 0x1004#64 },
  { name := "ASL 1.0 Audit: BFM/SBFM/UBFM wrap-around (imms < immr), EXTR lsb=0/63, and CSINC/CSINV/CSNEG AL/NV"
    check :=
      let sAlu0 := ({} : State)
        |>.writeReg64 .x0 0x123456789abcdef0#64
        |>.writeReg64 .x1 0xfedcba9876543281#64
        |>.writeReg64 .x4 0xaaaaaaaaaaaaaaaa#64
      let sAlu := runWords [
        0xb3703c04#32, -- bfm x4, x0, #48, #15 (inserts x0[15:0]=0xdef0 at x4[31:16])
        0x93781c25#32, -- sbfm x5, x1, #56, #7 (sbfiz x5, x1, #8, #8: x1[7:0]=0x81 sign-extended << 8)
        0x53181c06#32, -- ubfm w6, w0, #24, #7 (ubfiz w6, w0, #8, #8: w0[7:0]=0xf0 << 8)
        0x93c10007#32, -- extr x7, x0, x1, #0  (lsb=0 -> x1)
        0x93c1fc08#32, -- extr x8, x0, x1, #63
        0x9a80e409#32, -- csinc x9, x0, x0, al (cond=1110 true -> x0)
        0xda81f02a#32, -- csinv x10, x1, x1, nv (cond=1111 true -> x1)
        0x5a80e40b#32, -- csneg w11, w0, w0, al (cond=1110 true -> zero-extended w0)
        0xd65f03c0#32  -- ret
      ] sAlu0
      sAlu.status == .Running &&
      sAlu.readReg64 .x4 == 0xaaaaaaaadef0aaaa#64 &&
      sAlu.readReg64 .x5 == 0xffffffffffff8100#64 &&
      sAlu.readReg64 .x6 == 0x000000000000f000#64 &&
      sAlu.readReg64 .x7 == 0xfedcba9876543281#64 &&
      sAlu.readReg64 .x8 == 0x2468acf13579bde1#64 &&
      sAlu.readReg64 .x9 == 0x123456789abcdef0#64 &&
      sAlu.readReg64 .x10 == 0xfedcba9876543281#64 &&
      sAlu.readReg64 .x11 == 0x000000009abcdef0#64 },
  { name := "ASL 1.0 Audit: LDPSW pre-index 64-bit writeback, SADDLP/UADDLP 2S vs SADDLV/UADDLV/ADDV 2S UNDEFINED, FMOV D[1], FCVT same-size fault, and FMA DefaultNaN"
    check :=
      let sMem0 := withMem64
        (rwState.writeReg64 .x2 0x1000000000001000#64
          |>.writeReg64 .x0 0xdeadbeefcafebabe#64
          |>.writeVReg128 0#5 0x1122334455667788_80000000ffffffff#128
          |>.writeVReg128 5#5 0x0000000000000000_0102030405060708#128)
        [(0x1000000000001008#64, 0x80000005fffffffe#64)]
      let sMem := runWords [
        0x69c10443#32, -- ldpsw x3, x1, [x2, #8]! (64-bit writeback to x2, sign-extended 32-bit loads)
        0x0ea02802#32, -- saddlp v2.1d, v0.2s (-2147483648 + -1 = -2147483649 = 0xffffffff7fffffff)
        0x2ea02803#32, -- uaddlp v3.1d, v0.2s (0x80000000 + 0xffffffff = 0x17fffffff)
        0x9eae0004#32, -- fmov x4, v0.d[1] (opcode = 110)
        0x9eaf0005#32, -- fmov v5.d[1], x0 (opcode = 111, preserves v5.d[0] = 0x0102030405060708)
        0xd65f03c0#32  -- ret
      ] sMem0
      let acrossLanes2SFault :=
        [0x0eb1b800#32, 0x0eb03802#32, 0x2eb03803#32].all fun w =>
          match decode w with
          | some inst => (execInst inst sMem0).status != .Running
          | none => false
      let fcvtSameFault :=
        (execInst (.fpDataProc1 0b00#2 0b000100#6 0#5 0#5) sMem0).status != .Running &&
        (execInst (.fpDataProc1 0b01#2 0b000101#6 0#5 0#5) sMem0).status != .Running
      let fmaNanOk :=
        fpFma32 0x7fc00001#32 0x00000000#32 0x7f800000#32 == 0x7fc00000#32 &&
        fpFma32 0x7f800001#32 0x00000000#32 0x7f800000#32 == 0x7fc00001#32 &&
        fpFma64 0x7ff8000000000001#64 0x0000000000000000#64 0x7ff0000000000000#64 == 0x7ff8000000000000#64 &&
        fpFma64 0x7ff0000000000001#64 0x0000000000000000#64 0x7ff0000000000000#64 == 0x7ff8000000000001#64
      sMem.status == .Running &&
      sMem.readReg64 .x2 == 0x1000000000001008#64 &&
      sMem.readReg64 .x3 == 0xfffffffffffffffe#64 &&
      sMem.readReg64 .x1 == 0xffffffff80000005#64 &&
      sMem.readVReg128 2#5 == 0x0000000000000000_ffffffff7fffffff#128 &&
      sMem.readVReg128 3#5 == 0x0000000000000000_000000017fffffff#128 &&
      sMem.readReg64 .x4 == 0x1122334455667788#64 &&
      sMem.readVReg128 5#5 == 0xdeadbeefcafebabe_0102030405060708#128 &&
      acrossLanes2SFault && fcvtSameFault && fmaNanOk },
  { name := "FPSR Cumulative Exception Flags (IOC, DZC, OFC, UFC, IXC) & Sticky Accumulation"
    check :=
      let s0 := ({} : State)
        |>.writeVReg64 1#5 0x3ff0000000000000#64 -- 1.0
        |>.writeVReg64 2#5 0x3ca0000000000000#64 -- 2^-53 (inexact add)
        |>.writeVReg64 3#5 0x0000000000000000#64 -- +0.0
        |>.writeVReg64 4#5 0x7fefffffffffffff#64 -- DBL_MAX
        |>.writeVReg64 5#5 0x0000000000000001#64 -- min_subnormal
        |>.writeVReg64 6#5 0x4000000000000000#64 -- 2.0
        |>.writeVReg64 7#5 0x7ff8000000000000#64 -- qNaN
        |>.writeVReg64 8#5 0x3ff8000000000000#64 -- 1.5
        |>.writeVReg64 9#5 0x46293e5939a08cea#64 -- 1e30 (out-of-range i64)
      -- 1) Inexact FADD (IXC = 0x10), then exact FADD preserves IXC (sticky)
      let sIxc := runWords [0x1e622820#32, 0x1e612820#32, 0xd65f03c0#32] s0
      -- 2) Divide by zero FDIV 1.0 / 0.0 (DZC = 0x02)
      let sDzc := runWords [0x1e631820#32, 0xd65f03c0#32] s0
      -- 3) Invalid 0.0 / 0.0 (IOC = 0x01)
      let sIoc := runWords [0x1e631860#32, 0xd65f03c0#32] s0
      -- 4) Overflow DBL_MAX + DBL_MAX (OFC | IXC = 0x14)
      let sOfc := runWords [0x1e642880#32, 0xd65f03c0#32] s0
      -- 5) Underflow min_subnormal / 2.0 (UFC | IXC = 0x18)
      let sUfc := runWords [0x1e6618a0#32, 0xd65f03c0#32] s0
      -- 6) FCCMPE D7, D1, #0, EQ: condition false (Z=0) -> 0; condition true (Z=1) -> IOC (0x01)
      let sFccmpeFalse := runWords [0x1e6104f0#32, 0xd65f03c0#32] ({ s0 with pstate := { s0.pstate with z := false } })
      let sFccmpeTrue := runWords [0x1e6104f0#32, 0xd65f03c0#32] ({ s0 with pstate := { s0.pstate with z := true } })
      -- 7) FCVTZS X0, D8 (1.5 -> IXC = 0x10) vs FCVTZS X0, D9 (1e30 -> IOC = 0x01 without IXC)
      let sFcvtIxc := runWords [0x9e780100#32, 0xd65f03c0#32] s0
      let sFcvtIoc := runWords [0x9e780120#32, 0xd65f03c0#32] s0
      -- 8) FRINTN D0, D8 (1.5 -> 0) vs FRINTX D0, D8 (1.5 -> IXC = 0x10)
      let sFrintn := runWords [0x1e644100#32, 0xd65f03c0#32] s0
      let sFrintx := runWords [0x1e674100#32, 0xd65f03c0#32] s0
      sIxc.fpsr == 0x10#32 &&
      sDzc.fpsr == 0x02#32 &&
      sIoc.fpsr == 0x01#32 &&
      sOfc.fpsr == 0x14#32 &&
      sUfc.fpsr == 0x18#32 &&
      sFccmpeFalse.fpsr == 0x00#32 &&
      sFccmpeTrue.fpsr == 0x01#32 &&
      sFcvtIxc.fpsr == 0x10#32 &&
      sFcvtIoc.fpsr == 0x01#32 &&
      sFrintn.fpsr == 0x00#32 &&
      sFrintx.fpsr == 0x10#32 },
  { name := "FPSR.QC Sticky SIMD Saturation Flag (SQADD, UQSUB, SQXTN)"
    check :=
      let s0 := ({} : State)
        |>.writeVReg128 1#5 0x00000000_00000000_00000001_7fffffff#128
        |>.writeVReg128 2#5 0x00000000_00000000_00000001_00000001#128
      -- Non-saturating SQADD V0.4S, V2.4S, V2.4S leaves QC=0
      let sNoSat := runWords [0x0ea20c40#32, 0xd65f03c0#32] s0
      -- Saturating SQADD V0.4S, V1.4S, V2.4S followed by non-saturating SQADD preserves QC (bit 27)
      let sSat := runWords [0x0ea20c20#32, 0x0ea20c43#32, 0xd65f03c0#32] s0
      sNoSat.fpsr == 0#32 &&
      sSat.fpsr == 0x08000000#32 &&
      (sSat.readVReg128 0#5).truncate 32 == 0x7fffffff#32 },
  { name := "MRS/MSR FPSR and FPCR: 0x0800009f mask (NZCV[31:28] RAZ/WI), sticky sequence, and fail-closed FPCR!=0"
    check :=
      -- 1) MSR FPSR, ~0 (0xd51b4420) masks to 0x0800009f; MRS X1, FPSR (0xd53b4421) reads 0x0800009f;
      --    MRS X2, FPCR (0xd53b4402) reads 0; MSR FPCR, XZR (0xd51b441f) succeeds.
      let sAllOnes := ({} : State).writeReg64 .x0 0xffffffff_ffffffff#64
      let sRoundTrip := runWords [0xd51b4420#32, 0xd53b4421#32, 0xd53b4402#32, 0xd51b441f#32, 0xd65f03c0#32] sAllOnes
      -- 2) Sticky across sequence: fdiv 1.0/0.0 (DZC); fadd 1.0+1.0 (exact); mrs x3, fpsr; msr fpsr, xzr; mrs x4, fpsr
      let sSticky0 := ({} : State)
        |>.writeVReg128 0#5 0x3ff0000000000000#128 -- 1.0
        |>.writeVReg128 1#5 0x0000000000000000#128 -- 0.0
      let sSticky := runWords [
        0x1e611802#32, -- fdiv d2, d0, d1 (1.0 / 0.0 -> DZC = 0x02)
        0x1e602803#32, -- fadd d3, d0, d0 (1.0 + 1.0 -> exact, DZC sticky)
        0xd53b4423#32, -- mrs x3, fpsr
        0xd51b443f#32, -- msr fpsr, xzr
        0xd53b4424#32, -- mrs x4, fpsr
        0xd65f03c0#32
      ] sSticky0
      -- 3) Fail-closed MSR FPCR, X0 for every nonzero bit family (RMode, FZ, DN, AHP, IOE..IDE, FZ16, high bits)
      let badFpcrVals : List (BitVec 64) := [
        1#64 <<< 22, -- RMode = RP
        3#64 <<< 22, -- RMode = RZ
        1#64 <<< 24, -- FZ
        1#64 <<< 25, -- DN
        1#64 <<< 26, -- AHP
        1#64 <<< 8,  -- IOE (trap enable)
        1#64 <<< 12, -- IXE (trap enable)
        1#64 <<< 15, -- IDE (trap enable)
        1#64 <<< 19, -- FZ16
        1#64,        -- reserved low bit
        1#64 <<< 32  -- upper 32-bit bit
      ]
      let allBadFpcrTrap := badFpcrVals.all fun v =>
        let sf := runWords [0xd51b4400#32, 0xd65f03c0#32] (({} : State).writeReg64 .x0 v)
        sf.status == .Exception "unsupported FPCR value" && sf.pc == 0x1000#64
      sRoundTrip.status == .Running &&
      sRoundTrip.fpsr == 0x0800009f#32 &&
      sRoundTrip.readReg64 .x1 == 0x0800009f#64 &&
      sRoundTrip.readReg64 .x2 == 0#64 &&
      sSticky.status == .Running &&
      sSticky.readReg64 .x3 == 0x02#64 &&
      sSticky.readReg64 .x4 == 0#64 &&
      sSticky.fpsr == 0#32 &&
      allBadFpcrTrap },
  { name := "musl src/fenv/aarch64/fenv.s replay: fegetround, __fesetround, fetestexcept, feclearexcept, feraiseexcept, fegetenv, fesetenv"
    check :=
      -- Exact machine words from third_party/musl-1.2.5/upstream/src/fenv/aarch64/fenv.s:
      let fegetroundWords : List (BitVec 32) := [0xd53b4400#32, 0x120a0400#32, 0xd65f03c0#32]
      let fesetroundWords : List (BitVec 32) := [0xd53b4401#32, 0x12087421#32, 0x2a000021#32, 0xd51b4401#32, 0x52800000#32, 0xd65f03c0#32]
      let fetestexceptWords : List (BitVec 32) := [0x12001000#32, 0xd53b4421#32, 0x0a010000#32, 0xd65f03c0#32]
      let feclearexceptWords : List (BitVec 32) := [0x12001000#32, 0xd53b4421#32, 0x0a200021#32, 0xd51b4421#32, 0x52800000#32, 0xd65f03c0#32]
      let feraiseexceptWords : List (BitVec 32) := [0x12001000#32, 0xd53b4421#32, 0x2a000021#32, 0xd51b4421#32, 0x52800000#32, 0xd65f03c0#32]
      let fegetenvWords : List (BitVec 32) := [0xd53b4401#32, 0xd53b4422#32, 0x29000801#32, 0x52800000#32, 0xd65f03c0#32]
      let fesetenvWords : List (BitVec 32) := [
        0xd2800001#32, 0xd2800002#32, 0xb100041f#32, 0x54000040#32,
        0x29400801#32, 0xd51b4401#32, 0xd51b4422#32, 0x52800000#32, 0xd65f03c0#32
      ]
      let s0 := rwState
      -- 1) fegetround() == 0; __fesetround(0) == 0; __fesetround(0x400000) traps
      let sGetRound := runWords fegetroundWords (s0.writeReg64 .x0 0xdead#64)
      let sSetRound0 := runWords fesetroundWords (s0.writeReg64 .x0 0#64)
      let sSetRoundUp := runWords fesetroundWords (s0.writeReg64 .x0 0x400000#64)
      -- 2) feraiseexcept(FE_INVALID | FE_INEXACT = 0x11), fetestexcept(0x1f) == 0x11,
      --    feclearexcept(FE_INVALID = 0x01), fetestexcept(0x1f) == 0x10
      let sRaised := runWords feraiseexceptWords (s0.writeReg64 .x0 0x11#64)
      let sTest1 := runWords fetestexceptWords (sRaised.writeReg64 .x0 0x1f#64)
      let sCleared := runWords feclearexceptWords (sRaised.writeReg64 .x0 0x01#64)
      let sTest2 := runWords fetestexceptWords (sCleared.writeReg64 .x0 0x1f#64)
      -- 3) fegetenv(&env) stores (fpcr=0, fpsr=0x11); fesetenv(FE_DFL_ENV = -1) resets fpsr=0;
      --    fesetenv(&env) restores fpsr=0x11
      let sSaved := runWords fegetenvWords (sRaised.writeReg64 .x0 dataBase)
      let sDflEnv := runWords fesetenvWords (sSaved.writeReg64 .x0 (-1#64))
      let sRestored := runWords fesetenvWords (sDflEnv.writeReg64 .x0 dataBase)
      sGetRound.readReg64 .x0 == 0#64 &&
      sSetRound0.status == .Running && sSetRound0.readReg64 .x0 == 0#64 &&
      sSetRoundUp.status == .Exception "unsupported FPCR value" &&
      sRaised.fpsr == 0x11#32 &&
      sTest1.readReg64 .x0 == 0x11#64 &&
      sCleared.fpsr == 0x10#32 &&
      sTest2.readReg64 .x0 == 0x10#64 &&
      sSaved.mem.read32 dataBase == 0#32 &&
      sSaved.mem.read32 (dataBase + 4#64) == 0x11#32 &&
      sDflEnv.fpsr == 0#32 &&
      sRestored.fpsr == 0x11#32 },
  { name := "ELF Process Semantics: fcntl (F_GETFD / F_SETFD / -EBADF), openat(O_CREAT) parent/trailing-slash checks, and resolveCwdPath ./ & // normalization"
    check := Testing.Process.checkProcessModelGapsConformance },
  { name := "ELF Process Semantics: fail-closed ELF64 parser negative tests (ET_REL, ET_DYN/PIE, PT_DYNAMIC, PT_INTERP, W+X, executable stack)"
    check := Testing.Process.checkElfParserFailClosed },
  -- The checks below embed generated test ELFs at elaboration time; each reports SKIP when its
  -- ELF is absent (see `ProofLib.TestFiles`). The path lists match the `requires_test_files`
  -- blocks that define the checks.
  if_test_files_exist% ["fixtures/echo_stdin.elf"]
  then { name := "ELF Process Semantics: Linux AArch64 initial stack, argc/argv/envp, auxv, and fd 0/1/2 layout on echo_stdin.elf"
         check := Testing.Process.checkInitialStackAndAuxv }
  else Harness.UnitTestCase.skipMissingFiles "ELF Process Semantics: initial stack and auxv on echo_stdin.elf"
    ["Arm64/Testing/Regression/fixtures/echo_stdin.elf"],
  if_test_files_exist% ["fixtures/echo_stdin.elf"]
  then { name := "ELF Process Semantics: stock zig/musl echo_stdin.elf end-to-end execution (_start -> __libc_start_main -> main -> exit_group 0)"
         check := Testing.Process.checkEchoStdinProcess }
  else Harness.UnitTestCase.skipMissingFiles "ELF Process Semantics: echo_stdin.elf end-to-end execution"
    ["Arm64/Testing/Regression/fixtures/echo_stdin.elf"],
  if_test_files_exist% ["fixtures/echo_stdin.elf"]
  then { name := "ELF Process Semantics: runElfImageFast vs reference runElfImage cross-check on echo_stdin.elf (final memory/regs/outcome equal)"
         check := Testing.Process.checkEchoStdinFastVsRef }
  else Harness.UnitTestCase.skipMissingFiles "ELF Process Semantics: runElfImageFast vs runElfImage on echo_stdin.elf"
    ["Arm64/Testing/Regression/fixtures/echo_stdin.elf"],
  if_test_files_exist% ["fixtures/abort_status.elf"]
  then { name := "ELF Process Semantics: stock zig/musl abort_status.elf abort() (rt_sigprocmask fail-closed) vs exit(134) (134, signal none) fast-vs-ref check"
         check := Testing.Process.checkAbortStatusProcess }
  else Harness.UnitTestCase.skipMissingFiles "ELF Process Semantics: abort_status.elf fast-vs-ref check"
    ["Arm64/Testing/Regression/fixtures/abort_status.elf"],
  if_test_files_exist% ["../ElfLoaderDiff/bin/tiny_asm.elf", "../ElfLoaderDiff/bin/layout_multi_rw.elf",
      "../ElfLoaderDiff/bin/layout_midpage_bss.elf", "../ElfLoaderDiff/bin/layout_tls_relro.elf",
      "../ElfLoaderDiff/bin/reject_pie.elf", "../ElfLoaderDiff/bin/reject_dynamic.elf",
      "../ElfLoaderDiff/bin/reject_relocatable.elf", "../ElfLoaderDiff/bin/reject_wx_segment.elf",
      "../ElfLoaderDiff/bin/reject_exec_stack.elf", "../ElfLoaderDiff/bin/reject_ro_bss.elf"]
  then { name := "ELF Loader vs QEMU: unusual layout & fail-closed ELF64 parser corpus conformance (multi-RW, mid-page filesz/bss, PT_TLS+RELRO, PIE/dynamic/reloc/WX/exec-stack/ro-bss)"
         check := Testing.ElfLoaderDiff.checkElfLoaderDiffCorpusConformance }
  else Harness.UnitTestCase.skipMissingFiles "ELF Loader vs QEMU: corpus conformance"
    ["Arm64/Testing/ElfLoaderDiff/bin/*.elf"]
]

/-- `SVC #0` tests for guard pages (`mmap(PROT_NONE)`, `MAP_FIXED`), split out so elaborating a
    single test list stays well within the heartbeat budget. -/
def guardPageTests : List TestCase := [
  { name := "execWords: SVC #0 mmap PROT_NONE / MAP_FIXED guard pages (mallocng), fail-closed MAP_FIXED cases"
    check :=
      let callSvc (s : State) (nr x0 x1 x2 x3 : BitVec 64) : State :=
        runWordsRaw [0xd4000001#32, 0xd65f03c0#32]
          (s |>.writeReg64 .x8 nr |>.writeReg64 .x0 x0 |>.writeReg64 .x1 x1 |>.writeReg64 .x2 x2
             |>.writeReg64 .x3 x3 |>.writeReg64 .x4 (-1#64) |>.writeReg64 .x5 0#64)
      -- Three RW pages [0x50000, 0x53000) seeded with 0x41/0x42/0x43, one frozen RO page [0x60000, 0x61000)
      let mem0 := ((((Memory.empty.mapZero 0x50000#64 0x3000).write8 0x50000#64 0x41#8).write8
        0x51000#64 0x42#8).write8 0x52000#64 0x43#8).mapFresh 0x60000#64 0x1000 .ro
      let s0 : State := { mem := mem0, oracle := testOracle 0x80000#64, physMemAvail := 0x10000 }
      -- 1. mmap(0x51000, 0x1000, PROT_NONE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_FIXED, -1, 0) -> 0x51000:
      --    the middle page becomes zero-filled PROT_NONE; its neighbours and the oracle are untouched
      let sGuard := callSvc s0 222#64 0x51000#64 0x1000#64 0#64 0x32#64
      -- A load from and a store to the guard page fault (ldr w0, [x1]; str w0, [x1])
      let sLoad := runWordsRaw [0xb9400020#32, 0xd65f03c0#32] (sGuard.writeReg64 .x1 0x51000#64)
      let sStore := runWordsRaw [0xb9000020#32, 0xd65f03c0#32] (sGuard.writeReg64 .x1 0x51ffc#64)
      -- 2. MAP_FIXED PROT_NONE over an unmapped range [0x70000, 0x72000) maps it PROT_NONE
      let sFresh := callSvc s0 222#64 0x70000#64 0x1001#64 0#64 0x32#64
      -- 3. MAP_FIXED PROT_READ|PROT_WRITE (demand-zero overlay & OOM accounting) and fail-closed cases:
      --    frozen range, range touching a frozen page, unaligned, below MMAP_MIN_ADDR (even over anon),
      --    past 2^48; len = 0 -> -EINVAL
      let sFixFrozen := callSvc s0 222#64 0x60000#64 0x1000#64 0#64 0x32#64
      let sFixTouch := callSvc s0 222#64 0x5f000#64 0x2000#64 0#64 0x32#64
      let sFixRw := callSvc s0 222#64 0x51000#64 0x1000#64 3#64 0x32#64
      let sFixRwNew := callSvc s0 222#64 0x70000#64 0x2000#64 3#64 0x32#64
      let sFixRwOom := callSvc { s0 with physMemAvail := 0x1000 } 222#64 0x70000#64 0x2000#64 3#64 0x32#64
      let sFixUnal := callSvc s0 222#64 0x51001#64 0x1000#64 0#64 0x32#64
      let sFixLow := callSvc s0 222#64 0xf000#64 0x1000#64 0#64 0x32#64
      let sFixLowAnon := callSvc { s0 with mem := s0.mem.mapZero 0xf000#64 0x1000 } 222#64 0xf000#64 0x1000#64 3#64 0x32#64
      let sFixHigh := callSvc s0 222#64 0xfffffffff000#64 0x2000#64 0#64 0x32#64
      let sFixZero := callSvc s0 222#64 0x51000#64 0#64 0#64 0x32#64
      -- 4. Non-fixed PROT_NONE mmap at oracle query 0 (0x80000), then mprotect RW and munmap
      let sNone := callSvc s0 222#64 0#64 0x2000#64 0#64 0x22#64
      let sNoneRw := callSvc sNone 226#64 0x80000#64 0x1000#64 3#64 0#64
      let sNoneUnmap := callSvc sNoneRw 215#64 0x80000#64 0x2000#64 0#64 0#64
      -- Non-fixed PROT_NONE when the oracle candidate is taken -> sanitized fallback at MMAP_MIN_ADDR (0x10000);
      -- requesting 2^48 bytes -> .OutOfMemory
      let sNoneSanitized := callSvc { sNone with oracleIdx := 0 } 222#64 0#64 0x1000#64 0#64 0x22#64
      let sNoneOom := callSvc { sNone with oracleIdx := 0 } 222#64 0#64 0x0001000000000000#64 0#64 0x22#64
      -- 5. Still unmodeled: PROT_READ alone, MAP_FIXED without MAP_ANONYMOUS, MAP_SHARED
      let sProtR := callSvc s0 222#64 0#64 0x1000#64 1#64 0x22#64
      let sFixFile := callSvc s0 222#64 0x51000#64 0x1000#64 0#64 0x12#64
      let sShared := callSvc s0 222#64 0#64 0x1000#64 0#64 0x21#64
      -- 6. the allocator pattern: brk grows by two pages, the lower one becomes a MAP_FIXED guard page,
      --    and the upper one stays writable
      let sB0 : State := { brkStart := 0x355000#64, brk := 0x355000#64, physMemAvail := 0x10000 }
      let sBrk := callSvc sB0 214#64 0x357000#64 0#64 0#64 0#64
      let sBGuard := callSvc sBrk 222#64 0x355000#64 0x1000#64 0#64 0x32#64
      let sBStore := runWordsRaw [0xb9000020#32, 0xd65f03c0#32]
        ((sBGuard.writeReg64 .x1 0x356000#64).writeReg64 .x0 0x11223344#64)
      sGuard.readReg64 .x0 == 0x51000#64 &&
      sGuard.oracleIdx == 0 &&
      sGuard.mem.perm 0x51000#64 == some .protNone &&
      sGuard.mem.perm 0x51fff#64 == some .protNone &&
      sGuard.mem.read8 0x51000#64 == 0#8 &&
      sGuard.mem.perm 0x50fff#64 == some .rw &&
      sGuard.mem.read8 0x50000#64 == 0x41#8 &&
      sGuard.mem.perm 0x52000#64 == some .rw &&
      sGuard.mem.read8 0x52000#64 == 0x43#8 &&
      (match sLoad.status with | .Exception _ => true | _ => false) &&
      (match sStore.status with | .Exception _ => true | _ => false) &&
      sFresh.readReg64 .x0 == 0x70000#64 &&
      sFresh.mem.perm 0x70000#64 == some .protNone &&
      sFresh.mem.perm 0x71fff#64 == some .protNone &&
      sFresh.mem.perm 0x72000#64 == none &&
      sFixFrozen.status == .Exception "MAP_FIXED on frozen memory" &&
      sFixFrozen.mem.perm 0x60000#64 == some .ro &&
      sFixTouch.status == .Exception "MAP_FIXED on frozen memory" &&
      sFixRw.status == .Running &&
      sFixRw.readReg64 .x0 == 0x51000#64 &&
      sFixRw.oracleIdx == 0 &&
      sFixRw.mem.perm 0x51000#64 == some .rw &&
      sFixRw.mem.read8 0x51000#64 == 0#8 &&
      sFixRw.mem.read8 0x50000#64 == 0x41#8 &&
      sFixRw.mem.read8 0x52000#64 == 0x43#8 &&
      sFixRw.physMemAvail == 0x10000 &&
      sFixRwNew.status == .Running &&
      sFixRwNew.readReg64 .x0 == 0x70000#64 &&
      sFixRwNew.mem.perm 0x70000#64 == some .rw &&
      sFixRwNew.mem.perm 0x71fff#64 == some .rw &&
      sFixRwNew.physMemAvail == 0xe000 &&
      sFixRwOom.status == .OutOfMemory &&
      sFixUnal.status == .Exception "unmodeled MAP_FIXED address" &&
      sFixLow.status == .Exception "unmodeled MAP_FIXED address" &&
      sFixLowAnon.status == .Exception "unmodeled MAP_FIXED address" &&
      sFixHigh.status == .Exception "unmodeled MAP_FIXED address" &&
      sFixZero.readReg64 .x0 == -22#64 &&
      sNone.readReg64 .x0 == 0x80000#64 &&
      sNone.oracleIdx == 1 &&
      sNone.mem.perm 0x80000#64 == some .protNone &&
      sNone.mem.perm 0x81fff#64 == some .protNone &&
      !sNone.mem.canRead 0x80000#64 1 &&
      sNoneRw.readReg64 .x0 == 0#64 &&
      sNoneRw.mem.perm 0x80000#64 == some .rw &&
      sNoneRw.mem.read8 0x80000#64 == 0#8 &&
      sNoneRw.mem.perm 0x81000#64 == some .protNone &&
      sNoneUnmap.readReg64 .x0 == 0#64 &&
      sNoneUnmap.mem.canMap 0x80000#64 0x2000 &&
      sNoneSanitized.status == .Running &&
      sNoneSanitized.readReg64 .x0 == 0x10000#64 &&
      sNoneSanitized.oracleIdx == 1 &&
      sNoneSanitized.mem.perm 0x10000#64 == some .protNone &&
      sNoneOom.status == .OutOfMemory &&
      (match sProtR.status with | .Exception _ => true | _ => false) &&
      (match sFixFile.status with | .Exception _ => true | _ => false) &&
      (match sShared.status with | .Exception _ => true | _ => false) &&
      sBrk.readReg64 .x0 == 0x357000#64 &&
      sBGuard.readReg64 .x0 == 0x355000#64 &&
      sBGuard.mem.perm 0x355000#64 == some .protNone &&
      sBGuard.mem.perm 0x356000#64 == some .rw &&
      sBStore.status == .Running &&
      sBStore.mem.read32 0x356000#64 == 0x11223344#32 }
]

def allTests (_ : Unit := ()) : List TestCase :=
  allTestsPart1 () ++ allTestsPart2 ()

end Testing

structure FullSuiteSlot where
  batch  : Testing.Harness.ParallelTestBatch := {}
  flagOk : Bool := false
  deriving Inhabited

/-- Checks that `runParallelWorkItemsIO` returns results in submission order under priority
    dispatch and turns uncaught `IO.Error`s into `onErr` values in both multi- and single-worker
    modes. -/
def checkParallelHarnessConformanceIO : IO Unit := do
  let dispatchLog ← IO.mkRef (#[] : Array Nat)
  let items : Array (Testing.Harness.ParallelWorkItem String) := #[
    { label := "item0", priority := 10,  run := fun () => do dispatchLog.modify (·.push 0); return "v0" },
    { label := "item1", priority := 100, run := fun () => do dispatchLog.modify (·.push 1); return "v1" },
    { label := "item2", priority := 50,  run := fun () => throw (IO.userError "injected-boom") },
    { label := "item3", priority := 80,  run := fun () => do dispatchLog.modify (·.push 3); return "v3" },
    { label := "item4", priority := 20,  run := fun () => do dispatchLog.modify (·.push 4); return "v4" }
  ]
  let onErr := fun idx label (e : IO.Error) => s!"err:{idx}:{label}:{e}"
  let multi ← Testing.Harness.runParallelWorkItemsIO items onErr (some 3)
  let single ← Testing.Harness.runParallelWorkItemsIO items onErr (some 1)
  let ok (arr : Array String) : Bool :=
    arr.size == 5 &&
    arr[0]! == "v0" &&
    arr[1]! == "v1" &&
    (arr[2]!.startsWith "err:2:item2:") &&
    arr[3]! == "v3" &&
    arr[4]! == "v4"
  unless ok multi && ok single do
    throw (IO.userError s!"runParallelWorkItemsIO conformance check failed: multi={repr multi} single={repr single}")

@[noinline] def evalAllTestsIO : IO (List Testing.TestCase) := do
  let items : Array (Testing.Harness.ParallelWorkItem Testing.Harness.ParallelTestBatch) := #[
    { label := "allTestsPart1", priority := 800, run := fun () => pure { cases := Testing.allTestsPart1 () } },
    { label := "allTestsPart2", priority := 800, run := fun () => pure { cases := Testing.allTestsPart2 () } }
  ]
  Testing.Harness.runParallelTestBatchesIO items

def main (args : List String) : IO UInt32 := do
  if args == ["--fs-diff-trace"] then
    Testing.dumpFsDiffTrace
    return 0
  if args == ["--mmap-diff-trace"] then
    Testing.dumpMmapDiffTrace
    return 0
  if args == ["--sigaltstack-diff-trace"] then
    Testing.dumpSigaltstackDiffTrace
    return 0
  if args == ["--process-e2e"] then
    let t0 ← IO.monoMsNow
    let e2eCases ← Testing.ProcessE2E.runAllProcessE2ETestsIO
    let t1 ← IO.monoMsNow
    IO.println s!"[unit_tests] Evaluated {e2eCases.length} Rust whole-ELF process e2e cases in {t1 - t0} ms"
    return (← Testing.runTestSuite e2eCases)
  if args == ["--elf-loader-diff"] then
    let t0 ← IO.monoMsNow
    let loaderCases ← Testing.ElfLoaderDiff.runDefaultElfLoaderDiffIO
    let t1 ← IO.monoMsNow
    IO.println s!"[unit_tests] Evaluated {loaderCases.length} ELF loader vs QEMU entry-state differential cases in {t1 - t0} ms"
    return (← Testing.runTestSuite loaderCases)
  if args == ["--syscall-diff"] then
    let t0 ← IO.monoMsNow
    let syscallDiffCases ← Testing.SyscallDiff.runSyscallDiffSuiteIO
    let t1 ← IO.monoMsNow
    IO.println s!"[unit_tests] Evaluated {syscallDiffCases.length} per-syscall Linux 7.3 / QEMU differential cases in {t1 - t0} ms"
    return (← Testing.runTestSuite syscallDiffCases)
  if args == ["--base"] then
    let t0 ← IO.monoMsNow
    let baseCases ← evalAllTestsIO
    let t1 ← IO.monoMsNow
    IO.println s!"[unit_tests] Evaluated {baseCases.length + Testing.guardPageTests.length} base & guard-page unit tests in {t1 - t0} ms"
    return (← Testing.runTestSuite (baseCases ++ Testing.guardPageTests))
  let stdout ← IO.getStdout
  let t0 ← IO.monoMsNow
  IO.println "[unit_tests] Phase 1/4: Verifying Rust->Lean export codec..."
  stdout.flush
  Testing.reportRustExportCodec
  checkParallelHarnessConformanceIO
  let t1 ← IO.monoMsNow
  IO.println s!"[unit_tests] Phase 1/4 completed in {t1 - t0} ms"
  let jobs ← Testing.Harness.parallelTestJobs
  IO.println s!"[unit_tests] Phases 2-4/4: Evaluating ISA/syscall, whole-ELF, and differential suites across up to {jobs} workers..."
  stdout.flush
  let e2eItems ← Testing.ProcessE2E.buildProcessE2EWorkItemsIO
  let loaderItems ← Testing.ElfLoaderDiff.buildDefaultElfLoaderDiffWorkItemsIO
  let syscallItems ← Testing.SyscallDiff.buildSyscallDiffWorkItemsIO
  let mut allItems : Array (Testing.Harness.ParallelWorkItem FullSuiteSlot) := #[]
  allItems := allItems.push
    { label := "allTestsPart1", priority := 800, run := fun () => pure { batch := { cases := Testing.allTestsPart1 () } } }
  allItems := allItems.push
    { label := "allTestsPart2", priority := 800, run := fun () => pure { batch := { cases := Testing.allTestsPart2 () } } }
  let abortElfRel := "Arm64/Testing/Regression/fixtures/abort_status.elf"
  let abortElfMissing ← Testing.Harness.missingTestFilesIO
    [← Testing.Harness.resolveRepoFilePath abortElfRel]
  let abortIdx := allItems.size
  allItems := allItems.push
    { label := "abort_status.elf", priority := 300, run := fun () => do
        if !abortElfMissing.isEmpty then return { flagOk := true }
        return { flagOk := (← Testing.Process.checkAbortStatusVsQemuIO) } }
  let phase4Start := allItems.size
  for it in e2eItems ++ loaderItems ++ syscallItems do
    allItems := allItems.push
      { label := it.label, priority := it.priority, run := fun () => do return { batch := (← it.run ()) } }
  let slots ← Testing.Harness.runParallelWorkItemsIO allItems
    (fun idx label err =>
      if idx == abortIdx then
        { flagOk := false, batch := { stderr := #[s!"[FAIL] {label}: {err}"] } }
      else
        { batch := { cases := [{ name := s!"{label} (IO error)", check := false }], stderr := #[s!"[FAIL] {label}: {err}"] } })
    (some jobs)
  let replayStderr (idx : Nat) : IO Unit := do
    for line in slots[idx]!.batch.stderr do
      IO.eprintln line
  replayStderr 0
  replayStderr 1
  let baseCases := slots[0]!.batch.cases ++ slots[1]!.batch.cases
  replayStderr abortIdx
  let abortQemuOk := slots[abortIdx]!.flagOk
  let mut phase4Cases : List Testing.TestCase := []
  for idx in [phase4Start:slots.size] do
    let b := slots[idx]!.batch
    for line in b.stdout do
      IO.println line
    for line in b.stderr do
      IO.eprintln line
    phase4Cases := phase4Cases ++ b.cases
  let t4 ← IO.monoMsNow
  IO.println s!"[unit_tests] Phases 2-4/4 ({baseCases.length} base + {1 + phase4Cases.length} process/diff cases, {allItems.size} work items) completed in {t4 - t1} ms (total {t4 - t0} ms)"
  stdout.flush
  let abortQemuName :=
    "ELF Process Semantics: differential qemu-aarch64 vs runElf on static musl abort() (QEMU 134 vs Lean rt_sigprocmask fail-closed; exit(134) match)"
  let extraCases : List Testing.TestCase := [
    if abortElfMissing.isEmpty then { name := abortQemuName, check := abortQemuOk }
    else Testing.Harness.UnitTestCase.skipMissingFiles abortQemuName [abortElfRel]
  ] ++ phase4Cases
  Testing.runTestSuite (baseCases ++ Testing.guardPageTests ++ extraCases)
