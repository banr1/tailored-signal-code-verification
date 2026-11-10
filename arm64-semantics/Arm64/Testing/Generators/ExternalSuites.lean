/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Testing.Harness.TestCase

/-!
# External Simulator and Reference Test Suites

Multi-instruction differential A64 test vectors adapted from external reference suites:
`unicornTestArm64Cases` (Unicorn Engine) and `vixlSimulatorCases` (ARM VIXL simulator).
-/

@[expose] public section

namespace Testing.Generators

open Arm64
open Testing.Harness

def unicornTestArm64Cases : Array IsaTestCase := #[
  makeAsmTestCase
    "Unicorn/test_arm64: add_sub_mov_mrs_style"
    "add x0, x1, x2\nadd x3, x0, #0x123\nsub x4, x3, x1"
    (regs := [(1, 0x1122334455667788#64), (2, 0x0101010101010101#64)])
]

def vixlAluAndLoadStoreCases : Array IsaTestCase := Id.run do
  let mut suite : Array IsaTestCase := #[]

  let boundaryPairs : List (BitVec 64 × BitVec 64) := [
    (0#64, 0#64),
    (1#64, 1#64),
    (0#64, 1#64),
    (0x7fffffffffffffff#64, 1#64),
    (0x8000000000000000#64, 1#64),
    (0xffffffffffffffff#64, 1#64),
    (0x000000007fffffff#64, 1#64),
    (0x0000000080000000#64, 1#64),
    (0xffffffffffffffff#64, 0xffffffffffffffff#64),
    (0x123456789abcdef0#64, 0xfedcba9876543210#64)
  ]
  for ((a, b), idx) in boundaryPairs.zipIdx do
    suite := suite.push (makeAsmTestCase
      s!"VIXL/AddSubFlags64_pair_{idx}"
      "adds x2, x0, x1\nadc x3, x0, x1\nsubs x4, x0, x1\nsbc x5, x0, x1\nadcs x6, x0, x1\nsbcs x7, x0, x1"
      (regs := [(0, a), (1, b)]))
    suite := suite.push (makeAsmTestCase
      s!"VIXL/AddSubFlags32_pair_{idx}"
      "adds w2, w0, w1\nadc w3, w0, w1\nsubs w4, w0, w1\nsbc w5, w0, w1\nadcs w6, w0, w1\nsbcs w7, w0, w1"
      (regs := [(0, a), (1, b)]))

  suite := suite.push (makeAsmTestCase
    "VIXL/AddSubShiftedReg"
    "add x2, x0, x1, lsl #3\nsub x3, x0, x1, lsr #4\nadd x4, x0, x1, asr #7\nadd w5, w0, w1, lsl #5\nsub w6, w0, w1, asr #3"
    (regs := [(0, 0xf000123456789abc#64), (1, 0x87654321fedcba98#64)]))

  suite := suite.push (makeAsmTestCase
    "VIXL/AddSubExtendedReg"
    "add x2, x0, w1, uxtb #2\nadd x3, x0, w1, uxth #1\nadd x4, x0, w1, uxtw #3\nadd x5, x0, w1, sxtb #2\nadd x6, x0, w1, sxth #1\nadd x7, x0, w1, sxtw #3\nsub x8, x0, x1, sxtx #2"
    (regs := [(0, 0x1000000000000000#64), (1, 0xffffffff8080ff80#64)]))

  suite := suite.push (makeAsmTestCase
    "VIXL/LogicalBitmaskImmediates"
    "and x2, x0, #0xff00ff00ff00ff00\norr x3, x0, #0x00ff00ff00ff00ff\neor x4, x0, #0x5555555555555555\nands x5, x0, #0x8000000000000001\nand w6, w0, #0x0f0f0f0f\norr w7, w0, #0xf0f0f0f0"
    (regs := [(0, 0x123456789abcdef1#64)]))

  suite := suite.push (makeAsmTestCase
    "VIXL/LogicalShiftedReg"
    "and x2, x0, x1, lsl #4\nbic x3, x0, x1, lsr #8\norr x4, x0, x1, asr #12\norn x5, x0, x1, ror #16\neor x6, x0, x1, lsl #1\neon x7, x0, x1, lsr #2\nbics x8, x0, x1"
    (regs := [(0, 0xa5a5a5a55a5a5a5a#64), (1, 0x123456789abcdef0#64)]))

  suite := suite.push (makeAsmTestCase
    "VIXL/MoveWideAndPCRel"
    "movz x0, #0x1234, lsl #0\nmovk x0, #0x5678, lsl #16\nmovk x0, #0x9abc, lsl #32\nmovk x0, #0xdef0, lsl #48\nmovn x1, #0x00ff, lsl #16\nadr x2, target\nadrp x3, target\ntarget:\nnop")

  suite := suite.push (makeAsmTestCase
    "VIXL/BitfieldAndExtract"
    "ubfm x2, x0, #8, #23\nsbfm x3, x0, #8, #23\nbfm x4, x0, #16, #31\nextr x5, x0, x1, #12\nextr w6, w0, w1, #7\nlsr x7, x0, #13\nasr x8, x0, #13\nlsl x9, x0, #13"
    (regs := [(0, 0xfedcba9887654321#64), (1, 0x0123456789abcdef#64), (4, 0xffffffffffffffff#64)]))

  let condPairs : List (BitVec 64 × BitVec 64) := [
    (10#64, 20#64),
    (20#64, 10#64),
    (15#64, 15#64),
    (-50#64, 10#64),
    (10#64, -50#64)
  ]
  for ((a, b), idx) in condPairs.zipIdx do
    suite := suite.push (makeAsmTestCase
      s!"VIXL/CondSelectAndCondCompare_{idx}"
      "cmp x0, x1\ncsel x2, x0, x1, eq\ncsinc x3, x0, x1, lt\ncsinv x4, x0, x1, ge\ncsneg x5, x0, x1, hi\nccmp x0, x1, #0b1010, ne\ncsel x6, x0, x1, eq"
      (regs := [(0, a), (1, b)]))

  let oneSourceVals : List (BitVec 64) := [
    0#64, 1#64, 0x8000000000000000#64, 0xffffffffffffffff#64,
    0x0123456789abcdef#64, 0x00000fff12345678#64
  ]
  for (val, idx) in oneSourceVals.zipIdx do
    suite := suite.push (makeAsmTestCase
      s!"VIXL/DataProc1Source_{idx}"
      "rbit x1, x0\nrev16 x2, x0\nrev32 x3, x0\nrev x4, x0\nclz x5, x0\ncls x6, x0\nrbit w7, w0\nrev w8, w0\nclz w9, w0\ncls w10, w0"
      (regs := [(0, val)]))

  let divPairs : List (BitVec 64 × BitVec 64) := [
    (100#64, 7#64),
    (100#64, 0#64),
    (0x8000000000000000#64, 0xffffffffffffffff#64),
    (0xffffffffffffff9c#64, 7#64),
    (0x123456789abcdef0#64, 19#64)
  ]
  for ((a, b), idx) in divPairs.zipIdx do
    suite := suite.push (makeAsmTestCase
      s!"VIXL/DataProc2Source_{idx}"
      "udiv x2, x0, x1\nsdiv x3, x0, x1\nlslv x4, x0, x1\nlsrv x5, x0, x1\nasrv x6, x0, x1\nrorv x7, x0, x1\nudiv w8, w0, w1\nsdiv w9, w0, w1"
      (regs := [(0, a), (1, b)]))

  suite := suite.push (makeAsmTestCase
    "VIXL/DataProc3Source_64x64_and_32x32"
    "madd x3, x0, x1, x2\nmsub x4, x0, x1, x2\nsmaddl x5, w0, w1, x2\nsmsubl x6, w0, w1, x2\nsmulh x7, x0, x1\numaddl x8, w0, w1, x2\numsubl x9, w0, w1, x2\numulh x10, x0, x1"
    (regs := [(0, 0xfedcba9876543210#64), (1, 0x123456789abcdef0#64), (2, 0x0000111122223333#64)]))

  suite := suite.push (makeAsmTestCase
    "VIXL/LoadStoreAllWidthsAndAddressingModes"
    "str x0, [x10, #0]\nstr x1, [x10, #8]\nldrb w2, [x10, #0]\nldrsb x3, [x10, #0]\nldrh w4, [x10, #0]\nldrsh x5, [x10, #0]\nldr w6, [x10, #0]\nldrsw x7, [x10, #0]\nldr x8, [x10, #0]\nstp x0, x1, [x10, #16]!\nldp x11, x12, [x10], #16\nsub x10, x10, #32\nmov x13, #1\nldr x14, [x10, x13, lsl #3]"
    (regs := [(0, 0x8090a0b0c0d0e0f0#64), (1, 0x1122334455667788#64), (10, dataBase)])
    (memWatchU64 := [dataBase, dataBase + 8#64, dataBase + 16#64, dataBase + 24#64]))

  return suite

def vixlBranchCases : Array IsaTestCase := #[
  makeAsmTestCase
    "VIXL/Branches_TBZ_TBNZ_BL_CondBranches"
    "mov x10, x30\nbl helper\nmov x30, x10\ntbz x0, #63, bit63_clear\nmov x2, #111\nb after_tbz\nbit63_clear:\nmov x2, #222\nafter_tbz:\ntbnz x0, #0, bit0_set\nmov x3, #333\nb done\nbit0_set:\nmov x3, #444\nb done\nhelper:\nadd x0, x0, #0x42\nret\ndone:\nnop"
    (regs := [(0, 0x8000000000000001#64)])
]

/-- Combined ARM VIXL simulator ALU, load/store, and branch test cases. -/
def vixlSimulatorCases : Array IsaTestCase :=
  vixlAluAndLoadStoreCases ++ vixlBranchCases

end Testing.Generators
