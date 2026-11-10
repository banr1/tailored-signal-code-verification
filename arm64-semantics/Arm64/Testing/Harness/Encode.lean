/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.ISA.Syntax
public import Arm64.Trusted.ISA.Decode

/-!
# ARM64 (AArch64 A64) AST-to-Binary Encoder (`Arm64.Testing.Harness.Encode`)

- **Layer / Role**: Untrusted `Arm64/Testing/Harness/` ISA validation suite (`Role::Test`, definitions only).
  This module is **not** part of the `Arm64/` Trusted Computing Base: no spec, theorem
  statement, or proof obligation depends on it, so a bug here can only make tests fail, never
  make a proof unsound. Symbols stay in `namespace Arm64` (`Arm64.encode`, `hex32`, …) so call
  sites are unchanged.
- **Purpose & Key Exports**: Encodes `Arm64.Instr` AST instructions into 32-bit A64 machine
  code words (`Option (BitVec 32)`) via `encode` and `encodeInst` (inverting the trusted
  `Arm64.decode`), plus bitmask immediate encoding (`encodeBitMasks`), hex formatting
  (`encodeHex`, `hex32`), batch program assembly helpers (`encodeProg`, `decodeProg`), and
  round-trip helpers (`roundTripWordHex`, `roundTripInstHex`).
- **Consumers**: paired with `Arm64/Testing/Proofs/EncoderDecoder.lean` (via `Common.lean`), which proves
  `encode_of_decode` (`decode w = some i → encode i = some w`), so the encoder serves as a
  readable, machine-checked restatement of the decoder; also used by `Arm64.Testing.Regression.UnitTests`
  (`unit_tests`) and `Arm64.Testing.Generators.TrustedSuite` / `Arm64.Testing.Harness.DifferentialEval`.
- **When to read**: Read only when extending instruction encodings or writing synthetic
  instruction encoder/decoder roundtrip tests; never needed during subroutine proof campaigns.
-/

@[expose] public section

namespace Arm64

namespace Reg

/-- Convert a `Reg` (`gpr idx`, `sp`, `xzr`) to its 5-bit architectural encoding (`0..31`). -/
def toBits (r : Reg) : BitVec 5 :=
  match r with
  | .gpr idx => idx
  | .sp      => 31#5
  | .xzr     => 31#5

/-- Whether `r` is a valid register in an `XZR`/`WZR`-encoded 5-bit field (`GPR 0..30` or `XZR`). -/
def isValidZR (r : Reg) : Bool :=
  match r with
  | .gpr idx => idx != 31#5
  | .xzr     => true
  | .sp      => false

/-- Whether `r` is a valid register in an `SP`/`WSP`-encoded 5-bit field (`GPR 0..30` or `SP`). -/
def isValidSP (r : Reg) : Bool :=
  match r with
  | .gpr idx => idx != 31#5
  | .sp      => true
  | .xzr     => false

end Reg

/-! ## Field encoders (inverse of the trusted `ofBits` decoders)

Moved out of the trusted `Arm64/Trusted/ISA/Syntax.lean`: specs only decode, so only the
encoder and its round-trip proof need these. -/

/-- Encode a `MemWidth` into its 2-bit `size` field. -/
def MemWidth.toBits : MemWidth → BitVec 2
  | .B8  => 0#2
  | .H16 => 1#2
  | .W32 => 2#2
  | .X64 => 3#2

/-- Encode an `ExtendType` into its 3-bit `option` field. -/
def ExtendType.toBits : ExtendType → BitVec 3
  | .UXTB => 0#3
  | .UXTH => 1#3
  | .UXTW => 2#3
  | .UXTX => 3#3
  | .SXTB => 4#3
  | .SXTH => 5#3
  | .SXTW => 6#3
  | .SXTX => 7#3

/-- Encode a `ShiftType` into its 2-bit `shift` field. -/
def ShiftType.toBits : ShiftType → BitVec 2
  | .LSL => 0#2
  | .LSR => 1#2
  | .ASR => 2#2
  | .ROR => 3#2

/-- Encode a `CondCode` into its 4-bit `cond` field. -/
def CondCode.toBits : CondCode → BitVec 4
  | .EQ => 0x0#4
  | .NE => 0x1#4
  | .CS => 0x2#4
  | .CC => 0x3#4
  | .MI => 0x4#4
  | .PL => 0x5#4
  | .VS => 0x6#4
  | .VC => 0x7#4
  | .HI => 0x8#4
  | .LS => 0x9#4
  | .GE => 0xa#4
  | .LT => 0xb#4
  | .GT => 0xc#4
  | .LE => 0xd#4
  | .AL => 0xe#4
  | .NV => 0xf#4

/-- Encode an `AddSubOp` into its `(isSub, setFlags)` (`op30`, `op29`) bits. -/
def AddSubOp.toBits : AddSubOp → Bool × Bool
  | .ADD  => (false, false)
  | .ADDS => (false, true)
  | .SUB  => (true,  false)
  | .SUBS => (true,  true)

/-- Encode a `LogicalOp` into its `(opc, nBit)` fields (`bits[30:29]`, `bit[21]`). -/
def LogicalOp.toBits : LogicalOp → BitVec 2 × Bool
  | .AND  => (0#2, false)
  | .BIC  => (0#2, true)
  | .ORR  => (1#2, false)
  | .ORN  => (1#2, true)
  | .EOR  => (2#2, false)
  | .EON  => (2#2, true)
  | .ANDS => (3#2, false)
  | .BICS => (3#2, true)

/-- Encode a `MoveWideOp` into its 2-bit `opc` field (`bits[30:29]`). -/
def MoveWideOp.toBits : MoveWideOp → BitVec 2
  | .MOVN => 0#2
  | .MOVZ => 2#2
  | .MOVK => 3#2

/-- Encode a `BitfieldOp` into its 2-bit `opc` field (`bits[30:29]`). -/
def BitfieldOp.toBits : BitfieldOp → BitVec 2
  | .SBFM => 0#2
  | .BFM  => 1#2
  | .UBFM => 2#2

/-- Encode a `CondSelectOp` into its `(op30, o2)` bits (`bit[30]`, `bit[10]`). -/
def CondSelectOp.toBits : CondSelectOp → Bool × Bool
  | .CSEL  => (false, false)
  | .CSINC => (false, true)
  | .CSINV => (true,  false)
  | .CSNEG => (true,  true)

/-- Encode a `DataProc1Op` at register width `w` into its 6-bit `opcode` field (`bits[15:10]`). -/
def DataProc1Op.toBits (w : RegWidth) : DataProc1Op → Option (BitVec 6)
  | .RBIT  => some 0#6
  | .REV16 => some 1#6
  | .REV32 => if w == .W64 then some 2#6 else none
  | .REV   => some (if w == .W64 then 3#6 else 2#6)
  | .CLZ   => some 4#6
  | .CLS   => some 5#6

/-- Encode a `DataProc2Op` into its 6-bit `opcode` field (`bits[15:10]`). -/
def DataProc2Op.toBits : DataProc2Op → BitVec 6
  | .UDIV => 2#6
  | .SDIV => 3#6
  | .LSLV => 8#6
  | .LSRV => 9#6
  | .ASRV => 10#6
  | .RORV => 11#6

namespace AesOp

/-- Encode an AES opcode as its 2-bit opcode field. Inverse of `AesOp.ofBits`. -/
def toBits (op : AesOp) : BitVec 2 :=
  match op with
  | .AESE   => 0#2
  | .AESD   => 1#2
  | .AESMC  => 2#2
  | .AESIMC => 3#2

end AesOp

namespace AtomicOp

/-- Encode an LSE atomic op as its 3-bit `opc` field (`SWP` uses `opc = 000` with `o3 = 1`).
    Inverse of `AtomicOp.ofBits` on the non-`SWP` ops. -/
def toBits : AtomicOp → BitVec 3
  | .ADD => 0#3 | .CLR => 1#3 | .EOR => 2#3 | .SET => 3#3
  | .SMAX => 4#3 | .SMIN => 5#3 | .UMAX => 6#3 | .UMIN => 7#3
  | .SWP => 0#3

/-- The `o3` bit of an LSE atomic: set only for `SWP`. -/
def isSwp : AtomicOp → Bool
  | .SWP => true
  | _ => false

end AtomicOp

/-- `sf`-style selector for pair/exclusive-pair element size: `W32 ↦ false`, `X64 ↦ true`,
    other widths are not encodable. -/
def pairSf? : MemWidth → Option Bool
  | .W32 => some false
  | .W64 => some true
  | _ => none

/-- `opcode` field of SIMD `LD1`/`ST1` (multiple structures) for `nregs ∈ {1,2,3,4}`. -/
def ld1MultiOpcode? : Nat → Option (BitVec 4)
  | 1 => some 7#4
  | 2 => some 10#4
  | 3 => some 6#4
  | 4 => some 2#4
  | _ => none

/-- `opcode` field of SIMD `LD2`/`LD3`/`LD4`/`ST2`/`ST3`/`ST4` (multiple structures) for `selem ∈ {2,3,4}`. -/
def ldMultiOpcode? : Nat → Option (BitVec 4)
  | 2 => some 8#4
  | 3 => some 4#4
  | 4 => some 0#4
  | _ => none

/-- Count trailing zeros of a non-zero 64-bit vector (`0..63`) as a `BitVec 6`. -/
def ctz64 (x : BitVec 64) : BitVec 6 :=
  let b5 := (x &&& 0x00000000ffffffff#64) == 0#64
  let x  := if b5 then x >>> 32#64 else x
  let b4 := (x &&& 0x000000000000ffff#64) == 0#64
  let x  := if b4 then x >>> 16#64 else x
  let b3 := (x &&& 0x00000000000000ff#64) == 0#64
  let x  := if b3 then x >>> 8#64  else x
  let b2 := (x &&& 0x000000000000000f#64) == 0#64
  let x  := if b2 then x >>> 4#64  else x
  let b1 := (x &&& 0x0000000000000003#64) == 0#64
  let x  := if b1 then x >>> 2#64  else x
  let b0 := (x &&& 0x0000000000000001#64) == 0#64
  (if b5 then 32#6 else 0#6) |||
  (if b4 then 16#6 else 0#6) |||
  (if b3 then 8#6  else 0#6) |||
  (if b2 then 4#6  else 0#6) |||
  (if b1 then 2#6  else 0#6) |||
  (if b0 then 1#6  else 0#6)

/-- Population count (number of 1-bits, `1..63`) of a 64-bit vector as a `BitVec 6`. -/
def popcount64 (x : BitVec 64) : BitVec 6 :=
  let x := x - ((x >>> 1#64) &&& 0x5555555555555555#64)
  let x := (x &&& 0x3333333333333333#64) + ((x >>> 2#64) &&& 0x3333333333333333#64)
  let x := (x + (x >>> 4#64)) &&& 0x0f0f0f0f0f0f0f0f#64
  let x := x + (x >>> 8#64)
  let x := x + (x >>> 16#64)
  let x := x + (x >>> 32#64)
  x.extractLsb' 0 6

/-- Recover the `levels` mask (`esize - 1`) of a 64-bit replicated bitmask by finding the
    smallest power-of-two element width at which `mask` is periodic. Inverse of
    `decodeBitMasksLevels`. -/
def encodeBitMasksLevels (mask : BitVec 64) : BitVec 6 :=
  if (mask >>> 2#64)  == (mask &&& 0x3fffffffffffffff#64) then 1#6
  else if (mask >>> 4#64)  == (mask &&& 0x0fffffffffffffff#64) then 3#6
  else if (mask >>> 8#64)  == (mask &&& 0x00ffffffffffffff#64) then 7#6
  else if (mask >>> 16#64) == (mask &&& 0x0000ffffffffffff#64) then 15#6
  else if (mask >>> 32#64) == (mask &&& 0x00000000ffffffff#64) then 31#6
  else 63#6

/-- Recover the `N` bit of a 64-bit replicated bitmask (`true` iff the element width is 64). -/
def encodeBitMasksImmN (mask : BitVec 64) : Bool :=
  encodeBitMasksLevels mask == 63#6

/-- Recover the `imms` field of a 64-bit replicated bitmask: the element-width prefix
    (`0b0`, `0b10`, `0b110`, ...) OR'd with `S = popcount(element) - 1`. -/
def encodeBitMasksImms (mask : BitVec 64) : BitVec 6 :=
  let levels := encodeBitMasksLevels mask
  let elemMask : BitVec 64 := (2#64 <<< levels.zeroExtend 64) - 1#64
  let elem : BitVec 64 := mask &&& elemMask
  let s : BitVec 6 := popcount64 elem - 1#6
  let immsPrefix : BitVec 6 :=
    if levels == 63#6 || levels == 31#6 then 0b000000#6
    else if levels == 15#6 then 0b100000#6
    else if levels == 7#6  then 0b110000#6
    else if levels == 3#6  then 0b111000#6
    else 0b111100#6
  immsPrefix ||| (s &&& levels)

/-- Recover the `immr` (rotate) field of a 64-bit replicated bitmask, by locating the start
    of the run of ones inside one element. -/
def encodeBitMasksImmr (mask : BitVec 64) : BitVec 6 :=
  let levels := encodeBitMasksLevels mask
  let elemMask : BitVec 64 := (2#64 <<< levels.zeroExtend 64) - 1#64
  let elem : BitVec 64 := mask &&& elemMask
  let onesCount : BitVec 6 := popcount64 elem
  let s : BitVec 6 := onesCount - 1#6
  let elemOnes : BitVec 64 := (2#64 <<< s.zeroExtend 64) - 1#64
  let r : BitVec 6 :=
    if elem == elemOnes then 0#6
    else if !(elem.getLsbD 0) then (levels + 1#6) - ctz64 elem
    else onesCount - ctz64 (~~~elem)
  r &&& levels

/-- Encode a 64-bit replicated bitmask into `(immN, imms, immr)` for width `w`.
    Computes the unique `(immN, imms, immr)` in O(1) bitvector arithmetic and verifies
    that `decodeBitMasks immN imms immr == some mask`. -/
def encodeBitMasks (w : RegWidth) (mask : BitVec 64) : Option (Bool × BitVec 6 × BitVec 6) :=
  let immN := encodeBitMasksImmN mask
  let imms := encodeBitMasksImms mask
  let immr := encodeBitMasksImmr mask
  if (w == .W32 && immN) then
    none
  else if decodeBitMasks immN imms immr == some mask then
    some (immN, imms, immr)
  else
    none

/-!
## Bit-Level Instruction Word Packers (`pack*`)

Each `pack*` function constructs a 32-bit machine instruction word exclusively from
fixed-width `BitVec` and `Bool` parameters, matching the bit layout of `Arm64.decode`.
-/

/-- Assemble the 32-bit `NOP` (`HINT #0`) instruction word. -/
def packNop : BitVec 32 :=
  0xd503201f#32

/-- Assemble the 32-bit `SVC #imm16` (`isHalt = false`, `0xd4000001`) or `BRK #imm16` (`isHalt = true`, `0xd4200000`) instruction word. -/
def packSystem (isHalt : Bool) (imm : BitVec 16) : BitVec 32 :=
  (if isHalt then 0xd4200000#32 else 0xd4000001#32) |||
  (imm.zeroExtend 32 <<< 5)

/-- Assemble the 32-bit `ADR`/`ADRP` PC-relative address computation instruction word. -/
def packAdr (page : Bool) (immlo : BitVec 2) (immhi : BitVec 19) (rd : BitVec 5) : BitVec 32 :=
  (if page then 0x90000000#32 else 0x10000000#32) |||
  (immlo.zeroExtend 32 <<< 29) |||
  (immhi.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit add/subtract (immediate) instruction word. -/
def packAddSubImm (sf op30 op29 sh : Bool) (imm12 : BitVec 12) (rn rd : BitVec 5) : BitVec 32 :=
  (if sf then 0x80000000#32 else 0#32) |||
  (if op30 then 0x40000000#32 else 0#32) |||
  (if op29 then 0x20000000#32 else 0#32) |||
  0x11000000#32 |||
  (if sh then 0x00400000#32 else 0#32) |||
  (imm12.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit logical (immediate), with the bitmask given as `(immN, immr, imms)` instruction word. -/
def packLogicalImm (sf : Bool) (opc : BitVec 2) (immN : Bool) (immr imms : BitVec 6) (rn rd : BitVec 5) : BitVec 32 :=
  (if sf then 0x80000000#32 else 0#32) |||
  (opc.zeroExtend 32 <<< 29) |||
  0x12000000#32 |||
  (if immN then 0x00400000#32 else 0#32) |||
  (immr.zeroExtend 32 <<< 16) |||
  (imms.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit `MOVN`/`MOVZ`/`MOVK` move wide (immediate) instruction word. -/
def packMoveWide (sf : Bool) (opc hwBits : BitVec 2) (imm16 : BitVec 16) (rd : BitVec 5) : BitVec 32 :=
  (if sf then 0x80000000#32 else 0#32) |||
  (opc.zeroExtend 32 <<< 29) |||
  0x12800000#32 |||
  (hwBits.zeroExtend 32 <<< 21) |||
  (imm16.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit `SBFM`/`BFM`/`UBFM` bitfield move instruction word. -/
def packBitfield (sf : Bool) (opc : BitVec 2) (immr imms : BitVec 6) (rn rd : BitVec 5) : BitVec 32 :=
  (if sf then 0x80000000#32 else 0#32) |||
  (opc.zeroExtend 32 <<< 29) |||
  0x13000000#32 |||
  (if sf then 0x00400000#32 else 0#32) |||
  (immr.zeroExtend 32 <<< 16) |||
  (imms.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit `EXTR` extract register from a register pair instruction word. -/
def packExtr (sf : Bool) (rm : BitVec 5) (lsb : BitVec 6) (rn rd : BitVec 5) : BitVec 32 :=
  (if sf then 0x80000000#32 else 0#32) |||
  0x13800000#32 |||
  (if sf then 0x00400000#32 else 0#32) |||
  (rm.zeroExtend 32 <<< 16) |||
  (lsb.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit `B`/`BL` unconditional PC-relative branch instruction word. -/
def packB (link : Bool) (imm26 : BitVec 26) : BitVec 32 :=
  (if link then 0x94000000#32 else 0x14000000#32) |||
  imm26.zeroExtend 32

/-- Assemble the 32-bit `CBZ`/`CBNZ` compare and branch on zero instruction word. -/
def packCbz (sf isNonZero : Bool) (imm19 : BitVec 19) (rt : BitVec 5) : BitVec 32 :=
  (if sf then 0x80000000#32 else 0#32) |||
  0x34000000#32 |||
  (if isNonZero then 0x01000000#32 else 0#32) |||
  (imm19.zeroExtend 32 <<< 5) |||
  rt.zeroExtend 32

/-- Assemble the 32-bit `TBZ`/`TBNZ` test bit and branch instruction word. -/
def packTbz (b5 isNonZero : Bool) (b40 : BitVec 5) (imm14 : BitVec 14) (rt : BitVec 5) : BitVec 32 :=
  (if b5 then 0x80000000#32 else 0#32) |||
  0x36000000#32 |||
  (if isNonZero then 0x01000000#32 else 0#32) |||
  (b40.zeroExtend 32 <<< 19) |||
  (imm14.zeroExtend 32 <<< 5) |||
  rt.zeroExtend 32

/-- Assemble the 32-bit `B.<cond>` conditional PC-relative branch instruction word. -/
def packBCond (imm19 : BitVec 19) (cond : BitVec 4) : BitVec 32 :=
  0x54000000#32 |||
  (imm19.zeroExtend 32 <<< 5) |||
  cond.zeroExtend 32

/-- Assemble the 32-bit `BR`/`BLR`/`RET` unconditional branch to register instruction word. -/
def packBr (opc : BitVec 2) (rn : BitVec 5) : BitVec 32 :=
  0xd61f0000#32 |||
  (opc.zeroExtend 32 <<< 21) |||
  (rn.zeroExtend 32 <<< 5)

/-- Assemble the 32-bit logical (shifted register) instruction word. -/
def packLogicalReg (sf : Bool) (opc shift : BitVec 2) (nBit : Bool) (rm : BitVec 5) (imm6 : BitVec 6) (rn rd : BitVec 5) : BitVec 32 :=
  (if sf then 0x80000000#32 else 0#32) |||
  (opc.zeroExtend 32 <<< 29) |||
  0x0a000000#32 |||
  (shift.zeroExtend 32 <<< 22) |||
  (if nBit then 0x00200000#32 else 0#32) |||
  (rm.zeroExtend 32 <<< 16) |||
  (imm6.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit add/subtract (shifted register) instruction word. -/
def packAddSubReg (sf op30 op29 : Bool) (shift : BitVec 2) (rm : BitVec 5) (imm6 : BitVec 6) (rn rd : BitVec 5) : BitVec 32 :=
  (if sf then 0x80000000#32 else 0#32) |||
  (if op30 then 0x40000000#32 else 0#32) |||
  (if op29 then 0x20000000#32 else 0#32) |||
  0x0b000000#32 |||
  (shift.zeroExtend 32 <<< 22) |||
  (rm.zeroExtend 32 <<< 16) |||
  (imm6.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit add/subtract (extended register) instruction word. -/
def packAddSubExt (sf op30 op29 : Bool) (rm : BitVec 5) (ext imm3 : BitVec 3) (rn rd : BitVec 5) : BitVec 32 :=
  (if sf then 0x80000000#32 else 0#32) |||
  (if op30 then 0x40000000#32 else 0#32) |||
  (if op29 then 0x20000000#32 else 0#32) |||
  0x0b200000#32 |||
  (rm.zeroExtend 32 <<< 16) |||
  (ext.zeroExtend 32 <<< 13) |||
  (imm3.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit `ADC`/`ADCS`/`SBC`/`SBCS` add/subtract with carry instruction word. -/
def packAddSubCarry (sf op30 op29 : Bool) (rm rn rd : BitVec 5) : BitVec 32 :=
  (if sf then 0x80000000#32 else 0#32) |||
  (if op30 then 0x40000000#32 else 0#32) |||
  (if op29 then 0x20000000#32 else 0#32) |||
  0x1a000000#32 |||
  (rm.zeroExtend 32 <<< 16) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit `CCMP`/`CCMN` conditional compare (register or immediate) instruction word. -/
def packCondCompare (sf isSub isImm : Bool) (rmOrImm : BitVec 5) (cond : BitVec 4) (rn : BitVec 5) (nzcv : BitVec 4) : BitVec 32 :=
  (if sf then 0x80000000#32 else 0#32) |||
  (if isSub then 0x40000000#32 else 0#32) |||
  0x3a400000#32 |||
  (rmOrImm.zeroExtend 32 <<< 16) |||
  (cond.zeroExtend 32 <<< 12) |||
  (if isImm then 0x00000800#32 else 0#32) |||
  (rn.zeroExtend 32 <<< 5) |||
  nzcv.zeroExtend 32

/-- Assemble the 32-bit `CSEL`/`CSINC`/`CSINV`/`CSNEG` conditional select instruction word. -/
def packCondSelect (sf op30 o2 : Bool) (rm : BitVec 5) (cond : BitVec 4) (rn rd : BitVec 5) : BitVec 32 :=
  (if sf then 0x80000000#32 else 0#32) |||
  (if op30 then 0x40000000#32 else 0#32) |||
  0x1a800000#32 |||
  (rm.zeroExtend 32 <<< 16) |||
  (cond.zeroExtend 32 <<< 12) |||
  (if o2 then 0x00000400#32 else 0#32) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit 1-source data processing (`RBIT`, `REV*`, `CLZ`, `CLS`) instruction word. -/
def packDataProc1 (sf : Bool) (opcode : BitVec 6) (rn rd : BitVec 5) : BitVec 32 :=
  (if sf then 0xdac00000#32 else 0x5ac00000#32) |||
  (opcode.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit 2-source data processing (`UDIV`, `SDIV`, `LSLV`, `LSRV`, `ASRV`, `RORV`) instruction word. -/
def packDataProc2 (sf : Bool) (rm : BitVec 5) (opcode : BitVec 6) (rn rd : BitVec 5) : BitVec 32 :=
  (if sf then 0x9ac00000#32 else 0x1ac00000#32) |||
  (rm.zeroExtend 32 <<< 16) |||
  (opcode.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit 3-source data processing (`MADD`, `MSUB`, `SMADDL`, ..., `UMULH`) instruction word. -/
def packDataProc3 (sf : Bool) (op31 : BitVec 3) (rm : BitVec 5) (o0 : Bool) (ra rn rd : BitVec 5) : BitVec 32 :=
  (if sf then 0x80000000#32 else 0#32) |||
  0x1b000000#32 |||
  (op31.zeroExtend 32 <<< 21) |||
  (rm.zeroExtend 32 <<< 16) |||
  (if o0 then 0x00008000#32 else 0#32) |||
  (ra.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit `LDP`/`STP`/`LDPSW` load/store pair of registers instruction word. -/
def packLoadStorePair (opc modeBits : BitVec 2) (isLoad : Bool) (imm7 : BitVec 7) (rt2 rn rt1 : BitVec 5) : BitVec 32 :=
  (opc.zeroExtend 32 <<< 30) |||
  0x28000000#32 |||
  (modeBits.zeroExtend 32 <<< 23) |||
  (if isLoad then 0x00400000#32 else 0#32) |||
  (imm7.zeroExtend 32 <<< 15) |||
  (rt2.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rt1.zeroExtend 32

/-- Assemble the 32-bit load/store register with a scaled unsigned 12-bit immediate offset instruction word. -/
def packLoadStoreUImm (sizeBits opc : BitVec 2) (imm12 : BitVec 12) (rn rt : BitVec 5) : BitVec 32 :=
  (sizeBits.zeroExtend 32 <<< 30) |||
  0x39000000#32 |||
  (opc.zeroExtend 32 <<< 22) |||
  (imm12.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rt.zeroExtend 32

/-- Assemble the 32-bit load/store register with an unscaled signed 9-bit immediate (`LDUR`/`STUR`, pre- and post-index) instruction word. -/
def packLoadStoreSimm9 (sizeBits opc mode2 : BitVec 2) (imm9 : BitVec 9) (rn rt : BitVec 5) : BitVec 32 :=
  (sizeBits.zeroExtend 32 <<< 30) |||
  0x38000000#32 |||
  (opc.zeroExtend 32 <<< 22) |||
  (imm9.zeroExtend 32 <<< 12) |||
  (mode2.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rt.zeroExtend 32

/-- Assemble the 32-bit load/store register with a register offset (`[Xn, Xm, <ext> #amount]`) instruction word. -/
def packLoadStoreRegOff (sizeBits opc : BitVec 2) (rm : BitVec 5) (ext : BitVec 3) (sBit : Bool) (rn rt : BitVec 5) : BitVec 32 :=
  (sizeBits.zeroExtend 32 <<< 30) |||
  0x38200800#32 |||
  (opc.zeroExtend 32 <<< 22) |||
  (rm.zeroExtend 32 <<< 16) |||
  (ext.zeroExtend 32 <<< 13) |||
  (if sBit then 0x00001000#32 else 0#32) |||
  (rn.zeroExtend 32 <<< 5) |||
  rt.zeroExtend 32

/-- Assemble the 32-bit `LDR`/`LDRSW` (literal, PC-relative) instruction word. -/
def packLdrLit (opc : BitVec 2) (imm19 : BitVec 19) (rt : BitVec 5) : BitVec 32 :=
  (opc.zeroExtend 32 <<< 30) |||
  0x18000000#32 |||
  (imm19.zeroExtend 32 <<< 5) |||
  rt.zeroExtend 32

/-- Assemble the 32-bit `LDAR`/`LDARB`/`LDARH` and `STLR`/`STLRB`/`STLRH` load-acquire / store-release instruction word. -/
def packLdarStlr (sizeBits : BitVec 2) (isLoad : Bool) (rn rt : BitVec 5) : BitVec 32 :=
  (sizeBits.zeroExtend 32 <<< 30) |||
  0x089ffc00#32 |||
  (if isLoad then 0x00400000#32 else 0#32) |||
  (rn.zeroExtend 32 <<< 5) |||
  rt.zeroExtend 32

/-- Assemble the 32-bit `LDXR`/`LDAXR` (and `B`/`H` forms) load-exclusive instruction word
    (`Rs` and `Rt2` are should-be-one `11111`). -/
def packLdxr (sizeBits : BitVec 2) (acq : Bool) (rn rt : BitVec 5) : BitVec 32 :=
  (sizeBits.zeroExtend 32 <<< 30) |||
  0x085f7c00#32 |||
  (if acq then 0x00008000#32 else 0#32) |||
  (rn.zeroExtend 32 <<< 5) |||
  rt.zeroExtend 32

/-- Assemble the 32-bit `STXR`/`STLXR` (and `B`/`H` forms) store-exclusive instruction word
    (`Rt2` is should-be-one `11111`). -/
def packStxr (sizeBits : BitVec 2) (rel : Bool) (rs rn rt : BitVec 5) : BitVec 32 :=
  (sizeBits.zeroExtend 32 <<< 30) |||
  0x08007c00#32 |||
  (rs.zeroExtend 32 <<< 16) |||
  (if rel then 0x00008000#32 else 0#32) |||
  (rn.zeroExtend 32 <<< 5) |||
  rt.zeroExtend 32

/-- Assemble the 32-bit `HINT #imm7` instruction word. -/
def packHint (imm : BitVec 7) : BitVec 32 :=
  0xd503201f#32 ||| (imm.zeroExtend 32 <<< 5)

/-- Assemble the 32-bit `UDF #imm16` instruction word. -/
def packUdf (imm : BitVec 16) : BitVec 32 :=
  imm.zeroExtend 32

/-- Assemble the 32-bit `DC ZVA, Xt` instruction word. -/
def packDcZva (rt : BitVec 5) : BitVec 32 :=
  0xd50b7420#32 ||| rt.zeroExtend 32

/-- Assemble the 32-bit `CRC32{B,H,W,X}` / `CRC32C{B,H,W,X}` instruction word. -/
def packCrc32 (sf c : Bool) (sz : BitVec 2) (rm rn rd : BitVec 5) : BitVec 32 :=
  (if sf then 0x80000000#32 else 0#32) |||
  0x1ac04000#32 |||
  (rm.zeroExtend 32 <<< 16) |||
  (if c then 0x00001000#32 else 0#32) |||
  (sz.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit LSE atomic memory operation word (`LD<OP>`, `SWP`, `LDAPR`):
    `size:111:0:00:A:R:1:Rs:o3:opc:00:Rn:Rt`. -/
def packLse (sizeBits : BitVec 2) (acq rel : Bool) (rs : BitVec 5) (o3 : Bool) (opc : BitVec 3)
    (rn rt : BitVec 5) : BitVec 32 :=
  (sizeBits.zeroExtend 32 <<< 30) |||
  0x38200000#32 |||
  (if acq then 0x00800000#32 else 0#32) |||
  (if rel then 0x00400000#32 else 0#32) |||
  (rs.zeroExtend 32 <<< 16) |||
  (if o3 then 0x00008000#32 else 0#32) |||
  (opc.zeroExtend 32 <<< 12) |||
  (rn.zeroExtend 32 <<< 5) |||
  rt.zeroExtend 32

/-- Assemble the 32-bit RCpc unscaled `STLUR*` / `LDAPUR*` / `LDAPURS*` word. -/
def packRcpcUnscaled (sizeBits opc : BitVec 2) (imm9 : BitVec 9) (rn rt : BitVec 5) : BitVec 32 :=
  (sizeBits.zeroExtend 32 <<< 30) |||
  0x19000000#32 |||
  (opc.zeroExtend 32 <<< 22) |||
  (imm9.zeroExtend 32 <<< 12) |||
  (rn.zeroExtend 32 <<< 5) |||
  rt.zeroExtend 32

/-- Assemble the 32-bit SIMD/FP `LDR St/Dt/Qt, label` (literal) word. -/
def packSimdLdrLit (opc : BitVec 2) (imm19 : BitVec 19) (vt : BitVec 5) : BitVec 32 :=
  (opc.zeroExtend 32 <<< 30) |||
  0x1c000000#32 |||
  (imm19.zeroExtend 32 <<< 5) |||
  vt.zeroExtend 32

/-- Assemble the 32-bit exclusive-pair / compare-and-swap word
    `sizeBits:001000:o2:L:o1:Rs:o0:Rt2:Rn:Rt` (shared by `LDXP`, `STXP`, `CAS`, `CASP`). -/
def packExclPair (sizeBits : BitVec 2) (o2 l o1 : Bool) (rs : BitVec 5) (o0 : Bool)
    (rt2 rn rt : BitVec 5) : BitVec 32 :=
  (sizeBits.zeroExtend 32 <<< 30) |||
  0x08000000#32 |||
  (if o2 then 0x00800000#32 else 0#32) |||
  (if l then 0x00400000#32 else 0#32) |||
  (if o1 then 0x00200000#32 else 0#32) |||
  (rs.zeroExtend 32 <<< 16) |||
  (if o0 then 0x00008000#32 else 0#32) |||
  (rt2.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rt.zeroExtend 32

/-- Assemble the 32-bit SIMD `LD1`/`ST1` (multiple structures) / `LD1R` word
    `0:Q:0011:0:op:post:L:R:Rm:opcode:S:size:Rn:Rt` (`base` carries bits 29..24 and `R`). -/
def packSimdLdStStruct (base : BitVec 32) (q post isLoad : Bool) (rm : BitVec 5) (opcode : BitVec 4)
    (size : BitVec 2) (rn vt : BitVec 5) : BitVec 32 :=
  base |||
  (if q then 0x40000000#32 else 0#32) |||
  (if post then 0x00800000#32 else 0#32) |||
  (if isLoad then 0x00400000#32 else 0#32) |||
  (rm.zeroExtend 32 <<< 16) |||
  (opcode.zeroExtend 32 <<< 12) |||
  (size.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  vt.zeroExtend 32

/-- Assemble the 32-bit SIMD `TBL`/`TBX` word. -/
def packSimdTbl (q : Bool) (rm : BitVec 5) (len : BitVec 2) (isTbx : Bool) (rn rd : BitVec 5) : BitVec 32 :=
  (if q then 0x40000000#32 else 0#32) |||
  0x0e000000#32 |||
  (rm.zeroExtend 32 <<< 16) |||
  (len.zeroExtend 32 <<< 13) |||
  (if isTbx then 0x00001000#32 else 0#32) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit SIMD scalar `ADDP Dd, Vn.2D` word. -/
def packSimdAddpScalar (rn rd : BitVec 5) : BitVec 32 :=
  0x5ef1b800#32 ||| (rn.zeroExtend 32 <<< 5) ||| rd.zeroExtend 32

/-- Assemble the 32-bit SIMD `PMULL`/`PMULL2` word `0:Q:0:01110:size:1:Rm:1110:00:Rn:Rd`
    (`size = 00` when `is64 = false`, `size = 11` when `is64 = true`). -/
def packSimdPmull (q is64 : Bool) (rm rn rd : BitVec 5) : BitVec 32 :=
  (if q then 0x40000000#32 else 0#32) |||
  0x0e20e000#32 |||
  (if is64 then 0x00c00000#32 else 0#32) |||
  (rm.zeroExtend 32 <<< 16) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit `FEAT_SHA1`/`FEAT_SHA256` 2-register SHA word `01011110:00101000:0:opcode:10:Rn:Rd`. -/
def packCryptoSha2Reg (opcode rn rd : BitVec 5) : BitVec 32 :=
  0x5e280800#32 |||
  (opcode.zeroExtend 32 <<< 12) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit `FEAT_SHA1`/`FEAT_SHA256` 3-register SHA word `01011110:000:Rm:0:opcode:00:Rn:Rd`. -/
def packCryptoSha3Reg (opcode : BitVec 3) (rm rn rd : BitVec 5) : BitVec 32 :=
  0x5e000000#32 |||
  (rm.zeroExtend 32 <<< 16) |||
  (opcode.zeroExtend 32 <<< 12) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit `SHA512SU0` word `11001110:11000000:100000:Rn:Rd`. -/
def packCryptoSha512Reg2 (rn rd : BitVec 5) : BitVec 32 :=
  0xcec08000#32 |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit `FEAT_SHA512`/`FEAT_SHA3` 3-register word `11001110:011:Rm:1:000:opcode:Rn:Rd`. -/
def packCryptoSha512Reg3 (opcode : BitVec 2) (rm rn rd : BitVec 5) : BitVec 32 :=
  0xce608000#32 |||
  (rm.zeroExtend 32 <<< 16) |||
  (opcode.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit `FEAT_SHA3` 4-register (`EOR3`/`BCAX`) word `11001110:00:isBcax:Rm:0:Ra:Rn:Rd`. -/
def packCryptoSha3FourReg (isBcax : Bool) (rm ra rn rd : BitVec 5) : BitVec 32 :=
  0xce000000#32 |||
  (if isBcax then 0x00200000#32 else 0#32) |||
  (rm.zeroExtend 32 <<< 16) |||
  (ra.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit `XAR` word `11001110:100:Rm:imm6:Rn:Rd`. -/
def packCryptoXar (rm : BitVec 5) (imm6 : BitVec 6) (rn rd : BitVec 5) : BitVec 32 :=
  0xce800000#32 |||
  (rm.zeroExtend 32 <<< 16) |||
  (imm6.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit `MRS`/`MSR` system register move instruction word. -/
def packSysReg (isRead : Bool) (sysreg : BitVec 15) (rt : BitVec 5) : BitVec 32 :=
  0xd5100000#32 |||
  (if isRead then 0x00200000#32 else 0#32) |||
  (sysreg.zeroExtend 32 <<< 5) |||
  rt.zeroExtend 32

/-- Assemble the 32-bit `DMB`/`DSB`/`ISB`/`CLREX` memory barrier instruction word. -/
def packBarrier (crm : BitVec 4) (op2 : BitVec 3) : BitVec 32 :=
  0xd503301f#32 |||
  (crm.zeroExtend 32 <<< 8) |||
  (op2.zeroExtend 32 <<< 5)

/-- Assemble the 32-bit SIMD/FP `LDP`/`STP` load/store pair instruction word. -/
def packSimdLoadStorePair (opc modeBits : BitVec 2) (isLoad : Bool) (imm7 : BitVec 7) (vt2 rn vt1 : BitVec 5) : BitVec 32 :=
  (opc.zeroExtend 32 <<< 30) |||
  0x2c000000#32 |||
  (modeBits.zeroExtend 32 <<< 23) |||
  (if isLoad then 0x00400000#32 else 0#32) |||
  (imm7.zeroExtend 32 <<< 15) |||
  (vt2.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  vt1.zeroExtend 32

/-- Assemble the 32-bit SIMD/FP load/store register with a scaled unsigned 12-bit immediate offset instruction word. -/
def packSimdLoadStoreUImm (sizeBits opc : BitVec 2) (imm12 : BitVec 12) (rn vt : BitVec 5) : BitVec 32 :=
  (sizeBits.zeroExtend 32 <<< 30) |||
  0x3d000000#32 |||
  (opc.zeroExtend 32 <<< 22) |||
  (imm12.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  vt.zeroExtend 32

/-- Assemble the 32-bit SIMD/FP load/store register with an unscaled signed 9-bit immediate (`LDUR`/`STUR`, pre- and post-index) instruction word. -/
def packSimdLoadStoreSimm9 (sizeBits opc mode2 : BitVec 2) (imm9 : BitVec 9) (rn vt : BitVec 5) : BitVec 32 :=
  (sizeBits.zeroExtend 32 <<< 30) |||
  0x3c000000#32 |||
  (opc.zeroExtend 32 <<< 22) |||
  (imm9.zeroExtend 32 <<< 12) |||
  (mode2.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  vt.zeroExtend 32

/-- Assemble the 32-bit SIMD/FP load/store register with a register offset instruction word. -/
def packSimdLoadStoreRegOff (sizeBits opc : BitVec 2) (rm : BitVec 5) (ext : BitVec 3) (sBit : Bool) (rn vt : BitVec 5) : BitVec 32 :=
  (sizeBits.zeroExtend 32 <<< 30) |||
  0x3c200800#32 |||
  (opc.zeroExtend 32 <<< 22) |||
  (rm.zeroExtend 32 <<< 16) |||
  (ext.zeroExtend 32 <<< 13) |||
  (if sBit then 0x00001000#32 else 0#32) |||
  (rn.zeroExtend 32 <<< 5) |||
  vt.zeroExtend 32

/-- Assemble the 32-bit `ST1 { Vt.<T> }[index], [Xn], <imm|Xm>` single-structure post-indexed store instruction word. -/
def packSt1SinglePost (q : Bool) (rm : BitVec 5) (opcode : BitVec 3) (sBit : Bool) (size : BitVec 2) (rn vt : BitVec 5) : BitVec 32 :=
  (if q then 0x40000000#32 else 0#32) |||
  0x0d800000#32 |||
  (rm.zeroExtend 32 <<< 16) |||
  (opcode.zeroExtend 32 <<< 13) |||
  (if sBit then 0x00001000#32 else 0#32) |||
  (size.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  vt.zeroExtend 32

/-- Assemble the 32-bit `LD1`/`ST1 { Vt.<T> }[index], [Xn] (, <imm|Xm>)` single-structure lane load/store instruction word. -/
def packSimdLdSt1Single (isLoad q postIdx : Bool) (rm : BitVec 5) (opcode : BitVec 3) (sBit : Bool) (size : BitVec 2) (rn vt : BitVec 5) : BitVec 32 :=
  (if q then 0x40000000#32 else 0#32) |||
  0x0d000000#32 |||
  (if postIdx then 0x00800000#32 else 0#32) |||
  (if isLoad then 0x00400000#32 else 0#32) |||
  (rm.zeroExtend 32 <<< 16) |||
  (opcode.zeroExtend 32 <<< 13) |||
  (if sBit then 0x00001000#32 else 0#32) |||
  (size.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  vt.zeroExtend 32

/-- Assemble the 32-bit `AESE`/`AESD`/`AESMC`/`AESIMC` AES cryptographic operation instruction word. -/
def packAes (op : BitVec 2) (rn rd : BitVec 5) : BitVec 32 :=
  0x4e284800#32 |||
  (op.zeroExtend 32 <<< 12) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit `FMOV` between a GPR and a SIMD/FP scalar or vector lane instruction word. -/
def packFmovGprVec (sf : Bool) (ftype rmode : BitVec 2) (opcode : BitVec 3) (rn rd : BitVec 5) : BitVec 32 :=
  (if sf then 0x80000000#32 else 0#32) |||
  0x1e200000#32 |||
  (ftype.zeroExtend 32 <<< 22) |||
  (rmode.zeroExtend 32 <<< 19) |||
  (opcode.zeroExtend 32 <<< 16) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit SIMD modified immediate (`MOVI`/`MVNI`) and SIMD shift by immediate (`SHL`, `USHLL`, `USHR`) instruction word. -/
def packSimdImmShift (q op : Bool) (immh : BitVec 4) (immb : BitVec 3) (opcode : BitVec 5) (rn rd : BitVec 5) : BitVec 32 :=
  (if q then 0x40000000#32 else 0#32) |||
  (if op then 0x20000000#32 else 0#32) |||
  0x0f000400#32 |||
  (immh.zeroExtend 32 <<< 19) |||
  (immb.zeroExtend 32 <<< 16) |||
  (opcode.zeroExtend 32 <<< 11) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit SIMD copy (`DUP`, `INS`, `UMOV`, `MOV`) instruction word. -/
def packSimdInsDup (q op : Bool) (imm5 : BitVec 5) (imm4 : BitVec 4) (rn rd : BitVec 5) : BitVec 32 :=
  (if q then 0x40000000#32 else 0#32) |||
  (if op then 0x20000000#32 else 0#32) |||
  0x0e000400#32 |||
  (imm5.zeroExtend 32 <<< 16) |||
  (imm4.zeroExtend 32 <<< 11) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit scalar `DUP <V><d>, <Vn>.<Ts>[<index>]` instruction word. -/
def packSimdDupScalar (imm5 : BitVec 5) (rn rd : BitVec 5) : BitVec 32 :=
  0x5e000400#32 |||
  (imm5.zeroExtend 32 <<< 16) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit SIMD three-register-same vector operation instruction word. -/
def packSimdThreeSame (q u : Bool) (size : BitVec 2) (rm opcode rn rd : BitVec 5) : BitVec 32 :=
  (if q then 0x40000000#32 else 0#32) |||
  (if u then 0x20000000#32 else 0#32) |||
  0x0e200400#32 |||
  (size.zeroExtend 32 <<< 22) |||
  (rm.zeroExtend 32 <<< 16) |||
  (opcode.zeroExtend 32 <<< 11) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit SIMD three-register-different vector operation (`SMULL`, `UMULL`, `SMLAL`, `UMLAL`, `ADDHN`, `UADDW`, ...) instruction word. -/
def packSimdThreeDiff (q u : Bool) (size : BitVec 2) (rm : BitVec 5) (opcode : BitVec 4) (rn rd : BitVec 5) : BitVec 32 :=
  (if q then 0x40000000#32 else 0#32) |||
  (if u then 0x20000000#32 else 0#32) |||
  0x0e200000#32 |||
  (size.zeroExtend 32 <<< 22) |||
  (rm.zeroExtend 32 <<< 16) |||
  (opcode.zeroExtend 32 <<< 12) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit SIMD two-register miscellaneous vector operation instruction word. -/
def packSimdTwoRegMisc (q u : Bool) (size : BitVec 2) (opcode rn rd : BitVec 5) : BitVec 32 :=
  (if q then 0x40000000#32 else 0#32) |||
  (if u then 0x20000000#32 else 0#32) |||
  0x0e200800#32 |||
  (size.zeroExtend 32 <<< 22) |||
  (opcode.zeroExtend 32 <<< 12) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit SIMD across-lanes reduction instruction word. -/
def packSimdAcrossLanes (q u : Bool) (size : BitVec 2) (opcode rn rd : BitVec 5) : BitVec 32 :=
  (if q then 0x40000000#32 else 0#32) |||
  (if u then 0x20000000#32 else 0#32) |||
  0x0e300800#32 |||
  (size.zeroExtend 32 <<< 22) |||
  (opcode.zeroExtend 32 <<< 12) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit SIMD vector permute (`UZP1`/`TRN1`/`ZIP1`/`UZP2`/`TRN2`/`ZIP2`) instruction word. -/
def packSimdPermute (q : Bool) (size : BitVec 2) (rm : BitVec 5) (opcode : BitVec 3) (rn rd : BitVec 5) : BitVec 32 :=
  (if q then 0x40000000#32 else 0#32) |||
  0x0e000800#32 |||
  (size.zeroExtend 32 <<< 22) |||
  (rm.zeroExtend 32 <<< 16) |||
  (opcode.zeroExtend 32 <<< 12) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit `EXT` byte-wise vector extract instruction word. -/
def packSimdExt (q : Bool) (rm : BitVec 5) (imm4 : BitVec 4) (rn rd : BitVec 5) : BitVec 32 :=
  (if q then 0x40000000#32 else 0#32) |||
  0x2e000000#32 |||
  (rm.zeroExtend 32 <<< 16) |||
  (imm4.zeroExtend 32 <<< 11) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit scalar floating-point data-processing (1 source) instruction word. -/
def packFpDataProc1 (ftype : BitVec 2) (opcode : BitVec 6) (rn rd : BitVec 5) : BitVec 32 :=
  0x1e204000#32 |||
  (ftype.zeroExtend 32 <<< 22) |||
  (opcode.zeroExtend 32 <<< 15) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit scalar floating-point data-processing (2 source) instruction word. -/
def packFpDataProc2 (ftype : BitVec 2) (rm : BitVec 5) (opcode : BitVec 4) (rn rd : BitVec 5) : BitVec 32 :=
  0x1e200800#32 |||
  (ftype.zeroExtend 32 <<< 22) |||
  (rm.zeroExtend 32 <<< 16) |||
  (opcode.zeroExtend 32 <<< 12) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit scalar floating-point compare (`FCMP`/`FCMPE`) instruction word. -/
def packFpCompare (ftype : BitVec 2) (rm : BitVec 5) (op : BitVec 2) (rn opcode2 : BitVec 5) : BitVec 32 :=
  0x1e202000#32 |||
  (ftype.zeroExtend 32 <<< 22) |||
  (rm.zeroExtend 32 <<< 16) |||
  (op.zeroExtend 32 <<< 14) |||
  (rn.zeroExtend 32 <<< 5) |||
  opcode2.zeroExtend 32

/-- Assemble the 32-bit scalar floating-point immediate (`FMOV Sd/Dd, #imm8`) instruction word. -/
def packFpImm (ftype : BitVec 2) (imm8 : BitVec 8) (rd : BitVec 5) : BitVec 32 :=
  0x1e201000#32 |||
  (ftype.zeroExtend 32 <<< 22) |||
  (imm8.zeroExtend 32 <<< 13) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit scalar floating-point conditional compare (`FCCMP`/`FCCMPE`) instruction word. -/
def packFpCondCompare (ftype : BitVec 2) (rm : BitVec 5) (cond : BitVec 4) (rn : BitVec 5) (op : Bool) (nzcv : BitVec 4) : BitVec 32 :=
  0x1e200400#32 |||
  (ftype.zeroExtend 32 <<< 22) |||
  (rm.zeroExtend 32 <<< 16) |||
  (cond.zeroExtend 32 <<< 12) |||
  (rn.zeroExtend 32 <<< 5) |||
  (if op then 0x00000010#32 else 0#32) |||
  nzcv.zeroExtend 32

/-- Assemble the 32-bit scalar floating-point conditional select (`FCSEL`) instruction word. -/
def packFpCondSelect (ftype : BitVec 2) (rm : BitVec 5) (cond : BitVec 4) (rn rd : BitVec 5) : BitVec 32 :=
  0x1e200c00#32 |||
  (ftype.zeroExtend 32 <<< 22) |||
  (rm.zeroExtend 32 <<< 16) |||
  (cond.zeroExtend 32 <<< 12) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit scalar floating-point data-processing (3 source) instruction word. -/
def packFpDataProc3 (ftype : BitVec 2) (o1 : Bool) (rm : BitVec 5) (o0 : Bool) (ra rn rd : BitVec 5) : BitVec 32 :=
  0x1f000000#32 |||
  (ftype.zeroExtend 32 <<< 22) |||
  (if o1 then 0x00200000#32 else 0#32) |||
  (rm.zeroExtend 32 <<< 16) |||
  (if o0 then 0x00008000#32 else 0#32) |||
  (ra.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-- Assemble the 32-bit scalar floating-point / fixed-point conversion instruction word. -/
def packFpFixedConv (sf : Bool) (ftype rmode : BitVec 2) (opcode : BitVec 3) (scale : BitVec 6) (rn rd : BitVec 5) : BitVec 32 :=
  (if sf then 0x80000000#32 else 0#32) |||
  0x1e000000#32 |||
  (ftype.zeroExtend 32 <<< 22) |||
  (rmode.zeroExtend 32 <<< 19) |||
  (opcode.zeroExtend 32 <<< 16) |||
  (scale.zeroExtend 32 <<< 10) |||
  (rn.zeroExtend 32 <<< 5) |||
  rd.zeroExtend 32

/-!
## Instruction Class Encoding Helpers
-/

/-- Encode a Load/Store Pair (`LDP`/`STP`/`LDPSW`) instruction over `AddrMode`. -/
def encodeLoadStorePair (opc : BitVec 2) (isLoad : Bool) (rt1 rt2 : Reg) (addr : AddrMode) : Option (BitVec 32) :=
  if !rt1.isValidZR || !rt2.isValidZR then
    none
  else
    let rt1Bits := rt1.toBits
    let rt2Bits := rt2.toBits
    let scale := if opc == 2#2 then 3 else 2
    let encodeWith (rn : Reg) (offset : BitVec 64) (wback : Bool) (modeBits : BitVec 2) : Option (BitVec 32) :=
      if !rn.isValidSP then none
      else
        let rnBits := rn.toBits
        let overlap := (isLoad && rt1Bits == rt2Bits) ||
          (wback && (rt1Bits == rnBits || rt2Bits == rnBits) && rnBits != 31#5)
        let imm7 : BitVec 7 := offset.extractLsb' scale 7
        if !overlap && (imm7.signExtend 64) <<< scale == offset then
          some (packLoadStorePair opc modeBits isLoad imm7 rt2Bits rnBits rt1Bits)
        else
          none
    match addr with
    | .PostIndex rn offset => encodeWith rn offset true  1#2
    | .Offset    rn offset => encodeWith rn offset false 2#2
    | .PreIndex  rn offset => encodeWith rn offset true  3#2
    | .UnscaledOffset _ _ | .RegOffset _ _ _ _ => none

/-- Encode a single-register GPR load/store instruction (`LDR*`, `LDUR*`, `STR*`, `STUR*`) over `AddrMode`. -/
def encodeLoadStore (sizeBits opc : BitVec 2) (rt : Reg) (addr : AddrMode) : Option (BitVec 32) :=
  if !rt.isValidZR then
    none
  else
    let rtBits := rt.toBits
    let scale := sizeBits.toNat
    match addr with
    | .Offset rn offset =>
      let imm12 : BitVec 12 := offset.extractLsb' scale 12
      if rn.isValidSP && (imm12.zeroExtend 64) <<< scale == offset then
        some (packLoadStoreUImm sizeBits opc imm12 rn.toBits rtBits)
      else
        none
    | .UnscaledOffset rn offset =>
      let imm9 : BitVec 9 := offset.extractLsb' 0 9
      if rn.isValidSP && imm9.signExtend 64 == offset then
        some (packLoadStoreSimm9 sizeBits opc 0#2 imm9 rn.toBits rtBits)
      else
        none
    | .PostIndex rn offset =>
      let rnBits := rn.toBits
      let wbOverlap := rtBits == rnBits && rnBits != 31#5
      let imm9 : BitVec 9 := offset.extractLsb' 0 9
      if rn.isValidSP && !wbOverlap && imm9.signExtend 64 == offset then
        some (packLoadStoreSimm9 sizeBits opc 1#2 imm9 rnBits rtBits)
      else
        none
    | .PreIndex rn offset =>
      let rnBits := rn.toBits
      let wbOverlap := rtBits == rnBits && rnBits != 31#5
      let imm9 : BitVec 9 := offset.extractLsb' 0 9
      if rn.isValidSP && !wbOverlap && imm9.signExtend 64 == offset then
        some (packLoadStoreSimm9 sizeBits opc 3#2 imm9 rnBits rtBits)
      else
        none
    | .RegOffset rn rm ext amount =>
      if rn.isValidSP && rm.isValidZR && (ext.toBits).getLsbD 1 &&
          (amount == 0 || (scale > 0 && amount == scale)) then
        let sBit := amount != 0
        some (packLoadStoreRegOff sizeBits opc rm.toBits ext.toBits sBit rn.toBits rtBits)
      else
        none

/-- Encode a literal PC-relative load (`LDR`/`LDRSW (literal)`). -/
def encodeLdrLit (opc : BitVec 2) (rt : Reg) (offset : BitVec 64) : Option (BitVec 32) :=
  let imm19 : BitVec 19 := offset.extractLsb' 2 19
  if rt.isValidZR && (imm19.signExtend 64) <<< 2 == offset then
    some (packLdrLit opc imm19 rt.toBits)
  else
    none

/-- Encode SIMD/FP single-register `(sizeBits, opc, scale)` from `(isLoad, sz)`. -/
def encodeSimdLoadStoreType (isLoad : Bool) (sz : SimdMemSize) : BitVec 2 × BitVec 2 × Nat :=
  match sz with
  | .B8   => (0#2, if isLoad then 1#2 else 0#2, 0)
  | .H16  => (1#2, if isLoad then 1#2 else 0#2, 1)
  | .S32  => (2#2, if isLoad then 1#2 else 0#2, 2)
  | .D64  => (3#2, if isLoad then 1#2 else 0#2, 3)
  | .Q128 => (0#2, if isLoad then 3#2 else 2#2, 4)

/-- Encode SIMD/FP single-register load/store instruction (`LDR`/`STR`/`LDUR`/`STUR` B/H/S/D/Q). -/
def encodeSimdLoadStoreAddr (isLoad : Bool) (sz : SimdMemSize) (vt : BitVec 5) (addr : AddrMode) : Option (BitVec 32) :=
  let (sizeBits, opc, scale) := encodeSimdLoadStoreType isLoad sz
  match addr with
  | .Offset rn offset =>
    let imm12 : BitVec 12 := offset.extractLsb' scale 12
    if rn.isValidSP && (imm12.zeroExtend 64) <<< scale == offset then
      some (packSimdLoadStoreUImm sizeBits opc imm12 rn.toBits vt)
    else
      none
  | .UnscaledOffset rn offset =>
    let imm9 : BitVec 9 := offset.extractLsb' 0 9
    if rn.isValidSP && imm9.signExtend 64 == offset then
      some (packSimdLoadStoreSimm9 sizeBits opc 0#2 imm9 rn.toBits vt)
    else
      none
  | .PostIndex rn offset =>
    let imm9 : BitVec 9 := offset.extractLsb' 0 9
    if rn.isValidSP && imm9.signExtend 64 == offset then
      some (packSimdLoadStoreSimm9 sizeBits opc 1#2 imm9 rn.toBits vt)
    else
      none
  | .PreIndex rn offset =>
    let imm9 : BitVec 9 := offset.extractLsb' 0 9
    if rn.isValidSP && imm9.signExtend 64 == offset then
      some (packSimdLoadStoreSimm9 sizeBits opc 3#2 imm9 rn.toBits vt)
    else
      none
  | .RegOffset rn rm ext amount =>
    if rn.isValidSP && rm.isValidZR && (ext.toBits).getLsbD 1 && (amount == 0 || amount == scale) then
      let sBit := amount != 0
      some (packSimdLoadStoreRegOff sizeBits opc rm.toBits ext.toBits sBit rn.toBits vt)
    else
      none

/-- Encode SIMD/FP Load/Store Pair (`LDP`/`STP` S/D/Q). -/
def encodeSimdLoadStorePair (isLoad : Bool) (sz : SimdMemSize) (vt1 vt2 : BitVec 5) (addr : AddrMode) : Option (BitVec 32) :=
  if isLoad && vt1 == vt2 then
    none
  else
    let opcScale? : Option (BitVec 2 × Nat) :=
      match sz with
      | .S32  => some (0#2, 2)
      | .D64  => some (1#2, 3)
      | .Q128 => some (2#2, 4)
      | _     => none
    match opcScale? with
    | none => none
    | some (opc, scale) =>
      match addr with
      | .PostIndex rn offset =>
        let imm7 : BitVec 7 := offset.extractLsb' scale 7
        if rn.isValidSP && (imm7.signExtend 64) <<< scale == offset then
          some (packSimdLoadStorePair opc 1#2 isLoad imm7 vt2 rn.toBits vt1)
        else
          none
      | .Offset rn offset =>
        let imm7 : BitVec 7 := offset.extractLsb' scale 7
        if rn.isValidSP && (imm7.signExtend 64) <<< scale == offset then
          some (packSimdLoadStorePair opc 2#2 isLoad imm7 vt2 rn.toBits vt1)
        else
          none
      | .PreIndex rn offset =>
        let imm7 : BitVec 7 := offset.extractLsb' scale 7
        if rn.isValidSP && (imm7.signExtend 64) <<< scale == offset then
          some (packSimdLoadStorePair opc 3#2 isLoad imm7 vt2 rn.toBits vt1)
        else
          none
      | .UnscaledOffset _ _ | .RegOffset _ _ _ _ => none

/-- Encode a GPR non-temporal pair (`LDNP`/`STNP` W/X): signed-offset `LDP`/`STP` with mode `00`. -/
def encodeLdStNp (isLoad : Bool) (sz : MemWidth) (rn rt rt2 : Reg) (offset : BitVec 64) : Option (BitVec 32) :=
  match pairSf? sz with
  | none => none
  | some is64 =>
    let scale := if is64 then 3 else 2
    let imm7 : BitVec 7 := offset.extractLsb' scale 7
    if rn.isValidSP && rt.isValidZR && rt2.isValidZR &&
        !(isLoad && rt.toBits == rt2.toBits) &&
        (imm7.signExtend 64) <<< scale == offset then
      some (packLoadStorePair (if is64 then 2#2 else 0#2) 0#2 isLoad imm7 rt2.toBits rn.toBits rt.toBits)
    else
      none

/-- Encode a SIMD/FP non-temporal pair (`LDNP`/`STNP` S/D/Q): SIMD `LDP`/`STP` with mode `00`. -/
def encodeSimdNp (isLoad : Bool) (sz : SimdMemSize) (vt1 vt2 : BitVec 5) (rn : Reg) (offset : BitVec 64) :
    Option (BitVec 32) :=
  if isLoad && vt1 == vt2 then
    none
  else
    let opcScale? : Option (BitVec 2 × Nat) :=
      match sz with
      | .S32  => some (0#2, 2)
      | .D64  => some (1#2, 3)
      | .Q128 => some (2#2, 4)
      | _     => none
    match opcScale? with
    | none => none
    | some (opc, scale) =>
      let imm7 : BitVec 7 := offset.extractLsb' scale 7
      if rn.isValidSP && (imm7.signExtend 64) <<< scale == offset then
        some (packSimdLoadStorePair opc 0#2 isLoad imm7 vt2 rn.toBits vt1)
      else
        none

/-- Encode `PRFM`/`PRFUM` (immediate, unscaled, register offset): the `LDR X` encodings with `opc = 10`. -/
def encodePrfm (prfop : BitVec 5) (addr : AddrMode) : Option (BitVec 32) :=
  match addr with
  | .Offset rn offset =>
    let imm12 : BitVec 12 := offset.extractLsb' 3 12
    if rn.isValidSP && (imm12.zeroExtend 64) <<< 3 == offset then
      some (packLoadStoreUImm 3#2 2#2 imm12 rn.toBits prfop)
    else
      none
  | .UnscaledOffset rn offset =>
    let imm9 : BitVec 9 := offset.extractLsb' 0 9
    if rn.isValidSP && imm9.signExtend 64 == offset then
      some (packLoadStoreSimm9 3#2 2#2 0#2 imm9 rn.toBits prfop)
    else
      none
  | .RegOffset rn rm ext amount =>
    if rn.isValidSP && rm.isValidZR && ext.toBits.getLsbD 1 && (amount == 0 || amount == 3) then
      some (packLoadStoreRegOff 3#2 2#2 rm.toBits ext.toBits (amount == 3) rn.toBits prfop)
    else
      none
  | .PreIndex _ _ | .PostIndex _ _ => none

/-- Encode an `Arm64.Instr` AST node into a 32-bit machine instruction word (`Option (BitVec 32)`). -/
def encode (p : Instr) : Option (BitVec 32) :=
  match p with
  | .nop =>
    some packNop

  | .system isHalt imm =>
    some (packSystem isHalt imm)

  | .adr page rd offset =>
    if !rd.isValidZR then none
    else if page then
      let imm21 : BitVec 21 := offset.extractLsb' 12 21
      if (imm21.signExtend 64) <<< 12 == offset then
        some (packAdr true (imm21.extractLsb' 0 2) (imm21.extractLsb' 2 19) rd.toBits)
      else
        none
    else
      let imm21 : BitVec 21 := offset.extractLsb' 0 21
      if imm21.signExtend 64 == offset then
        some (packAdr false (imm21.extractLsb' 0 2) (imm21.extractLsb' 2 19) rd.toBits)
      else
        none

  | .addSubImm w op rd rn imm12 shift12 =>
    let (op30, op29) := op.toBits
    let rdValid := if op29 then rd.isValidZR else rd.isValidSP
    if rdValid && rn.isValidSP then
      some (packAddSubImm w.toBool op30 op29 shift12 imm12 rn.toBits rd.toBits)
    else
      none

  | .logicalImm w op rd rn mask =>
    let (opc, nBit) := op.toBits
    let rdValid := if opc == 3#2 then rd.isValidZR else rd.isValidSP
    if !nBit && rdValid && rn.isValidZR then
      match encodeBitMasks w mask with
      | some (immN, imms, immr) =>
        some (packLogicalImm w.toBool opc immN immr imms rn.toBits rd.toBits)
      | none => none
    else
      none

  | .moveWide w op rd imm16 hw =>
    let hwBits? : Option (BitVec 2) :=
      match w, hw with
      | _,    0  => some 0#2
      | _,    16 => some 1#2
      | .W64, 32 => some 2#2
      | .W64, 48 => some 3#2
      | _,    _  => none
    match hwBits? with
    | some hwBits =>
      if rd.isValidZR then
        some (packMoveWide w.toBool op.toBits hwBits imm16 rd.toBits)
      else
        none
    | none => none

  | .bitfield w op rd rn immr imms =>
    let bound := if w == .W64 then 64 else 32
    if rd.isValidZR && rn.isValidZR && immr < bound && imms < bound then
      some (packBitfield w.toBool op.toBits (BitVec.ofNat 6 immr) (BitVec.ofNat 6 imms) rn.toBits rd.toBits)
    else
      none

  | .extr w rd rn rm lsb =>
    let bound := if w == .W64 then 64 else 32
    if rd.isValidZR && rn.isValidZR && rm.isValidZR && lsb < bound then
      some (packExtr w.toBool rm.toBits (BitVec.ofNat 6 lsb) rn.toBits rd.toBits)
    else
      none

  | .b offset =>
    let imm26 : BitVec 26 := offset.extractLsb' 2 26
    if (imm26.signExtend 64) <<< 2 == offset then some (packB false imm26) else none

  | .bl offset =>
    let imm26 : BitVec 26 := offset.extractLsb' 2 26
    if (imm26.signExtend 64) <<< 2 == offset then some (packB true imm26) else none

  | .cbz w isNonZero rt offset =>
    let imm19 : BitVec 19 := offset.extractLsb' 2 19
    if rt.isValidZR && (imm19.signExtend 64) <<< 2 == offset then
      some (packCbz w.toBool isNonZero imm19 rt.toBits)
    else
      none

  | .tbz w isNonZero rt bitPos offset =>
    let imm14 : BitVec 14 := offset.extractLsb' 2 14
    let b5 := bitPos >= 32
    if rt.isValidZR && bitPos < 64 && b5 == (w == .W64) && (imm14.signExtend 64) <<< 2 == offset then
      let b40 := BitVec.ofNat 5 (bitPos % 32)
      some (packTbz b5 isNonZero b40 imm14 rt.toBits)
    else
      none

  | .bCond cond offset =>
    let imm19 : BitVec 19 := offset.extractLsb' 2 19
    if (imm19.signExtend 64) <<< 2 == offset then
      some (packBCond imm19 cond.toBits)
    else
      none

  | .br rn  => if rn.isValidZR then some (packBr 0#2 rn.toBits) else none
  | .blr rn => if rn.isValidZR then some (packBr 1#2 rn.toBits) else none
  | .ret rn => if rn.isValidZR then some (packBr 2#2 rn.toBits) else none

  | .logicalShift w op rd rn rm shift amount =>
    let (opc, nBit) := op.toBits
    let bound := if w == .W64 then 64 else 32
    if rd.isValidZR && rn.isValidZR && rm.isValidZR && amount < bound then
      some (packLogicalReg w.toBool opc shift.toBits nBit rm.toBits (BitVec.ofNat 6 amount) rn.toBits rd.toBits)
    else
      none

  | .addSubShift w op rd rn rm shift amount =>
    let (op30, op29) := op.toBits
    let bound := if w == .W64 then 64 else 32
    if rd.isValidZR && rn.isValidZR && rm.isValidZR && shift != .ROR && amount < bound then
      some (packAddSubReg w.toBool op30 op29 shift.toBits rm.toBits (BitVec.ofNat 6 amount) rn.toBits rd.toBits)
    else
      none

  | .addSubExt w op rd rn rm ext amount =>
    let (op30, op29) := op.toBits
    let rdValid := if op29 then rd.isValidZR else rd.isValidSP
    if rdValid && rn.isValidSP && rm.isValidZR && amount <= 4 then
      some (packAddSubExt w.toBool op30 op29 rm.toBits ext.toBits (BitVec.ofNat 3 amount) rn.toBits rd.toBits)
    else
      none

  | .addSubCarry w op rd rn rm =>
    let (op30, op29) := op.toBits
    if rd.isValidZR && rn.isValidZR && rm.isValidZR then
      some (packAddSubCarry w.toBool op30 op29 rm.toBits rn.toBits rd.toBits)
    else
      none

  | .condCompareReg w isSub rn rm nzcv cond =>
    if rn.isValidZR && rm.isValidZR then
      some (packCondCompare w.toBool isSub false rm.toBits cond.toBits rn.toBits nzcv)
    else
      none

  | .condCompareImm w isSub rn imm5 nzcv cond =>
    if rn.isValidZR then
      some (packCondCompare w.toBool isSub true imm5 cond.toBits rn.toBits nzcv)
    else
      none

  | .condSelect w op rd rn rm cond =>
    let (op30, o2) := op.toBits
    if rd.isValidZR && rn.isValidZR && rm.isValidZR then
      some (packCondSelect w.toBool op30 o2 rm.toBits cond.toBits rn.toBits rd.toBits)
    else
      none

  | .dataProc1 w op rd rn =>
    match op.toBits w with
    | some opcode =>
      if rd.isValidZR && rn.isValidZR then
        some (packDataProc1 w.toBool opcode rn.toBits rd.toBits)
      else
        none
    | none => none

  | .dataProc2 w op rd rn rm =>
    if rd.isValidZR && rn.isValidZR && rm.isValidZR then
      some (packDataProc2 w.toBool rm.toBits op.toBits rn.toBits rd.toBits)
    else
      none

  | .dataProc3 w op rd rn rm ra =>
    if !rd.isValidZR || !rn.isValidZR || !rm.isValidZR || !ra.isValidZR then
      none
    else
      match op with
      | .MADD   => some (packDataProc3 w.toBool 0#3 rm.toBits false ra.toBits rn.toBits rd.toBits)
      | .MSUB   => some (packDataProc3 w.toBool 0#3 rm.toBits true  ra.toBits rn.toBits rd.toBits)
      | .SMADDL => if w == .W64 then some (packDataProc3 true 1#3 rm.toBits false ra.toBits rn.toBits rd.toBits) else none
      | .SMSUBL => if w == .W64 then some (packDataProc3 true 1#3 rm.toBits true  ra.toBits rn.toBits rd.toBits) else none
      | .SMULH  => if w == .W64 && ra == .xzr then some (packDataProc3 true 2#3 rm.toBits false 31#5 rn.toBits rd.toBits) else none
      | .UMADDL => if w == .W64 then some (packDataProc3 true 5#3 rm.toBits false ra.toBits rn.toBits rd.toBits) else none
      | .UMSUBL => if w == .W64 then some (packDataProc3 true 5#3 rm.toBits true  ra.toBits rn.toBits rd.toBits) else none
      | .UMULH  => if w == .W64 && ra == .xzr then some (packDataProc3 true 6#3 rm.toBits false 31#5 rn.toBits rd.toBits) else none

  | .ldp w signed rt1 rt2 addr =>
    match w, signed with
    | .W32, false => encodeLoadStorePair 0#2 true rt1 rt2 addr
    | .W64, true  => encodeLoadStorePair 1#2 true rt1 rt2 addr
    | .W64, false => encodeLoadStorePair 2#2 true rt1 rt2 addr
    | .W32, true  => none

  | .stp w rt1 rt2 addr =>
    encodeLoadStorePair (if w == .W64 then 2#2 else 0#2) false rt1 rt2 addr

  | .ldr w sz signed rt addr =>
    let sizeOpc? : Option (BitVec 2 × BitVec 2) :=
      match w, sz, signed with
      | .W32, .B8,  false => some (0#2, 1#2)
      | .W64, .B8,  true  => some (0#2, 2#2)
      | .W32, .B8,  true  => some (0#2, 3#2)
      | .W32, .H16, false => some (1#2, 1#2)
      | .W64, .H16, true  => some (1#2, 2#2)
      | .W32, .H16, true  => some (1#2, 3#2)
      | .W32, .W32, false => some (2#2, 1#2)
      | .W64, .W32, true  => some (2#2, 2#2)
      | .W64, .X64, false => some (3#2, 1#2)
      | _,    _,    _     => none
    match sizeOpc? with
    | some (sizeBits, opc) => encodeLoadStore sizeBits opc rt addr
    | none => none

  | .ldrLit w signed rt offset =>
    let opc? : Option (BitVec 2) :=
      match w, signed with
      | .W32, false => some 0#2
      | .W64, false => some 1#2
      | .W64, true  => some 2#2
      | .W32, true  => none
    match opc? with
    | some opc => encodeLdrLit opc rt offset
    | none => none

  | .str sz rt addr =>
    encodeLoadStore sz.toBits 0#2 rt addr

  | .ldarStlr sz isLoad rn rt =>
    if rn.isValidSP && rt.isValidZR then
      some (packLdarStlr sz.toBits isLoad rn.toBits rt.toBits)
    else
      none

  | .ldxr sz acq rn rt =>
    if rn.isValidSP && rt.isValidZR then
      some (packLdxr sz.toBits acq rn.toBits rt.toBits)
    else
      none

  | .stxr sz rel rs rn rt =>
    if rs.isValidZR && rn.isValidSP && rt.isValidZR then
      some (packStxr sz.toBits rel rs.toBits rn.toBits rt.toBits)
    else
      none

  | .sysReg isRead sysreg rt =>
    if rt.isValidZR then
      some (packSysReg isRead sysreg rt.toBits)
    else
      none

  | .barrier crm op2 =>
    if op2 == 2#3 || op2 == 4#3 || op2 == 5#3 || op2 == 6#3 then
      some (packBarrier crm op2)
    else
      none

  | .ldpSimd sz vt1 vt2 addr =>
    encodeSimdLoadStorePair true sz vt1 vt2 addr

  | .stpSimd sz vt1 vt2 addr =>
    encodeSimdLoadStorePair false sz vt1 vt2 addr

  | .ldrSimd sz vt addr =>
    encodeSimdLoadStoreAddr true sz vt addr

  | .strSimd sz vt addr =>
    encodeSimdLoadStoreAddr false sz vt addr

  | .st1SinglePost q rm opcode sBit size rn vt =>
    if rn.isValidSP then
      some (packSt1SinglePost q rm opcode sBit size rn.toBits vt)
    else
      none

  | .aes op rd rn =>
    some (packAes op.toBits rn rd)

  | .fmovGprVec sf ftype rmode opcode rn rd =>
    some (packFmovGprVec sf ftype rmode opcode rn rd)

  | .simdImmShift q op immh immb opcode rn rd =>
    some (packSimdImmShift q op immh immb opcode rn rd)

  | .simdInsDup q op imm5 imm4 rn rd =>
    some (packSimdInsDup q op imm5 imm4 rn rd)

  | .simdThreeSame q u size rm opcode rn rd =>
    some (packSimdThreeSame q u size rm opcode rn rd)

  | .simdTwoRegMisc q u size opcode rn rd =>
    some (packSimdTwoRegMisc q u size opcode rn rd)

  | .simdAcrossLanes q u size opcode rn rd =>
    some (packSimdAcrossLanes q u size opcode rn rd)

  | .simdPermute q size rm opcode rn rd =>
    some (packSimdPermute q size rm opcode rn rd)

  | .simdExt q rm imm4 rn rd =>
    some (packSimdExt q rm imm4 rn rd)

  | .fpDataProc1 ftype opcode rn rd =>
    some (packFpDataProc1 ftype opcode rn rd)

  | .fpDataProc2 ftype rm opcode rn rd =>
    some (packFpDataProc2 ftype rm opcode rn rd)

  | .fpCompare ftype rm op rn opcode2 =>
    some (packFpCompare ftype rm op rn opcode2)

  | .fpImm ftype imm8 rd =>
    some (packFpImm ftype imm8 rd)

  | .fpCondCompare ftype rm cond rn op nzcv =>
    some (packFpCondCompare ftype rm cond rn op nzcv)

  | .fpCondSelect ftype rm cond rn rd =>
    some (packFpCondSelect ftype rm cond rn rd)

  | .fpDataProc3 ftype o1 rm o0 ra rn rd =>
    some (packFpDataProc3 ftype o1 rm o0 ra rn rd)

  | .fpFixedConv sf ftype rmode opcode scale rn rd =>
    some (packFpFixedConv sf ftype rmode opcode scale rn rd)

  | .ldxp sz acq rn rt rt2 =>
    match pairSf? sz with
    | some is64 =>
      if rn.isValidSP && rt.isValidZR && rt2.isValidZR && !(rt.toBits == rt2.toBits) then
        some (packExclPair (if is64 then 3#2 else 2#2) false true true 31#5 acq rt2.toBits rn.toBits rt.toBits)
      else none
    | none => none

  | .stxp sz rel rs rn rt rt2 =>
    match pairSf? sz with
    | some is64 =>
      if rs.isValidZR && rn.isValidSP && rt.isValidZR && rt2.isValidZR then
        some (packExclPair (if is64 then 3#2 else 2#2) false false true rs.toBits rel rt2.toBits rn.toBits rt.toBits)
      else none
    | none => none

  | .cas sz acq rel rs rn rt =>
    if rs.isValidZR && rn.isValidSP && rt.isValidZR then
      some (packExclPair sz.toBits true acq true rs.toBits rel 31#5 rn.toBits rt.toBits)
    else none

  | .casp sz acq rel rs rs2 rn rt rt2 =>
    match pairSf? sz with
    | some is64 =>
      if rs.isValidZR && rs2.isValidZR && rn.isValidSP && rt.isValidZR && rt2.isValidZR &&
          !rs.toBits.getLsbD 0 && !rt.toBits.getLsbD 0 &&
          rs2.toBits == rs.toBits + 1#5 && rt2.toBits == rt.toBits + 1#5 then
        some (packExclPair (if is64 then 1#2 else 0#2) false acq true rs.toBits rel 31#5 rn.toBits rt.toBits)
      else none
    | none => none

  | .atomicRmw op sz acq rel rs rn rt =>
    if rs.isValidZR && rn.isValidSP && rt.isValidZR then
      some (packLse sz.toBits acq rel rs.toBits op.isSwp op.toBits rn.toBits rt.toBits)
    else none

  | .ldapr sz rn rt =>
    if rn.isValidSP && rt.isValidZR then
      some (packLse sz.toBits true false 31#5 true 4#3 rn.toBits rt.toBits)
    else none

  | .ldapurStlur sz opc rn rt offset =>
    let imm9 : BitVec 9 := offset.extractLsb' 0 9
    if rn.isValidSP && rt.isValidZR && imm9.signExtend 64 == offset &&
        !((sz.toBits == 3#2 && opc.getLsbD 1) || (sz.toBits == 2#2 && opc == 3#2)) then
      some (packRcpcUnscaled sz.toBits opc imm9 rn.toBits rt.toBits)
    else none

  | .hint imm => some (packHint imm)

  | .prfm prfop addr => encodePrfm prfop addr

  | .prfmLit prfop offset =>
    let imm19 : BitVec 19 := offset.extractLsb' 2 19
    if (imm19.signExtend 64) <<< 2 == offset then some (packLdrLit 3#2 imm19 prfop) else none

  | .ldrSimdLit sz vt offset =>
    let opc? : Option (BitVec 2) :=
      match sz with
      | .S32 => some 0#2
      | .D64 => some 1#2
      | .Q128 => some 2#2
      | _ => none
    let imm19 : BitVec 19 := offset.extractLsb' 2 19
    match opc? with
    | some opc =>
      if (imm19.signExtend 64) <<< 2 == offset then some (packSimdLdrLit opc imm19 vt) else none
    | none => none

  | .ldnp sz rn rt rt2 offset => encodeLdStNp true sz rn rt rt2 offset
  | .stnp sz rn rt rt2 offset => encodeLdStNp false sz rn rt rt2 offset
  | .ldnpSimd sz vt1 vt2 rn offset => encodeSimdNp true sz vt1 vt2 rn offset
  | .stnpSimd sz vt1 vt2 rn offset => encodeSimdNp false sz vt1 vt2 rn offset

  | .crc32 c sz rd rn rm =>
    if rd.isValidZR && rn.isValidZR && rm.isValidZR then
      some (packCrc32 (sz.toBits == 3#2) c sz.toBits rm.toBits rn.toBits rd.toBits)
    else none

  | .simdTbl q rm len isTbx rn rd => some (packSimdTbl q rm len isTbx rn rd)

  | .simdAddpScalar rn rd => some (packSimdAddpScalar rn rd)

  | .simdLdSt1Multi isLoad q size nregs rn postIdx rm vt =>
    match ld1MultiOpcode? nregs with
    | some opcode =>
      if rn.isValidSP && (postIdx || rm == 0#5) then
        some (packSimdLdStStruct 0x0c000000#32 q postIdx isLoad rm opcode size rn.toBits vt)
      else none
    | none => none

  | .simdLdStMulti isLoad q size selem rn postIdx rm vt =>
    match ldMultiOpcode? selem with
    | some opcode =>
      if rn.isValidSP && (postIdx || rm == 0#5) then
        some (packSimdLdStStruct 0x0c000000#32 q postIdx isLoad rm opcode size rn.toBits vt)
      else none
    | none => none

  | .simdLdSt1Single isLoad q postIdx rm opcode sBit size rn vt =>
    if rn.isValidSP then
      some (packSimdLdSt1Single isLoad q postIdx rm opcode sBit size rn.toBits vt)
    else none

  | .simdDupScalar imm5 rn rd =>
    some (packSimdDupScalar imm5 rn rd)

  | .simdThreeDiff q u size rm opcode rn rd =>
    some (packSimdThreeDiff q u size rm opcode rn rd)

  | .simdLd1r q size rn postIdx rm vt =>
    if rn.isValidSP && (postIdx || rm == 0#5) then
      some (packSimdLdStStruct 0x0d000000#32 q postIdx true rm 12#4 size rn.toBits vt)
    else none

  | .dcZva rt => if rt.isValidZR then some (packDcZva rt.toBits) else none

  | .udf imm => some (packUdf imm)

  | .simdPmull q is64 rm rn rd => some (packSimdPmull q is64 rm rn rd)

  | .cryptoSha2Reg opcode rn rd =>
    if opcode == 0#5 || opcode == 1#5 || opcode == 2#5 then
      some (packCryptoSha2Reg opcode rn rd)
    else none

  | .cryptoSha3Reg opcode rm rn rd =>
    if opcode != 7#3 then
      some (packCryptoSha3Reg opcode rm rn rd)
    else none

  | .cryptoSha512Reg2 rn rd => some (packCryptoSha512Reg2 rn rd)

  | .cryptoSha512Reg3 opcode rm rn rd => some (packCryptoSha512Reg3 opcode rm rn rd)

  | .cryptoSha3FourReg isBcax rm ra rn rd => some (packCryptoSha3FourReg isBcax rm ra rn rd)

  | .cryptoXar rm imm6 rn rd => some (packCryptoXar rm imm6 rn rd)

/-- Decidable well-formedness predicate on `Instr`: `true` iff `encode p` succeeds. -/
def Instr.wellFormed (p : Instr) : Bool :=
  (encode p).isSome

/-- Total encoder on `Instr` (returns `0xd503201f#32` (`NOP`) if `p` is not well-formed). -/
def encodeInst (p : Instr) : BitVec 32 :=
  (encode p).getD packNop

/-- Total decoder on `BitVec 32` (returns `.nop` if `w` is not a valid instruction word). -/
def decodeInst (w : BitVec 32) : Instr :=
  (decode w).getD .nop

/-- Subtype of well-formed (encodable) A64 AST instructions. -/
abbrev ValidInst := { p : Instr // p.wellFormed = true }

/-- Total encoder on `ValidInst`. -/
def encodeValid (p : ValidInst) : BitVec 32 :=
  encodeInst p.val

/-- Format a 32-bit machine word as an 8-digit lowercase hex string (`"0x........"`). -/
def hex32 (w : BitVec 32) : String :=
  let digits := "0123456789abcdef".toList
  Id.run do
    let mut n := w.toNat
    let mut chars : List Char := []
    for _ in [0:8] do
      let d := n % 16
      chars := (digits[d]?.getD '0') :: chars
      n := n / 16
    return "0x" ++ String.ofList chars

/-- Encode an `Instr` directly to an 8-digit lowercase hex string (`"0x........"`). -/
def encodeHex (p : Instr) : Option String :=
  (encode p).map hex32

/-- Encode a program (`List Instr`) to a list of 32-bit binary words. -/
def encodeProg (insts : List Instr) : Option (List (BitVec 32)) :=
  insts.mapM encode

/-- Decode a list of 32-bit binary words to a program (`List Instr`). -/
def decodeProg (words : List (BitVec 32)) : Option (List Instr) :=
  words.mapM decode

/-- Encode a program (`List Instr`) to a list of 8-digit hex strings. -/
def encodeProgHex (insts : List Instr) : Option (List String) :=
  (encodeProg insts).map (List.map hex32)

/-- Format a list of 32-bit binary words as a list of 8-digit hex strings. -/
def wordsToHex (words : List (BitVec 32)) : List String :=
  words.map hex32

/-- Perform a `decode` -> `encode` round-trip on a 32-bit word and return `(originalHex, reencodedHex)`. -/
def roundTripWordHex (w : BitVec 32) : Option (String × String) := do
  let inst ← decode w
  let w' ← encode inst
  return (hex32 w, hex32 w')

/-- Perform an `encode` -> `decode` -> `encode` round-trip on an AST instruction `p`,
    returning `(encodedHex, roundTripEncodedHex, decodedInst == p)`. -/
def roundTripInstHex (p : Instr) : Option (String × String × Bool) := do
  let w1 ← encode p
  let p' ← decode w1
  let w2 ← encode p'
  return (hex32 w1, hex32 w2, p' == p)

end Arm64
