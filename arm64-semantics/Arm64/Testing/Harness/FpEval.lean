/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean.Data.Json
public import Arm64
public import Arm64.Testing.Harness.TestCase

/-!
# IEEE-754 Floating-Point Test Harness

Evaluates 32-byte `FpBatchRecord` records (`f32` opcodes `0..22`, `f64` opcodes `32..54`, and
rounding modes `0..4`) directly against the format-generic `(result, fpsrFlags)` operations in
`Arm64.Trusted.ISA.Float`.
-/

@[expose] public section

namespace Testing.Harness

open Lean
open Arm64

/-! ## Rounding-Mode and Opcode Decoding -/

/-- Decode a raw `FpBatchRecord` rounding-mode code (`0..4`) into `Arm64.FpRoundMode`. -/
def decodeRoundMode (rmCode : UInt64) : FpRoundMode :=
  match rmCode.toNat with
  | 0 => .RNE
  | 1 => .RTP
  | 2 => .RTN
  | 3 => .RTZ
  | _ => .RNA

/-- Human-readable IEEE-754 rounding-mode name. -/
def roundModeName (rm : FpRoundMode) : String :=
  match rm with
  | .RNE => "RNE"
  | .RTP => "RTP"
  | .RTN => "RTN"
  | .RTZ => "RTZ"
  | .RNA => "RNA"

/-- Human-readable operation mnemonic for an `FpBatchRecord` opcode (`0..22` = `f32`, `32..54` = `f64`). -/
def fpOpName (op : Nat) : String :=
  match op with
  | 0  => "FADD.S"   | 1  => "FSUB.S"   | 2  => "FMUL.S"   | 3  => "FDIV.S"
  | 4  => "FSQRT.S"  | 5  => "FMADD.S"  | 6  => "FRINT.S"  | 7  => "FCVT.D.S"
  | 8  => "FCVTZS.W.S" | 9 => "FCVTZU.W.S" | 10 => "FCVTZS.X.S" | 11 => "FCVTZU.X.S"
  | 12 => "SCVTF.S.W"  | 13 => "UCVTF.S.W" | 14 => "SCVTF.S.X"  | 15 => "UCVTF.S.X"
  | 16 => "FMIN.S"   | 17 => "FMAX.S"   | 18 => "FMINNM.S" | 19 => "FMAXNM.S"
  | 20 => "FCMP.S"   | 21 => "FRINTX.S" | 22 => "FCMPE.S"
  | 32 => "FADD.D"   | 33 => "FSUB.D"   | 34 => "FMUL.D"   | 35 => "FDIV.D"
  | 36 => "FSQRT.D"  | 37 => "FMADD.D"  | 38 => "FRINT.D"  | 39 => "FCVT.S.D"
  | 40 => "FCVTZS.W.D" | 41 => "FCVTZU.W.D" | 42 => "FCVTZS.X.D" | 43 => "FCVTZU.X.D"
  | 44 => "SCVTF.D.W"  | 45 => "UCVTF.D.W" | 46 => "SCVTF.D.X"  | 47 => "UCVTF.D.X"
  | 48 => "FMIN.D"   | 49 => "FMAX.D"   | 50 => "FMINNM.D" | 51 => "FMAXNM.D"
  | 52 => "FCMP.D"   | 53 => "FRINTX.D" | 54 => "FCMPE.D"
  | _  => s!"FP_OP_{op}"

/-! ## Single-Record and Batch Evaluation -/

def packPair {w : Nat} (p : BitVec w × BitVec 32) : UInt64 × UInt64 :=
  (p.1.toNat.toUInt64, p.2.toNat.toUInt64)

def packCmpPair (p : PState × BitVec 32) : UInt64 × UInt64 :=
  ((pstateToBits4 p.1).toNat.toUInt64, p.2.toNat.toUInt64)

/-- Evaluate a single 32-byte `FpBatchRecord` `(metaWord, a, b, c)` directly against the
    format-generic `(result, fpsrFlags)` primitives in `Arm64.Trusted.ISA.Float`. -/
def evalFpBatchRecordWithFlags (metaWord a b c : UInt64) : UInt64 × UInt64 :=
  let op := (metaWord &&& 0xff).toNat
  let rm := decodeRoundMode ((metaWord >>> 8) &&& 0xff)
  let fbits := ((metaWord >>> 16) &&& 0xff).toNat
  let a32 : BitVec 32 := BitVec.ofNat 32 (a &&& 0xffffffff).toNat
  let b32 : BitVec 32 := BitVec.ofNat 32 (b &&& 0xffffffff).toNat
  let c32 : BitVec 32 := BitVec.ofNat 32 (c &&& 0xffffffff).toNat
  let a64 : BitVec 64 := BitVec.ofNat 64 a.toNat
  let b64 : BitVec 64 := BitVec.ofNat 64 b.toNat
  let c64 : BitVec 64 := BitVec.ofNat 64 c.toNat
  match op with
  | 0  => packPair (fpAdd fpFormat32 rm a32 b32)
  | 1  => packPair (fpSub fpFormat32 rm a32 b32)
  | 2  => packPair (fpMul fpFormat32 rm a32 b32)
  | 3  => packPair (fpDiv fpFormat32 rm a32 b32)
  | 4  => packPair (fpSqrt fpFormat32 rm a32)
  | 5  => packPair (fpFma fpFormat32 rm c32 a32 b32)
  | 6  => packPair (fpRint fpFormat32 rm false a32)
  | 7  => packPair (fpConvert fpFormat32 fpFormat64 rm a32)
  | 8  => packPair (fpToInt fpFormat32 32 false rm fbits a32)
  | 9  => packPair (fpToInt fpFormat32 32 true  rm fbits a32)
  | 10 => packPair (fpToInt fpFormat32 64 false rm fbits a32)
  | 11 => packPair (fpToInt fpFormat32 64 true  rm fbits a32)
  | 12 => packPair (fixedToFp fpFormat32 false rm fbits a32)
  | 13 => packPair (fixedToFp fpFormat32 true  rm fbits a32)
  | 14 => packPair (fixedToFp fpFormat32 false rm fbits a64)
  | 15 => packPair (fixedToFp fpFormat32 true  rm fbits a64)
  | 16 => packPair (fpMinMax fpFormat32 false false a32 b32)
  | 17 => packPair (fpMinMax fpFormat32 true  false a32 b32)
  | 18 => packPair (fpMinMax fpFormat32 false true  a32 b32)
  | 19 => packPair (fpMinMax fpFormat32 true  true  a32 b32)
  | 20 => packCmpPair (fpCmp fpFormat32 false a32 b32)
  | 21 => packPair (fpRint fpFormat32 rm true a32)
  | 22 => packCmpPair (fpCmp fpFormat32 true a32 b32)
  | 32 => packPair (fpAdd fpFormat64 rm a64 b64)
  | 33 => packPair (fpSub fpFormat64 rm a64 b64)
  | 34 => packPair (fpMul fpFormat64 rm a64 b64)
  | 35 => packPair (fpDiv fpFormat64 rm a64 b64)
  | 36 => packPair (fpSqrt fpFormat64 rm a64)
  | 37 => packPair (fpFma fpFormat64 rm c64 a64 b64)
  | 38 => packPair (fpRint fpFormat64 rm false a64)
  | 39 => packPair (fpConvert fpFormat64 fpFormat32 rm a64)
  | 40 => packPair (fpToInt fpFormat64 32 false rm fbits a64)
  | 41 => packPair (fpToInt fpFormat64 32 true  rm fbits a64)
  | 42 => packPair (fpToInt fpFormat64 64 false rm fbits a64)
  | 43 => packPair (fpToInt fpFormat64 64 true  rm fbits a64)
  | 44 => packPair (fixedToFp fpFormat64 false rm fbits a32)
  | 45 => packPair (fixedToFp fpFormat64 true  rm fbits a32)
  | 46 => packPair (fixedToFp fpFormat64 false rm fbits a64)
  | 47 => packPair (fixedToFp fpFormat64 true  rm fbits a64)
  | 48 => packPair (fpMinMax fpFormat64 false false a64 b64)
  | 49 => packPair (fpMinMax fpFormat64 true  false a64 b64)
  | 50 => packPair (fpMinMax fpFormat64 false true  a64 b64)
  | 51 => packPair (fpMinMax fpFormat64 true  true  a64 b64)
  | 52 => packCmpPair (fpCmp fpFormat64 false a64 b64)
  | 53 => packPair (fpRint fpFormat64 rm true a64)
  | 54 => packCmpPair (fpCmp fpFormat64 true a64 b64)
  | _  => (0, 0)

/-- Evaluate a single 32-byte `FpBatchRecord` `(metaWord, a, b, c)`, returning the raw 64-bit
    IEEE-754 result (or 4-bit `NZCV` for `FCMP`). -/
def evalFpBatchRecord (metaWord a b c : UInt64) : UInt64 :=
  (evalFpBatchRecordWithFlags metaWord a b c).1

/-- Evaluate the IEEE-754 cumulative `FPSR` exception flags (`IOC=0x01`, `DZC=0x02`, `OFC=0x04`,
    `UFC=0x08`, `IXC=0x10`) raised by a single `FpBatchRecord`. -/
def evalFpBatchRecordFlags (metaWord a b c : UInt64) : UInt64 :=
  (evalFpBatchRecordWithFlags metaWord a b c).2

/-- Evaluate a structured `FpBatchRecord` against `Arm64.Trusted.ISA.Float`. -/
def evalFpRecord (r : FpBatchRecord) : UInt64 :=
  let metaWord : UInt64 :=
    (r.op.toUInt64 &&& (0xff : UInt64)) |||
    ((r.rmCode &&& (0xff : UInt64)) <<< (8 : UInt64)) |||
    ((r.fbits.toUInt64 &&& (0xff : UInt64)) <<< (16 : UInt64))
  evalFpBatchRecord metaWord r.a r.b r.c

/-- Evaluate an `FpBatchRecord` and format its inputs and Lean `Float.lean` output as JSON. -/
def evalFpRecordJson (r : FpBatchRecord) : Json :=
  let rm := decodeRoundMode r.rmCode
  let out := evalFpRecord r
  Json.mkObj [
    ("op", toJson r.op),
    ("op_name", Json.str (fpOpName r.op)),
    ("rm", Json.str (roundModeName rm)),
    ("fbits", toJson r.fbits),
    ("a", Json.str (hex64 (BitVec.ofNat 64 r.a.toNat))),
    ("b", Json.str (hex64 (BitVec.ofNat 64 r.b.toNat))),
    ("c", Json.str (hex64 (BitVec.ofNat 64 r.c.toNat))),
    ("lean_out", Json.str (hex64 (BitVec.ofNat 64 out.toNat)))
  ]

end Testing.Harness
