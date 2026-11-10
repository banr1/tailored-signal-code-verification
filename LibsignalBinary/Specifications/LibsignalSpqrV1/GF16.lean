/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Core
import Batteries.Lean.Except

/-!
# SPQR V1: `GF(2^16)` arithmetic (`src/encoding/gf.rs`)

**Trusted in part.** The theorems of `Computational/Theorems/` use every definition in this file
except `reduce.REDUCE_BYTES`, which is checked by Lean (see
`Computational/docs/TRUSTED_BASE.md`).

Unaccelerated software specification of $\mathrm{GF}(2^{16}) = \mathbb{F}_2[x]/(x^{16} + x^{12} + x^3 + x + 1)$
(`POLY = 0x1100b`, taken under `TokenInit`, DEV-SPQR1): `GF16` (`ZERO`, `ONE`, `new`, `add`, `sub`,
`constSub`, `mul`, `constMul`, `divImpl`, `div`, `constDiv`), byte-table reduction
(`reduceFromByte`, `REDUCE_BYTES`, `reduceByteEntry`, `polyReduce`), carryless multiplication
(`polyMul`), and paired/slice scaling (`mul2U16`, `parallelMult`). All `GF16` operations are
panic- and overflow-free on `u16` inputs; division computes `self * other^(2^16 - 2)` so division
by `0` returns `0`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalSpqrV1

/-! ## Field polynomial and element type (`src/encoding/gf.rs:7–18`) -/

/-- Irreducible polynomial $x^{16} + x^{12} + x^3 + x + 1$ for $\mathrm{GF}(2^{16})$
(`pub const POLY: u32 = 0x1100b`, `src/encoding/gf.rs:7`). -/
def POLY : BitVec 32 := 0x1100b#32

/-- Element of $\mathrm{GF}(2^{16})$ (`pub struct GF16 { pub value: u16 }`,
`src/encoding/gf.rs:16–18`). -/
structure GF16 where
  value : BitVec 16
  deriving DecidableEq, Repr, Inhabited

namespace GF16

def ZERO : GF16 := ⟨0#16⟩

def ONE : GF16 := ⟨1#16⟩

def new (value : BitVec 16) : GF16 := ⟨value⟩

/-! ## Addition and subtraction in $\mathrm{GF}(2^{16})$ (`src/encoding/gf.rs:20–123, 565–569`) -/

def add (self other : GF16) : GF16 :=
  ⟨self.value ^^^ other.value⟩

def sub (self other : GF16) : GF16 :=
  add self other

def constSub (self other : GF16) : GF16 :=
  ⟨self.value ^^^ other.value⟩

end GF16

/-! ## Polynomial reduction modulo `POLY` (`src/encoding/gf.rs:449–538`) -/

namespace reduce

def reduceFromByteLoop : Nat → BitVec 8 → BitVec 32 → BitVec 32
  | 0, _, out => out
  | i + 1, a, out =>
    let mask : BitVec 8 := 1#8 <<< i
    if (mask &&& a) != 0#8 then
      let shiftedPoly : BitVec 32 := POLY <<< i
      let out' := out ^^^ shiftedPoly
      let a' := a ^^^ ((shiftedPoly >>> 16).truncate 8)
      reduceFromByteLoop i a' out'
    else
      reduceFromByteLoop i a out

/-- `reduce::reduce_from_byte(mut a: u8) -> u32` (`src/encoding/gf.rs:502–515`). -/
def reduceFromByte (a : BitVec 8) : BitVec 32 :=
  reduceFromByteLoop 8 a 0#32

/-- Precomputed 256-entry reduction table `reduce::REDUCE_BYTES` (`src/encoding/gf.rs:519–537`). -/
def REDUCE_BYTES : List (BitVec 16) :=
  (List.range 256).map (fun i => (reduceFromByte (BitVec.ofNat 8 i)).truncate 16)

def reduceByteEntry (idx : BitVec 8) : BitVec 16 :=
  (reduceFromByte idx).truncate 16

/-- `reduce::poly_reduce(v: u32) -> u16` (`src/encoding/gf.rs:489–498`): reduces a 32-bit
carryless product modulo `POLY = 0x1100b` in two byte-table lookups. -/
def polyReduce (v : BitVec 32) : BitVec 16 :=
  let i1 : BitVec 8 := (v >>> 24).truncate 8
  let r1 : BitVec 32 := (reduceByteEntry i1).zeroExtend 32
  let v1 : BitVec 32 := v ^^^ (r1 <<< 8)
  let i2 : BitVec 8 := (v1 >>> 16).truncate 8
  let r2 : BitVec 32 := (reduceByteEntry i2).zeroExtend 32
  let v2 : BitVec 32 := v1 ^^^ r2
  v2.truncate 16

end reduce

/-! ## Unaccelerated carryless multiplication (`src/encoding/gf.rs:375–447`) -/

namespace unaccelerated

def polyMulLoop (me : BitVec 32) (b : BitVec 16) : Nat → Nat → BitVec 32 → BitVec 32
  | 0, _, acc => acc
  | fuel + 1, shift, acc =>
    let acc' :=
      if 0#16 != (b &&& (1#16 <<< shift)) then
        acc ^^^ (me <<< shift)
      else
        acc
    polyMulLoop me b fuel (shift + 1) acc'

/-- `unaccelerated::poly_mul(a: u16, b: u16) -> u32` (`src/encoding/gf.rs:381–427`). -/
def polyMul (a b : BitVec 16) : BitVec 32 :=
  polyMulLoop (a.zeroExtend 32) b 16 0 0#32

/-- `unaccelerated::mul(a: u16, b: u16) -> u16` (`src/encoding/gf.rs:444–446`). -/
def mul (a b : BitVec 16) : BitVec 16 :=
  reduce.polyReduce (polyMul a b)

end unaccelerated

/-! ## Pair multiplication, field multiplication, and division (`src/encoding/gf.rs:125–225, 548–589`) -/

/-- `mul2_u16` (`src/encoding/gf.rs:216–225`, unaccelerated path). -/
def mul2U16 (a b1 b2 : BitVec 16) : BitVec 16 × BitVec 16 :=
  (unaccelerated.mul a b1, unaccelerated.mul a b2)

/-- `parallel_mult` (`src/encoding/gf.rs:201–214`). -/
def parallelMult (a : GF16) : List GF16 → List GF16
  | [] => []
  | [x] => [⟨unaccelerated.mul x.value a.value⟩]
  | x1 :: x2 :: rest =>
    let (r1, r2) := mul2U16 a.value x1.value x2.value
    ⟨r1⟩ :: ⟨r2⟩ :: parallelMult a rest

namespace GF16

def mul (self other : GF16) : GF16 :=
  ⟨unaccelerated.mul self.value other.value⟩

def constMul (self other : GF16) : GF16 :=
  ⟨unaccelerated.mul self.value other.value⟩

def divImplLoop : Nat → BitVec 16 → BitVec 16 → BitVec 16
  | 0, _, out => out
  | n + 1, square, out =>
    let (square', out') := mul2U16 square square out
    divImplLoop n square' out'

/-- `GF16::div_impl` (`src/encoding/gf.rs:548–557`): `self * other^(2^16 - 2)` (`ZERO` when
`other = ZERO`). -/
def divImpl (self other : GF16) : GF16 :=
  let square := (mul other other).value
  let out := self.value
  ⟨divImplLoop 15 square out⟩

def div (self other : GF16) : GF16 :=
  divImpl self other

def constDivLoop : Nat → GF16 → GF16 → GF16
  | 0, _, out => out
  | n + 1, square, out =>
    let square' := square.constMul square
    let out' := out.constMul square'
    constDivLoop n square' out'

def constDiv (self other : GF16) : GF16 :=
  constDivLoop 15 other self

end GF16

/-! ## Test vectors -/

theorem test_gf_barrett_vector :
    unaccelerated.polyMul 0x00f5#16 0x0093#16 = 0x000074cf#32 ∧
    reduce.polyReduce 0x000074cf#32 = 0x74cf#16 ∧
    unaccelerated.mul 0x00f5#16 0x0093#16 = 0x74cf#16 := by
  decide +kernel

theorem test_reduce_bytes_spot :
    reduce.REDUCE_BYTES.length = 256 ∧
    reduce.reduceByteEntry 0x00#8 = 0x0000#16 ∧
    reduce.reduceByteEntry 0x01#8 = 0x100b#16 ∧
    reduce.reduceByteEntry 0x02#8 = 0x2016#16 ∧
    reduce.reduceByteEntry 0x08#8 = 0x8058#16 ∧
    reduce.reduceByteEntry 0x10#8 = 0x10bb#16 ∧
    reduce.reduceByteEntry 0x80#8 = 0x85d8#16 ∧
    reduce.reduceByteEntry 0xff#8 = 0x0690#16 := by
  decide +kernel

theorem test_poly_reduce_multiples_of_poly :
    (List.range 16).all (fun k => reduce.polyReduce (POLY <<< k) == 0#16) = true := by
  decide +kernel

theorem test_poly_reduce_low16_id :
    reduce.polyReduce 0x00000000#32 = 0x0000#16 ∧
    reduce.polyReduce 0x00000001#32 = 0x0001#16 ∧
    reduce.polyReduce 0x0000beef#32 = 0xbeef#16 ∧
    reduce.polyReduce 0x0000ffff#32 = 0xffff#16 := by
  decide +kernel

theorem test_poly_reduce_monomials :
    reduce.polyReduce 0x00010000#32 = 0x100b#16 ∧
    reduce.polyReduce 0x00020000#32 = 0x2016#16 ∧
    reduce.polyReduce 0x01000000#32 = 0x1bbb#16 ∧
    reduce.polyReduce 0x80000000#32 = 0x0dff#16 := by
  decide +kernel

theorem test_gf16_add_sub :
    GF16.add GF16.ZERO ⟨0x1234#16⟩ = ⟨0x1234#16⟩ ∧
    GF16.add ⟨0x1234#16⟩ ⟨0x1234#16⟩ = GF16.ZERO ∧
    GF16.sub ⟨0xabcd#16⟩ ⟨0x1234#16⟩ = GF16.add ⟨0xabcd#16⟩ ⟨0x1234#16⟩ ∧
    GF16.constSub ⟨0xabcd#16⟩ ⟨0x1234#16⟩ = ⟨0xb9f9#16⟩ := by
  decide +kernel

theorem test_gf16_mul_zero_one :
    GF16.mul GF16.ZERO GF16.ZERO = GF16.ZERO ∧
    GF16.mul GF16.ZERO GF16.ONE = GF16.ZERO ∧
    GF16.mul GF16.ONE GF16.ZERO = GF16.ZERO ∧
    GF16.mul GF16.ONE GF16.ONE = GF16.ONE ∧
    GF16.mul ⟨0xffff#16⟩ GF16.ZERO = GF16.ZERO ∧
    GF16.mul ⟨0xffff#16⟩ GF16.ONE = ⟨0xffff#16⟩ ∧
    GF16.mul GF16.ONE ⟨0xffff#16⟩ = ⟨0xffff#16⟩ := by
  decide +kernel

theorem test_gf16_generator_wrap :
    unaccelerated.mul 0x8000#16 0x0002#16 = 0x100b#16 ∧
    unaccelerated.mul 0x0002#16 0x8000#16 = 0x100b#16 ∧
    unaccelerated.mul 0x4000#16 0x0004#16 = 0x100b#16 := by
  decide +kernel

theorem test_gf16_ring_laws_sample :
    let a : GF16 := ⟨0x9d2c#16⟩
    let b : GF16 := ⟨0x56ef#16⟩
    let c : GF16 := ⟨0xa731#16⟩
    GF16.mul a b = GF16.mul b a ∧
    GF16.mul (GF16.mul a b) c = GF16.mul a (GF16.mul b c) ∧
    GF16.mul a (GF16.add b c) = GF16.add (GF16.mul a b) (GF16.mul a c) := by
  decide +kernel

theorem test_mul2_u16_and_parallel_mult :
    mul2U16 0x9d2c#16 0x56ef#16 0xa731#16 =
      (unaccelerated.mul 0x9d2c#16 0x56ef#16, unaccelerated.mul 0x9d2c#16 0xa731#16) ∧
    parallelMult ⟨0x0002#16⟩ [⟨0x0001#16⟩, ⟨0x8000#16⟩, ⟨0x4000#16⟩] =
      [⟨0x0002#16⟩, ⟨0x100b#16⟩, ⟨0x8000#16⟩] ∧
    parallelMult ⟨0x0002#16⟩ [] = [] := by
  decide +kernel

theorem test_gf16_div_by_zero :
    GF16.divImpl GF16.ZERO GF16.ZERO = GF16.ZERO ∧
    GF16.divImpl GF16.ONE GF16.ZERO = GF16.ZERO ∧
    GF16.divImpl ⟨0x1234#16⟩ GF16.ZERO = GF16.ZERO ∧
    GF16.divImpl ⟨0xffff#16⟩ GF16.ZERO = GF16.ZERO ∧
    GF16.constDiv ⟨0x1234#16⟩ GF16.ZERO = GF16.ZERO := by
  decide +kernel

theorem test_gf16_div_zero_and_one :
    GF16.div GF16.ZERO GF16.ONE = GF16.ZERO ∧
    GF16.div GF16.ZERO ⟨0xbeef#16⟩ = GF16.ZERO ∧
    GF16.div GF16.ONE GF16.ONE = GF16.ONE ∧
    GF16.div ⟨0xbeef#16⟩ GF16.ONE = ⟨0xbeef#16⟩ ∧
    GF16.div ⟨0xffff#16⟩ GF16.ONE = ⟨0xffff#16⟩ := by
  decide +kernel

theorem test_gf16_inv_generator :
    GF16.div GF16.ONE ⟨0x0002#16⟩ = ⟨0x8805#16⟩ ∧
    GF16.mul ⟨0x0002#16⟩ ⟨0x8805#16⟩ = GF16.ONE ∧
    GF16.div GF16.ONE ⟨0x8805#16⟩ = ⟨0x0002#16⟩ := by
  decide +kernel

theorem test_gf16_inverses_batch :
    ([0x0001#16, 0x0002#16, 0x0003#16, 0x00ff#16, 0x0100#16, 0x100b#16,
      0x1234#16, 0x5678#16, 0x8000#16, 0x9abc#16, 0xdead#16, 0xffff#16].all (fun v =>
      let a : GF16 := ⟨v⟩
      let inv := GF16.div GF16.ONE a
      GF16.mul a inv == GF16.ONE && GF16.mul inv a == GF16.ONE)) = true := by
  decide +kernel

theorem test_gf16_mul_div_roundtrip :
    ([(0x0001#16, 0xffff#16),
      (0xffff#16, 0xffff#16),
      (0x00f5#16, 0x0093#16),
      (0x1234#16, 0x5678#16),
      (0xdead#16, 0xbeef#16),
      (0x8000#16, 0x8000#16),
      (0x100b#16, 0x8805#16),
      (0x0042#16, 0x7fff#16),
      (0xcafe#16, 0xbabe#16),
      (0x0102#16, 0x0304#16)].all (fun (x, y) =>
      let a : GF16 := ⟨x⟩
      let b : GF16 := ⟨y⟩
      GF16.div (GF16.mul a b) b == a &&
      GF16.mul (GF16.div a b) b == a &&
      GF16.constDiv a b == GF16.div a b)) = true := by
  decide +kernel

theorem test_is_non_zero_all_u8 :
    isNonZero 0x00#8 = 0#8 ∧
    isNonZero 0x01#8 = 1#8 ∧
    isNonZero 0x7f#8 = 1#8 ∧
    isNonZero 0x80#8 = 1#8 ∧
    isNonZero 0xff#8 = 1#8 ∧
    ((List.range 256).all (fun i =>
      let b := BitVec.ofNat 8 i
      isNonZero b == (if b == 0#8 then 0#8 else 1#8))) = true := by
  decide +kernel

theorem test_is_non_zero_aarch64_equiv :
    ((List.range 256).all (fun i =>
      let b := BitVec.ofNat 8 i
      let asm := ((0#32 - b.zeroExtend 32) >>> 31).truncate 8
      isNonZero b == asm)) = true := by
  decide +kernel

theorem test_util_compare :
    compare [] [] = .ok 0#8 ∧
    compare [0x12#8, 0x34#8, 0x56#8] [0x12#8, 0x34#8, 0x56#8] = .ok 0#8 ∧
    compare [0x12#8, 0x34#8, 0x56#8] [0x12#8, 0x35#8, 0x56#8] = .ok 1#8 ∧
    compare [0x00#8] [0x80#8] = .ok 1#8 ∧
    compare [0x12#8, 0x34#8] [0x12#8, 0x34#8, 0x56#8] = .ok 0#8 ∧
    compare [0x12#8, 0x34#8, 0x56#8] [0x12#8, 0x34#8] = .error .compareBounds := by
  decide +kernel

theorem test_gf16_concrete_mul_vectors :
    unaccelerated.mul 0xffff#16 0xffff#16 = 0x0733#16 ∧
    unaccelerated.mul 0x1234#16 0x5678#16 = 0x6324#16 ∧
    unaccelerated.mul 0xdead#16 0xbeef#16 = 0xa837#16 ∧
    unaccelerated.mul 0xcafe#16 0xbabe#16 = 0xcb57#16 := by
  decide +kernel

theorem test_gf16_concrete_div_vectors :
    (GF16.div ⟨0x6324#16⟩ ⟨0x5678#16⟩).value = 0x1234#16 ∧
    (GF16.div ⟨0x6324#16⟩ ⟨0x1234#16⟩).value = 0x5678#16 ∧
    (GF16.div ⟨0xa837#16⟩ ⟨0xbeef#16⟩).value = 0xdead#16 ∧
    (GF16.div ⟨0xcb57#16⟩ ⟨0xbabe#16⟩).value = 0xcafe#16 := by
  decide +kernel

end CryptoVerification.LibsignalSpqrV1
