/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

/-!
# ASCII Decimal Integer Formatting and Parsing

Computable base-10 ASCII formatting and parsing functions over `List (BitVec 8)`.
Unsigned parsers accept non-empty `'0'..'9'` sequences (including leading zeros) within
`0 ≤ n < 2 ^ width`; signed parsers accept an optional leading `'-'` (`0x2d#8`) followed by
non-empty digits (`"-0"` maps to `0 : Int`, rejecting bare `"-"`, leading `'+'`, and whitespace)
within `-2 ^ (width - 1) ≤ z < 2 ^ (width - 1)` for `width > 0`.
-/

@[expose] public section

namespace Arm64

/-- Fuel-bounded helper converting `n` into its base-10 digits (most-significant digit first). -/
def natToDigits10Aux : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
    let acc' := (n % 10) :: acc
    if n < 10 then acc' else natToDigits10Aux fuel (n / 10) acc'

/-- Base-10 digits `0..9` of `n` (`natToDigits10 0 = [0]`), most-significant digit first. -/
def natToDigits10 (n : Nat) : List Nat :=
  natToDigits10Aux (n + 1) n []

/-- Format `n : Nat` as its base-10 ASCII bytes (`'0'..'9'`, `0x30#8..0x39#8`),
    e.g. `0 ↦ [0x30#8]`, `42 ↦ [0x34#8, 0x32#8]`. -/
def formatDecimalNat (n : Nat) : List (BitVec 8) :=
  (natToDigits10 n).map fun d => BitVec.ofNat 8 (0x30 + d)

/-- Format `z : Int` as its base-10 ASCII bytes, prefixing `'-'` (`0x2d#8`) when `z < 0`. -/
def formatDecimalInt (z : Int) : List (BitVec 8) :=
  if z < 0 then 0x2d#8 :: formatDecimalNat z.natAbs
  else formatDecimalNat z.toNat

/-- Parse a non-empty ASCII decimal byte list (`'0'..'9'`, `0x30#8..0x39#8`) into a `Nat`.
    Leading zeros are allowed; returns `none` on `[]` or any non-digit byte. -/
def parseDecimalNat (bs : List (BitVec 8)) : Option Nat :=
  if bs.isEmpty then none
  else
    bs.foldlM (init := 0) fun acc b =>
      if 0x30#8 ≤ b && b ≤ 0x39#8 then
        some (acc * 10 + (b.toNat - 0x30))
      else none

/-- Parse a non-empty ASCII decimal byte list into an unsigned `BitVec width` (`0 ≤ n < 2 ^ width`),
    returning `none` on malformed input or overflow `n ≥ 2 ^ width`. -/
def parseDecimalUInt (width : Nat) (bs : List (BitVec 8)) : Option (BitVec width) :=
  match parseDecimalNat bs with
  | some n => if n < 2 ^ width then some (BitVec.ofNat width n) else none
  | none => none

/-- Parse a non-empty ASCII decimal byte list into an unsigned 64-bit integer (`< 2 ^ 64`). -/
abbrev parseDecimalU64 : List (BitVec 8) → Option (BitVec 64) := parseDecimalUInt 64

/-- Parse a non-empty ASCII decimal byte list into an unsigned 32-bit integer (`< 2 ^ 32`). -/
abbrev parseDecimalU32 : List (BitVec 8) → Option (BitVec 32) := parseDecimalUInt 32

/-- Parse an optional leading `'-'` (`0x2d#8`) followed by non-empty ASCII decimal digits (`'0'..'9'`)
    into an `Int`. `"-0"` parses to `(0 : Int)`; `[]`, bare `"-"`, leading `'+'`, whitespace, and
    non-digit bytes return `none`. -/
def parseDecimalInt : List (BitVec 8) → Option Int
  | 0x2d#8 :: rest => (parseDecimalNat rest).map fun n => -(n : Int)
  | bs => (parseDecimalNat bs).map Int.ofNat

/-- Parse an ASCII signed decimal byte list into a two's-complement `BitVec width`
    (`-2 ^ (width - 1) ≤ z < 2 ^ (width - 1)` for `width > 0`; `none` when `width = 0`, on
    malformed input, or on signed overflow). -/
def parseDecimalSInt (width : Nat) (bs : List (BitVec 8)) : Option (BitVec width) :=
  if width = 0 then none
  else
    match parseDecimalInt bs with
    | some z =>
      let half : Int := Int.ofNat (2 ^ (width - 1))
      if -half ≤ z && z < half then some (BitVec.ofInt width z) else none
    | none => none

/-- Parse an ASCII signed decimal byte list into a two's-complement 64-bit integer
    (`-2 ^ 63 ≤ z < 2 ^ 63`). -/
abbrev parseDecimalI64 : List (BitVec 8) → Option (BitVec 64) := parseDecimalSInt 64

end Arm64
