/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean

/-!
# Compile-Time ASCII Literal Macros

Compile-time checked ASCII character and string macros (`asciiCode!`, `asciic!`, and `ascii!`)
producing `Nat`, `BitVec 8`, and `List (BitVec 8)` literals and rejecting code points `>= 128` at
elaboration time.
-/

@[expose] public section

namespace Arm64

/-- Convert a single-character ASCII literal (`< 128`) to its numeric code point (`Nat`),
    e.g. `asciiCode!"0" = 48`. -/
macro:max "asciiCode!" s:str : term => do
  match s.getString.toList with
  | [ch] =>
    if ch.toNat ≥ 128 then
      Lean.Macro.throwError s!"asciiCode! expects an ASCII character (< 128), got '{ch}'"
    let numStx := Lean.Syntax.mkNumLit (toString ch.toNat)
    `(($numStx : _root_.Nat))
  | _ =>
    Lean.Macro.throwError "asciiCode! expects a single-character ASCII string literal"

/-- Convert a single-character ASCII literal (`< 128`) to its 8-bit byte (`BitVec 8`),
    e.g. `asciic!"0" = 48#8`, `asciic!"." = 46#8`, `asciic!"-" = 45#8`, `asciic!"e" = 101#8`. -/
macro:max "asciic!" s:str : term => do
  match s.getString.toList with
  | [ch] =>
    if ch.toNat ≥ 128 then
      Lean.Macro.throwError s!"asciic! expects an ASCII character (< 128), got '{ch}'"
    let numStx := Lean.Syntax.mkNumLit (toString ch.toNat)
    `(_root_.BitVec.ofNat 8 $numStx)
  | _ =>
    Lean.Macro.throwError "asciic! expects a single-character ASCII string literal"

/-- Convert an ASCII string literal (`< 128` per character) to its byte list (`List (BitVec 8)`),
    e.g. `ascii!"" = []`, `ascii!"NaN" = [78#8, 97#8, 78#8]`. -/
macro:max "ascii!" s:str : term => do
  let chars := s.getString.toList.toArray
  if chars.isEmpty then
    `(([] : _root_.List (_root_.BitVec 8)))
  else
    let elems ← chars.mapM fun ch => do
      if ch.toNat ≥ 128 then
        Lean.Macro.throwError s!"ascii! expects ASCII characters (< 128), got '{ch}'"
      let numStx := Lean.Syntax.mkNumLit (toString ch.toNat)
      `(_root_.BitVec.ofNat 8 $numStx)
    `([$[$elems],*])

end Arm64
