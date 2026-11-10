/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean.Elab.Term
public import Arm64.Trusted.ISA.Semantics
public meta import Lean.Elab.Term.TermElabM

/-!
# Hexadecimal Instruction-Word Elaborators

Elaboration-time hexadecimal instruction-word parsers and elaborators (`parseHexWords`,
`parseHexWords?`, `hex_words%`, `elabHexWordsStrLit`) and `Program.ofHex` for inline
machine-code specifications.
-/

@[expose] public section

namespace Arm64.Program

meta section

/-- Convert a single hexadecimal character (`0..9`, `a..f`, `A..F`) to its numeric value `0..15`. -/
def hexDigitVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Strip `--` and `//` line comments from a character stream by structural recursion. -/
def stripCommentsChars : Bool → List Char → List Char
  | _, [] => []
  | true, '\n' :: cs => '\n' :: stripCommentsChars false cs
  | true, _ :: cs => stripCommentsChars true cs
  | false, '-' :: '-' :: cs => ' ' :: stripCommentsChars true cs
  | false, '/' :: '/' :: cs => ' ' :: stripCommentsChars true cs
  | false, c :: cs => c :: stripCommentsChars false cs

/-- Extract hexadecimal digit values (`0..15`) from a character stream, skipping `0x`/`0X`
    prefixes, whitespace, and separators. -/
def extractHexDigits : List Char → List Nat
  | [] => []
  | '0' :: 'x' :: cs => extractHexDigits cs
  | '0' :: 'X' :: cs => extractHexDigits cs
  | c :: cs =>
    match hexDigitVal? c with
    | some d => d :: extractHexDigits cs
    | none => extractHexDigits cs

/-- Pack a list of hexadecimal nibbles (`0..15`) into 32-bit instruction words (8 hex digits per word). -/
def hexDigitsToWords : List Nat → List (BitVec 32)
  | d7 :: d6 :: d5 :: d4 :: d3 :: d2 :: d1 :: d0 :: rest =>
    let val :=
      (d7 <<< 28) ||| (d6 <<< 24) ||| (d5 <<< 20) ||| (d4 <<< 16) |||
      (d3 <<< 12) ||| (d2 <<< 8)  ||| (d1 <<< 4)  ||| d0
    BitVec.ofNat 32 val :: hexDigitsToWords rest
  | _ => []

/-- Parse a hex string of 32-bit ARM64 instruction words (e.g.
    `"a9bf7bf3 91000013 97fffffa 8b130000 a8c17bf3 d65f03c0"`, ignoring whitespace,
    separators, `0x` prefixes, and `--`/`//` comments) into `List (BitVec 32)`. -/
def parseHexWords (s : String) : List (BitVec 32) :=
  hexDigitsToWords (extractHexDigits (stripCommentsChars false s.toList))

/-- Optional variant of `parseHexWords` returning `some words` when `s` contains a non-empty
    multiple of 8 hexadecimal digits. -/
def parseHexWords? (s : String) : Option (List (BitVec 32)) :=
  let digits := extractHexDigits (stripCommentsChars false s.toList)
  if !digits.isEmpty && digits.length % 8 == 0 then
    some (hexDigitsToWords digits)
  else
    none

/-- Build a `List (BitVec 32)` kernel expression directly from `words`. -/
def mkWordsExpr (words : List (BitVec 32)) : Lean.Expr :=
  let bv32 := Lean.mkApp (Lean.mkConst ``BitVec) (Lean.mkNatLit 32)
  let nil := Lean.mkApp (Lean.mkConst ``List.nil [0]) bv32
  let cons := Lean.mkApp (Lean.mkConst ``List.cons [0]) bv32
  let ofNat32 := Lean.mkApp (Lean.mkConst ``BitVec.ofNat) (Lean.mkNatLit 32)
  words.foldr (init := nil) fun w acc =>
    Lean.mkApp2 cons (Lean.mkApp ofNat32 (Lean.mkNatLit w.toNat)) acc

/-- Extract a string literal or `++`-concatenation of string literals from `Syntax`
    (with structural fuel `fuel`). -/
def extractStrLitTree? : Nat → Lean.Syntax → Option String
  | 0, _ => none
  | fuel + 1, stx =>
    if let some s := stx.isStrLit? then
      some s
    else if stx.isOfKind ``Lean.Parser.Term.paren then
      extractStrLitTree? fuel (stx[1])
    else if stx.isOfKind ``Lean.Parser.Term.binop &&
        stx[1].getId.eraseMacroScopes == ``HAppend.hAppend then do
      let l ← extractStrLitTree? fuel (stx[2])
      let r ← extractStrLitTree? fuel (stx[3])
      some (l ++ r)
    else if stx.getNumArgs == 3 && stx[1].getAtomVal == "++" then do
      let l ← extractStrLitTree? fuel (stx[0])
      let r ← extractStrLitTree? fuel (stx[2])
      some (l ++ r)
    else
      none

/-- Elaboration-time hex word parsing with instruction-boundary validation: equals
    `parseHexWords str` (same `hexDigitsToWords ∘ extractHexDigits ∘ stripCommentsChars` pipeline),
    but throws an error instead of silently dropping 1-7 trailing hex digits. -/
def elabHexWordsOfStr (str : String) : Lean.Elab.TermElabM Lean.Expr := do
  let digits := extractHexDigits (stripCommentsChars false str.toList)
  if digits.length % 8 != 0 then
    Lean.throwError m!"Hex word string literal has {digits.length} hex digits, which is not a \
      multiple of 8 (each 32-bit ARM64 instruction word requires 8 hex digits)"
  return mkWordsExpr (hexDigitsToWords digits)

/-- Parse a hex string literal (or `++`-concatenated string literals) of 32-bit ARM64 instruction
    words at elaboration time into a concrete `List (BitVec 32)` expression. -/
elab "hex_words% " s:term : term => do
  match extractStrLitTree? 1024 s.raw with
  | some str => elabHexWordsOfStr str
  | none => Lean.Elab.throwUnsupportedSyntax

/-- Elaborate string literals (or `++`-concatenations of string literals) directly to
    `List (BitVec 32)` when the expected type is `List (BitVec 32)`, avoiding any kernel
    `String.toList` / `parseHexWords` reduction. -/
@[term_elab str, term_elab Lean.Parser.Term.binop]
def elabHexWordsStrLit : Lean.Elab.Term.TermElab := fun stx expectedType? => do
  let some expTy := expectedType? | Lean.Elab.throwUnsupportedSyntax
  let expTy ← Lean.Meta.whnf expTy
  if expTy.isAppOfArity ``List 1 then
    let elemTy ← Lean.Meta.whnf (expTy.getArg! 0)
    if elemTy.isAppOfArity ``BitVec 1 then
      let nTy ← Lean.Meta.whnf (elemTy.getArg! 0)
      if nTy.rawNatLit? == some 32 then
        if let some str := extractStrLitTree? 1024 stx then
          return ← elabHexWordsOfStr str
  Lean.Elab.throwUnsupportedSyntax

end

/-- Build a `Program` from a list of 32-bit instruction words (or a hex string literal elaborated
    at elaboration time) starting at `base`, with an optional symbol table `symbols`. -/
def ofHex (base : BitVec 64) (hex : List (BitVec 32))
    (symbols : List (String × BitVec 64) := []) : Program :=
  ofWords base hex symbols

end Arm64.Program
