/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import LibsignalBinary.Specifications.LibsignalSignalMessage -- shake: keep
public import LibsignalBinary.Specifications.LibsignalSignalMessage
public meta import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToAdditive
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import VCVio.Prelude.Core

/-!
# Differential Test of `protoSignalCodec` Against `prost` 0.14.4

Checks `CryptoVerification.LibsignalProtoCodec.protoSignalCodec` at elaboration time against the
seed-generated `prost` 0.14.4 test vectors in `data/prost_signal_vectors.txt`. Verifies decode
failure (`D <hex> ERR`), decode agreement (`D <hex> OK <fields>`), and encode plus round-trip
agreement (`E <fields> <hex>`), where `-` denotes empty/`none`, `x<hex>` a byte field, and decimal
literals `uint32` fields.
-/

@[expose] public section

namespace CryptoVerification.LibsignalProtoCodec.DiffTest

open CryptoGames.LibsignalSession CryptoVerification.LibsignalProtoCodec

open Lean Elab Term in
/-- Path to `data/prost_signal_vectors.txt` relative to this source file. -/
elab "vectors_path%" : term => do
  let f ← IO.FS.realPath (← getFileName)
  return Lean.mkStrLit ((f.parent.getD ".") / "data" / "prost_signal_vectors.txt").toString

def hexDigit (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def parseHexChars : List Char → Option (List (BitVec 8))
  | [] => some []
  | a :: b :: rest => do
    let x ← hexDigit a
    let y ← hexDigit b
    let r ← parseHexChars rest
    return BitVec.ofNat 8 (16 * x + y) :: r
  | [_] => none

def parseHex (s : String) : Option (List (BitVec 8)) :=
  if s == "-" then some [] else parseHexChars s.toList

def parseBytesField (s : String) : Option (Option (List (BitVec 8))) :=
  if s == "-" then some none
  else match s.toList with
    | 'x' :: rest => (parseHexChars rest).map some
    | _ => none

def parseU32Field (s : String) : Option (Option (BitVec 32)) :=
  if s == "-" then some none else s.toNat?.map fun n => some (BitVec.ofNat 32 n)

def parseMsg : List String → Option ProtoSignalMessage
  | [a, b, c, d, e, f] => do
    return { ratchetKey := ← parseBytesField a, counter := ← parseU32Field b,
             previousCounter := ← parseU32Field c, ciphertext := ← parseBytesField d,
             pqRatchet := ← parseBytesField e, addresses := ← parseBytesField f }
  | _ => none

/-- Validates one vector line, returning `none` on blank/comment lines or `'D'`/`'E'` on match. -/
def checkLine (line : String) : Except String (Option Char) :=
  match line.splitOn " " |>.filter (· ≠ "") with
  | [] => .ok none
  | "#" :: _ => .ok none
  | ["D", inp, "ERR"] =>
    match parseHex inp with
    | none => .error s!"unparsable: {line}"
    | some bs => if (protoSignalCodec.decode bs).isNone then .ok (some 'D')
      else .error s!"decode should fail: {line}"
  | "D" :: inp :: "OK" :: fs =>
    match parseHex inp, parseMsg fs with
    | some bs, some m =>
      if protoSignalCodec.decode bs = some m then .ok (some 'D')
      else .error s!"decode mismatch: {line}"
    | _, _ => .error s!"unparsable: {line}"
  | ["E", a, b, c, d, e, f, enc] =>
    match parseMsg [a, b, c, d, e, f], parseHex enc with
    | some m, some bs =>
      if protoSignalCodec.encode m ≠ bs then .error s!"encode mismatch: {line.take 300}"
      else if protoSignalCodec.decode bs ≠ some m then .error s!"decode of encoding: {line.take 300}"
      else .ok (some 'E')
    | _, _ => .error s!"unparsable: {line.take 300}"
  | _ => .error s!"unknown line: {line.take 300}"

#eval show IO Unit from do
  let t0 ← IO.monoMsNow
  let txt ← IO.FS.readFile vectors_path%
  let mut nD := 0
  let mut nE := 0
  let mut errs : Array String := #[]
  for line in txt.splitOn "\n" do
    match checkLine line with
    | .ok none => pure ()
    | .ok (some 'D') => nD := nD + 1
    | .ok (some _) => nE := nE + 1
    | .error e => errs := errs.push e
  unless errs.isEmpty do
    throw (IO.userError s!"{errs.size} MISMATCHES, first: {errs.toList.take 10}")
  unless nD ≥ 5000 ∧ nE ≥ 1000 do
    throw (IO.userError s!"too few vectors: {nD} decode, {nE} encode")
  IO.println s!"protoSignalCodec agrees with prost 0.14.4 on all {nD} decode and {nE} encode vectors ({(← IO.monoMsNow) - t0} ms)"

end CryptoVerification.LibsignalProtoCodec.DiffTest
