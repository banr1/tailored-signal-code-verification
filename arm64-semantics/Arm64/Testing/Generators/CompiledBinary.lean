/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Arm64
public import Arm64.Testing.Harness.Encode
public import Arm64.Testing.Harness.TestCase
public import Arm64.Testing.Generators.CompiledBinaryFixture

/-!
# Compiled Binary Test Generators

Differential and decode/encode round-trip test generators backed by compiled `rustc -O` ELF object
placements (`CompiledBinaryFixture`).
-/

@[expose] public section

namespace Testing.Generators

open Lean
open Arm64
open Testing.Harness

/-- Extract the 32-bit little-endian instruction words of a `Program`, up to its first extern
    stub (the stubs follow the defined code and are hooks, not instructions). -/
def programWords (prog : Program) : Array (BitVec 32) := Id.run do
  let codeEnd := prog.stubs.foldl (fun m (_, off) => min m off) prog.code.length
  let numWords := codeEnd / 4
  let mut out : Array (BitVec 32) := Array.mkEmpty numWords
  for i in [0:numWords] do
    if let some w := prog.readWordOff (i * 4) then
      out := out.push w
  return out

open Lean in
/-- Replace every constant of `env` marked `noncomputable` in `e` by its (recursively inlined)
    definition body. -/
meta partial def inlineNoncomputable (env : Environment) (e : Expr) : Expr :=
  e.replace fun
    | .const c [] =>
      if isNoncomputable env c then
        match env.find? c with
        | some (.defnInfo d) => some (inlineNoncomputable env d.value)
        | _ => none
      else none
    | _ => none

open Lean Elab Term in
/-- `def_value% c` elaborates to the body of `c` with all `noncomputable` constants recursively
    inlined, allowing executable test runners to compile small exported fixture definitions. -/
elab "def_value% " id:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let some (.defnInfo d) := (← getEnv).find? n | throwError "`{n}` is not a definition"
  unless d.levelParams.isEmpty do throwError "`{n}` is universe polymorphic"
  return inlineNoncomputable (← getEnv) d.value

/-- Default placement of `fixturePlacedLib` at `codeBase`, placing extern stubs right after `.text`. -/
def fixturePlacement : Obj.Placement :=
  { base := codeBase
    ρ := fun s =>
      match fixturePlacedLib.text.externs.idxOf? s with
      | some idx => codeBase + BitVec.ofNat 64 (fixturePlacedLib.text.code.length + 4 * idx)
      | none => codeBase + BitVec.ofNat 64 fixturePlacedLib.text.code.length }

/-- The compiled Rust fixture placed at `codeBase` with the Rust panic hooks. -/
def fixtureProg : Program :=
  fixturePlacedLib.program fixturePlacement Rust.withPanics

/-- Instruction words of `fixtureProg`. -/
def fixtureWords : List (BitVec 32) := (programWords fixtureProg).toList

/-- Words that fail to `decode` or do not `encode` back to the original 32-bit word. -/
def codecMismatches (words : List (BitVec 32)) : List (BitVec 32) :=
  words.filter fun w =>
    match decode w with
    | none => true
    | some inst => encode inst != some w

/-- Execute `prog` from `entry` until it returns to `0xdead0000`. -/
def runExportedProg (prog : Program) (entry : BitVec 64) (s0 : State) (fuel : Nat := 200) : State :=
  runProgram prog entry s0 fuel

/-- Print the instruction count of `fixtureWords` and report any decode/encode mismatches. -/
def reportRustExportCodec : IO Unit := do
  let words := fixtureWords
  let bad := codecMismatches words
  IO.println
    s!"Compiled Rust fixture image: {words.length} instruction words, \
       {words.length - bad.length} decode and re-encode identically"
  for w in bad do
    IO.eprintln s!"[FAIL] exported Rust word does not round-trip: {w}"

/-- Create a differential test case directly from a compiled Rust `Program`. -/
def makeProgTestCase
    (name : String)
    (prog : Program)
    (fnSymbol : String)
    (regs : List (Nat × BitVec 64) := [])
    (sp : BitVec 64 := defaultSP)
    (nzcv : Nat := 0)
    (memInitU64 : List (BitVec 64 × BitVec 64) := [])
    (memWatchU64 : List (BitVec 64) := [])
    (maxSteps : Nat := 500) : IsaTestCase :=
  { name := name
    asm := none
    basePC := prog.base
    startPC := prog.fnAddr fnSymbol
    exitPC := exitPC
    maxSteps := maxSteps
    words := programWords prog
    regs := initRegArray regs
    sp := sp
    nzcv := nzcv
    memInit := (memInitU64.map fun (a, v) => { addr := a, val := v, size := 8 }).toArray
    memWatch := (memWatchU64.map fun a => { addr := a, size := 8 }).toArray }

/-- Differential test cases executing compiled `rustc -O` subroutines from `fixtureProg`. -/
def compiledRustSubroutineCases : Array IsaTestCase := #[
  makeProgTestCase
    "RustExport/functions::arith_shift(10)"
    fixtureProg "examples::functions::arith_shift"
    (regs := [(0, 10#64)]),

  makeProgTestCase
    "RustExport/functions::max_u64(100, 250)"
    fixtureProg "examples::functions::max_u64"
    (regs := [(0, 100#64), (1, 250#64)]),

  makeProgTestCase
    "RustExport/functions::clamp_u64(500, 100, 300)"
    fixtureProg "examples::functions::clamp_u64"
    (regs := [(0, 500#64), (1, 100#64), (2, 300#64)]),

  makeProgTestCase
    "RustExport/functions::abs_diff_u64(42, 100)"
    fixtureProg "examples::functions::abs_diff_u64"
    (regs := [(0, 42#64), (1, 100#64)]),

  makeProgTestCase
    "RustExport/functions::saturating_add_u64(UINT64_MAX, 10)"
    fixtureProg "examples::functions::saturating_add_u64"
    (regs := [(0, 0xffffffffffffffff#64), (1, 10#64)]),

  makeProgTestCase
    "RustExport/functions::extract_bitfield(0x123456789abcdef0)"
    fixtureProg "examples::functions::extract_bitfield"
    (regs := [(0, 0x123456789abcdef0#64)]),

  makeProgTestCase
    "RustExport/functions::bit_tricks"
    fixtureProg "examples::functions::bit_tricks"
    (regs := [(0, 0xf0f0f0f00f0f0f0f#64), (1, 0x123456789abcdef0#64)]),

  makeProgTestCase
    "RustExport/functions::widening_mul_u64"
    fixtureProg "examples::functions::widening_mul_u64"
    (regs := [(0, 0x123456789abcdef0#64), (1, 0xfedcba9876543210#64)]),

  makeProgTestCase
    "RustExport/functions::mem_swap"
    fixtureProg "examples::functions::mem_swap"
    (regs := [(0, dataBase), (1, dataBase + 8#64)])
    (memInitU64 := [(dataBase, 0x1111222233334444#64), (dataBase + 8#64, 0x5555666677778888#64)])
    (memWatchU64 := [dataBase, dataBase + 8#64]),

  makeProgTestCase
    "RustExport/functions::pair_sum_diff"
    fixtureProg "examples::functions::pair_sum_diff"
    (regs := [(0, dataBase), (1, dataBase + 16#64)])
    (memInitU64 := [(dataBase, 100#64), (dataBase + 8#64, 35#64)])
    (memWatchU64 := [dataBase + 16#64, dataBase + 24#64]),

  makeProgTestCase
    "RustExport/functions::countdown_loop"
    fixtureProg "examples::functions::countdown_loop"
    (regs := [(0, 0x123456789abcdef0#64), (1, 10#64)]),

  makeProgTestCase
    "RustExport/algorithms::fnv1a_u64"
    fixtureProg "examples::algorithms::fnv1a_u64"
    (regs := [(0, dataBase), (1, 3#64)])
    (memInitU64 := [(dataBase, 0x1122334455667788#64), (dataBase + 8#64, 0x99aabbccddeeff00#64), (dataBase + 16#64, 0x0123456789abcdef#64)]),

  makeProgTestCase
    "RustExport/algorithms::gcd_u64(1071, 462)"
    fixtureProg "examples::algorithms::gcd_u64"
    (regs := [(0, 1071#64), (1, 462#64)]),

  makeProgTestCase
    "RustExport/algorithms::pow_u64(3, 13)"
    fixtureProg "examples::algorithms::pow_u64"
    (regs := [(0, 3#64), (1, 13#64)])
]

end Testing.Generators
