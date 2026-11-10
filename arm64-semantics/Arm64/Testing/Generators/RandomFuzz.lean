/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Testing.Harness.TestCase

/-!
# Multi-Instruction Random Block Fuzz Generator

Generates deterministic seeded 8-instruction basic blocks with randomized 64-bit register inputs
and initial `NZCV` flags (`buildRandomFuzzSuite`) for differential testing against hardware and
reference ISA emulators. Single-instruction and IEEE-754 floating-point batch fuzzers live in
`tools/run-trusted-tests/src/fuzz.rs`.
-/

@[expose] public section

namespace Testing.Generators

open Arm64
open Testing.Harness

inductive FuzzTemplate where
  | r3 (mnemonic : String) (is32 : Bool)
  | condSel (mnemonic : String) (cond : String)
  | r2 (mnemonic : String)
  | r4 (mnemonic : String)
  deriving Repr, Inhabited

def fuzzTemplates : Array FuzzTemplate := #[
  .r3 "add" false,
  .r3 "adds" false,
  .r3 "sub" false,
  .r3 "subs" false,
  .r3 "add" true,
  .r3 "sub" true,
  .r3 "and" false,
  .r3 "orr" false,
  .r3 "eor" false,
  .r3 "bic" false,
  .r3 "orn" false,
  .r3 "eon" false,
  .condSel "csel" "eq",
  .condSel "csinc" "cs",
  .condSel "csinv" "lt",
  .condSel "csneg" "ge",
  .r2 "rbit",
  .r2 "rev",
  .r2 "rev32",
  .r2 "rev16",
  .r2 "clz",
  .r2 "cls",
  .r3 "lslv" false,
  .r3 "lsrv" false,
  .r3 "asrv" false,
  .r3 "rorv" false,
  .r4 "madd",
  .r4 "msub",
  .r3 "umulh" false,
  .r3 "smulh" false
]

def renderFuzzInst (tmpl : FuzzTemplate) (d n m a : Nat) : String :=
  match tmpl with
  | .r3 mnem true  => s!"{mnem} w{d}, w{n}, w{m}"
  | .r3 mnem false => s!"{mnem} x{d}, x{n}, x{m}"
  | .condSel mnem c => s!"{mnem} x{d}, x{n}, x{m}, {c}"
  | .r2 mnem => s!"{mnem} x{d}, x{n}"
  | .r4 mnem => s!"{mnem} x{d}, x{n}, x{m}, x{a}"

def pad3 (n : Nat) : String :=
  if n < 10 then s!"00{n}"
  else if n < 100 then s!"0{n}"
  else toString n

/-- Generate `count` (default 100) deterministic seeded basic-block test cases
    using `SplitMix64` (`seed` defaults to `20260918`, `insnsPerBlock` defaults to `8`). -/
def buildRandomFuzzSuite (count : Nat := 100) (seed : UInt64 := 20260918)
    (insnsPerBlock : Nat := 8) : Array IsaTestCase := Id.run do
  let mut rng : SplitMix64 := { state := seed }
  let mut cases : Array IsaTestCase := Array.mkEmpty count
  let nInsns := Nat.max 1 insnsPerBlock
  for i in [0:count] do
    let mut lines : Array String := Array.mkEmpty nInsns
    for _ in [0:nInsns] do
      let (tIdx, r1) := rng.nextNat fuzzTemplates.size
      let (d, r2) := r1.nextNat 8
      let (n, r3) := r2.nextNat 8
      let (m, r4) := r3.nextNat 8
      let (a, r5) := r4.nextNat 8
      rng := r5
      lines := lines.push (renderFuzzInst fuzzTemplates[tIdx]! d n m a)
    let mut initRegs : List (Nat × BitVec 64) := []
    for r in [0:8] do
      let (v, rNext) := rng.nextUInt64
      rng := rNext
      initRegs := (r, BitVec.ofNat 64 v.toNat) :: initRegs
    let (nzcv, rNext) := rng.nextNat 16
    rng := rNext
    let asmBlock := String.intercalate "\n" lines.toList
    let caseName :=
      if seed == 20260918 && insnsPerBlock == 8 then
        s!"RandomFuzz/block_{pad3 i}"
      else
        s!"RandomFuzz/seed_{seed}_block_{pad3 i}"
    cases := cases.push (makeAsmTestCase
      caseName
      asmBlock
      (regs := initRegs)
      (nzcv := nzcv))
  return cases

end Testing.Generators
