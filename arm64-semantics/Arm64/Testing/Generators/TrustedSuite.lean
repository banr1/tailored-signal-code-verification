/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean.Data.Json
public import Arm64
public import Arm64.Testing.Harness.Encode
public import Arm64.Testing.Harness.TestCase
public import Arm64.Testing.Generators.ExternalSuites
public import Arm64.Testing.Generators.HandWrittenVectors
public import Arm64.Testing.Generators.RandomFuzz
public import Arm64.Testing.Generators.CompiledBinary

/-!
# Assembled Differential Suite & Generator-to-JSON Glue (`Arm64.Testing.Generators.TrustedSuite`)

- **Layer / Role**: Untrusted ISA differential test suite aggregator & JSON export glue (`Lib::Arm64Testing`, `Role::Test`).
- **Purpose & Key Exports**: Connects the four `IsaTestCase` generator modules into the canonical
  JSON test suite consumed by `lake exe diff_eval` and `tools/run-trusted-tests`:
  1. `ExternalSuites`: Unicorn `test_arm64.c` (1) + ARM VIXL simulator vectors (44).
  2. `HandWrittenVectors`: C algorithmic loops (3) + ISA surface & scalar FP (16) + extended
     FP/SIMD/LSE/RCpc/CRC32/ASL/single-step/tie-to-even/FPSR boundary vectors (46).
  3. `RandomFuzz`: 100 deterministic seeded 8-instruction blocks (`buildRandomFuzzSuite 100`), plus
     on-demand freshly seeded random blocks (`buildRandomFuzzSuite count seed insnsPerBlock`).
  4. `CompiledBinary`: 14 compiled `rustc -O` subroutines from `Arm64.Testing.Generators.CompiledBinaryFixture`.
  5. **Generator $\to$ JSON Glue**: `suiteToJson`, `dumpTrustedSuiteJson`, and `dumpRandomSuiteJson`
     serialize any `Array IsaTestCase` into the wire JSON format (`lake exe diff_eval --dump-suite`
     and `lake exe diff_eval --dump-random <seed> <count> [<insns_per_block>]`).
- **When to build / read**: Imported by `Arm64.Testing.Harness.DifferentialEval` (`lake exe diff_eval`)
  and `Arm64.Testing.Regression.UnitTests`.
-/

@[expose] public section

namespace Testing.TrustedSuite

open Lean
open Arm64
open Testing.Harness

export Testing.Harness (
  codeBase dataBase defaultSP exitPC
  hex64 hex128
  MemWrite MemWatch
  IsaTestCase DiffTestCase
  initRegArray initVRegArray makeAsmTestCase
  SplitMix64 testCaseToJson
)

export Testing.Generators (
  programWords inlineNoncomputable fixturePlacement fixtureProg
  fixtureWords codecMismatches runExportedProg reportRustExportCodec
  makeProgTestCase compiledRustSubroutineCases
  FuzzTemplate fuzzTemplates renderFuzzInst pad3 buildRandomFuzzSuite
  unicornTestArm64Cases vixlAluAndLoadStoreCases vixlBranchCases vixlSimulatorCases
  cAlgorithmicSubroutineCases isaSurfaceAndScalarFpCases
  extendedFpSimdAtomicsAndBoundaryCases handWrittenVectorCases
)

/-- Complete differential test suite (224 cases, 10,526 instruction words):
    Unicorn `test_arm64.c` (1) + VIXL ALU/load-store (43) + C algorithmic loops (3) + VIXL branches (1)
    + 100 seeded 8-instruction random fuzz blocks (100) + ISA surface & scalar FP (16)
    + compiled `rustc -O` subroutines (14) + extended FP/SIMD/Atomics/ASL/single-step/FPSR vectors (46). -/
def buildTrustedSuite : Array DiffTestCase :=
  unicornTestArm64Cases ++
  vixlAluAndLoadStoreCases ++
  cAlgorithmicSubroutineCases ++
  vixlBranchCases ++
  buildRandomFuzzSuite 100 ++
  isaSurfaceAndScalarFpCases ++
  compiledRustSubroutineCases ++
  extendedFpSimdAtomicsAndBoundaryCases

/-- Serialize an array of `IsaTestCase` / `DiffTestCase` values into a JSON array. -/
def suiteToJson (cases : Array DiffTestCase) : Json :=
  Json.arr (cases.map testCaseToJson)

/-- Serialize `buildTrustedSuite` (optionally filtered by case-name substring) to a JSON string. -/
def dumpTrustedSuiteJson (filterSubstr : Option String := none) : String :=
  let cases := match filterSubstr with
    | none => buildTrustedSuite
    | some pat => buildTrustedSuite.filter (fun tc => (tc.name.splitOn pat).length > 1)
  (suiteToJson cases).compress

/-- Generate `count` freshly seeded random basic-block `IsaTestCase`s from `seed` and serialize to JSON. -/
def dumpRandomSuiteJson (seed : UInt64) (count : Nat) (insnsPerBlock : Nat := 8) : String :=
  let cases := buildRandomFuzzSuite count seed insnsPerBlock
  (suiteToJson cases).compress

/-- Execute a pre-encoded `DiffTestCase` in Lean and check that all words round-trip through
    `decode`/`encode` and execution reaches `tc.exitPC`. -/
def checkPreEncodedCase (tc : DiffTestCase) : Bool := Id.run do
  if tc.words.isEmpty then
    return false
  for w in tc.words do
    match decode w with
    | none => return false
    | some inst =>
      if encode inst != some w then
        return false
  let (prog, st) := tc.toInitialState
  let sf := execUntilPC tc.maxSteps prog tc.exitPC st
  return sf.pc == tc.exitPC

end Testing.TrustedSuite
