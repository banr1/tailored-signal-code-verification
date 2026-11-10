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
public import Arm64.Testing.Harness.FpEval
public import Arm64.Testing.Harness.Compare
public import Arm64.Testing.Harness.Serve
public import Arm64.Testing.Generators.SyscallTraces
public import Arm64.Testing.Generators.TrustedSuite

/-!
# Differential Execution CLI Driver

Standalone `diff_eval` executable for ISA differential testing against Unicorn, ARM Sail, and
Berkeley SoftFloat 3e. Supports persistent binary oracle serving (`--serve`), deterministic and
random test-suite JSON export (`--dump-suite`, `--dump-random`), batch and single floating-point
evaluation (`--batch-fp`, `--eval-fp`), syscall differential traces (`--fs-diff-trace`,
`--mmap-diff-trace`, `--sigaltstack-diff-trace`), and JSON suite verification (`--verify`).
-/

@[expose] public section

namespace Testing.DifferentialEval

open Lean
open Arm64
open Testing.Harness
open Testing.TrustedSuite

def runTestCase (tc : Json) : Json :=
  (evalTestCase tc).json

def verifySuiteJson (arr : Array Json) (oracleMode : String := "all") : IO UInt32 := do
  let mut passed := 0
  let mut failed := 0
  let mut totalWords := 0
  let mut executedBoth := 0
  let mut skippedSail := 0
  let mut unmodeledDecode := 0
  let mut execException := 0

  for tc in arr do
    let o := evalTestCase tc
    let errs := o.mismatches
    match o.outcomeClass with
    | .executed => executedBoth := executedBoth + 1
    | .skippedOracle _ => skippedSail := skippedSail + 1
    | .unmodeledDecode => unmodeledDecode := unmodeledDecode + 1
    | .execException => execException := execException + 1
    | .nonNopHint => pure ()
    totalWords := totalWords + o.totalWords
    if errs.isEmpty then
      passed := passed + 1
    else
      failed := failed + 1
      IO.println s!"[FAIL] {o.name}:"
      for m in errs.extract 0 8 do
        IO.println s!"    {m}"

  IO.println s!"\nDifferential Validation Summary (Lean `diff_eval --verify`, mode={oracleMode}):"
  IO.println s!"  Total test cases        : {arr.size}"
  IO.println s!"  Total instruction words : {totalWords}"
  IO.println s!"  Outcome classification  : executed={executedBoth}, skipped_sail={skippedSail}, unmodeled_decode={unmodeledDecode}, exec_exception={execException}"
  IO.println s!"  Passed                  : {passed}"
  IO.println s!"  Failed                  : {failed}"
  return if failed == 0 then 0 else 1

def runFpBatch (inPath outPath : String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile inPath
  let count := bytes.size / 32
  let numTasks := 32
  let chunk := (count + numTasks - 1) / numTasks
  let mut tasks : Array (Task ByteArray) := Array.mkEmpty numTasks
  for t in [0:numTasks] do
    let startIdx := t * chunk
    let endIdx := Nat.min count ((t + 1) * chunk)
    if startIdx < endIdx then
      tasks := tasks.push <| Task.spawn fun () => Id.run do
        let mut sub := ByteArray.emptyWithCapacity ((endIdx - startIdx) * 16)
        for i in [startIdx:endIdx] do
          let off := i * 32
          let m := readU64LE bytes off
          let a := readU64LE bytes (off + 8)
          let b := readU64LE bytes (off + 16)
          let c := readU64LE bytes (off + 24)
          let (val, flags) := evalFpBatchRecordWithFlags m a b c
          sub := pushU64LE sub val
          sub := pushU64LE sub flags
        return sub
  let mut out := ByteArray.emptyWithCapacity (count * 16)
  for task in tasks do
    out := out ++ task.get
  IO.FS.writeBinFile outPath out
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--serve"] =>
    serveLoop
  | ["--dump-suite"] =>
    IO.println (dumpTrustedSuiteJson none)
    return 0
  | ["--dump-suite", "--filter", pat] =>
    IO.println (dumpTrustedSuiteJson (some pat))
    return 0
  | ["--dump-random", seedStr, countStr] =>
    let seed := (parseNat (Json.str seedStr)).toUInt64
    let count := Nat.max 1 (parseNat (Json.str countStr))
    IO.println (dumpRandomSuiteJson seed count 8)
    return 0
  | ["--dump-random", seedStr, countStr, insnsStr] =>
    let seed := (parseNat (Json.str seedStr)).toUInt64
    let count := Nat.max 1 (parseNat (Json.str countStr))
    let insns := Nat.max 1 (parseNat (Json.str insnsStr))
    IO.println (dumpRandomSuiteJson seed count insns)
    return 0
  | ["--eval-fp", opStr, rmStr, aStr, bStr] =>
    let fpRec : FpBatchRecord := {
      op := parseNat (Json.str opStr)
      rmCode := (parseNat (Json.str rmStr)).toUInt64
      fbits := 0
      a := (parseNat (Json.str aStr)).toUInt64
      b := (parseNat (Json.str bStr)).toUInt64
      c := 0
    }
    IO.println (evalFpRecordJson fpRec).compress
    return 0
  | ["--eval-fp", opStr, rmStr, aStr, bStr, cStr] =>
    let fpRec : FpBatchRecord := {
      op := parseNat (Json.str opStr)
      rmCode := (parseNat (Json.str rmStr)).toUInt64
      fbits := 0
      a := (parseNat (Json.str aStr)).toUInt64
      b := (parseNat (Json.str bStr)).toUInt64
      c := (parseNat (Json.str cStr)).toUInt64
    }
    IO.println (evalFpRecordJson fpRec).compress
    return 0
  | ["--batch-fp", inPath, outPath] =>
    runFpBatch inPath outPath
  | ["--fs-diff-trace"] =>
    Testing.Generators.dumpFsDiffTrace
    return 0
  | ["--mmap-diff-trace"] =>
    Testing.Generators.dumpMmapDiffTrace
    return 0
  | ["--sigaltstack-diff-trace"] =>
    Testing.Generators.dumpSigaltstackDiffTrace
    return 0
  | ["--verify", path] =>
    let input ← IO.FS.readFile path
    match Json.parse input with
    | .error err =>
      IO.eprintln s!"Failed to parse JSON input: {err}"
      return 1
    | .ok j =>
      match j.getArr? with
      | .ok arr => verifySuiteJson arr "all"
      | .error err =>
        IO.eprintln s!"Expected JSON array of test cases: {err}"
        return 1
  | ["--verify", "--oracle", mode, path] =>
    let input ← IO.FS.readFile path
    match Json.parse input with
    | .error err =>
      IO.eprintln s!"Failed to parse JSON input: {err}"
      return 1
    | .ok j =>
      match j.getArr? with
      | .ok arr => verifySuiteJson arr mode
      | .error err =>
        IO.eprintln s!"Expected JSON array of test cases: {err}"
        return 1
  | _ =>
    let input ← match args with
      | path :: _ => IO.FS.readFile path
      | [] => (← IO.getStdin).readToEnd
    match Json.parse input with
    | .error err =>
      IO.eprintln s!"Failed to parse JSON input: {err}"
      return 1
    | .ok j =>
      match j.getArr? with
      | .ok arr =>
        let results := arr.map runTestCase
        IO.println (Json.arr results).compress
        return 0
      | .error _ =>
        let res := runTestCase j
        IO.println res.compress
        return 0

end Testing.DifferentialEval

def main (args : List String) : IO UInt32 :=
  Testing.DifferentialEval.main args
