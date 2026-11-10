/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CaseStudies.Hashbrown.Spec.Top

/-!
# Checked Examples for `CaseStudies.Hashbrown.Spec.Top` (`CaseStudies.Hashbrown.SpecExamples`)

Concrete, kernel-checked (`:= by decide`) examples demonstrating the exact behaviour of the
top-level CLI specification in [`CaseStudies/Hashbrown/Spec/Top.lean`](Spec/Top.lean):
1. Valid command parsing (`insert`, `get`, `remove`, `contains`, `with_capacity`, `len`,
   `is_empty`, `clear`, leading zeros, `MaxWithCapacity = 4096`, and `u64::MAX`).
2. Malformed lines, whitespace sensitivity, arithmetic overflow (`≥ 2 ^ 64`), `with_capacity`
   above `MaxWithCapacity`, and wrong arity.
3. Line splitting and optional trailing-newline handling (`splitLines`).
4. End-to-end whole-process input/output runs (`HashbrownCliPost` and `evalLines`), including
   overwrites, missing-key lookups/removals, membership/length/emptiness queries, `clear` and
   `with_capacity` resets, interleaved error recovery on `stderr`, the `4096`-byte `MaxLineLen`
   boundary, and whole-run rejection (`exitCode = 1`) on overlong lines.
-/

@[expose] public section

namespace CaseStudies.Hashbrown.SpecExamples

open Arm64.Process CaseStudies.Hashbrown

instance instDecidableHashbrownCliPost (stdin : List (BitVec 8)) (out : ProcessOutcome) :
    Decidable (HashbrownCliPost stdin out) := by
  unfold HashbrownCliPost
  infer_instance

instance instDecidableHashbrownStdinBudget (inputs : ProcessInputs) :
    Decidable (HashbrownStdinBudget inputs) :=
  inferInstanceAs
    (Decidable (inputs.stdin.length ≤ HashbrownCliMaxStdin ∧
      8 * 2 ^ 20 + 8 * inputs.stdin.length ≤ inputs.init.physMemAvail))

/-- Helper constructing a `ProcessOutcome` with default final filesystem state for concise examples. -/
private def outcome (code : BitVec 64) (stdout stderr : String)
    (signal : Option Nat := none) : ProcessOutcome :=
  { exitCode := code
    signal   := signal
    stdout   := bytesOfString stdout
    stderr   := bytesOfString stderr
    fs       := default }

/-! ## 1. Valid Command Parsing (`parseCommand`) -/

example : parseCommand (bytesOfString "insert 3 7") = some (.insert 3 7) := by decide
example : parseCommand (bytesOfString "get 0") = some (.get 0) := by decide
example : parseCommand (bytesOfString "remove 42") = some (.remove 42) := by decide
example : parseCommand (bytesOfString "contains 42") = some (.contains 42) := by decide
example : parseCommand (bytesOfString "with_capacity 0") = some (.withCapacity 0) := by decide
example : parseCommand (bytesOfString "with_capacity 4096") = some (.withCapacity 4096) := by decide
example : parseCommand (bytesOfString "len") = some .len := by decide
example : parseCommand (bytesOfString "is_empty") = some .isEmpty := by decide
example : parseCommand (bytesOfString "clear") = some .clear := by decide

-- Leading zeros are accepted on decimal `u64` arguments.
example : parseCommand (bytesOfString "insert 007 000") = some (.insert 7 0) := by decide
example : parseCommand (bytesOfString "get 0000") = some (.get 0) := by decide
example : parseCommand (bytesOfString "contains 0042") = some (.contains 42) := by decide
example : parseCommand (bytesOfString "with_capacity 0016") = some (.withCapacity 16) := by decide

-- Largest representable `u64` (`2^64 - 1 = 18446744073709551615`).
example :
    parseCommand (bytesOfString "insert 18446744073709551615 18446744073709551615") =
      some (.insert 0xffffffffffffffff#64 0xffffffffffffffff#64) := by decide

/-! ## 2. Malformed Lines, Whitespace, & Overflow Edge Cases (`parseCommand = none`) -/

-- Empty line and whitespace-only line.
example : parseCommand (bytesOfString "") = none := by decide
example : parseCommand (bytesOfString " ") = none := by decide

-- Leading space, trailing space, multiple spaces between fields, tabs, and CRLF `\r`.
example : parseCommand (bytesOfString " get 3") = none := by decide
example : parseCommand (bytesOfString "get 3 ") = none := by decide
example : parseCommand (bytesOfString "get  3") = none := by decide
example : parseCommand (bytesOfString "insert  3 7") = none := by decide
example : parseCommand (bytesOfString "insert 3  7") = none := by decide
example : parseCommand (bytesOfString "insert 3 7 ") = none := by decide
example : parseCommand (bytesOfString "len ") = none := by decide
example : parseCommand (bytesOfString "is_empty ") = none := by decide
example : parseCommand (bytesOfString "clear ") = none := by decide
example : parseCommand (bytesOfString "get\t3") = none := by decide
example : parseCommand (bytesOfString "get 3\r") = none := by decide

-- `with_capacity` above `MaxWithCapacity` (`4096`) and decimal overflow at `2^64`.
example : parseCommand (bytesOfString "with_capacity 4097") = none := by decide
example : parseCommand (bytesOfString "with_capacity 18446744073709551615") = none := by decide
example : parseCommand (bytesOfString "get 18446744073709551616") = none := by decide
example : parseCommand (bytesOfString "insert 1 18446744073709551616") = none := by decide
example : parseCommand (bytesOfString "get 99999999999999999999999999999") = none := by decide

-- Non-decimal characters, signs, hex prefixes, wrong field count, and unknown/uppercase verbs.
example : parseCommand (bytesOfString "get -1") = none := by decide
example : parseCommand (bytesOfString "get +3") = none := by decide
example : parseCommand (bytesOfString "get 0x10") = none := by decide
example : parseCommand (bytesOfString "insert abc 7") = none := by decide
example : parseCommand (bytesOfString "insert 3 7x") = none := by decide
example : parseCommand (bytesOfString "insert 3") = none := by decide
example : parseCommand (bytesOfString "insert 3 7 9") = none := by decide
example : parseCommand (bytesOfString "get") = none := by decide
example : parseCommand (bytesOfString "get 3 7") = none := by decide
example : parseCommand (bytesOfString "remove") = none := by decide
example : parseCommand (bytesOfString "remove 3 7") = none := by decide
example : parseCommand (bytesOfString "contains") = none := by decide
example : parseCommand (bytesOfString "contains 3 7") = none := by decide
example : parseCommand (bytesOfString "with_capacity") = none := by decide
example : parseCommand (bytesOfString "len 0") = none := by decide
example : parseCommand (bytesOfString "clear 0") = none := by decide
example : parseCommand (bytesOfString "GET 3") = none := by decide
example : parseCommand (bytesOfString "delete 3") = none := by decide

/-! ## 3. Line Splitting & Trailing-Newline Semantics (`splitLines`) -/

-- Empty `stdin` has zero lines (`[]`), whereas a lone `"\n"` is one empty line (`[[]]`).
example : splitLines (bytesOfString "") = [] := by decide
example : splitLines (bytesOfString "\n") = [[]] := by decide

-- One optional trailing `\n` is stripped, while a second `\n` produces a trailing empty line.
example :
    splitLines (bytesOfString "insert 1 2\nget 1\n") =
      [bytesOfString "insert 1 2", bytesOfString "get 1"] := by decide
example :
    splitLines (bytesOfString "insert 1 2\nget 1") =
      [bytesOfString "insert 1 2", bytesOfString "get 1"] := by decide
example :
    splitLines (bytesOfString "get 1\n\n") =
      [bytesOfString "get 1", []] := by decide

/-! ## 4. Whole-Run Input / Output Examples (`HashbrownCliPost`) -/

-- 4a. Empty `stdin`: exits 0 with empty `stdout` and `stderr`.
example : HashbrownCliPost (bytesOfString "") (outcome 0#64 "" "") := by decide

-- 4b. Normal sessions exercising all 8 CLI commands (`insert`, `get`, `remove`, `contains`,
--     `with_capacity`, `len`, `is_empty`, `clear`) including overwrite, missing key, and resets.
example :
    HashbrownCliPost
      (bytesOfString
        ("is_empty\nlen\n" ++
         "insert 3 7\ncontains 3\ncontains 9\nis_empty\nlen\n" ++
         "insert 3 99\nget 3\nremove 3\ncontains 3\nget 3\n"))
      (outcome 0#64
        ("true\n0\n" ++
         "true\nfalse\nfalse\n1\n" ++
         "99\nfalse\nnone\n")
        "") := by decide

example :
    HashbrownCliPost
      (bytesOfString
        ("insert 8 80\nlen\nclear\nis_empty\nlen\nget 8\n" ++
         "insert 5 55\nwith_capacity 64\nis_empty\nlen\nget 5\ninsert 5 66\nget 5\n"))
      (outcome 0#64
        ("1\ntrue\n0\nnone\n" ++
         "true\n0\nnone\n66\n")
        "") := by decide

-- 4c. Missing final newline produces the exact same output as a newline-terminated input.
example :
    HashbrownCliPost
      (bytesOfString "insert 10 20\nget 10")
      (outcome 0#64 "20\n" "") := by decide

-- 4d. Malformed lines (including `with_capacity 4097` > `MaxWithCapacity`) emit
--     `"error: invalid command\n"` on `stderr` and are skipped while preserving map state.
example :
    HashbrownCliPost
      (bytesOfString "insert 5 50\nbad line\nwith_capacity 4097\n\nget  5\nget 18446744073709551616\nget 5\n")
      (outcome 0#64
        "50\n"
        ("error: invalid command\n" ++
         "error: invalid command\n" ++
         "error: invalid command\n" ++
         "error: invalid command\n" ++
         "error: invalid command\n")) := by decide

-- 4e. Boundary line of exact length `MaxLineLen = 4096` (`"get "` + 4092 `'0'`s = 4096 bytes)
--     is accepted and executes normally (`exitCode = 0`).
set_option maxRecDepth 100000 in
example :
    HashbrownCliPost
      (bytesOfString "get " ++ List.replicate 4092 0x30#8 ++ bytesOfString "\n")
      (outcome 0#64 "none\n" "") := by decide

-- 4f. Any line strictly longer than `MaxLineLen` (here 4097 `'a'` bytes after valid commands)
--     rejects the entire input BEFORE executing earlier valid commands (`stdout = ""`, exit 1).
set_option maxRecDepth 100000 in
example :
    HashbrownCliPost
      (bytesOfString "insert 1 99\nget 1\n" ++ List.replicate 4097 0x61#8)
      (outcome 1#64 "" "error: line too long\n") := by decide

set_option maxRecDepth 100000 in
example :
    ¬ HashbrownCliPost
      (bytesOfString "insert 1 99\nget 1\n" ++ List.replicate 4097 0x61#8)
      (outcome 1#64 "99\n" "error: line too long\n") := by decide

-- 4g. Termination via signal (`signal = some 6`) never satisfies `HashbrownCliPost`.
example :
    ¬ HashbrownCliPost (bytesOfString "") (outcome 0#64 "" "" (signal := some 6)) := by decide

end CaseStudies.Hashbrown.SpecExamples
