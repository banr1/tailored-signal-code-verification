/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import ProofLib.TestFiles
meta import Lean

/-!
# Regression tests for `ProofLib.TestFiles`

Positive and negative tests for `requires_test_files` and `if_test_files_exist%`, using
`TestFiles.lean` as an existing file fixture and `does_not_exist.elf` as a missing file.
-/

namespace ProofLib.Testing.TestFiles

open Lean Elab Command

/-! ## `requires_test_files`: present files elaborate the block -/

requires_test_files ["TestFiles.lean"]
def present : Nat := 1

theorem present_eq : present = 1 := rfl
end_requires_test_files

example : present = 1 := present_eq

/-! ## `requires_test_files`: a missing file skips the whole block with one info message -/

/--
info: SKIPPED: missing generated test file(s) [does_not_exist.elf]; run `scripts/build-test-elfs.sh` to build them
-/
#guard_msgs in
requires_test_files ["TestFiles.lean", "does_not_exist.elf"]
def absent : Nat := 1

-- Not elaborated: an ill-typed command inside a skipped block is not an error.
example : absent = 2 := rfl
end_requires_test_files

#guard_msgs in
run_cmd do
  if (← getEnv).contains `ProofLib.Testing.TestFiles.absent then
    throwError "`absent` must not exist after a skipped block"

/-! ## `if_test_files_exist%` -/

def chosenPresent : String := if_test_files_exist% ["TestFiles.lean"] then "built" else "skipped"
def chosenMissing : String :=
  if_test_files_exist% ["does_not_exist.elf"] then (unknownIdentifier : String) else "skipped"

example : chosenPresent = "built" := rfl
example : chosenMissing = "skipped" := rfl

end ProofLib.Testing.TestFiles
