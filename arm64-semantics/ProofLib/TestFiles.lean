/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean

/-!
# Optional Generated Test Inputs

Test-only commands that report `SKIPPED` when generated test binaries (`file_bytes%`, `elf_image%`)
are absent on disk (regenerate with `scripts/build-test-elfs.sh`):
- `requires_test_files ["a.elf", ...] <commands> end_requires_test_files` elaborates the enclosed
  commands only when every listed file (relative to the current Lean file) exists, and otherwise
  logs one `SKIPPED` info message without elaborating any declaration in the block.
- `if_test_files_exist% ["a.elf", ...] then t else e` elaborates only the chosen branch.

Use only in test, tour, and regression modules; never wrap a theorem used by `Theorems/` or a
comparator challenge. Place `open` commands before `requires_test_files`, since the entire block is
parsed before elaboration.
-/

public meta section

namespace ProofLib.TestFiles

open Lean Elab Command Term

/-- The command that regenerates the test binaries, quoted in every SKIPPED message. -/
def regenerateHint : String := "run `scripts/build-test-elfs.sh` to build them"

/-- Resolve `rel` against the directory of the Lean file being elaborated. -/
def resolveTestFile (fileName rel : String) : System.FilePath :=
  let p : System.FilePath := rel
  if p.isAbsolute then p else ((System.FilePath.mk fileName).parent.getD ".") / p

/-- The entries of `rels` (relative to `fileName`'s directory) that do not exist on disk. -/
def missingTestFiles (fileName : String) (rels : Array String) : IO (Array String) :=
  rels.filterM fun rel => return !(← (resolveTestFile fileName rel).pathExists)

/-- The SKIPPED message for the missing files `missing`. -/
def skippedMessage (missing : Array String) : String :=
  s!"SKIPPED: missing generated test file(s) {missing.toList}; {regenerateHint}"

/-- `requires_test_files ["a.elf", ...] <commands> end_requires_test_files`: elaborate the
    commands only when every listed file (relative to this Lean file) exists; otherwise log one
    `SKIPPED` info message and elaborate none of them. -/
syntax (name := requiresTestFiles)
  "requires_test_files " "[" str,* "]" (ppLine command)* ppDedent(ppLine "end_requires_test_files")
  : command

@[command_elab requiresTestFiles]
def elabRequiresTestFiles : CommandElab := fun stx => do
  match stx with
  | `(requires_test_files [$paths,*] $cmds* end_requires_test_files) =>
    let missing ← missingTestFiles (← getFileName) (paths.getElems.map (·.getString))
    if missing.isEmpty then
      for cmd in cmds do
        elabCommand cmd
    else
      logInfoAt stx[0] (skippedMessage missing)
  | _ => throwUnsupportedSyntax

/-- `if_test_files_exist% ["a.elf", ...] then t else e`: elaborate `t` when every listed file
    (relative to this Lean file) exists, and `e` otherwise. Only the chosen branch is elaborated. -/
syntax (name := ifTestFilesExist)
  "if_test_files_exist% " "[" str,* "]" " then " term " else " term : term

@[term_elab ifTestFilesExist]
def elabIfTestFilesExist : TermElab := fun stx expectedType? => do
  match stx with
  | `(if_test_files_exist% [$paths,*] then $t else $e) =>
    let missing ← missingTestFiles (← getFileName) (paths.getElems.map (·.getString))
    elabTerm (if missing.isEmpty then t else e) expectedType?
  | _ => throwUnsupportedSyntax

end ProofLib.TestFiles
