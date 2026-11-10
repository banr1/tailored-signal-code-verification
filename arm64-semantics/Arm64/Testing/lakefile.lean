/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import Lake
open Lake DSL
open System (FilePath)

/-!
Lake package for the untrusted testing library and executables (`Arm64.Testing` +
`Arm64/Testing/**`, plus `unit_tests`, `diff_eval`, `elf_eval`, `placed_eval`, and `elf_run`).
It depends only on `arm64` and `prooflib`, so `Examples` is never on `LEAN_PATH` and
`ensureRustExports` never runs when building here. Module paths are resolved from the repository
root (`srcDir = "../.."`).

`generatedInputFacet` (from `scripts/LakeExports.lean`) mixes every ELF a module embeds
(`file_bytes%`, `elf_image%`) or guards (`requires_test_files`, `if_test_files_exist%`) into the
module's input trace, so a module that reported `SKIPPED` rebuilds once
`scripts/build-test-elfs.sh` has produced its inputs.
-/

open Lean Elab Command in
elab "include_lake_file " rel:str : command => do
  let curDir := (System.FilePath.mk (← read).fileName).parent.getD "."
  let path := curDir / rel.getString
  let src ← IO.FS.readFile path
  let env ← getEnv
  let ictx := Parser.mkInputContext src path.toString
  let mut pstate : Parser.ModuleParserState := {}
  let scope := (← get).scopes.head!
  while !ictx.atEnd pstate.pos do
    let (stx, pstate', msgs) := Parser.parseCommand ictx { env, options := scope.opts } pstate (← get).messages
    modify fun s => { s with messages := msgs }
    pstate := pstate'
    if Parser.isTerminalCommand stx then break
    withReader (fun ctx => { ctx with fileName := path.toString, fileMap := ictx.fileMap }) do
      elabCommandTopLevel stx

include_lake_file "../../scripts/LakeExports.lean"

package «arm64-testing» where
  version := v!"0.1.0"
  srcDir := "../.."
  packagesDir := "../../.lake/packages"
  testDriver := "unit_tests"
  leanOptions := #[
    ⟨`warningAsError, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  weakLeanArgs := #["-M", "12288"]
  moreGlobalServerArgs := #["-M", "12288"]

require arm64 from ".."
require prooflib from "../../ProofLib"

@[«module_facet»] def generatedInputFacet : ModuleFacetDecl := mkGeneratedInputFacet

@[default_target]
lean_lib Arm64Testing where
  roots := #[`Arm64.Testing]
  -- A recursive glob over the package root would also match this lakefile, so list the top-level
  -- modules and directories of `Arm64/Testing/` explicitly; add new ones here.
  globs := #[.one `Arm64.Testing, .one `Arm64.Testing.AsciiTests, .one `Arm64.Testing.SyscallDiff,
    .submodules `Arm64.Testing.Conformance, .submodules `Arm64.Testing.Generators,
    .submodules `Arm64.Testing.Harness, .submodules `Arm64.Testing.Proofs,
    .submodules `Arm64.Testing.Regression, .submodules `Arm64.Testing.Tours]

@[default_target]
lean_exe unit_tests where
  root := `Arm64.Testing.Regression.UnitTests

@[default_target]
lean_exe diff_eval where
  root := `Arm64.Testing.Harness.DifferentialEval

@[default_target]
lean_exe elf_eval where
  root := `Arm64.Testing.Harness.ElfEval

@[default_target]
lean_exe placed_eval where
  root := `Arm64.Testing.Harness.PlacedEval

@[default_target]
lean_exe elf_run where
  root := `Arm64.Testing.Harness.ElfRunCli
