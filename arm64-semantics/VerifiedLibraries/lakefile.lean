/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import Lake
open Lake DSL
open System (FilePath)

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

include_lake_file "../scripts/LakeExports.lean"

def mallocngExportSpecs : Array ExportTargetSpec := #[
  { name := "mallocng"
    config := "Mallocng/Implementation/translation.toml"
    inputs := #[
      "Mallocng/Implementation/translation.toml",
      "Mallocng/Implementation/build.sh",
      "Mallocng/Implementation/common_bss.s"
    ]
    outputs := #[
      "Mallocng/Generated/MallocngPlacedObj.lean",
      "Mallocng/Generated/MallocngPlacedObj.bin"
    ] }
]

def muslExportSpecs : Array ExportTargetSpec := #[
  { name := "musl-string"
    config := "Musl/Implementation/translation.toml"
    inputs := #[
      "Musl/Implementation/translation.toml",
      "Musl/Implementation/build.sh"
    ]
    outputs := #[
      "Musl/Generated/MuslStringPlacedObj.lean",
      "Musl/Generated/MuslStringPlacedObj.bin"
    ] }
]

def mallocngExportOutputs : Array String :=
  mallocngExportSpecs.foldl (fun acc s => acc ++ s.outputs) #[]

def muslExportOutputs : Array String :=
  muslExportSpecs.foldl (fun acc s => acc ++ s.outputs) #[]

def rustStdExportSpecs : Array ExportTargetSpec := #[
  { name := "rust-std-io"
    config := "RustStd/Implementation/translation.toml"
    inputs := #[
      "RustStd/Implementation/translation.toml",
      "RustStd/Implementation/build.sh"
    ]
    outputs := #[
      "RustStd/Generated/RustStdIoPlacedObj.lean",
      "RustStd/Generated/RustStdIoPlacedObj.bin"
    ] },
  { name := "rust-core"
    config := "RustStd/Implementation/core.toml"
    inputs := #[
      "RustStd/Implementation/core.toml",
      "RustStd/Implementation/build.sh"
    ]
    outputs := #[
      "RustStd/Generated/CorePlacedObj.lean",
      "RustStd/Generated/CorePlacedObj.bin"
    ] },
  { name := "rust-alloc"
    config := "RustStd/Implementation/alloc.toml"
    inputs := #[
      "RustStd/Implementation/alloc.toml",
      "RustStd/Implementation/build.sh"
    ]
    outputs := #[
      "RustStd/Generated/AllocPlacedObj.lean",
      "RustStd/Generated/AllocPlacedObj.bin"
    ] },
  { name := "rust-time"
    config := "RustStd/Implementation/time.toml"
    inputs := #[
      "RustStd/Implementation/time.toml",
      "RustStd/Implementation/build.sh"
    ]
    outputs := #[
      "RustStd/Generated/TimePlacedObj.lean",
      "RustStd/Generated/TimePlacedObj.bin"
    ] },
]

def rustStdExportOutputs : Array String :=
  rustStdExportSpecs.foldl (fun acc s => acc ++ s.outputs) #[]

package «verified-libraries» where
  version := v!"0.1.0"
  srcDir := ".."
  packagesDir := "../.lake/packages"
  leanOptions := standardLeanOptions
  weakLeanArgs := leanMemoryCapArgs
  moreGlobalServerArgs := leanMemoryCapArgs

require prooflib from "../ProofLib"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.34.0"

target rustExports pkg : Array FilePath := Job.async do
  setTraceCaption "rustExports"
  let repoRoot := pkg.dir / ".."
  let (depTrace1, outFiles1) ←
    ensureRustExports pkg.dir mallocngExportSpecs "rustExportsMallocng" #["none"]
      repoRoot "Mallocng/Generated" "VerifiedLibraries.Mallocng.Generated"
  addTrace depTrace1
  cleanupStaleGeneratedFiles (pkg.dir / "Mallocng" / "Generated")
    "Mallocng/Generated" mallocngExportOutputs
  let (depTrace2, outFiles2) ←
    ensureRustExports pkg.dir muslExportSpecs "rustExportsMusl" #["none"]
      repoRoot "Musl/Generated" "VerifiedLibraries.Musl.Generated"
  addTrace depTrace2
  cleanupStaleGeneratedFiles (pkg.dir / "Musl" / "Generated")
    "Musl/Generated" muslExportOutputs
  let (depTrace3, outFiles3) ←
    ensureRustExports pkg.dir rustStdExportSpecs "rustExportsRustStd" #["none"]
      repoRoot "RustStd/Generated" "VerifiedLibraries.RustStd.Generated"
  addTrace depTrace3
  cleanupStaleGeneratedFiles (pkg.dir / "RustStd" / "Generated")
    "RustStd/Generated" rustStdExportOutputs
  let outTrace ←
    computeRelativeFilesTrace pkg.dir "outputs"
      (mallocngExportOutputs ++ muslExportOutputs ++ rustStdExportOutputs)
  addTrace outTrace
  return (outFiles1 ++ outFiles2 ++ outFiles3)

@[«module_facet»] def generatedInputFacet : ModuleFacetDecl :=
  mkGeneratedInputFacet `VerifiedLibraries.Mallocng.Generated

lean_lib Generated where
  roots := #[`VerifiedLibraries.Mallocng.Generated.MallocngPlacedObj,
             `VerifiedLibraries.Musl.Generated.MuslStringPlacedObj,
             `VerifiedLibraries.RustStd.Generated.RustStdIoPlacedObj,
             `VerifiedLibraries.RustStd.Generated.CorePlacedObj,
             `VerifiedLibraries.RustStd.Generated.AllocPlacedObj,
             `VerifiedLibraries.RustStd.Generated.TimePlacedObj]
  globs := #[.one `VerifiedLibraries.Mallocng.Generated.MallocngPlacedObj,
             .one `VerifiedLibraries.Musl.Generated.MuslStringPlacedObj,
             .one `VerifiedLibraries.RustStd.Generated.RustStdIoPlacedObj,
             .one `VerifiedLibraries.RustStd.Generated.CorePlacedObj,
             .one `VerifiedLibraries.RustStd.Generated.AllocPlacedObj,
             .one `VerifiedLibraries.RustStd.Generated.TimePlacedObj]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib «VerifiedLibraries.Mallocng» where
  roots := #[]
  globs := #[.one `VerifiedLibraries.Mallocng,
             .andSubmodules `VerifiedLibraries.Mallocng.Spec,
             .submodules `VerifiedLibraries.Mallocng.Proofs]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib «VerifiedLibraries.Musl» where
  roots := #[]
  globs := #[.andSubmodules `VerifiedLibraries.Musl.Spec,
             .submodules `VerifiedLibraries.Musl.Proofs]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib «VerifiedLibraries.RustStd» where
  roots := #[]
  globs := #[.andSubmodules `VerifiedLibraries.RustStd.Spec,
             .submodules `VerifiedLibraries.RustStd.Proofs]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib «VerifiedLibraries.SwissTable» where
  roots := #[]
  globs := #[.one `VerifiedLibraries.SwissTable,
             .one `VerifiedLibraries.SwissTable.Spec,
             .submodules `VerifiedLibraries.SwissTable.Proofs]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]
