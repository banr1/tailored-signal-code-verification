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

-- Shared export helpers (`ensureRustExports` passes `--module-prefix` to `rust-obj2lean`).
include_lake_file "../../scripts/LakeExports.lean"

def exportTargetSpecs : Array ExportTargetSpec := #[
  { name := "hashbrown"
    config := "Implementation/translation.toml"
    inputs := #[
      "Implementation/translation.toml",
      "Implementation/Cargo.toml",
      "Implementation/Cargo.lock",
      "Implementation/.cargo/config.toml",
      "Implementation/build.rs",
      "Implementation/src/lib.rs",
      "Implementation/src/main.rs",
      "Implementation/hashbrown_cli.elf",
      "../../../third_party/hashbrown-0.17.1/Cargo.toml",
      "../../../third_party/hashbrown-0.17.1/src/alloc.rs",
      "../../../third_party/hashbrown-0.17.1/src/control/bitmask.rs",
      "../../../third_party/hashbrown-0.17.1/src/control/group/generic.rs",
      "../../../third_party/hashbrown-0.17.1/src/control/group/lsx.rs",
      "../../../third_party/hashbrown-0.17.1/src/control/group/mod.rs",
      "../../../third_party/hashbrown-0.17.1/src/control/group/neon.rs",
      "../../../third_party/hashbrown-0.17.1/src/control/group/sse2.rs",
      "../../../third_party/hashbrown-0.17.1/src/control/mod.rs",
      "../../../third_party/hashbrown-0.17.1/src/control/tag.rs",
      "../../../third_party/hashbrown-0.17.1/src/external_trait_impls/mod.rs",
      "../../../third_party/hashbrown-0.17.1/src/external_trait_impls/rayon/helpers.rs",
      "../../../third_party/hashbrown-0.17.1/src/external_trait_impls/rayon/map.rs",
      "../../../third_party/hashbrown-0.17.1/src/external_trait_impls/rayon/mod.rs",
      "../../../third_party/hashbrown-0.17.1/src/external_trait_impls/rayon/raw.rs",
      "../../../third_party/hashbrown-0.17.1/src/external_trait_impls/rayon/set.rs",
      "../../../third_party/hashbrown-0.17.1/src/external_trait_impls/rayon/table.rs",
      "../../../third_party/hashbrown-0.17.1/src/external_trait_impls/serde.rs",
      "../../../third_party/hashbrown-0.17.1/src/hasher.rs",
      "../../../third_party/hashbrown-0.17.1/src/lib.rs",
      "../../../third_party/hashbrown-0.17.1/src/macros.rs",
      "../../../third_party/hashbrown-0.17.1/src/map.rs",
      "../../../third_party/hashbrown-0.17.1/src/raw.rs",
      "../../../third_party/hashbrown-0.17.1/src/raw_entry.rs",
      "../../../third_party/hashbrown-0.17.1/src/rustc_entry.rs",
      "../../../third_party/hashbrown-0.17.1/src/scopeguard.rs",
      "../../../third_party/hashbrown-0.17.1/src/set.rs",
      "../../../third_party/hashbrown-0.17.1/src/table.rs",
      "../../../third_party/hashbrown-0.17.1/src/util.rs"
    ]
    outputs := #[
      "Generated/HashbrownPlacedObj.lean",
      "Generated/HashbrownPlacedObj.bin",
      "Generated/HashbrownElfObj.lean",
      "Generated/HashbrownElfFacts.lean",
      "Generated/HashbrownPlacedWitness.lean"
    ] }
]

def exportOutputs : Array String := exportTargetSpecs.foldl (fun acc s => acc ++ s.outputs) #[]

package «casestudy-hashbrown» where
  version := v!"0.1.0"
  srcDir := "../.."
  packagesDir := "../../.lake/packages"
  leanOptions := standardLeanOptions
  weakLeanArgs := leanMemoryCapArgs
  moreGlobalServerArgs := leanMemoryCapArgs

require prooflib from "../../ProofLib"
require «verified-libraries» from "../../VerifiedLibraries"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.34.0"

target rustExports pkg : Array FilePath := Job.async do
  setTraceCaption "rustExports"
  let repoRoot := pkg.dir / ".." / ".."
  let genRelDir := "Generated"
  let genModPrefix := "CaseStudies.Hashbrown.Generated"
  let (depTrace, outFiles) ←
    ensureRustExports pkg.dir exportTargetSpecs "rustExports" #["none"] repoRoot genRelDir genModPrefix
  addTrace depTrace
  cleanupStaleGeneratedFiles (pkg.dir / "Generated") genRelDir exportOutputs
  let outTrace ← computeRelativeFilesTrace pkg.dir "outputs" exportOutputs
  addTrace outTrace
  return outFiles

@[«module_facet»] def generatedInputFacet : ModuleFacetDecl :=
  mkGeneratedInputFacet `CaseStudies.Hashbrown.Generated

lean_lib Generated where
  roots := #[`CaseStudies.Hashbrown.Generated]
  globs := #[.one `CaseStudies.Hashbrown.Generated]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib «CaseStudies.Hashbrown» where
  roots := #[]
  globs := #[.one `CaseStudies.Hashbrown,
             .one `CaseStudies.Hashbrown.SpecExamples,
             .andSubmodules `CaseStudies.Hashbrown.Spec,
             .submodules `CaseStudies.Hashbrown.Proofs]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Testing where
  roots := #[]
  globs := #[.submodules `CaseStudies.Hashbrown.Testing]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Theorems where
  roots := #[]
  globs := #[.andSubmodules `CaseStudies.Hashbrown.Theorems]
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]
