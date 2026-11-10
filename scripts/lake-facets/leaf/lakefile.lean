/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import Lake
open Lake DSL System

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

include_lake_file "../../LakeInputFacet.lean"

package «cv-input-facet-leaf»

@[«module_facet»] def generatedInputFacet : ModuleFacetDecl :=
  mkWorkspaceGeneratedInputFacet
