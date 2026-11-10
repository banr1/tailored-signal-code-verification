/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux

/-!
# Sparse `BinTree` Checkpoint Patches and Line Updates

Structural diff patches (`TreePatch`, `applyTreePatch`) and sparse 64-byte line updates
(`applyLineUpdates`) over `BinTree` and `Line64` for intermediate execution checkpoints.
-/

@[expose] public section

namespace Symbolic.BugInjection.Proofs.CliExec.TreePatch

set_option autoImplicit false

open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree Line64 btSet58Line)

/-- Structural diff patch over `BinTree α` that shares untouched subtrees (`keep`) across
intermediate checkpoints. -/
inductive TreePatch (α : Type) where
  | keep   : TreePatch α
  | set    : BinTree α → TreePatch α
  | branch : TreePatch α → TreePatch α → TreePatch α
  deriving Repr, Inhabited

def applyTreePatch {α : Type} (base : BinTree α) (p : TreePatch α) : BinTree α :=
  match p with
  | .keep => base
  | .set t => t
  | .branch pl pr =>
    match base with
    | .branch bl br => .branch (applyTreePatch bl pl) (applyTreePatch br pr)
    | _ => .branch (applyTreePatch .empty pl) (applyTreePatch .empty pr)

/-- Apply sparse `(lineIdx, line)` updates to `base` via `btSet58Line`, matching the updated root
before recursing so untouched `.twig` leaves stay unforced under kernel WHNF. -/
def applyLineUpdates (base : BinTree Line64) : List (Nat × Line64) → BinTree Line64
  | [] => base
  | (hi, ln) :: rest =>
    match btSet58Line base hi ln with
    | .empty => applyLineUpdates .empty rest
    | .twig j u => applyLineUpdates (.twig j u) rest
    | .branch x y => applyLineUpdates (.branch x y) rest

end Symbolic.BugInjection.Proofs.CliExec.TreePatch
