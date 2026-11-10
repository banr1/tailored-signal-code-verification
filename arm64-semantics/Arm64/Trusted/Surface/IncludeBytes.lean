/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean.Elab.Term
public meta import Lean.Elab.Term.TermElabM

/-!
# Compile-Time Binary Slice Elaborator

Defines the `include_bytes% "path" off len` term elaborator, which splices bytes `[off, off + len)`
of a companion binary file into a `List (BitVec 8)` literal at elaboration time, along with shared
`BitVec` and `List` `Expr` builders (`IncludeBytes.bv8Exprs`, `IncludeBytes.toListExpr`,
`IncludeBytes.toChunkedListExpr`). Kept separate from `Arm64.lean` so core specifications do not
import `Lean.Elab.Term`.
-/

@[expose] public meta section

namespace Arm64

open Lean Elab Term

/-- Single-entry `(path, bytes)` cache avoiding repeated full-file reads across multiple
    `include_bytes%` slices in the same file. -/
initialize includeBytesCache : IO.Ref (Option (System.FilePath × ByteArray)) ← IO.mkRef none

/-- Read bytes `[off, off + len)` of `path`, resolved relative to the current Lean file's directory. -/
def IncludeBytes.read (path : String) (off len : Nat) : TermElabM ByteArray := do
  let p : System.FilePath := path
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let resolved := if p.isAbsolute then p else dir / p
  let bytes ← match ← includeBytesCache.get with
    | some (cachedPath, cachedBytes) =>
      if cachedPath == resolved then
        pure cachedBytes
      else
        let b ← IO.FS.readBinFile resolved
        includeBytesCache.set (some (resolved, b))
        pure b
    | none =>
      let b ← IO.FS.readBinFile resolved
      includeBytesCache.set (some (resolved, b))
      pure b
  if off + len > bytes.size then
    throwError "include_bytes%: {resolved} has {bytes.size} bytes, but bytes \
      [{off}, {off + len}) were requested"
  return bytes.extract off (off + len)

/-- Shared `BitVec 8` `Expr` constants for byte values `0..255` so slices share DAG nodes. -/
def IncludeBytes.bv8Exprs : Array Expr :=
  let ofNat := mkApp (mkConst ``BitVec.ofNat) (mkNatLit 8)
  (Array.range 256).map fun b => mkApp ofNat (mkNatLit b)

/-- `List (BitVec 8)` literal of `bs`, built from `IncludeBytes.bv8Exprs`. -/
def IncludeBytes.toListExpr (bs : ByteArray) : Expr := Id.run do
  let bv8 := mkApp (mkConst ``BitVec) (mkNatLit 8)
  let cons := mkApp (mkConst ``List.cons [Level.zero]) bv8
  let mut acc := mkApp (mkConst ``List.nil [Level.zero]) bv8
  for i in [0:bs.size] do
    acc := mkApp2 cons IncludeBytes.bv8Exprs[(bs.get! (bs.size - 1 - i)).toNat]! acc
  return acc

def IncludeBytes.bv64Expr (n : Nat) : Expr :=
  mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit n)

def IncludeBytes.listExpr (ty : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) ty x acc)
    (mkApp (mkConst ``List.nil [Level.zero]) ty)

/-- `bs` as a `List (BitVec 8)` term of bounded depth: `List.flatten` of literals of at most
    4096 bytes each, definitionally equal to `toListExpr bs` without exceeding kernel recursion
    depth on multi-page regions. -/
def IncludeBytes.toChunkedListExpr (bs : ByteArray) : Expr :=
  let chunk := 4096
  if bs.size ≤ chunk then IncludeBytes.toListExpr bs else
  let bv8 := mkApp (mkConst ``BitVec) (mkNatLit 8)
  let chunks := (List.range ((bs.size + chunk - 1) / chunk)).map fun k =>
    IncludeBytes.toListExpr (bs.extract (k * chunk) ((k + 1) * chunk))
  mkApp2 (mkConst ``List.flatten [Level.zero]) bv8
    (IncludeBytes.listExpr (mkApp (mkConst ``List [Level.zero]) bv8) chunks)

/-- `include_bytes% "path" off len`: bytes `[off, off + len)` of `path` as a
    `List (BitVec 8)` literal. -/
syntax (name := includeBytes) "include_bytes% " str ppSpace num ppSpace num : term

@[term_elab includeBytes]
def elabIncludeBytes : TermElab := fun stx _ => do
  match stx with
  | `(include_bytes% $path:str $off:num $len:num) =>
    let bs ← IncludeBytes.read path.getString off.getNat len.getNat
    return IncludeBytes.toListExpr bs
  | _ => throwUnsupportedSyntax

end Arm64
