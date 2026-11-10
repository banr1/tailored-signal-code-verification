/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean.Elab.Term
public meta import Lean.Elab.Term.TermElabM
public meta import Arm64.Trusted.Surface.IncludeBytes

/-!
# Compile-Time SHA-256-Pinned File Elaborator `file_bytes%` (`Arm64.Trusted.Surface.FileBytes`)

- **Layer / Role**: `Arm64` Trusted Surface Specification Support (`Role::Spec`, definitions and
  elaboration-time file loader only, 0 theorems).
- **Purpose & Key Exports**: Defines `elabFileBytes` and the `file_bytes% "path" sha256 "<hex>"`
  term elaborator in `namespace Arm64.Process`, splicing the raw bytes of a binary file (after
  checking its SHA-256 digest) into a `List (BitVec 8)` literal at elaboration time.
- **When to read**: Read when auditing how whole-binary specifications embed static ELF images.
  Re-exported by `Arm64.Trusted.Process` so `Arm64/Trusted/Process/*` core modules stay `Init`-only.
-/

@[expose] public meta section

namespace Arm64.Process

open Lean Elab Term

/-- Elaborate a binary file at `filePath` (relative to the current Lean file) into a
    `List (BitVec 8)` literal after verifying its lowercase hex SHA-256 digest `expectedSha256`. -/
def elabFileBytes (filePath expectedSha256 : String) : TermElabM Expr := do
  let p : System.FilePath := filePath
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let resolved := if p.isAbsolute then p else dir / p
  let bs ← IO.FS.readBinFile resolved
  let out ← IO.Process.output { cmd := "sha256sum", args := #[resolved.toString] }
  let actual := ((out.stdout.splitOn " ").headD "").trimAscii.toString
  if out.exitCode != 0 || actual != expectedSha256.toLower then
    throwError "file_bytes%: {resolved}: sha256 mismatch (expected {expectedSha256}, got {actual})"
  return IncludeBytes.toListExpr bs

/-- `file_bytes% "path/to/file" sha256 "<64-char-hex>"`: splice the raw bytes of a file (verified
    against its SHA-256 digest) into a `List (BitVec 8)` literal at elaboration time. -/
syntax (name := fileBytesLit) "file_bytes% " str ident str : term

@[term_elab fileBytesLit]
def elabFileBytesTerm : TermElab := fun stx _ => do
  match stx with
  | `(file_bytes% $p:str $kw:ident $h:str) =>
    if kw.getId != `sha256 then
      throwErrorAt kw "file_bytes%: expected 'sha256'"
    elabFileBytes p.getString h.getString
  | _ => throwUnsupportedSyntax

end Arm64.Process
