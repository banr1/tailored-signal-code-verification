/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process
public import ProofLib.Process.Assumptions
public import ProofLib.Process.ByteArray
public import ProofLib.Process.Core
public import ProofLib.Process.NonFs
public import ProofLib.Process.PureMem
public import ProofLib.Process.FastParse
public import ProofLib.Process.OracleEq
public import ProofLib.Exec
public import ProofLib.Simulation
public import ProofLib.Invariant
public import ProofLib.SepLogic.Defs
public import ProofLib.Hoare.SubroutineOk
public meta import Arm64.Trusted.Surface.IncludeBytes
public meta import Arm64.Trusted.Process.Types
public meta import Arm64.Trusted.Process.Loader
public meta import ProofLib.Process.ByteArray
import Arm64.Trusted.Spec.SepLogic
import Arm64.Trusted.Spec.Hoare

/-!
# Whole-Binary ELF Process Verification and Execution

Re-exports `ProofLib.Process.{Assumptions,ByteArray,Core,NonFs,PureMem,FastParse}` for whole-binary
`ElfRunsTo`, `ElfCorrect`, and `ElfSafe` proofs, and defines the `elf_image%` elaborator for
reifying static AArch64 ELF64 `ET_EXEC` binaries into concrete `ElfImage` terms at compile time.
-/

@[expose] public meta section

namespace Arm64.Process

open Lean Elab Term

def regionToExpr (r : Snapshot.Region) : Expr :=
  let permE := mkApp5 (mkConst ``Perm.mk)
    (if r.perm.r then mkConst ``true else mkConst ``false)
    (if r.perm.w then mkConst ``true else mkConst ``false)
    (if r.perm.x then mkConst ``true else mkConst ``false)
    (if r.perm.lazyFree then mkConst ``true else mkConst ``false)
    (if r.perm.anon then mkConst ``true else mkConst ``false)
  mkApp4 (mkConst ``Snapshot.Region.mk)
    (IncludeBytes.bv64Expr r.start.toNat)
    permE
    (IncludeBytes.toListExpr (byteArrayOfBytes r.bytes))
    (mkNatLit r.nonAnonLen)

/-- Elaborate an ELF64 `ET_EXEC` binary file at `elfPath` (relative to the current Lean file)
    into a concrete `ElfImage` expression at compile time via `ElfImage.parseByteArray`. -/
def elabElfImageFile (elfPath : String) : TermElabM Expr := do
  let p : System.FilePath := elfPath
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let resolved := if p.isAbsolute then p else dir / p
  let bs ← IO.FS.readBinFile resolved
  let img ← match ElfImage.parseByteArray bs with
    | .ok img => pure img
    | .error e => throwError "elf_image%: {resolved}: {e}"
  let segExprs := img.segments.map regionToExpr
  let bv64Ty := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let symTy := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``String) bv64Ty
  let symExprs := img.symbols.map fun (name, addr) =>
    mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``String) bv64Ty
      (mkStrLit name) (IncludeBytes.bv64Expr addr.toNat)
  return mkApp7 (mkConst ``ElfImage.mk)
    (IncludeBytes.bv64Expr img.entry.toNat)
    (IncludeBytes.bv64Expr img.phdrVaddr.toNat)
    (mkNatLit img.phent)
    (mkNatLit img.phnum)
    (IncludeBytes.listExpr (mkConst ``Snapshot.Region) segExprs)
    (IncludeBytes.bv64Expr img.brkStart.toNat)
    (IncludeBytes.listExpr symTy symExprs)

/-- `elf_image% "path/to/binary.elf"` parses a static AArch64 ELF64 binary at elaboration time
    into a concrete `ElfImage` witness for `ElfImage.parse`. -/
syntax (name := elfImageLit) "elf_image% " str : term

@[term_elab elfImageLit]
def elabElfImage : TermElab := fun stx _ => do
  match stx with
  | `(elf_image% $p:str) => elabElfImageFile p.getString
  | _ => throwUnsupportedSyntax

end Arm64.Process
