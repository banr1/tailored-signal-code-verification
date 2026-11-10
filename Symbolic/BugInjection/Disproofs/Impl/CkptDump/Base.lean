/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public meta import Arm64
public import ProofLib.Process.FastParse
public meta import ProofLib.Process.FastParse
public import ProofLib.ProgramReflection
public meta import ProofLib.ProgramReflection
public import LibsignalBinary.Specifications.SignalSession.CliProcess
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public meta import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public meta import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public meta import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemLine
public meta import Symbolic.BugInjection.Proofs.CliExec.RadixMemLine
public import Symbolic.BugInjection.Proofs.CliExec.FastStepInit
public meta import Symbolic.BugInjection.Proofs.CliExec.FastStepInit
public import Symbolic.BugInjection.Proofs.CliExec.FastStep
public meta import Symbolic.BugInjection.Proofs.CliExec.FastStep
public import Symbolic.BugInjection.Disproofs.Impl.CkptDump.Common
public meta import Symbolic.BugInjection.Disproofs.Impl.CkptDump.Common

/-!
# Checkpoint Base-Spec Dumper

Parses a mutant CLI ELF via `Arm64.Process.fastParse`, validates prebuild and depth-3/4 invariants,
constructs `mutantHooks` from `libsignalSessionImage.stubs` and the token-patched cache-line tree
`baseLines`, and writes the base specification JSON consumed by `scripts/bug_injection_ckpt.py`.
Invoke under `CV_BUG_INJECTION=<bug>` so `libsignalSessionImage` resolves to the target mutant.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.CkptDump.Base

open Arm64 Arm64.Process
open ProofLib.ProgramReflection
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree)
open Symbolic.BugInjection.Proofs.CliExec.RadixMem (FastMem)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemLine (loadRegionsLines)
open Symbolic.BugInjection.Proofs.CliExec.FastStepInit (checkElfPrebuildOk overlayHooks patchTokenFastMem)
open Symbolic.BugInjection.Proofs.CliExec.FastStep (isFullDepth3 treeL treeR treeSub3)
open Symbolic.BugInjection.Disproofs.Impl.CkptDump.Common (byteArrayToBvList encodeHooks
  encodeLineTree fmtBv64Lit jsonEscape jsonStrArray)

noncomputable def rawMutantStubs : List (String × Nat) :=
  CryptoVerification.libsignalSessionImage.stubs

def mutantStubChars : List (List Char × Nat) :=
  assoc_chars_of% rawMutantStubs

def mutantHooks : BinTree String :=
  overlayHooks compHooks0 (toStringSymbols mutantStubChars) .empty

def dumpBaseJson (elfPath outPath : String) : IO Unit := do
  let ba ← IO.FS.readBinFile elfPath
  let bs := byteArrayToBvList ba
  let elf ← match fastParse bs with
    | .ok e => pure e
    | .error msg => throw (IO.userError s!"fastParse failed on {elfPath}: {msg}")
  let regsWithLen := mapRegionsWithLen elf.segments
  unless elf.phent == 56 && checkElfPrebuildOk elf regsWithLen do
    throw (IO.userError s!"checkElfPrebuildOk / phent=56 failed on {elfPath} (phent={elf.phent})")
  let hooks := mutantHooks
  let fm0 : FastMem := { lines := loadRegionsLines elf.segments, stackBase := 0, stackTop := 0 }
  let baseLines := (patchTokenFastMem fm0).lines
  let fullD3 := isFullDepth3 baseLines
  let fullD4 := match baseLines with
    | .branch l r => isFullDepth3 l && isFullDepth3 r
    | _ => false
  unless fullD3 && fullD4 do
    throw (IO.userError s!"isFullDepth3/4 baseLines = false on {elfPath} (d3={fullD3}, d4={fullD4})")
  let hooksChunks := encodeHooks hooks
  let subsChunks := (List.range 16).map fun m =>
    let sub := if m < 8 then treeL (treeSub3 m baseLines) else treeR (treeSub3 (m - 8) baseLines)
    encodeLineTree sub
  let subsJson := "[" ++ String.intercalate ",\n    " (subsChunks.map jsonStrArray) ++ "]"
  let json := String.intercalate "\n" [
    "{",
    s!"  \"entry\": {jsonEscape (fmtBv64Lit elf.entry)},",
    s!"  \"phdrVaddr\": {jsonEscape (fmtBv64Lit elf.phdrVaddr)},",
    s!"  \"phnum\": {elf.phnum},",
    s!"  \"brkStart\": {jsonEscape (fmtBv64Lit elf.brkStart)},",
    s!"  \"isFullDepth3\": {if fullD3 then "true" else "false"},",
    s!"  \"isFullDepth4\": {if fullD4 then "true" else "false"},",
    s!"  \"hooks\": {jsonStrArray hooksChunks},",
    s!"  \"subs\": {subsJson}",
    "}\n"
  ]
  IO.FS.writeFile outPath json
  IO.println s!"OK CkptDump.Base: {elfPath} -> {outPath} (entry={fmtBv64Lit elf.entry}, phnum={elf.phnum}, hooks_chunks={hooksChunks.length})"

def runMain (args : List String) : IO Unit := do
  match args with
  | [elfPath, outPath] => dumpBaseJson elfPath outPath
  | _ =>
    IO.eprintln "Usage: lake env lean --run Symbolic/BugInjection/Disproofs/Impl/CkptDump/Base.lean <elf-path> <out-base.json>"
    IO.Process.exit 1

end Symbolic.BugInjection.Disproofs.Impl.CkptDump.Base

def main (args : List String) : IO Unit :=
  Symbolic.BugInjection.Disproofs.Impl.CkptDump.Base.runMain args
