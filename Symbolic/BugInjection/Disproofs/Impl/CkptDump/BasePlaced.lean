/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public meta import Arm64
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore
public meta import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore
public import Symbolic.BugInjection.Disproofs.Impl.CkptDump.CommonPlaced
public meta import Symbolic.BugInjection.Disproofs.Impl.CkptDump.CommonPlaced

/-!
# Placed Checkpoint Base-Spec Dumper

Loads a mutant CLI ELF and its `link.json` stub table via `prebuildPlacedFromPaths`, validates
placed prebuild and depth-3/4 invariants, and writes the base specification JSON (scalar symbol
addresses, hooked stub tree, and 16 `treeSub4` cache-line subtrees) consumed by
`scripts/bug_injection_ckpt.py --placed`. Defaults `<link.json>` to `<dir-of-elf>/link.json` when
omitted on the command line.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.CkptDump.BasePlaced

open Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore (treeSub4)
open Symbolic.BugInjection.Disproofs.Impl.CkptDump.CommonPlaced (defaultLinkJsonPath encodeHooks
  encodeLineTree extractOptFlag fmtBv64Lit jsonEscape jsonStrArray prebuildPlacedFromPaths)

def dumpBasePlacedJson (elfPath linkJsonPath outPath : String) : IO Unit := do
  let (elf, tokStorageAddr, tokOnceAddr, pb) ← prebuildPlacedFromPaths elfPath linkJsonPath
  let addrs := pb.prog.addrs
  let hooksChunks := encodeHooks pb.prog.hooks
  let subsChunks := (List.range 16).map fun m =>
    encodeLineTree (treeSub4 m pb.baseLines)
  let subsJson := "[" ++ String.intercalate ",\n    " (subsChunks.map jsonStrArray) ++ "]"
  let json := String.intercalate "\n" [
    "{",
    s!"  \"entry\": {jsonEscape (fmtBv64Lit elf.entry)},",
    s!"  \"phdrVaddr\": {jsonEscape (fmtBv64Lit elf.phdrVaddr)},",
    s!"  \"phnum\": {elf.phnum},",
    s!"  \"brkStart\": {jsonEscape (fmtBv64Lit elf.brkStart)},",
    s!"  \"tokStorageAddr\": {jsonEscape (fmtBv64Lit tokStorageAddr)},",
    s!"  \"tokOnceAddr\": {jsonEscape (fmtBv64Lit tokOnceAddr)},",
    s!"  \"callocAddr\": {jsonEscape (fmtBv64Lit addrs.callocAddr)},",
    s!"  \"callocSentinel\": {jsonEscape (fmtBv64Lit addrs.callocSentinel)},",
    s!"  \"mallocAddr\": {jsonEscape (fmtBv64Lit addrs.mallocAddr)},",
    s!"  \"mallocSentinel\": {jsonEscape (fmtBv64Lit addrs.mallocSentinel)},",
    s!"  \"freeAddr\": {jsonEscape (fmtBv64Lit addrs.freeAddr)},",
    s!"  \"freeSentinel\": {jsonEscape (fmtBv64Lit addrs.freeSentinel)},",
    "  \"isFullDepth3\": true,",
    "  \"isFullDepth4\": true,",
    s!"  \"hooks\": {jsonStrArray hooksChunks},",
    s!"  \"subs\": {subsJson}",
    "}\n"
  ]
  IO.FS.writeFile outPath json
  IO.println
    s!"OK CkptDump.BasePlaced: {elfPath} ({linkJsonPath}) -> {outPath} (entry={fmtBv64Lit elf.entry}, phnum={elf.phnum}, hooks_chunks={hooksChunks.length})"

def runMain (args : List String) : IO Unit := do
  let (linkOpt, posArgs) := extractOptFlag "--link-json" args
  match posArgs, linkOpt with
  | [elfPath, outPath], some lj => dumpBasePlacedJson elfPath lj outPath
  | [elfPath, outPath], none => dumpBasePlacedJson elfPath (defaultLinkJsonPath elfPath) outPath
  | [elfPath, linkJsonPath, outPath], none => dumpBasePlacedJson elfPath linkJsonPath outPath
  | _, _ =>
    IO.eprintln
      "Usage: lake env lean --run Symbolic/BugInjection/Disproofs/Impl/CkptDump/BasePlaced.lean [--link-json <link.json>] <elf-path> [<link.json>] <out-base.json>"
    IO.Process.exit 1

end Symbolic.BugInjection.Disproofs.Impl.CkptDump.BasePlaced

def main (args : List String) : IO Unit :=
  Symbolic.BugInjection.Disproofs.Impl.CkptDump.BasePlaced.runMain args
