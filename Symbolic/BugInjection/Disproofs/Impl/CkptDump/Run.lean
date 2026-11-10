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
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public meta import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public meta import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.FastStepInit
public meta import Symbolic.BugInjection.Proofs.CliExec.FastStepInit
public import Symbolic.BugInjection.Proofs.CliExec.FastStep
public meta import Symbolic.BugInjection.Proofs.CliExec.FastStep
public import Symbolic.BugInjection.Disproofs.Impl.CkptDump.Common
public meta import Symbolic.BugInjection.Disproofs.Impl.CkptDump.Common
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.FastInputs
public meta import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.FastInputs
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.FastInputs
public meta import Symbolic.BugInjection.Disproofs.Impl.WeakState.FastInputs

/-!
# Checkpoint Run-Trace Dumper

Parses a mutant CLI ELF, constructs `PrebuiltElf` with `mutantHooks`, steps each witness CLI call
(`0..2` for `small-subgroup`, `0..6` for `weak-state`, or a single `--call <k>`) in `2^12`-step
chunks via `fastRunChunkCached`, checks `checkFastExited0`, and writes the run-trace JSON consumed
by `scripts/bug_injection_ckpt.py`. Invoke under `CV_BUG_INJECTION=<bug>` so `libsignalSessionImage`
resolves to the target mutant.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.CkptDump.Run

open Arm64 Arm64.Process
open ProofLib.ProgramReflection
open CryptoVerification.SignalSession (Inputs)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree)
open Symbolic.BugInjection.Proofs.CliExec.RadixMem (FastMem)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemLine (loadRegionsLines)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows (FastState)
open Symbolic.BugInjection.Proofs.CliExec.FastStepInit (PrebuiltElf checkElfPrebuildOk
  initFastStateFromBase overlayHooks patchTokenFastMem)
open Symbolic.BugInjection.Proofs.CliExec.FastStep (checkFastExited0 fastRunChunkCached fastStep
  isFullDepth3)
open Symbolic.BugInjection.Disproofs.Impl.CkptDump.Common (byteArrayToBvList
  collectDirtyLineUpdates fmtBv32Lit fmtBv64Lit fmtMkCkptBody jsonEscape)

noncomputable def rawMutantStubs : List (String × Nat) :=
  CryptoVerification.libsignalSessionImage.stubs

def mutantStubChars : List (List Char × Nat) :=
  assoc_chars_of% rawMutantStubs

def mutantHooks : BinTree String :=
  overlayHooks compHooks0 (toStringSymbols mutantStubChars) .empty

/-- Specification of one CLI call in a multi-call counterexample carrier. -/
structure CallSpec where
  callIdx       : Nat
  inpIdent      : String
  inp           : Inputs
  outStdoutExpr : String
  outStdout     : List (BitVec 8)
  outFilesIdent : String
  outFiles      : List (String × List (BitVec 8))

open Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.FastInputs in
def ssCallSpecs : List CallSpec :=
  [ { callIdx := 0, inpIdent := "ssFastInp0", inp := ssFastInp0,
      outStdoutExpr := "[]", outStdout := [], outFilesIdent := "ssFiles0", outFiles := ssFiles0 },
    { callIdx := 1, inpIdent := "ssFastInp1", inp := ssFastInp1,
      outStdoutExpr := "ssFastOut1", outStdout := ssFastOut1, outFilesIdent := "ssFiles1", outFiles := ssFiles1 },
    { callIdx := 2, inpIdent := "hbFastInp2", inp := hbFastInp2,
      outStdoutExpr := "ssFastOut2", outStdout := ssFastOut2, outFilesIdent := "hbFiles2", outFiles := hbFiles2 } ]

open Symbolic.BugInjection.Disproofs.Impl.WeakState.FastInputs in
def wsCallSpecs : List CallSpec :=
  [ { callIdx := 0, inpIdent := "wsFastInp0", inp := wsFastInp0,
      outStdoutExpr := "[]", outStdout := [], outFilesIdent := "wsFiles0", outFiles := wsFiles0 },
    { callIdx := 1, inpIdent := "wsFastInp1", inp := wsFastInp1,
      outStdoutExpr := "wsFastOut1", outStdout := wsFastOut1, outFilesIdent := "wsFiles1", outFiles := wsFiles1 },
    { callIdx := 2, inpIdent := "wsFastInp2", inp := wsFastInp2,
      outStdoutExpr := "wsFastOut2", outStdout := wsFastOut2, outFilesIdent := "wsFiles2", outFiles := wsFiles2 },
    { callIdx := 3, inpIdent := "wsFastInp3", inp := wsFastInp3,
      outStdoutExpr := "wsFastOut3", outStdout := wsFastOut3, outFilesIdent := "wsFiles3", outFiles := wsFiles3 },
    { callIdx := 4, inpIdent := "wsFastInp4", inp := wsFastInp4,
      outStdoutExpr := "[]", outStdout := [], outFilesIdent := "wsFiles4", outFiles := wsFiles4 },
    { callIdx := 5, inpIdent := "wsFastInp5", inp := wsFastInp5,
      outStdoutExpr := "wsFastOut5", outStdout := wsFastOut5, outFilesIdent := "wsFiles5", outFiles := wsFiles5 },
    { callIdx := 6, inpIdent := "wsFastInp6", inp := wsFastInp6,
      outStdoutExpr := "wsFastOut6", outStdout := wsFastOut6, outFilesIdent := "wsFiles6", outFiles := wsFiles6 } ]

def resolveBugSpecs (rawBug : String) : IO (String × List CallSpec) := do
  match rawBug with
  | "small-subgroup" | "cheval26-small-subgroup" => pure ("small-subgroup", ssCallSpecs)
  | "weak-state" | "cheval26-weak-state" => pure ("weak-state", wsCallSpecs)
  | _ => throw (IO.userError s!"Unknown bug '{rawBug}' (expected small-subgroup or weak-state)")

def prebuildFromElfPath (elfPath : String) : IO (ElfImage × PrebuiltElf) := do
  let ba ← IO.FS.readBinFile elfPath
  let bs := byteArrayToBvList ba
  let elf ← match fastParse bs with
    | .ok e => pure e
    | .error msg => throw (IO.userError s!"fastParse failed on {elfPath}: {msg}")
  let regsWithLen := mapRegionsWithLen elf.segments
  unless elf.phent == 56 && checkElfPrebuildOk elf regsWithLen do
    throw (IO.userError s!"checkElfPrebuildOk / phent=56 failed on {elfPath} (phent={elf.phent})")
  let fm0 : FastMem := { lines := loadRegionsLines elf.segments, stackBase := 0, stackTop := 0 }
  let baseLines := (patchTokenFastMem fm0).lines
  unless isFullDepth3 baseLines do
    throw (IO.userError s!"isFullDepth3 baseLines = false on {elfPath}")
  let pb : PrebuiltElf := { baseLines := baseLines, prog := { hooks := mutantHooks, rxLines := baseLines } }
  return (elf, pb)

def countExactStepsInChunk (pb : PrebuiltElf) (startFs : FastState) (maxSteps : Nat) :
    Except String Nat := Id.run do
  let mut cur := startFs
  let mut k : Nat := 0
  while k < maxSteps && cur.status == .Running do
    match fastStep pb.prog cur with
    | some nxt =>
      cur := nxt
      k := k + 1
    | none =>
      let w := cur.mem.read32 cur.pc
      return .error
        s!"step_offset={k} pc={fmtBv64Lit cur.pc} sp={fmtBv64Lit cur.sp} x8={(cur.readReg64 Reg.x8).toNat} word={fmtBv32Lit w} decoded={reprStr (Arm64.decode w)}"
  return .ok k

def runAndFormatCall (elf : ElfImage) (pb : PrebuiltElf) (cs : CallSpec)
    (exp : Nat := 12) (maxChunks : Nat := 64) : IO String := do
  let t0 ← IO.monoMsNow
  let fs0 ← match initFastStateFromBase elf pb cs.inp with
    | some s => pure s
    | none => throw (IO.userError s!"Call {cs.callIdx}: initFastStateFromBase returned none")
  let mut fs := fs0
  let mut curSrc := "init"
  let mut chunkIdx : Nat := 0
  let mut fullSteps : Nat := 0
  let mut totalSteps : Nat := 0
  let mut chunkObjs : Array String := #[]
  let mut ckptObjs : Array String := #[]

  while chunkIdx < maxChunks && fs.status == .Running do
    let chunkName := toString chunkIdx
    match fastRunChunkCached pb.prog exp fs with
    | none =>
      match countExactStepsInChunk pb fs (2 ^ exp) with
      | .error diag =>
        throw (IO.userError s!"FIRST_NONE call={cs.callIdx} chunk={chunkIdx} base_step={fullSteps} {diag}")
      | .ok k =>
        throw (IO.userError s!"FIRST_NONE call={cs.callIdx} chunk={chunkIdx} fastRunChunkCached=none after {k} single steps")
    | some fsNext =>
      if fsNext.status == .Running then
        let dstName := toString (chunkIdx + 1)
        let (dirtyCount, mkBody) ← match fmtMkCkptBody pb fs0 fsNext 200 with
          | .ok res => pure res
          | .error e => throw (IO.userError s!"Call {cs.callIdx} ckpt {dstName}: {e}")
        let cObj :=
          s!"        \{\"idx\": {chunkIdx}, \"name\": {jsonEscape chunkName}, \"exp\": {exp}, \"src\": {jsonEscape curSrc}, \"dst\": {jsonEscape dstName}, \"dirtyCount\": {dirtyCount}}"
        let kObj :=
          s!"        \{\"name\": {jsonEscape dstName}, \"mkCkptBody\": {jsonEscape mkBody}}"
        chunkObjs := chunkObjs.push cObj
        ckptObjs := ckptObjs.push kObj
        curSrc := dstName
        fs := fsNext
        fullSteps := fullSteps + (2 ^ exp)
        chunkIdx := chunkIdx + 1
      else
        let remSteps ← match countExactStepsInChunk pb fs (2 ^ exp) with
          | .ok k => pure k
          | .error diag => throw (IO.userError s!"Call {cs.callIdx} final chunk step count failed: {diag}")
        totalSteps := fullSteps + remSteps
        unless checkFastExited0 fsNext cs.outStdout cs.outFiles do
          throw (IO.userError s!"FALSIFIED call={cs.callIdx}: checkFastExited0 = false (status={reprStr fsNext.status}, totalSteps={totalSteps})")
        let dirtyCount := (collectDirtyLineUpdates pb.baseLines fsNext.mem.lines).size
        let cObj :=
          s!"        \{\"idx\": {chunkIdx}, \"name\": {jsonEscape chunkName}, \"exp\": {exp}, \"src\": {jsonEscape curSrc}, \"dst\": null, \"dirtyCount\": {dirtyCount}}"
        chunkObjs := chunkObjs.push cObj
        fs := fsNext
        chunkIdx := chunkIdx + 1

  if fs.status == .Running then
    throw (IO.userError s!"Call {cs.callIdx}: exceeded maxChunks={maxChunks} while still Running")

  let dt := (← IO.monoMsNow) - t0
  IO.println s!"OK CkptDump.Run call={cs.callIdx} ({cs.inpIdent}): totalSteps={totalSteps} chunks={chunkObjs.size} ckpts={ckptObjs.size} ({dt} ms)"
  let chunksStr := "[\n" ++ String.intercalate ",\n" chunkObjs.toList ++ "\n      ]"
  let ckptsStr :=
    if ckptObjs.isEmpty then "[]"
    else "[\n" ++ String.intercalate ",\n" ckptObjs.toList ++ "\n      ]"
  return String.intercalate "\n" [
    "    {",
    s!"      \"call\": {cs.callIdx},",
    s!"      \"inpIdent\": {jsonEscape cs.inpIdent},",
    s!"      \"outStdoutExpr\": {jsonEscape cs.outStdoutExpr},",
    s!"      \"outFilesIdent\": {jsonEscape cs.outFilesIdent},",
    s!"      \"totalSteps\": {totalSteps},",
    s!"      \"chunks\": {chunksStr},",
    s!"      \"ckpts\": {ckptsStr}",
    "    }"
  ]

def dumpAllCallsJson (rawBug elfPath outPath : String) : IO Unit := do
  let (bugCanon, specs) ← resolveBugSpecs rawBug
  let (elf, pb) ← prebuildFromElfPath elfPath
  let mut callJsons : Array String := #[]
  for cs in specs do
    let cj ← runAndFormatCall elf pb cs
    callJsons := callJsons.push cj
  let callsBlock := "[\n" ++ String.intercalate ",\n" callJsons.toList ++ "\n  ]"
  let doc := String.intercalate "\n" [
    "{",
    s!"  \"bug\": {jsonEscape bugCanon},",
    s!"  \"calls\": {callsBlock}",
    "}\n"
  ]
  IO.FS.writeFile outPath doc
  IO.println s!"OK CkptDump.Run: {bugCanon} ({specs.length} calls) -> {outPath}"

def dumpSingleCallJson (rawBug callStr elfPath outPath : String) : IO Unit := do
  let (_, specs) ← resolveBugSpecs rawBug
  let k ← match callStr.toNat? with
    | some n => pure n
    | none => throw (IO.userError s!"Invalid call index: {callStr}")
  let cs ← match specs.find? (fun s => s.callIdx == k) with
    | some s => pure s
    | none => throw (IO.userError s!"Call {k} out of range for {rawBug}")
  let (elf, pb) ← prebuildFromElfPath elfPath
  let cj ← runAndFormatCall elf pb cs
  IO.FS.writeFile outPath (cj ++ "\n")

def runMain (args : List String) : IO Unit := do
  match args with
  | [rawBug, elfPath, outPath] =>
    dumpAllCallsJson rawBug elfPath outPath
  | [rawBug, "--call", callStr, elfPath, outPath] =>
    dumpSingleCallJson rawBug callStr elfPath outPath
  | _ =>
    IO.eprintln "Usage: lake env lean --run Symbolic/BugInjection/Disproofs/Impl/CkptDump/Run.lean <small-subgroup|weak-state> [--call <k>] <elf-path> <out.json>"
    IO.Process.exit 1

end Symbolic.BugInjection.Disproofs.Impl.CkptDump.Run

def main (args : List String) : IO Unit :=
  Symbolic.BugInjection.Disproofs.Impl.CkptDump.Run.runMain args
