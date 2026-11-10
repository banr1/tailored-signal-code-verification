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
public import LibsignalBinary.Specifications.SignalSession.Run
public meta import LibsignalBinary.Specifications.SignalSession.Run
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public meta import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public meta import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore
public meta import Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore
public import Symbolic.BugInjection.Disproofs.Impl.CkptDump.CommonPlaced
public meta import Symbolic.BugInjection.Disproofs.Impl.CkptDump.CommonPlaced
public import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.FastInputs
public meta import Symbolic.BugInjection.Disproofs.Impl.SmallSubgroup.FastInputs
public import Symbolic.BugInjection.Disproofs.Impl.WeakState.FastInputs
public meta import Symbolic.BugInjection.Disproofs.Impl.WeakState.FastInputs

/-!
# Placed Checkpoint Run-Trace Dumper

Loads `PrebuiltElfPlaced` from a mutant CLI ELF and `link.json`, steps each witness CLI call
(`0..2` for `small-subgroup`, `0..6` for `weak-state`, or a single `--call <k>`) using either
adaptive `2^exp`-step chunks (`chooseChunkPlaced`) or a fixed chunk schedule (`--plan <plan.json>`),
verifies `checkFastExited0`, and writes the run-trace JSON consumed by
`scripts/bug_injection_ckpt.py --placed`. Defaults `<link.json>` to `<dir-of-elf>/link.json` when
omitted.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.CkptDump.RunPlaced

open Arm64 Arm64.Process
open CryptoVerification.SignalSession (Inputs)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore (PrebuiltElfPlaced checkFastExited0
  fastEvalInstPlaced fastRunPow2CachedPlacedCoreW fastStepPlacedSub initFastStateFromBasePlaced)
open Symbolic.BugInjection.Disproofs.Impl.CkptDump.CommonPlaced (ChunkCfg MiniJson chooseChunkPlaced
  collectDirtyLineUpdates countExactStepsInChunk defaultLinkJsonPath extractOptFlag fmtExpHist
  fmtMkCkptBody jsonEscape parseMiniJsonAt prebuildPlacedFromPaths)

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

/-- One deterministic chunk transition from `ckpt_chunk_plan.json`. -/
structure PlannedChunk where
  name    : String
  exp     : Nat
  dst     : Option String
  batched : Bool
  deriving Inhabited

def loadPlannedChunks (planPath bugCanon : String) (callIdx : Nat) :
    IO (Array PlannedChunk) := do
  let ba ← IO.FS.readBinFile planPath
  let root ← match parseMiniJsonAt ba 0 with
    | .ok (j, _) => pure j
    | .error msg => throw (IO.userError s!"{planPath}: {msg}")
  let some bugObj := root.field? bugCanon
    | throw (IO.userError s!"{planPath}: missing bug entry '{bugCanon}'")
  let callKey := toString callIdx
  let some (.arr rawChunks) := bugObj.field? callKey
    | throw (IO.userError s!"{planPath}: missing call array '{bugCanon}.{callKey}'")
  if rawChunks.isEmpty then
    throw (IO.userError s!"{planPath}: empty chunk plan for '{bugCanon}.{callKey}'")
  let mut out : Array PlannedChunk := #[]
  for idx in [0:rawChunks.size] do
    let item := rawChunks[idx]!
    let some (.str name) := item.field? "name"
      | throw (IO.userError s!"{planPath}: {bugCanon}.{callKey}[{idx}] missing string 'name'")
    let some (.nat exp) := item.field? "exp"
      | throw (IO.userError s!"{planPath}: {bugCanon}.{callKey}[{idx}] ('{name}') missing nat 'exp'")
    let dst ← match item.field? "dst" with
      | none | some .null => pure none
      | some (.str d) => pure (some d)
      | _ => throw (IO.userError s!"{planPath}: {bugCanon}.{callKey}[{idx}] ('{name}') invalid 'dst'")
    let batched ← match item.field? "batched" with
      | none | some .null => pure false
      | some (.bool b) => pure b
      | _ => throw (IO.userError s!"{planPath}: {bugCanon}.{callKey}[{idx}] ('{name}') invalid 'batched'")
    if dst.isNone && idx + 1 != rawChunks.size then
      throw (IO.userError s!"{planPath}: {bugCanon}.{callKey}[{idx}] ('{name}') has null dst before final chunk")
    if dst.isSome && idx + 1 == rawChunks.size then
      throw (IO.userError s!"{planPath}: {bugCanon}.{callKey}[{idx}] ('{name}') final chunk must have null dst")
    out := out.push { name, exp, dst, batched }
  return out

def runAndFormatPlannedCall (elf : ElfImage) (pb : PrebuiltElfPlaced) (cs : CallSpec)
    (plan : Array PlannedChunk) : IO String := do
  let t0 ← IO.monoMsNow
  let fs0 ← match initFastStateFromBasePlaced elf pb cs.inp with
    | some s => pure s
    | none => throw (IO.userError s!"Call {cs.callIdx}: initFastStateFromBasePlaced returned none")
  let mut fs := fs0
  let mut curSrc := "init"
  let mut fullSteps : Nat := 0
  let mut totalSteps : Nat := 0
  let mut chunkObjs : Array String := #[]
  let mut ckptObjs : Array String := #[]

  for chunkIdx in [0:plan.size] do
    let ch := plan[chunkIdx]!
    if fs.status != .Running then
      throw (IO.userError s!"Call {cs.callIdx}: halted before planned chunk {chunkIdx} ('{ch.name}')")
    let fsNext ← match fastRunPow2CachedPlacedCoreW compHooks0 fastEvalInstPlaced
        fastStepPlacedSub pb.prog ch.exp .empty fs with
      | some (_, s) => pure s
      | none =>
        match countExactStepsInChunk pb fs (2 ^ ch.exp) with
        | .error diag =>
          throw (IO.userError s!"FIRST_NONE call={cs.callIdx} chunk={ch.name} base_step={fullSteps} {diag}")
        | .ok k =>
          throw (IO.userError s!"Call {cs.callIdx} chunk {ch.name}: fastRunPow2CachedPlacedCoreW=none after {k} steps")
    let batchedField := if ch.batched then ", \"batched\": true" else ""
    match ch.dst with
    | some dstName =>
      if fsNext.status != .Running then
        throw (IO.userError s!"Call {cs.callIdx} chunk {ch.name}: halted early before planned dst {dstName} (status={reprStr fsNext.status})")
      let (dirtyCount, mkBody) ← match fmtMkCkptBody pb fs0 fsNext 200 with
        | .ok res => pure res
        | .error e => throw (IO.userError s!"Call {cs.callIdx} ckpt {dstName}: {e}")
      let cObj :=
        s!"        \{\"idx\": {chunkIdx}, \"name\": {jsonEscape ch.name}, \"exp\": {ch.exp}, \"src\": {jsonEscape curSrc}, \"dst\": {jsonEscape dstName}, \"dirtyCount\": {dirtyCount}{batchedField}}"
      let kObj :=
        s!"        \{\"name\": {jsonEscape dstName}, \"mkCkptBody\": {jsonEscape mkBody}}"
      chunkObjs := chunkObjs.push cObj
      ckptObjs := ckptObjs.push kObj
      curSrc := dstName
      fs := fsNext
      fullSteps := fullSteps + (2 ^ ch.exp)
    | none =>
      let remSteps ← match countExactStepsInChunk pb fs (2 ^ ch.exp) with
        | .ok k => pure k
        | .error diag =>
          throw (IO.userError s!"FIRST_NONE call={cs.callIdx} chunk={ch.name} base_step={fullSteps} {diag}")
      totalSteps := fullSteps + remSteps
      unless checkFastExited0 fsNext cs.outStdout cs.outFiles do
        throw (IO.userError s!"FALSIFIED call={cs.callIdx}: checkFastExited0 = false (status={reprStr fsNext.status}, totalSteps={totalSteps})")
      let dirtyCount := (collectDirtyLineUpdates pb.baseLines fsNext.mem.lines).size
      let cObj :=
        s!"        \{\"idx\": {chunkIdx}, \"name\": {jsonEscape ch.name}, \"exp\": {ch.exp}, \"src\": {jsonEscape curSrc}, \"dst\": null, \"dirtyCount\": {dirtyCount}{batchedField}}"
      chunkObjs := chunkObjs.push cObj
      fs := fsNext

  let dt := (← IO.monoMsNow) - t0
  IO.println s!"OK CkptDump.RunPlaced (plan) call={cs.callIdx} ({cs.inpIdent}): totalSteps={totalSteps} chunks={chunkObjs.size} ckpts={ckptObjs.size} ({dt} ms)"
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

partial def runAndFormatCall (elf : ElfImage) (pb : PrebuiltElfPlaced) (cs : CallSpec)
    (cfg : ChunkCfg := {}) : IO String := do
  let t0 ← IO.monoMsNow
  let fs0 ← match initFastStateFromBasePlaced elf pb cs.inp with
    | some s => pure s
    | none => throw (IO.userError s!"Call {cs.callIdx}: initFastStateFromBasePlaced returned none")
  let mut fs := fs0
  let mut curSrc := "init"
  let mut chunkIdx : Nat := 0
  let mut fullSteps : Nat := 0
  let mut totalSteps : Nat := 0
  let mut chunkObjs : Array String := #[]
  let mut ckptObjs : Array String := #[]
  let mut expUsed : Array Nat := #[]

  while chunkIdx < cfg.maxChunks && fs.status == .Running do
    let chunkName := toString chunkIdx
    match chooseChunkPlaced pb cfg chunkIdx fs with
    | .error diag =>
      throw (IO.userError s!"FIRST_NONE call={cs.callIdx} chunk={chunkIdx} base_step={fullSteps} {diag}")
    | .ok (chosenExp, fsNext, haltedOpt) =>
      expUsed := expUsed.push chosenExp
      match haltedOpt with
      | none =>
        let dstName := toString (chunkIdx + 1)
        let (dirtyCount, mkBody) ← match fmtMkCkptBody pb fs0 fsNext 200 with
          | .ok res => pure res
          | .error e => throw (IO.userError s!"Call {cs.callIdx} ckpt {dstName}: {e}")
        let cObj :=
          s!"        \{\"idx\": {chunkIdx}, \"name\": {jsonEscape chunkName}, \"exp\": {chosenExp}, \"src\": {jsonEscape curSrc}, \"dst\": {jsonEscape dstName}, \"dirtyCount\": {dirtyCount}}"
        let kObj :=
          s!"        \{\"name\": {jsonEscape dstName}, \"mkCkptBody\": {jsonEscape mkBody}}"
        chunkObjs := chunkObjs.push cObj
        ckptObjs := ckptObjs.push kObj
        curSrc := dstName
        fs := fsNext
        fullSteps := fullSteps + (2 ^ chosenExp)
        chunkIdx := chunkIdx + 1
      | some remSteps =>
        totalSteps := fullSteps + remSteps
        unless checkFastExited0 fsNext cs.outStdout cs.outFiles do
          throw (IO.userError s!"FALSIFIED call={cs.callIdx}: checkFastExited0 = false (status={reprStr fsNext.status}, totalSteps={totalSteps})")
        let dirtyCount := (collectDirtyLineUpdates pb.baseLines fsNext.mem.lines).size
        let cObj :=
          s!"        \{\"idx\": {chunkIdx}, \"name\": {jsonEscape chunkName}, \"exp\": {chosenExp}, \"src\": {jsonEscape curSrc}, \"dst\": null, \"dirtyCount\": {dirtyCount}}"
        chunkObjs := chunkObjs.push cObj
        fs := fsNext
        chunkIdx := chunkIdx + 1

  if fs.status == .Running then
    throw (IO.userError s!"Call {cs.callIdx}: exceeded maxChunks={cfg.maxChunks} while still Running")

  let dt := (← IO.monoMsNow) - t0
  let hist := fmtExpHist expUsed cfg.minExp cfg.maxExp
  IO.println s!"OK CkptDump.RunPlaced call={cs.callIdx} ({cs.inpIdent}): exp={cfg.minExp}..{cfg.maxExp} hist={hist} totalSteps={totalSteps} chunks={chunkObjs.size} ckpts={ckptObjs.size} ({dt} ms)"
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

def dumpAllCallsJson (rawBug elfPath linkJsonPath outPath : String)
    (cfg : ChunkCfg := {}) (planOpt : Option String := none) : IO Unit := do
  let (bugCanon, specs) ← resolveBugSpecs rawBug
  let (elf, _, _, pb) ← prebuildPlacedFromPaths elfPath linkJsonPath
  let mut callJsons : Array String := #[]
  for cs in specs do
    let cj ← match planOpt with
      | some planPath => do
        let plan ← loadPlannedChunks planPath bugCanon cs.callIdx
        runAndFormatPlannedCall elf pb cs plan
      | none =>
        runAndFormatCall elf pb cs cfg
    callJsons := callJsons.push cj
  let callsBlock := "[\n" ++ String.intercalate ",\n" callJsons.toList ++ "\n  ]"
  let doc := String.intercalate "\n" [
    "{",
    s!"  \"bug\": {jsonEscape bugCanon},",
    s!"  \"calls\": {callsBlock}",
    "}\n"
  ]
  IO.FS.writeFile outPath doc
  IO.println s!"OK CkptDump.RunPlaced: {bugCanon} ({specs.length} calls, exp={cfg.minExp}..{cfg.maxExp}) -> {outPath}"

def dumpSingleCallJson (rawBug callStr elfPath linkJsonPath outPath : String)
    (cfg : ChunkCfg := {}) (planOpt : Option String := none) : IO Unit := do
  let (bugCanon, specs) ← resolveBugSpecs rawBug
  let k ← match callStr.toNat? with
    | some n => pure n
    | none => throw (IO.userError s!"Invalid call index: {callStr}")
  let cs ← match specs.find? (fun s => s.callIdx == k) with
    | some s => pure s
    | none => throw (IO.userError s!"Call {k} out of range for {rawBug}")
  let (elf, _, _, pb) ← prebuildPlacedFromPaths elfPath linkJsonPath
  let cj ← match planOpt with
    | some planPath => do
      let plan ← loadPlannedChunks planPath bugCanon cs.callIdx
      runAndFormatPlannedCall elf pb cs plan
    | none =>
      runAndFormatCall elf pb cs cfg
  IO.FS.writeFile outPath (cj ++ "\n")

def parseNatOpt (flag : String) (dflt : Nat) : Option String → IO Nat
  | none => pure dflt
  | some s =>
    match s.toNat? with
    | some n => pure n
    | none => throw (IO.userError s!"Invalid natural number for {flag}: {s}")

def runMain (args : List String) : IO Unit := do
  let (callOpt, args1) := extractOptFlag "--call" args
  let (minExpOpt, args2) := extractOptFlag "--min-exp" args1
  let (expOpt, args3) := extractOptFlag "--exp" args2
  let (budgetOpt, args4) := extractOptFlag "--budget" args3
  let (maxChunksOpt, args5) := extractOptFlag "--max-chunks" args4
  let (planOpt, args6) := extractOptFlag "--plan" args5
  let (linkOpt, posArgs) := extractOptFlag "--link-json" args6
  let maxExp ← parseNatOpt "--exp" 12 expOpt
  if maxExp == 0 || maxExp > 20 then
    throw (IO.userError s!"--exp must be in 1..20, got {maxExp}")
  let rawMinExp ← parseNatOpt "--min-exp" 9 minExpOpt
  if rawMinExp == 0 || rawMinExp > 20 then
    throw (IO.userError s!"--min-exp must be in 1..20, got {rawMinExp}")
  let minExp := Nat.min rawMinExp maxExp
  let budget ← parseNatOpt "--budget" 5000 budgetOpt
  let maxChunks ← parseNatOpt "--max-chunks" 2048 maxChunksOpt
  let cfg : ChunkCfg := { minExp, maxExp, budget, maxChunks }
  match posArgs, callOpt, linkOpt with
  | [rawBug, elfPath, outPath], none, some lj =>
    dumpAllCallsJson rawBug elfPath lj outPath cfg planOpt
  | [rawBug, elfPath, outPath], none, none =>
    dumpAllCallsJson rawBug elfPath (defaultLinkJsonPath elfPath) outPath cfg planOpt
  | [rawBug, elfPath, linkJsonPath, outPath], none, none =>
    dumpAllCallsJson rawBug elfPath linkJsonPath outPath cfg planOpt
  | [rawBug, elfPath, outPath], some callStr, some lj =>
    dumpSingleCallJson rawBug callStr elfPath lj outPath cfg planOpt
  | [rawBug, elfPath, outPath], some callStr, none =>
    dumpSingleCallJson rawBug callStr elfPath (defaultLinkJsonPath elfPath) outPath cfg planOpt
  | [rawBug, elfPath, linkJsonPath, outPath], some callStr, none =>
    dumpSingleCallJson rawBug callStr elfPath linkJsonPath outPath cfg planOpt
  | _, _, _ =>
    IO.eprintln
      "Usage: lake env lean --run Symbolic/BugInjection/Disproofs/Impl/CkptDump/RunPlaced.lean <small-subgroup|weak-state> [--call <k>] [--plan <plan.json>] [--min-exp <m>] [--exp <M>] [--budget <B>] [--max-chunks <n>] [--link-json <link.json>] <elf-path> [<link.json>] <out.json>"
    IO.Process.exit 1

end Symbolic.BugInjection.Disproofs.Impl.CkptDump.RunPlaced

def main (args : List String) : IO Unit :=
  Symbolic.BugInjection.Disproofs.Impl.CkptDump.RunPlaced.runMain args
