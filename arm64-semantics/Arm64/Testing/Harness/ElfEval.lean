/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean.Data.Json
public import Arm64
public import Arm64.Testing.Harness.TestCase
public import Arm64.Testing.Harness.ElfRegionLoad
public import Arm64.Testing.Harness.ElfLoaderDiff

/-!
# ELF Loader and Execution Differential Harness

Standalone `elf_eval` CLI for differential testing of `Arm64.Obj.LinkedImage.load` and
`Program.ofImage`. Reads JSON requests with `LinkedImage` fields, load `base`, and optional `exec`
parameters, emitting `Image.toLoadedRegions` and optional `ProofLib.execUntilPC` results.
-/

@[expose] public section

namespace Testing.ElfEval

open Lean
open Arm64
open Arm64.Obj
open Testing.Harness

/-! ## Hex and JSON helpers -/

def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hexToBytes (s : String) : Except String (List (BitVec 8)) :=
  let rec go : List Char → List (BitVec 8) → Except String (List (BitVec 8))
    | [], acc => pure acc.reverse
    | a :: b :: cs, acc =>
      match hexVal? a, hexVal? b with
      | some x, some y => go cs (BitVec.ofNat 8 (16 * x + y) :: acc)
      | _, _ => throw "invalid hex digit"
    | [_], _ => throw "odd-length hex string"
  go s.toList []

def hexChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

def bytesToHex (bs : List (BitVec 8)) : String :=
  String.ofList (bs.foldr (fun b acc => hexChar (b.toNat / 16) :: hexChar (b.toNat % 16) :: acc) [])

def natField (j : Json) (k : String) : Except String Nat := j.getObjValAs? Nat k

def natFieldD (j : Json) (k : String) (d : Nat) : Nat := (natField j k).toOption.getD d

def arrField (j : Json) (k : String) : Except String (List Json) :=
  return (← j.getObjValAs? (Array Json) k).toList

def hexField (j : Json) (k : String) : Except String (List (BitVec 8)) := do
  hexToBytes (← j.getObjValAs? String k)

def parseNamed (j : Json) : Except String (String × Nat) := do
  let #[n, o] ← j.getArr? | throw s!"expected [name, offset], got {j.compress}"
  return (← n.getStr?, ← o.getNat?)

/-! ## Parsing a `LinkedImage` -/

def parseGotEntry (j : Json) : Except String GotEntry :=
  match j.getObjValAs? Nat "addr", j.getObjValAs? Nat "tpoff" with
  | .ok off, .error _ => pure (.addr off)
  | .error _, .ok v => pure (.tpoff v)
  | _, _ => throw ("expected {\"addr\": n} or {\"tpoff\": n} in got, got " ++ j.compress)

def parseImage (j : Json) : Except String LinkedImage := do
  let roData ← (← arrField j "ro_data").mapM fun e => do
    let #[o, n] ← e.getArr? | throw "expected [offset, size] in ro_data"
    return (← o.getNat?, ← n.getNat?)
  let externData ← (← arrField j "extern_data").mapM fun e => do
    let #[x, o, n] ← e.getArr? | throw "expected [name, offset, size] in extern_data"
    return (← x.getStr?, ← o.getNat?, ← n.getNat?)
  let relocs ← (← arrField j "relocs").mapM fun r => do
    return ({ off := ← natField r "off", width := ← natField r "width",
              target := ← natField r "target" } : DataReloc)
  let objSymbols ← (← arrField j "obj_symbols").mapM fun e => do
    let #[o, syms] ← e.getArr? | throw "expected [object, symbols] in obj_symbols"
    return (← o.getStr?, ← (← syms.getArr?).toList.mapM parseNamed)
  let objects ← (← arrField j "objects").mapM fun o => do
    let fns ← (← arrField o "fns").mapM fun f => do
      let #[n, h] ← f.getArr? | throw "expected [name, hex] in fns"
      return (← n.getStr?, ← hexToBytes (← h.getStr?))
    return ({ name := ← o.getObjValAs? String "name", fns } : ObjectInfo)
  return {
    code := ← hexField j "code_hex"
    dataOff := ← natField j "data_off"
    data := ← hexField j "data_hex"
    bss := ← natField j "bss"
    roData, externData
    gotOff := ← natField j "got_off"
    got := ← (← arrField j "got").mapM parseGotEntry
    relocs
    symbols := ← (← arrField j "symbols").mapM parseNamed
    objSymbols
    stubs := ← (← arrField j "stubs").mapM parseNamed
    objects }

/-! ## Output -/

def permToStr (p : Arm64.Perm) : String :=
  s!"{if p.r then "r" else "-"}{if p.w then "w" else "-"}{if p.x then "x" else "-"}"

def regionToJson (r : LoadedRegion) : Json :=
  Json.mkObj [
    ("vaddr", toJson r.vaddr.toNat),
    ("size", toJson r.bytes.length),
    ("perm", Json.str (permToStr r.perm)),
    ("bytes_hex", Json.str (bytesToHex r.bytes))]

def namedToJson (base : BitVec 64) (x : String × Nat) : Json :=
  Json.mkObj [
    ("name", Json.str x.1),
    ("offset", toJson x.2),
    ("addr", toJson (base + BitVec.ofNat 64 x.2).toNat)]

def statusToStr : ExecStatus → String
  | .Running => "running"
  | .Halted => "halted"
  | .Exited code => s!"exited:{code.toNat}"
  | .Signaled sig => s!"signaled:{sig.toNat}"
  | .Panicked => "panicked"
  | .OutOfMemory => "oom"
  | .Exception msg => s!"exception:{msg}"

def evalExec (img : Image) (ex : Json) : Except String Json := do
  let reg (k : String) : BitVec 64 := BitVec.ofNat 64 (natFieldD ex k 0)
  let entryPC : BitVec 64 := BitVec.ofNat 64 (natFieldD ex "entry_pc" img.base.toNat)
  let exitPC : BitVec 64 := BitVec.ofNat 64 (natFieldD ex "exit_pc" 0xdead0000)
  let sp := natFieldD ex "sp" 0x80000000
  let stackBase := (sp / pageSize) * pageSize - 16384
  let stackRegion : LoadedRegion :=
    { vaddr := BitVec.ofNat 64 stackBase, bytes := List.replicate 32768 0#8, perm := .rw }
  let mut st : State :=
    { pc := entryPC, sp := BitVec.ofNat 64 sp, status := .Running,
      mem := stackRegion.applyToMemory img.loadIntoMemory,
      symtab := img.symtab, brkStart := img.brkStart, brk := img.brkStart }
  st := st.writeReg64 (.gpr 0#5) (reg "x0")
  st := st.writeReg64 (.gpr 1#5) (reg "x1")
  st := st.writeReg64 (.gpr 2#5) (reg "x2")
  st := st.writeReg64 (.gpr 30#5) exitPC
  let sf := execUntilPC (natFieldD ex "max_steps" 1024) (Program.ofImage img) exitPC st
  let reads ← ((ex.getObjValAs? (Array Json) "read_ranges").toOption.getD #[]).toList.mapM
    fun r => do
      let addr ← natField r "addr"
      let size ← natField r "size"
      let bs := (List.range size).map fun i => sf.mem.read8 (BitVec.ofNat 64 (addr + i))
      return Json.mkObj [("addr", toJson addr), ("size", toJson size),
        ("bytes_hex", Json.str (bytesToHex bs))]
  return Json.mkObj [
    ("pc", toJson sf.pc.toNat),
    ("sp", toJson sf.sp.toNat),
    ("x0", toJson (sf.readReg64 (.gpr 0#5)).toNat),
    ("x1", toJson (sf.readReg64 (.gpr 1#5)).toNat),
    ("x2", toJson (sf.readReg64 (.gpr 2#5)).toNat),
    ("status", Json.str (statusToStr sf.status)),
    ("read_results", Json.arr reads.toArray)]

def evalRequest' (req : Json) : Except String Json := do
  let li ← parseImage req
  let img ← li.load (BitVec.ofNat 64 (← natField req "base"))
  let execFields : List (String × Json) ← match req.getObjVal? "exec" with
    | .ok ex => if ex.isNull then pure [] else pure [("exec_result", ← evalExec img ex)]
    | .error _ => pure []
  return Json.mkObj ([
    ("status", Json.str "ok"),
    ("base", toJson img.base.toNat),
    ("code_hex", Json.str (bytesToHex img.code)),
    ("data_addr", toJson img.dataAddr.toNat),
    ("data_hex", Json.str (bytesToHex img.data)),
    ("ro_data", Json.arr (img.roData.map fun (a, n) =>
      Json.mkObj [("addr", toJson a.toNat), ("size", toJson n)]).toArray),
    ("extern_data", Json.arr (img.externData.map fun (x, a, n) =>
      Json.mkObj [("name", Json.str x), ("addr", toJson a.toNat), ("size", toJson n)]).toArray),
    ("got_addr", toJson img.gotAddr.toNat),
    ("got", Json.arr (img.got.map (toJson ·.toNat)).toArray),
    ("symbols", Json.arr (img.symbols.map (namedToJson img.base)).toArray),
    ("stubs", Json.arr (img.stubs.map (namedToJson img.base)).toArray),
    ("loaded_regions", Json.arr (img.toLoadedRegions.map regionToJson).toArray)
  ] ++ execFields)

def evalRequest (req : Json) : Json :=
  match evalRequest' req with
  | .ok j => j
  | .error e => Json.mkObj [("status", Json.str "error"), ("error", Json.str e)]

def parseHexArgs : List String → List String
  | "--hex" :: spec :: rest => spec :: parseHexArgs rest
  | _ :: rest => parseHexArgs rest
  | [] => []

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--loader-diff"] =>
    let cases ← Testing.ElfLoaderDiff.runDefaultElfLoaderDiffIO
    return (← runTestSuite cases)
  | ["--loader-diff", manifestPath] =>
    let cases ← Testing.ElfLoaderDiff.runManifestPathIO manifestPath
    return (← runTestSuite cases)
  | ["--loader-diff", elfPath, snapJsonPath] =>
    return (← Testing.ElfLoaderDiff.runSingleEntryDiffIO elfPath snapJsonPath)
  | ["--dump-load-state", elfPath] =>
    return (← Testing.ElfLoaderDiff.dumpLoadStateIO elfPath none [])
  | "--dump-load-state" :: elfPath :: snapJsonPath :: rest =>
    return (← Testing.ElfLoaderDiff.dumpLoadStateIO elfPath (some snapJsonPath) (parseHexArgs rest))
  | _ => pure ()
  let input ← match args with
    | path :: _ => IO.FS.readFile path
    | [] => (← IO.getStdin).readToEnd
  match Json.parse input with
  | .error err =>
    IO.eprintln s!"elf_eval: failed to parse JSON input: {err}"
    return 1
  | .ok j =>
    let res := match j.getArr? with
      | .ok arr => Json.arr (arr.map evalRequest)
      | .error _ => evalRequest j
    IO.println res.compress
    return 0

end Testing.ElfEval

def main (args : List String) : IO UInt32 :=
  Testing.ElfEval.main args
