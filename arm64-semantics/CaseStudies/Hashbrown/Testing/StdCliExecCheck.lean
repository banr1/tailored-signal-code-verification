/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Std.Data.HashMap
public import Arm64.Trusted.Process
public import ProofLib.Exec
public import ProofLib.Process.Core
public import CaseStudies.Hashbrown.Spec.Top
public meta import Std.Data.HashMap
public meta import Arm64.Trusted.Process
public meta import ProofLib.Exec
public meta import ProofLib.Process.Core
public meta import CaseStudies.Hashbrown.Spec.Top

/-!
# Concrete Execution Checks for `hashbrown_cli.elf`

Elaboration-time `#eval` / `#guard_msgs` tests running `hashbrown_cli.elf` on `Program.pureMem`
with patch-compacted memory and checking agreement with `HashbrownCliPost` across empty stdin,
all CLI operations, malformed lines, overlong lines, `argv` variations, and `SYS_brk` refusal
falling back to `SYS_mmap`.
-/

@[expose] public section

namespace CaseStudies.Hashbrown.Testing.StdCliExecCheck

open Arm64 Arm64.Process ProofLib CaseStudies.Hashbrown

meta def stdElfPaths : List System.FilePath :=
  [ "Implementation/hashbrown_cli.elf",
    "CaseStudies/Hashbrown/Implementation/hashbrown_cli.elf",
    "../../CaseStudies/Hashbrown/Implementation/hashbrown_cli.elf" ]

meta def loadStdElf : IO ElfImage := do
  let some path ← stdElfPaths.findM? (·.pathExists)
    | throw <| .userError "hashbrown_cli.elf not found"
  let bytes ← IO.FS.readBinFile path
  match ElfImage.parseByteArray bytes with
  | .ok img => pure img
  | .error e => throw <| .userError s!"ElfImage.parseByteArray failed: {e}"

meta def mkRegionArrays (regions : List Snapshot.Region) :
    Array (BitVec 64 × Perm × Array (BitVec 8)) :=
  (regions.map fun r => (r.start, r.perm, r.bytes.toArray)).toArray

meta def fastCellAt (arrs : Array (BitVec 64 × Perm × Array (BitVec 8))) (a : BitVec 64) :
    Option (Option Perm × BitVec 8) :=
  arrs.findSome? fun (start, perm, bs) =>
    let i := (a - start).toNat
    if h : i < bs.size then some (some perm, bs[i]) else none

meta def compactRegs (s : State) : State :=
  let gprs : Array (BitVec 64) := Array.ofFn fun (i : Fin 32) => s.regs.regs (BitVec.ofNat 5 i.val)
  let vecs : Array (BitVec 128) := Array.ofFn fun (i : Fin 32) => s.vregs.regs (BitVec.ofNat 5 i.val)
  { s with
    regs  := ⟨fun i => gprs[i.toNat]'(by rw [Array.size_ofFn]; exact i.isLt)⟩
    vregs := ⟨fun i => vecs[i.toNat]'(by rw [Array.size_ofFn]; exact i.isLt)⟩ }

/-- Address ranges `(base, len)` that `execInst inst s = s'` may have written in `s'.mem`. -/
meta def instWriteRanges (inst : Instr) (s s' : State) : List (BitVec 64 × Nat) :=
  match inst with
  | .str msz _ dst => [( (evalAddrMode s dst).1, msz.bytes )]
  | .stp w _ _ dst => [( (evalAddrMode s dst).1, 2 * (w : MemWidth).bytes )]
  | .strSimd sz _ addr => [( (evalAddrMode s addr).1, sz.bytes )]
  | .stpSimd sz _ _ addr => [( (evalAddrMode s addr).1, 2 * sz.bytes )]
  | .stnp sz rn _ _ offset => [( s.readReg64 rn + offset, 2 * sz.bytes )]
  | .stnpSimd sz _ _ rn offset => [( s.readReg64 rn + offset, 2 * sz.bytes )]
  | .dcZva rt => [( s.readReg64 rt &&& ~~~63#64, 64 )]
  | .ldarStlr sz isLoad rn _ => if isLoad then [] else [( s.readReg64 rn, sz.bytes )]
  | .stxr sz _ _ rn _ | .cas sz _ _ _ rn _ | .atomicRmw _ sz _ _ _ rn _ =>
    [( s.readReg64 rn, sz.bytes )]
  | .stxp sz _ _ rn _ _ | .casp sz _ _ _ _ rn _ _ =>
    [( s.readReg64 rn, 2 * sz.bytes )]
  | .ldapurStlur sz opc rn _ offset =>
    if opc == 0#2 then [( s.readReg64 rn + offset, sz.bytes )] else []
  | .system false 0#16 =>
    let nr := s.readReg64 .x8
    let ret := s'.readReg64 .x0
    if nr == SYS_READ || nr == SYS_PREAD64 then
      if ret.slt 0#64 || ret == 0#64 then [] else [( s.readReg64 .x1, ret.toNat )]
    else if nr == SYS_GETRANDOM then
      if ret.slt 0#64 || ret == 0#64 then [] else [( s.readReg64 .x0, ret.toNat )]
    else if nr == SYS_BRK then
      let oldPage := Arm64.pageAlignUp s.brk.toNat
      let newPage := Arm64.pageAlignUp s'.brk.toNat
      if oldPage < newPage then [( BitVec.ofNat 64 oldPage, newPage - oldPage )]
      else if newPage < oldPage then [( BitVec.ofNat 64 newPage, oldPage - newPage )]
      else []
    else if nr == SYS_MMAP then
      if ret.slt 0#64 then [] else [( ret, Arm64.pageAlignUp (s.readReg64 .x1).toNat )]
    else if nr == 132#64 then
      let oss := s.readReg64 .x1
      if ret.slt 0#64 || oss == 0#64 then [] else [( oss, 24 )]
    else if nr == SYS_RT_SIGACTION then
      let oact := s.readReg64 .x2
      if ret.slt 0#64 || oact == 0#64 then [] else [( oact, 32 )]
    else if nr == SYS_RT_SIGPROCMASK then
      let oset := s.readReg64 .x2
      if ret.slt 0#64 || oset == 0#64 then [] else [( oset, 8 )]
    else if nr == SYS_MUNMAP || nr == SYS_MPROTECT || nr == SYS_MADVISE then
      if ret.slt 0#64 then [] else [( s.readReg64 .x0, Arm64.pageAlignUp (s.readReg64 .x1).toNat )]
    else if nr == SYS_MREMAP then
      if ret.slt 0#64 then []
      else [( s.readReg64 .x0, Arm64.pageAlignUp (s.readReg64 .x1).toNat ),
            ( ret, Arm64.pageAlignUp (s.readReg64 .x2).toNat )]
    else []
  | _ => []

meta def mkFastMemMmap (baseMem : Memory) (rwBase rwCapEnd stkBase stackTop : BitVec 64)
    (rwArr stkArr : Array (Option (Option Perm × BitVec 8)))
    (extraMap : Std.HashMap UInt64 (Option (Option Perm × BitVec 8))) : Memory :=
  ⟨fun a =>
    if rwBase ≤ a && a < rwCapEnd then
      let i := (a - rwBase).toNat
      if h : i < rwArr.size then rwArr[i] else baseMem.cells a
    else if stkBase ≤ a && a < stackTop then
      let i := (a - stkBase).toNat
      if h : i < stkArr.size then stkArr[i] else baseMem.cells a
    else
      match extraMap[a.toNat.toUInt64]? with
      | some cell => cell
      | none      => baseMem.cells a⟩

/-- Run `img` on `Program.pureMem` with incremental patch compaction.
    When `blockBrk = true`, a `PROT_NONE` page is pre-mapped at `s0.brk + 4096` (inside
    `BRK_GUARD_GAP`) so `execBrk` deterministically refuses heap expansion and `mallocng` falls
    back to `SYS_mmap`. -/
meta def runStdElfFast (maxSteps : Nat) (img : ElfImage) (inputs : ProcessInputs)
    (blockBrk : Bool := false) :
    Except String (State × Option ProcessOutcome) := do
  let s0 ← img.loadState inputs
  let (_, stackRegion) ← buildInitialStack img inputs
  let stackBase := BitVec.ofNat 64 (inputs.init.stackTop.toNat - inputs.init.stackSize)
  let stackTop := inputs.init.stackTop
  let stkLen : Nat := 16384
  let stkBase := BitVec.ofNat 64 (stackTop.toNat - stkLen)
  let regArrs := mkRegionArrays (img.segments ++ [stackRegion])
  let baseMem := (⟨fastCellAt regArrs⟩ : Memory).mapZero stackBase inputs.init.stackSize
  let rwBase : BitVec 64 := 0x280000#64
  let rwCapLen : Nat := if blockBrk then (s0.brk - rwBase).toNat else 0x30000
  let rwCapEnd := rwBase + BitVec.ofNat 64 rwCapLen
  let rwArrInit := Array.ofFn fun (i : Fin rwCapLen) => baseMem.cells (rwBase + BitVec.ofNat 64 i.val)
  let stkArrInit := Array.ofFn fun (i : Fin stkLen) => baseMem.cells (stkBase + BitVec.ofNat 64 i.val)
  let extraInit : Std.HashMap UInt64 (Option (Option Perm × BitVec 8)) :=
    if blockBrk then
      ({} : Std.HashMap UInt64 (Option (Option Perm × BitVec 8))).insert
        (s0.brk.toNat + 4096).toUInt64 (some (some .protNone, 0#8))
    else {}
  let sInit := compactRegs { s0 with mem := mkFastMemMmap baseMem rwBase rwCapEnd stkBase stackTop rwArrInit stkArrInit extraInit }
  let rec loop (fuel : Nat) (s : State)
      (rwArr stkArr : Array (Option (Option Perm × BitVec 8)))
      (extra : Std.HashMap UInt64 (Option (Option Perm × BitVec 8))) : State :=
    match fuel with
    | 0 => s
    | k + 1 =>
      if s.status != .Running then s
      else
        let s1 := if k % 64 == 0 then compactRegs s else s
        match Program.pureMem.fetchMem s1.mem s1.pc with
        | none => { s1 with status := .Halted }
        | some inst =>
          let s2 := execInst inst s1
          if s2.status != .Running then s2
          else
            let ranges := instWriteRanges inst s1 s2
            if ranges.isEmpty then
              loop k s2 rwArr stkArr extra
            else
              let patches := ranges.map fun (ea, len) =>
                (ea, Array.ofFn fun (i : Fin len) => s2.mem.cells (ea + BitVec.ofNat 64 i.val))
              let s2Empty := { s2 with mem := Memory.empty }
              let (rwArr', stkArr', extra') := Id.run do
                let mut rw := rwArr
                let mut stk := stkArr
                let mut ex := extra
                for (ea, cells) in patches do
                  for j in [0:cells.size] do
                    let a := ea + BitVec.ofNat 64 j
                    let c := cells[j]!
                    if rwBase ≤ a && a < rwCapEnd then
                      rw := rw.set! (a - rwBase).toNat c
                    else if stkBase ≤ a && a < stackTop then
                      stk := stk.set! (a - stkBase).toNat c
                    else
                      ex := ex.insert a.toNat.toUInt64 c
                return (rw, stk, ex)
              let mem' := mkFastMemMmap baseMem rwBase rwCapEnd stkBase stackTop rwArr' stkArr' extra'
              loop k { s2Empty with mem := mem' } rwArr' stkArr' extra'
  let sf := loop maxSteps sInit rwArrInit stkArrInit extraInit
  pure (sf, ProcessOutcome.ofTerminated? sf)

meta def assertStdCliRun (img : ElfImage) (label : String) (maxSteps : Nat)
    (inputs : ProcessInputs) (expExit : BitVec 64) (expOut expErr : String)
    (blockBrk : Bool := false) : IO Unit := do
  match runStdElfFast maxSteps img inputs blockBrk with
  | .ok (_, some out) =>
    unless out.exitCode == expExit do
      throw <| .userError s!"[{label}] exitCode = {out.exitCode}, expected {expExit}"
    unless out.signal.isNone do
      throw <| .userError s!"[{label}] unexpected signal {out.signal}"
    unless out.stdout == bytesOfString expOut do
      throw <| .userError s!"[{label}] stdout mismatch: got {String.fromUTF8? ⟨out.stdout.toArray.map (·.toNat.toUInt8)⟩}, expected {repr expOut}"
    unless out.stderr == bytesOfString expErr do
      throw <| .userError s!"[{label}] stderr mismatch: got {String.fromUTF8? ⟨out.stderr.toArray.map (·.toNat.toUInt8)⟩}, expected {repr expErr}"
    unless out.fs.files "" == (initFsState inputs).files "" do
      throw <| .userError s!"[{label}] filesystem mutated"
  | .ok (sf, none) =>
    throw <| .userError s!"[{label}] did not terminate within {maxSteps} steps (pc={sf.pc}, status={repr sf.status})"
  | .error e =>
    throw <| .userError s!"[{label}] loadState failed: {e}"

meta def runStdCliExecChecks : IO Unit := do
  let img ← loadStdElf
  -- (a) Empty stdin
  assertStdCliRun img "empty-stdin" 40000
    { stdin := bytesOfString "" }
    0#64 "" ""
  -- (b1) Full 10-op session: new, is_empty, len, insert, contains, overwrite, get, remove, clear, with_capacity, drop
  assertStdCliRun img "all-10-ops-with-newline" 120000
    { stdin := bytesOfString
        ("is_empty\nlen\n" ++
         "insert 3 7\ncontains 3\ncontains 9\nis_empty\nlen\n" ++
         "insert 3 99\ninsert 8 80\nlen\nget 3\nremove 3\ncontains 3\nlen\nget 3\n" ++
         "clear\nis_empty\nlen\nget 8\n" ++
         "insert 5 55\nwith_capacity 64\nis_empty\nlen\nget 5\ninsert 5 66\nget 5\n") }
    0#64
    ("true\n0\n" ++
     "true\nfalse\nfalse\n1\n" ++
     "2\n99\nfalse\n1\nnone\n" ++
     "true\n0\nnone\n" ++
     "true\n0\nnone\n66\n")
    ""
  -- (b2) Session without trailing newline
  assertStdCliRun img "crud-no-trailing-newline" 60000
    { stdin := bytesOfString "insert 10 20\nget 10" }
    0#64 "20\n" ""
  -- (c) Malformed command lines (including with_capacity 4097): skipped with "error: invalid command\n" on stderr, exit 0
  assertStdCliRun img "malformed-lines" 100000
    { stdin := bytesOfString "insert 5 50\nbad line\nwith_capacity 4097\n\nget  5\nget 18446744073709551616\nget 5\n" }
    0#64 "50\n"
    ("error: invalid command\n" ++
     "error: invalid command\n" ++
     "error: invalid command\n" ++
     "error: invalid command\n" ++
     "error: invalid command\n")
  -- (d) Overlong line > 4096: rejected before executing earlier valid commands, exit 1
  assertStdCliRun img "overlong-line-4097" 120000
    { stdin := bytesOfString "insert 1 99\nget 1\n" ++ List.replicate 4097 0x61#8 }
    1#64 "" "error: line too long\n"
  -- (e) Concrete argc/argv startup variations
  assertStdCliRun img "argv-empty" 60000
    { argv := [], stdin := bytesOfString "insert 1 42\nget 1\n" }
    0#64 "42\n" ""
  assertStdCliRun img "argv-multi" 60000
    { argv := [bytesOfString "hb", bytesOfString "ignored", bytesOfString "--flag"],
      stdin := bytesOfString "insert 1 42\nget 1\n" }
    0#64 "42\n" ""
  -- (f) SYS_brk refusal resilience (guard page at s0.brk + 4096 forces mallocng SYS_mmap fallback)
  assertStdCliRun img "brk-refusal-mmap-fallback" 80000
    { stdin := bytesOfString "with_capacity 32\ninsert 7 77\nget 7\n" }
    0#64 "77\n" "" (blockBrk := true)

/-- info: ok -/
#guard_msgs in
#eval do runStdCliExecChecks; IO.println "ok"

end CaseStudies.Hashbrown.Testing.StdCliExecCheck
