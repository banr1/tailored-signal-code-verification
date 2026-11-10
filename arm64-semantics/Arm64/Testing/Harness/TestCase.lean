/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean.Data.Json
public import Arm64
public import Arm64.Testing.Harness.Encode

/-!
# Canonical ISA Test Representations (`Arm64.Testing.Harness.TestCase`)

- **Layer / Role**: Untrusted ISA test harness (`Lib::Testing`, `Role::Test`).
- **Purpose & Key Exports**: Defines the canonical test case formats shared across all ISA
  differential and regression testing:
  1. **`IsaTestCase` (alias `DiffTestCase`)**: The canonical multi-instruction test case consisting
     of an initial architectural state (`regs`, `vregs`, `sp`, `nzcv`, `memInit`, `basePC`,
     `startPC`), an instruction stream (`asm` mnemonics or `words` 32-bit machine words + `exitPC`
     + `maxSteps`), watched memory ranges (`memWatch`), and optional `skipSail` when an oracle is
     inapplicable. `IsaTestCase.toInitialState` materializes the exact `Arm64.Program × Arm64.State`
     for execution.
  2. **`FpBatchRecord`**: Compact 32-byte (4 × `UInt64`) binary encoding of a pure IEEE-754
     floating-point test vector (`--batch-fp`) with operation code, precision (`f32`/`f64`),
     rounding mode (`RNE`/`RP`/`RM`/`RZ`), and up to 3 operands `(a, b, c)`.
  3. **`UnitTestCase` (alias `TestCase`)**: Thin `(name, check)` assertion wrapper and single-program
     execution helpers (`runProgram`, `runWords`, `runTestSuite`) for in-Lean regression tests.
- **When to read**: Start here when inspecting what a single ISA test looks like or how initial
  architectural states are constructed.
-/

@[expose] public section

namespace Testing.Harness

open Lean
open Arm64

/-! ## 1. Standard Test Address Layout, Concrete Stepper & Hex Formatting -/

/-- `m` with the code of `prog` at `prog.base`, mapped read-execute; other bytes unchanged. -/
def loadCode (prog : Program) (m : Memory) : Memory :=
  let code := prog.code.toArray
  ⟨fun a =>
    let i := (a - prog.base).toNat
    if h : i < code.size then some (some Perm.rx, code[i]) else m.cells a⟩

/-- `m` with every unmapped byte mapped read-write (a flat test memory). -/
def mapRestRw (m : Memory) : Memory :=
  ⟨fun a =>
    match m.cells a with
    | some (some p, b) => some (some p, b)
    | some (none, b)   => some (some Perm.rw, b)
    | none             => some (some Perm.rw, 0#8)⟩

/-- Deterministic single-step evaluator for a `Program` and `State`. -/
def stepState (prog : Program) (s : State) : Option State :=
  match s.status with
  | .Running =>
    match prog.externAt? s.pc with
    | some f => some (f s)
    | none =>
      match prog.fetchMem s.mem s.pc with
      | some inst => some (execInst inst s)
      | none      => some { s with status := .Halted }
  | _ => none

/-- Execute up to `n` steps of `prog` from state `s`, stopping immediately once `s.pc == target_pc`
    or `s.status != .Running`. -/
def execUntilPC (n : Nat) (prog : Program) (target_pc : BitVec 64) (s : State) : State :=
  match n with
  | 0 => s
  | n + 1 =>
    if s.pc == target_pc || s.status != .Running then
      s
    else
      match stepState prog s with
      | some s' => execUntilPC n prog target_pc s'
      | none    => s

/-- Default code base address (`0x10000`) for multi-instruction differential test cases. -/
def codeBase  : BitVec 64 := 0x10000#64
/-- Default data scratch base address (`0x80000`) for differential and unit test cases. -/
def dataBase  : BitVec 64 := 0x80000#64
/-- Default initial stack pointer (`0x88000`, 16-byte aligned). -/
def defaultSP : BitVec 64 := 0x88000#64
/-- Default return sentinel address (`0xdead0000`) placed in `X30` (`LR`). -/
def exitPC    : BitVec 64 := 0xdead0000#64
/-- Fixed 64-byte scratch memory base (`0x20000`) used by single-instruction batch fuzzing. -/
def batchScratchBase : BitVec 64 := 0x20000#64

/-- Convert `PState` (`N, Z, C, V`) into its 4-bit `nzcv` immediate (`N=bit 3 .. V=bit 0`).
    Inverse of `PState.ofBits4`. -/
def pstateToBits4 (ps : PState) : BitVec 4 :=
  (if ps.n then 8#4 else 0#4) |||
  (if ps.z then 4#4 else 0#4) |||
  (if ps.c then 2#4 else 0#4) |||
  (if ps.v then 1#4 else 0#4)

/-- Format a 64-bit bitvector as a zero-padded 16-digit lowercase hex string `"0x..."`. -/
def hex64 (bv : BitVec 64) : String :=
  let digits := "0123456789abcdef".toList
  Id.run do
    let mut n := bv.toNat
    let mut chars : List Char := []
    for _ in [0:16] do
      let d := n % 16
      chars := (digits[d]?.getD '0') :: chars
      n := n / 16
    return "0x" ++ String.ofList chars

/-- Format a 128-bit bitvector as a zero-padded 32-digit lowercase hex string `"0x..."`. -/
def hex128 (bv : BitVec 128) : String :=
  let digits := "0123456789abcdef".toList
  Id.run do
    let mut n := bv.toNat
    let mut chars : List Char := []
    for _ in [0:32] do
      let d := n % 16
      chars := (digits[d]?.getD '0') :: chars
      n := n / 16
    return "0x" ++ String.ofList chars

/-- Parse a decimal or `"0x..."` hex JSON scalar into a `Nat`. -/
def parseNat (j : Json) : Nat :=
  match j.getNat? with
  | .ok n => n
  | .error _ =>
    match j.getStr? with
    | .ok s =>
      let s := s.trimAscii.toString
      if s.startsWith "0x" || s.startsWith "0X" then
        let hex := (s.drop 2).toString.toList
        hex.foldl (fun acc c =>
          let d :=
            if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
            else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
            else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
            else 0
          acc * 16 + d) 0
      else
        s.toNat?.getD 0
    | .error _ => 0

/-! ## 2. Deterministic SplitMix64 PRNG (Shared by Batch State Expansion & Fuzz Generators) -/

/-- Deterministic SplitMix64 PRNG matching `tools/run-trusted-tests` bit-for-bit. -/
structure SplitMix64 where
  state : UInt64
  deriving Repr, Inhabited

namespace SplitMix64

def nextUInt64 (rng : SplitMix64) : UInt64 × SplitMix64 :=
  let s := rng.state + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  let z := z ^^^ (z >>> 31)
  (z, { state := s })

def nextNat (rng : SplitMix64) (bound : Nat) : Nat × SplitMix64 :=
  let (u, rng') := rng.nextUInt64
  if bound == 0 then (0, rng') else (u.toNat % bound, rng')

end SplitMix64

/-! ## 3. Canonical Multi-Instruction Test Case (`IsaTestCase` / `DiffTestCase`) -/

/-- Initial memory write of `size` bytes (`1`, `2`, `4`, or `8`, little-endian) at `addr`. -/
structure MemWrite where
  addr : BitVec 64
  val  : BitVec 64
  size : Nat := 8
  deriving Repr, Inhabited

/-- Memory range `[addr, addr + size)` (`size ∈ {1, 2, 4, 8}`) watched and compared post-execution. -/
structure MemWatch where
  addr : BitVec 64
  size : Nat := 8
  deriving Repr, Inhabited

/-- Canonical multi-instruction ISA test case:
    - **Initial state**: `basePC`, `startPC`, `regs` (`X0..X30`), `vregs` (`V0..V31`), `sp`, `nzcv`,
      `memInit`.
    - **Instructions**: assembly source `asm` (assembled to `words` by `run-trusted-tests`) or
      pre-encoded 32-bit machine words `words`, executed up to `exitPC` or `maxSteps`.
    - **Expected outcome / Oracles**: watched memory ranges `memWatch` and optional `skipSail`
      justification (used only on `System/Dczid_DcZva_LinuxUserspace` for `DC ZVA` and
      `SimdExtra/Addv_ByteLanes` for byte-lane `ADDV`). -/
structure IsaTestCase where
  name       : String
  asm        : Option String := none
  basePC     : BitVec 64 := codeBase
  startPC    : BitVec 64 := codeBase
  exitPC     : BitVec 64 := exitPC
  maxSteps   : Nat := 500
  words      : Array (BitVec 32) := #[]
  regs       : Array (BitVec 64) := (Array.replicate 31 0#64).set! 30 exitPC
  vregs      : Array (BitVec 128) := Array.replicate 32 0#128
  sp         : BitVec 64 := defaultSP
  nzcv       : Nat := 0
  memInit    : Array MemWrite := #[]
  memWatch   : Array MemWatch := #[]
  /-- If set, the Sail oracle is not run for this case; the string documents why (used on
      `System/Dczid_DcZva_LinuxUserspace` where Sail sets `DCZID_EL0.DZP=1` and traps `DC ZVA`,
      and `SimdExtra/Addv_ByteLanes` where Sail hits an internal assertion on byte-lane `ADDV`).
      Unicorn is still required. -/
  skipSail   : Option String := none
  deriving Repr, Inhabited

/-- Alias preserving backward compatibility with existing suites and golden tests. -/
abbrev DiffTestCase := IsaTestCase

/-- Build a 31-element GPR array (`X0..X30`, defaulting `X30 = exitPC` and other registers to `0`)
    with `(regIdx, val)` overrides applied. -/
def initRegArray (overrides : List (Nat × BitVec 64)) : Array (BitVec 64) := Id.run do
  let mut arr := Array.replicate 31 0#64
  arr := arr.set! 30 exitPC
  for (idx, val) in overrides do
    if idx < 31 then
      arr := arr.set! idx val
  return arr

/-- Build a 32-element 128-bit VReg array (`V0..V31`, defaulting to `0`) with `(vregIdx, val)`
    overrides applied. -/
def initVRegArray (overrides : List (Nat × BitVec 128)) : Array (BitVec 128) := Id.run do
  let mut arr := Array.replicate 32 0#128
  for (idx, val) in overrides do
    if idx < 32 then
      arr := arr.set! idx val
  return arr

/-- Create an assembly-backed differential test case ending with `ret` (returning to `exitPC` in `X30`). -/
def makeAsmTestCase
    (name : String)
    (asmText : String)
    (regs : List (Nat × BitVec 64) := [])
    (vregs : List (Nat × BitVec 128) := [])
    (sp : BitVec 64 := defaultSP)
    (nzcv : Nat := 0)
    (memInitU64 : List (BitVec 64 × BitVec 64) := [])
    (memWatchU64 : List (BitVec 64) := [])
    (maxSteps : Nat := 500) : IsaTestCase :=
  let fullAsm := asmText.trimAscii.toString ++ "\nret"
  { name := name
    asm := some fullAsm
    basePC := codeBase
    startPC := codeBase
    exitPC := exitPC
    maxSteps := maxSteps
    words := #[]
    regs := initRegArray regs
    vregs := initVRegArray vregs
    sp := sp
    nzcv := nzcv
    memInit := (memInitU64.map fun (a, v) => { addr := a, val := v, size := 8 }).toArray
    memWatch := (memWatchU64.map fun a => { addr := a, size := 8 }).toArray }

/-- Materialize the `Arm64.Program` and initial `Arm64.State` for an `IsaTestCase`.
    Code bytes at `[basePC, basePC + 4 * words.size)` are mapped `Perm.rx` via `prog.loadCode`,
    and all remaining addresses are mapped `Perm.rw` via `mapRestRw`. -/
def IsaTestCase.toInitialState (tc : IsaTestCase) : Program × State := Id.run do
  let mut st : State := {
    pc := tc.startPC
    sp := tc.sp
    pstate := PState.ofBits4 (BitVec.ofNat 4 tc.nzcv)
    status := .Running
  }
  for i in [0:Nat.min 31 tc.regs.size] do
    st := st.writeReg64 (.gpr (BitVec.ofNat 5 i)) tc.regs[i]!
  for i in [0:Nat.min 32 tc.vregs.size] do
    st := st.writeVReg128 (BitVec.ofNat 5 i) tc.vregs[i]!
  for m in tc.memInit do
    let memSz : MemWidth :=
      match m.size with
      | 1 => .B8
      | 2 => .H16
      | 4 => .W32
      | _ => .X64
    st := st.setMem (st.mem.writeSized memSz m.addr m.val)
  for i in [0:tc.words.size] do
    let addr := tc.basePC + BitVec.ofNat 64 (i * 4)
    st := st.setMem (st.mem.write32 addr tc.words[i]!)
  let prog := Program.ofWords tc.basePC tc.words.toList
  st := st.setMem (mapRestRw (loadCode prog st.mem))
  return (prog, st)

/-- Serialize an `IsaTestCase` to the JSON wire format consumed by `run-trusted-tests` and `diff_eval`. -/
def IsaTestCase.toJson (tc : IsaTestCase) : Json :=
  let memInitJson := tc.memInit.map fun m =>
    Json.arr #[Json.str (hex64 m.addr), Json.str (hex64 m.val), Lean.toJson m.size]
  let memWatchJson := tc.memWatch.map fun m =>
    Json.arr #[Json.str (hex64 m.addr), Lean.toJson m.size]
  let wordsJson := tc.words.map fun w => Json.str (hex32 w)
  let regsJson := tc.regs.map fun r => Json.str (hex64 r)
  let vregsJson := tc.vregs.map fun v => Json.str (hex128 v)
  let baseFields : List (String × Json) := [
    ("name", Json.str tc.name),
    ("base_pc", Json.str (hex64 tc.basePC)),
    ("start_pc", Json.str (hex64 tc.startPC)),
    ("exit_pc", Json.str (hex64 tc.exitPC)),
    ("max_steps", Lean.toJson tc.maxSteps),
    ("words", Json.arr wordsJson),
    ("regs", Json.arr regsJson),
    ("vregs", Json.arr vregsJson),
    ("sp", Json.str (hex64 tc.sp)),
    ("nzcv", Lean.toJson tc.nzcv),
    ("mem_init", Json.arr memInitJson),
    ("mem_watch", Json.arr memWatchJson)
  ]
  let fields := match tc.asm with
    | some asmText => ("asm", Json.str asmText) :: baseFields
    | none => baseFields
  let fields := match tc.skipSail with
    | some reason => ("skip_sail", Json.str reason) :: fields
    | none => fields
  Json.mkObj fields

abbrev testCaseToJson := IsaTestCase.toJson

/-- Parse an `IsaTestCase` from a JSON object (supporting both flat register arrays and `[idx, val]` pairs). -/
def IsaTestCase.fromJson (tc : Json) : IsaTestCase := Id.run do
  let name := (tc.getObjValAs? String "name").toOption.getD "unnamed"
  let basePC : BitVec 64 := BitVec.ofNat 64 (parseNat ((tc.getObjVal? "base_pc").toOption.getD (Json.num 0x1000)))
  let startPC : BitVec 64 :=
    match (tc.getObjVal? "start_pc").toOption with
    | some j => BitVec.ofNat 64 (parseNat j)
    | none   => basePC
  let wordsJson := (tc.getObjValAs? (Array Json) "words").toOption.getD #[]
  let words : Array (BitVec 32) := wordsJson.map (fun w => BitVec.ofNat 32 (parseNat w))
  let defaultExit : BitVec 64 := basePC + BitVec.ofNat 64 (words.size * 4)
  let exitPCVal : BitVec 64 :=
    match (tc.getObjVal? "exit_pc").toOption with
    | some j => BitVec.ofNat 64 (parseNat j)
    | none   => defaultExit
  let maxSteps : Nat :=
    match (tc.getObjVal? "max_steps").toOption with
    | some j => parseNat j
    | none   => 512
  let spVal := BitVec.ofNat 64 (parseNat ((tc.getObjVal? "sp").toOption.getD (Json.num 0x80000)))
  let nzcvVal := parseNat ((tc.getObjVal? "nzcv").toOption.getD (Json.num 0))
  let mut regs := Array.replicate 31 0#64
  if let .ok regArr := tc.getObjValAs? (Array Json) "regs" then
    for i in [0:regArr.size] do
      let entry := regArr[i]!
      if let .ok elems := entry.getArr? then
        if elems.size >= 2 then
          let idx := parseNat elems[0]!
          let val := BitVec.ofNat 64 (parseNat elems[1]!)
          if idx < 31 then
            regs := regs.set! idx val
      else if i < 31 then
        regs := regs.set! i (BitVec.ofNat 64 (parseNat entry))
  let mut vregs := Array.replicate 32 0#128
  if let .ok vregArr := tc.getObjValAs? (Array Json) "vregs" then
    for i in [0:vregArr.size] do
      let entry := vregArr[i]!
      if let .ok elems := entry.getArr? then
        if elems.size >= 2 then
          let idx := parseNat elems[0]!
          let val := BitVec.ofNat 128 (parseNat elems[1]!)
          if idx < 32 then
            vregs := vregs.set! idx val
      else if i < 32 then
        vregs := vregs.set! i (BitVec.ofNat 128 (parseNat entry))
  let mut memInit : Array MemWrite := #[]
  if let .ok memArr := tc.getObjValAs? (Array Json) "mem_init" then
    for item in memArr do
      if let .ok elems := item.getArr? then
        if elems.size >= 3 then
          memInit := memInit.push {
            addr := BitVec.ofNat 64 (parseNat elems[0]!)
            val  := BitVec.ofNat 64 (parseNat elems[1]!)
            size := parseNat elems[2]!
          }
      else if let .ok addrJson := item.getObjVal? "addr" then
        if let .ok valJson := item.getObjVal? "val" then
          memInit := memInit.push {
            addr := BitVec.ofNat 64 (parseNat addrJson)
            val  := BitVec.ofNat 64 (parseNat valJson)
            size := 8
          }
  let mut memWatch : Array MemWatch := #[]
  if let .ok watchArr := tc.getObjValAs? (Array Json) "mem_watch" then
    for item in watchArr do
      if let .ok elems := item.getArr? then
        if elems.size >= 2 then
          memWatch := memWatch.push {
            addr := BitVec.ofNat 64 (parseNat elems[0]!)
            size := parseNat elems[1]!
          }
      else
        memWatch := memWatch.push {
          addr := BitVec.ofNat 64 (parseNat item)
          size := 8
        }
  let skipSail := (tc.getObjValAs? String "skip_sail").toOption
  return {
    name := name
    basePC := basePC
    startPC := startPC
    exitPC := exitPCVal
    maxSteps := maxSteps
    words := words
    regs := regs
    vregs := vregs
    sp := spVal
    nzcv := nzcvVal
    memInit := memInit
    memWatch := memWatch
    skipSail := skipSail
  }

/-! ## 4. Little-Endian Binary Helpers & Pure Floating-Point Batch Record (`FpBatchRecord`) -/

/-- Read a little-endian `UInt64` at byte offset `off` from `ba`. -/
def readU64LE (ba : ByteArray) (off : Nat) : UInt64 :=
  (ba.get! (off + 0)).toUInt64 |||
  ((ba.get! (off + 1)).toUInt64 <<< 8) |||
  ((ba.get! (off + 2)).toUInt64 <<< 16) |||
  ((ba.get! (off + 3)).toUInt64 <<< 24) |||
  ((ba.get! (off + 4)).toUInt64 <<< 32) |||
  ((ba.get! (off + 5)).toUInt64 <<< 40) |||
  ((ba.get! (off + 6)).toUInt64 <<< 48) |||
  ((ba.get! (off + 7)).toUInt64 <<< 56)

/-- Append a little-endian `UInt64` to `ba`. -/
def pushU64LE (ba : ByteArray) (v : UInt64) : ByteArray :=
  ba.push (v &&& 0xff).toUInt8
  |> (·.push ((v >>> 8) &&& 0xff).toUInt8)
  |> (·.push ((v >>> 16) &&& 0xff).toUInt8)
  |> (·.push ((v >>> 24) &&& 0xff).toUInt8)
  |> (·.push ((v >>> 32) &&& 0xff).toUInt8)
  |> (·.push ((v >>> 40) &&& 0xff).toUInt8)
  |> (·.push ((v >>> 48) &&& 0xff).toUInt8)
  |> (·.push ((v >>> 56) &&& 0xff).toUInt8)

/-- Compact 32-byte (4 × `UInt64`) pure IEEE-754 floating-point test record (`--batch-fp`). -/
structure FpBatchRecord where
  /-- Operation code (`0..20` for single-precision `f32`, `32..52` for double-precision `f64`:
      `+0`=FADD, `+1`=FSUB, `+2`=FMUL, `+3`=FDIV, `+4`=FSQRT, `+5`=FMADD, `+6`=FRINT,
      `+7`=FCVT, `+8..11`=FCVTZS/FCVTZU, `+12..15`=SCVTF/UCVTF, `+16..19`=FMIN/FMAX/FMINNM/FMAXNM,
      `+20`=FCMP). -/
  op     : Nat
  /-- Raw IEEE-754 rounding mode code (`0`=RNE, `1`=RTP, `2`=RTN, `3`=RTZ, `4`=RNA). -/
  rmCode : UInt64
  /-- Fractional bit count for fixed-point conversions (`SCVTF`/`UCVTF`/`FCVTZS`/`FCVTZU`). -/
  fbits  : Nat
  /-- First operand raw bit pattern. -/
  a      : UInt64
  /-- Second operand raw bit pattern. -/
  b      : UInt64
  /-- Third operand raw bit pattern (addend for `FMADD`). -/
  c      : UInt64
  deriving Repr, Inhabited

/-- Decode a 32-byte `FpBatchRecord` starting at byte offset `off`. -/
def FpBatchRecord.fromByteArray (bytes : ByteArray) (off : Nat) : FpBatchRecord :=
  let metaWord := readU64LE bytes (off + 0)
  let a        := readU64LE bytes (off + 8)
  let b        := readU64LE bytes (off + 16)
  let c        := readU64LE bytes (off + 24)
  { op     := (metaWord &&& 0xff).toNat
    rmCode := (metaWord >>> 8) &&& 0xff
    fbits  := ((metaWord >>> 16) &&& 0xff).toNat
    a      := a
    b      := b
    c      := c }

/-! ## 6. Self-Contained In-Lean Regression Test Case (`UnitTestCase` / `TestCase`) -/

/-- Single boolean regression check with a human-readable test name. `skipped? = some reason`
    marks a check that did not run (for example because a generated test binary is absent); the
    runner reports it as `SKIP` and neither passes nor fails it. -/
structure UnitTestCase where
  name     : String
  check    : Bool
  skipped? : Option String := none

abbrev TestCase := UnitTestCase

/-- A `UnitTestCase` that did not run because generated test file(s) are absent. -/
def UnitTestCase.skipMissingFiles (name : String) (files : List String) : UnitTestCase :=
  { name, check := false,
    skipped? := some s!"missing generated test file(s) {files}; run `scripts/build-test-elfs.sh`" }

/-- The paths in `files` that do not exist (empty when every file is present). -/
def missingTestFilesIO (files : List System.FilePath) : IO (List String) :=
  files.filterMapM fun f => do return if ← f.pathExists then none else some f.toString

/-- Run a list of `UnitTestCase` assertions, printing flushed progress and `[FAIL]` on failure and
    returning exit code `0`/`1`. -/
def runTestSuite (cases : List UnitTestCase) : IO UInt32 := do
  let stdout ← IO.getStdout
  let total := cases.length
  let mut idx := 0
  let mut passed := 0
  let mut failed := 0
  let mut skipped := 0
  for tc in cases do
    idx := idx + 1
    if let some reason := tc.skipped? then
      skipped := skipped + 1
      IO.println s!"[unit_tests] [{idx}/{total}] SKIP {tc.name}: {reason}"
      stdout.flush
    else if tc.check then
      passed := passed + 1
      if idx % 20 == 0 || idx == total then
        IO.println s!"[unit_tests] [{idx}/{total}] PASS {tc.name}"
        stdout.flush
    else
      failed := failed + 1
      IO.eprintln s!"[FAIL] [{idx}/{total}] {tc.name}"
  let skippedNote := if skipped == 0 then "" else s!", {skipped} skipped"
  IO.println s!"Unit test summary: {passed} passed, {failed} failed (total {passed + failed}){skippedNote}"
  stdout.flush
  return if failed == 0 then 0 else 1

/-- Bounded-concurrency `IO` work item carrying a human-readable `label`, an optional scheduling
    `priority` (higher values are dispatched first; ties preserve original index order), and an
    `IO` thunk `run`. Output order is always the original input array order. -/
structure ParallelWorkItem (α : Type) where
  label    : String
  priority : Nat := 10
  run      : Unit → IO α

instance {α : Type} : Inhabited (ParallelWorkItem α) where
  default := { label := "", run := fun () => throw (IO.userError "uninhabited ParallelWorkItem") }

/-- Output of one parallel test batch: `UnitTestCase` assertions plus deterministic `stdout` and
    `stderr` diagnostic lines replayed in original submission order on the main thread. -/
structure ParallelTestBatch where
  cases  : List UnitTestCase := []
  stdout : Array String := #[]
  stderr : Array String := #[]
  deriving Inhabited

/-- Resolve the worker thread count for parallel `IO` test execution:
    `LEAN_UNIT_TESTS_JOBS` (if set to a positive integer), else `LEAN_NUM_THREADS` (clamped to
    `[1, 32]`), else `nproc` (clamped to `[1, 32]`, fallback `8`). -/
def parallelTestJobs : IO Nat := do
  let parsePos? (s? : Option String) : Option Nat :=
    match s? with
    | some raw =>
      match raw.trimAscii.toString.toNat? with
      | some n => if n > 0 then some n else none
      | none => none
    | none => none
  if let some n := parsePos? (← IO.getEnv "LEAN_UNIT_TESTS_JOBS") then
    return n
  if let some n := parsePos? (← IO.getEnv "LEAN_NUM_THREADS") then
    return Nat.min 32 n
  let nproc? ← try
    let out ← IO.Process.output { cmd := "nproc", args := #[] }
    if out.exitCode == 0 then pure (parsePos? (some out.stdout)) else pure none
  catch _ =>
    pure none
  return Nat.min 32 (nproc?.getD 8)

/-- Execute `items` across a bounded pool of dedicated worker threads using atomic work stealing
    ordered by descending `priority`, catching uncaught `IO.Error`s via `onError` and returning
    results in exact original array index order. -/
def runParallelWorkItemsIO {α : Type} [Inhabited α] (items : Array (ParallelWorkItem α))
    (onError : Nat → String → IO.Error → α) (maxJobs? : Option Nat := none) : IO (Array α) := do
  if items.isEmpty then
    return #[]
  let jobs ← match maxJobs? with
    | some j => pure (Nat.max 1 j)
    | none   => parallelTestJobs
  let workerCount := Nat.min jobs items.size
  if workerCount ≤ 1 then
    let mut out : Array α := Array.mkEmpty items.size
    for idx in [0:items.size] do
      let item := items[idx]!
      let v ← try item.run () catch e => pure (onError idx item.label e)
      out := out.push v
    return out
  let dispatchOrder : Array Nat :=
    ((Array.range items.size).qsort fun i j =>
      let pi := items[i]!.priority
      let pj := items[j]!.priority
      if pi != pj then pi > pj else i < j)
  let mut slots : Array (IO.Ref α) := Array.mkEmpty items.size
  for _ in [0:items.size] do
    slots := slots.push (← IO.mkRef default)
  let cursor ← IO.mkRef (0 : Nat)
  let mut workers : Array (Task (Except IO.Error Unit)) := Array.mkEmpty workerCount
  for _ in [0:workerCount] do
    let w ← IO.asTask (prio := .dedicated) do
      while true do
        let pos ← cursor.modifyGet fun c => (c, c + 1)
        if h : pos < dispatchOrder.size then
          let idx := dispatchOrder[pos]
          let item := items[idx]!
          let v ← try item.run () catch e => pure (onError idx item.label e)
          if let some slot := slots[idx]? then
            slot.set v
        else
          break
    workers := workers.push w
  for w in workers do
    match w.get with
    | .ok () => pure ()
    | .error e => throw e
  let mut out : Array α := Array.mkEmpty items.size
  for s in slots do
    out := out.push (← s.get)
  return out

/-- Execute `items` concurrently via `runParallelWorkItemsIO`, turning uncaught `IO.Error`s into
    failing `UnitTestCase` entries, replaying `stdout`/`stderr` diagnostics in deterministic
    submission order, and returning the concatenated `List UnitTestCase`. -/
def runParallelTestBatchesIO (items : Array (ParallelWorkItem ParallelTestBatch))
    (maxJobs? : Option Nat := none) : IO (List UnitTestCase) := do
  let batches ← runParallelWorkItemsIO items
    (fun _ label err =>
      { cases  := [{ name := s!"{label} (IO error)", check := false }]
        stderr := #[s!"[FAIL] {label}: {err}"] })
    maxJobs?
  let stdout ← IO.getStdout
  let mut allCases : List UnitTestCase := []
  for b in batches do
    for line in b.stdout do
      IO.println line
    if !b.stdout.isEmpty then
      stdout.flush
    for line in b.stderr do
      IO.eprintln line
    allCases := allCases ++ b.cases
  return allCases

/-- Execute a `Program` from `entry` with initial state `s0` for up to `fuel` steps until `RET` to
    `0xdead0000`. The code is loaded read-execute and every byte that `s0` leaves unmapped is
    mapped read-write. -/
def runProgram (prog : Program) (entry : BitVec 64) (s0 : State) (fuel : Nat := 200) : State :=
  let s1 := s0.setMem (mapRestRw (loadCode prog s0.mem))
  let sInit := { (s1.writeReg64 .lr 0xdead0000#64) with pc := entry, status := .Running }
  execUntilPC fuel prog 0xdead0000#64 sInit

/-- Execute a `Program` from `entry` with initial state `s0` without mapping unmapped memory
    (used for tests of `mmap` / `brk` that exercise `canMap` and `mapZero`). -/
def runProgramRaw (prog : Program) (entry : BitVec 64) (s0 : State) (fuel : Nat := 200) : State :=
  let s1 := s0.setMem (loadCode prog s0.mem)
  let sInit := { (s1.writeReg64 .lr 0xdead0000#64) with pc := entry, status := .Running }
  execUntilPC fuel prog 0xdead0000#64 sInit

/-- Execute a list of 32-bit machine code words loaded at `0x1000` from initial state `s0` for up to
    `fuel` steps until `RET` to `0xdead0000`. -/
def runWords (words : List (BitVec 32)) (s0 : State) (fuel : Nat := 200) : State :=
  runProgram (Program.ofWords 0x1000#64 words) 0x1000#64 s0 fuel

/-- Execute a list of 32-bit machine code words loaded at `0x1000` from initial state `s0` without
    mapping unmapped memory. -/
def runWordsRaw (words : List (BitVec 32)) (s0 : State) (fuel : Nat := 200) : State :=
  runProgramRaw (Program.ofWords 0x1000#64 words) 0x1000#64 s0 fuel

/-- Test oracle: `mmap` query `n` returns `base + n * 0x10000`, and `getrandom` query `n`
    fills byte `i` with `16 * n + i`. -/
def testOracle (base : BitVec 64) : Oracle where
  mmap n := base + BitVec.ofNat 64 (n * 0x10000)
  getrandom n i := BitVec.ofNat 8 (16 * n + i)

/-- Blank `State` with all memory mapped `Perm.rw`. -/
def rwState : State := ({} : State).setMem (mapRestRw ({} : State).mem)

/-- Seed 64-bit little-endian memory words `(address, value)` into `s`. -/
def withMem64 (s : State) (entries : List (BitVec 64 × BitVec 64)) : State :=
  entries.foldl (fun st (addr, val) => st.setMem (st.mem.write64 addr val)) s

/-- Resolve a repository-root-relative path whether the test binary was launched from the
    repository root or from a subpackage directory (`Arm64/Testing/`). -/
def resolveRepoFilePath (rel : System.FilePath) : IO System.FilePath := do
  if rel.isAbsolute then
    return rel
  if ← rel.pathExists then
    return rel
  let fromSubpkg := System.FilePath.mk "../.." / rel
  if ← fromSubpkg.pathExists then
    return fromSubpkg
  return rel

end Testing.Harness
