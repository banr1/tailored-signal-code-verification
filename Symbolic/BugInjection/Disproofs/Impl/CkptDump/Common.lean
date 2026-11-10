/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.FastStepInit
public import Symbolic.BugInjection.Proofs.CliExec.FastStep

/-!
# Checkpoint Serializer and JSON Formatter

Computable serializers inverse to the elaboration-time macros in `CkptMacro`, shared by
`CkptDump.Base` and `CkptDump.Run`. Memory-line and tree encoders check structural `BinTree`
equality against their reconstructions (`btSet 6`, `applyLineUpdates`, `applyTreePatch`) at dump
time so emitted `rfl_kernel` chunk obligations hold syntactically.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.CkptDump.Common

open Arm64
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree Cell FastRegs Line64 btGet btSet)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksAux (FastFs)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows (FastState)
open Symbolic.BugInjection.Proofs.CliExec.FastStepInit (PrebuiltElf)
open Symbolic.BugInjection.Proofs.CliExec.FastStep (TreePatch applyTreePatch applyLineUpdates)

def hexDigitLower (n : Nat) : Char :=
  let d := n % 16
  if d < 10 then Char.ofNat ('0'.toNat + d)
  else Char.ofNat ('a'.toNat + (d - 10))

def hexDigitUpper (n : Nat) : Char :=
  let d := n % 16
  if d < 10 then Char.ofNat ('0'.toNat + d)
  else Char.ofNat ('A'.toNat + (d - 10))

partial def natToHexLowerAux (n : Nat) (acc : List Char) : List Char :=
  let d := hexDigitLower (n % 16)
  let q := n / 16
  if q == 0 then d :: acc else natToHexLowerAux q (d :: acc)

def fmtBv64Lit (v : BitVec 64) : String :=
  "0x" ++ String.ofList (natToHexLowerAux v.toNat []) ++ "#64"

def fmtBv32Lit (v : BitVec 32) : String :=
  "0x" ++ String.ofList (natToHexLowerAux v.toNat []) ++ "#32"

def pushAscii (buf : ByteArray) (s : String) : ByteArray :=
  buf ++ s.toByteArray

def pushByteHexLower (buf : ByteArray) (b : UInt8) : ByteArray :=
  let n := b.toNat
  let hi := (hexDigitLower (n / 16)).toNat.toUInt8
  let lo := (hexDigitLower (n % 16)).toNat.toUInt8
  (buf.push hi).push lo

def bytesToHexLower (bs : List (BitVec 8)) : String := Id.run do
  let mut buf := ByteArray.emptyWithCapacity (bs.length * 2)
  for b in bs do
    buf := pushByteHexLower buf b.toNat.toUInt8
  return String.fromUTF8! buf

def byteArrayToBvList (ba : ByteArray) : List (BitVec 8) := Id.run do
  let mut acc : List (BitVec 8) := []
  let n := ba.size
  for idx in [0:n] do
    let b := ba.get! (n - 1 - idx)
    acc := BitVec.ofNat 8 b.toNat :: acc
  return acc

/-- Splits a UTF-8 `ByteArray` into chunks of at least `chunkBytes` bytes at UTF-8 codepoint boundaries. -/
def splitUtf8Chunks (ba : ByteArray) (chunkBytes : Nat := 200) : List String := Id.run do
  if ba.size == 0 then
    return [""]
  let mut out : Array String := #[]
  let mut start : Nat := 0
  while start < ba.size do
    let mut stop := Nat.min (start + chunkBytes) ba.size
    while stop < ba.size && (ba.get! stop &&& 0xc0) == 0x80 do
      stop := stop + 1
    out := out.push (String.fromUTF8! (ba.extract start stop))
    start := stop
  return out.toList

def jsonEscape (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    if c == '"' then out := out ++ "\\\""
    else if c == '\\' then out := out ++ "\\\\"
    else if c == '\n' then out := out ++ "\\n"
    else if c == '\r' then out := out ++ "\\r"
    else if c == '\t' then out := out ++ "\\t"
    else if c.toNat < 0x20 then
      let n := c.toNat
      out := out ++ "\\u00" ++ String.ofList [hexDigitUpper (n / 16), hexDigitUpper (n % 16)]
    else out := out.push c
  return out ++ "\""

def jsonStrArray (xs : List String) : String :=
  "[" ++ String.intercalate ", " (xs.map jsonEscape) ++ "]"

def leanQuoteStr (s : String) : String :=
  jsonEscape s

def fmtLeanStrList (elemIndent closeIndent : String) (xs : List String) : String :=
  match xs with
  | [] => "[]"
  | _ =>
    let items := String.intercalate ",\n" (xs.map fun x => elemIndent ++ leanQuoteStr x)
    "[\n" ++ items ++ "\n" ++ closeIndent ++ "]"

def encodeOptPermByte (cp : Option Perm) : UInt8 :=
  match cp with
  | none => '-'.toNat.toUInt8
  | some p =>
    let code :=
      (if p.r then 1 else 0) +
      (if p.w then 2 else 0) +
      (if p.x then 4 else 0) +
      (if p.lazyFree then 8 else 0) +
      (if p.anon then 16 else 0)
    ('A'.toNat + code).toUInt8

partial def encodeLine64Rec (buf : ByteArray) : Line64 → ByteArray
  | .empty => buf.push 'E'.toNat.toUInt8
  | .branch l r =>
    let b1 := buf.push 'B'.toNat.toUInt8
    let b2 := encodeLine64Rec b1 l
    encodeLine64Rec b2 r
  | .twig j (cp, bv) =>
    let b1 := pushAscii (buf.push 'T'.toNat.toUInt8) (toString j ++ ";")
    let b2 := b1.push (encodeOptPermByte cp)
    pushByteHexLower b2 bv.toNat.toUInt8

/-- Encodes `ln` with compact `'Z'` (all-zero) or `'F'` (dense 64-byte) tags when all 64 cells
share one `Option Perm` and `btSet 6` reconstruction equals `ln`, falling back to constructor
preorder (`'E'`, `'B'`, `'T'`). -/
def encodeLine64ToBuf (buf : ByteArray) (ln : Line64) : ByteArray := Id.run do
  match btGet 6 ln 0 with
  | some (cp, _) =>
    let mut uniform := true
    let mut allZero := true
    let mut built : Line64 := .empty
    for j in [0:64] do
      match btGet 6 ln j with
      | some (cpj, bvj) =>
        if cpj != cp then
          uniform := false
        if bvj != 0#8 then
          allZero := false
        built := btSet 6 built j (cpj, bvj)
      | none =>
        uniform := false
    if uniform && built == ln then
      let pByte := encodeOptPermByte cp
      if allZero then
        return (buf.push 'Z'.toNat.toUInt8).push pByte
      else
        let mut out := (buf.push 'F'.toNat.toUInt8).push pByte
        for j in [0:64] do
          match btGet 6 ln j with
          | some (_, bvj) => out := pushByteHexLower out bvj.toNat.toUInt8
          | none => pure ()
        return out
  | none => pure ()
  return encodeLine64Rec buf ln

partial def encodeLineTreeToBuf (buf : ByteArray) : BinTree Line64 → ByteArray
  | .empty => buf.push 'E'.toNat.toUInt8
  | .branch l r =>
    let b1 := buf.push 'B'.toNat.toUInt8
    let b2 := encodeLineTreeToBuf b1 l
    encodeLineTreeToBuf b2 r
  | .twig k ln =>
    let b1 := pushAscii (buf.push 'L'.toNat.toUInt8) (toString k ++ ";")
    encodeLine64ToBuf b1 ln

def encodeLineTree (t : BinTree Line64) (chunkBytes : Nat := 200) : List String :=
  splitUtf8Chunks (encodeLineTreeToBuf ByteArray.empty t) chunkBytes

partial def encodeHooksToBuf (buf : ByteArray) : BinTree String → ByteArray
  | .empty => buf.push 'E'.toNat.toUInt8
  | .branch l r =>
    let b1 := buf.push 'B'.toNat.toUInt8
    let b2 := encodeHooksToBuf b1 l
    encodeHooksToBuf b2 r
  | .twig k nm =>
    let nmBytes := nm.toByteArray
    let hdr := pushAscii (buf.push 'H'.toNat.toUInt8)
      (toString k ++ ";" ++ toString nmBytes.size ++ ";")
    hdr ++ nmBytes

def encodeHooks (t : BinTree String) (chunkBytes : Nat := 200) : List String :=
  splitUtf8Chunks (encodeHooksToBuf ByteArray.empty t) chunkBytes

partial def encodeRegTreeToBuf {w : Nat} (buf : ByteArray) : BinTree (BitVec w) → ByteArray
  | .empty => buf.push 'E'.toNat.toUInt8
  | .branch l r =>
    let b1 := buf.push 'B'.toNat.toUInt8
    let b2 := encodeRegTreeToBuf b1 l
    encodeRegTreeToBuf b2 r
  | .twig k val =>
    pushAscii (buf.push 'T'.toNat.toUInt8) (toString k ++ ";" ++ toString val.toNat ++ ";")

def encodeRegs (r : FastRegs) (chunkBytes : Nat := 200) : List String :=
  let b1 := encodeRegTreeToBuf ByteArray.empty r.gprs
  let b2 := encodeRegTreeToBuf b1 r.vregs
  splitUtf8Chunks b2 chunkBytes

def encodeTraceToBuf (evs : List TraceEvent) : Except String ByteArray := do
  let mut buf := ByteArray.empty
  for ev in evs do
    match ev with
    | .writeByte .stdout b =>
      buf := pushByteHexLower (buf.push 'O'.toNat.toUInt8) b.toNat.toUInt8
    | .writeByte .stderr b =>
      buf := pushByteHexLower (buf.push 'E'.toNat.toUInt8) b.toNat.toUInt8
    | .writeByte (.fd fd) b =>
      let b1 := pushAscii (buf.push 'F'.toNat.toUInt8) (toString fd.toNat ++ ";")
      buf := pushByteHexLower b1 b.toNat.toUInt8
    | .fileChanged path =>
      let pb := path.toByteArray
      let b1 := pushAscii (buf.push 'C'.toNat.toUInt8) (toString pb.size ++ ";")
      buf := b1 ++ pb
    | .userDefined tag _ =>
      throw s!"encodeTraceToBuf: unsupported TraceEvent.userDefined ({tag})"
  return buf

def encodeTrace (evs : List TraceEvent) (chunkBytes : Nat := 200) : Except String (List String) := do
  let buf ← encodeTraceToBuf evs
  return splitUtf8Chunks buf chunkBytes

def btSplitChildren {α : Type} : BinTree α → BinTree α × BinTree α
  | .empty => (.empty, .empty)
  | .twig kj u =>
    if kj % 2 == 0 then (.twig (kj / 2) u, .empty)
    else (.empty, .twig (kj / 2) u)
  | .branch l r => (l, r)

/-- Collects `(hi, ln)` twig updates where `cur` differs from `base`, skipping equal subtrees. -/
partial def collectDirtyLineUpdates (base cur : BinTree Line64)
    (pref : Nat := 0) (bitMult : Nat := 1) : Array (Nat × Line64) :=
  if base == cur then #[]
  else
    match cur with
    | .empty => #[]
    | .twig kj ln => #[(pref + kj * bitMult, ln)]
    | .branch cl cr =>
      let (bl, br) := btSplitChildren base
      collectDirtyLineUpdates bl cl pref (bitMult * 2) ++
        collectDirtyLineUpdates br cr (pref + bitMult) (bitMult * 2)

def encodeLineUpdatesToBuf (upds : List (Nat × Line64)) : ByteArray := Id.run do
  let mut buf := ByteArray.empty
  for (hi, ln) in upds do
    buf := pushAscii buf (toString hi ++ ";")
    buf := encodeLine64ToBuf buf ln
  return buf

partial def buildTreePatch (base cur : BinTree Line64) : TreePatch Line64 :=
  if base == cur then .keep
  else
    match base, cur with
    | .branch bl br, .branch cl cr =>
      .branch (buildTreePatch bl cl) (buildTreePatch br cr)
    | _, _ => .set cur

partial def encodeTreePatchToBuf (buf : ByteArray) : TreePatch Line64 → ByteArray
  | .keep => buf.push 'K'.toNat.toUInt8
  | .branch l r =>
    let b1 := buf.push 'P'.toNat.toUInt8
    let b2 := encodeTreePatchToBuf b1 l
    encodeTreePatchToBuf b2 r
  | .set t =>
    encodeLineTreeToBuf (buf.push 'S'.toNat.toUInt8) t

/-- Formats `cur` relative to `base` (`pb.baseLines`) as `(dirtyCount, leanExpr)`, using
`applyLineUpdates` when structurally equal and `applyTreePatch` as fallback. -/
def fmtMemLinesExpr (base cur : BinTree Line64) (chunkBytes : Nat := 200) :
    Except String (Nat × String) := do
  if base == cur then
    return (0, "pb.baseLines")
  let upds := (collectDirtyLineUpdates base cur).toList
  if applyLineUpdates base upds == cur then
    let chunks := splitUtf8Chunks (encodeLineUpdatesToBuf upds) chunkBytes
    let listStr := fmtLeanStrList "        " "      " chunks
    return (upds.length, s!"applyLineUpdates pb.baseLines (ckpt_lines {listStr})")
  let patch := buildTreePatch base cur
  if applyTreePatch base patch == cur then
    let chunks := splitUtf8Chunks (encodeTreePatchToBuf ByteArray.empty patch) chunkBytes
    let listStr := fmtLeanStrList "        " "      " chunks
    return (upds.length, s!"applyTreePatch pb.baseLines (ckpt_patch {listStr})")
  throw "fmtMemLinesExpr: internal error — neither applyLineUpdates nor applyTreePatch matched cur"

def fmtBool (b : Bool) : String :=
  if b then "true" else "false"

def fmtAccMode : FdAccessMode → String
  | .rdonly => ".rdonly"
  | .wronly => ".wronly"
  | .rdwr => ".rdwr"

def fmtFdKind : FdKind → String
  | .localFile => ".localFile"
  | .localDir => ".localDir"
  | .stdio => ".stdio"
  | .custom n => s!"(.custom {n})"

def fmtOptFdEntry : Option FdEntry → String
  | none => "none"
  | some e =>
    s!"some \{ path := {leanQuoteStr e.path}, accMode := {fmtAccMode e.accMode}, " ++
      s!"append := {fmtBool e.append}, cloexec := {fmtBool e.cloexec}, " ++
      s!"offset := {e.offset}, kind := {fmtFdKind e.kind} }"

def fmtBytesFastHex (elemIndent closeIndent : String) (bs : List (BitVec 8)) : String :=
  if bs.isEmpty then "[]"
  else
    let hex := bytesToHexLower bs
    let chunks := splitUtf8Chunks hex.toByteArray 180
    s!"fast_hex_chunks {fmtLeanStrList elemIndent closeIndent chunks}"

def fmtOptFsEntry : Option FsEntry → String
  | none => "none"
  | some .dir => "some .dir"
  | some (.file bs) =>
    if bs.isEmpty then "some (.file [])"
    else s!"some (.file ({fmtBytesFastHex "            " "          " bs}))"

def fmtFsPath (p : FsPath) : String :=
  "[" ++ String.intercalate ", " (p.map leanQuoteStr) ++ "]"

def fmtFastFsExpr (fs0 fs : FastFs) : String :=
  if fs.entries == fs0.entries && fs.stdin == fs0.stdin && fs.fds == fs0.fds then
    "fs0.fs"
  else
    let entriesStr :=
      if fs.entries == fs0.entries then "fs0.fs.entries"
      else if fs.entries.isEmpty then "[]"
      else
        let rows := fs.entries.map fun (p, oe) =>
          s!"        ({fmtFsPath p}, {fmtOptFsEntry oe})"
        "[\n" ++ String.intercalate ",\n" rows ++ "\n      ]"
    let stdinStr :=
      if fs.stdin == fs0.stdin then "fs0.fs.stdin"
      else fmtBytesFastHex "        " "      " fs.stdin
    let fdsStr :=
      if fs.fds == fs0.fds then "fs0.fs.fds"
      else if fs.fds.isEmpty then "[]"
      else
        let rows := fs.fds.map fun (fd, oe) =>
          s!"        ({fmtBv64Lit fd}, {fmtOptFdEntry oe})"
        "[\n" ++ String.intercalate ",\n" rows ++ "\n      ]"
    String.intercalate "\n" [
      "{",
      s!"      entries := {entriesStr}",
      s!"      stdin := {stdinStr}",
      s!"      fds := {fdsStr}",
      "    }"
    ]

def fmtHeapIvs (ivs : List (Nat × Nat)) : String := Id.run do
  if ivs.isEmpty then
    return "[]"
  let mut lines : Array String := #[]
  let mut cur : Array String := #[]
  for (a, b) in ivs do
    cur := cur.push s!"({a}, {b})"
    if cur.size >= 5 then
      lines := lines.push ("      " ++ String.intercalate ", " cur.toList)
      cur := #[]
  if !cur.isEmpty then
    lines := lines.push ("      " ++ String.intercalate ", " cur.toList)
  return "[\n" ++ String.intercalate ",\n" lines.toList ++ "\n    ]"

def fmtExecStatus : ExecStatus → String
  | .Running => ".Running"
  | .Halted => ".Halted"
  | .Exited c => s!"(.Exited {fmtBv64Lit c})"
  | .Signaled sig => s!"(.Signaled 0x{String.ofList (natToHexLowerAux sig.toNat [])}#7)"
  | .Panicked => ".Panicked"
  | .OutOfMemory => ".OutOfMemory"
  | .Exception msg => s!"(.Exception {leanQuoteStr msg})"

/-- Formats a `MkCkpt` body (`fun pb fs0 => { ... }`) for `fs` relative to `(pb, fs0)`, returning
`(dirtyLineCount, mkCkptBody)` with `layout-bypass` annotations on concrete address literals. -/
def fmtMkCkptBody (pb : PrebuiltElf) (fs0 fs : FastState) (chunkBytes : Nat := 200) :
    Except String (Nat × String) := do
  let regsChunks := encodeRegs fs.regs chunkBytes
  let regsStr := fmtLeanStrList "      " "    " regsChunks
  let (dirtyCount, linesExpr) ← fmtMemLinesExpr pb.baseLines fs.mem.lines chunkBytes
  let sbStr := if fs.mem.stackBase == fs0.mem.stackBase then "fs0.mem.stackBase"
    else toString fs.mem.stackBase
  let stStr := if fs.mem.stackTop == fs0.mem.stackTop then "fs0.mem.stackTop"
    else toString fs.mem.stackTop
  let tpidrLine :=
    if fs.tpidrEl0 == fs0.tpidrEl0 then
      "    tpidrEl0 := fs0.tpidrEl0"
    else
      s!"    tpidrEl0 := {fmtBv64Lit fs.tpidrEl0} -- layout-bypass: concrete-mutant-trace-checkpoint"
  let brkStartLine :=
    if fs.brkStart == fs0.brkStart then
      "    brkStart := fs0.brkStart"
    else
      s!"    brkStart := {fmtBv64Lit fs.brkStart} -- layout-bypass: concrete-mutant-trace-checkpoint"
  let physLine :=
    if fs.physMemAvail == fs0.physMemAvail then "fs0.physMemAvail"
    else toString fs.physMemAvail
  let exclStr :=
    if fs.exclFails == fs0.exclFails then "fs0.exclFails"
    else "[" ++ String.intercalate ", " (fs.exclFails.map fmtBool) ++ "]"
  let traceStr ←
    if fs.trace.isEmpty then pure "[]"
    else do
      let tc ← encodeTrace fs.trace chunkBytes
      pure s!"ckpt_trace {fmtLeanStrList "      " "    " tc}"
  let sigAltStr :=
    if fs.sigAltStack == fs0.sigAltStack then "fs0.sigAltStack"
    else
      s!"\{ sp := {fmtBv64Lit fs.sigAltStack.sp}, " ++
        s!"ssFlags := {fmtBv32Lit fs.sigAltStack.ssFlags}, " ++
        s!"size := {fmtBv64Lit fs.sigAltStack.size} } -- layout-bypass: concrete-mutant-trace-checkpoint"
  let body := String.intercalate "\n" [
    "fun pb fs0 =>",
    s!"  \{ regs := ckpt_regs {regsStr}",
    s!"    sp := {fmtBv64Lit fs.sp} -- layout-bypass: concrete-mutant-trace-checkpoint",
    s!"    pc := {fmtBv64Lit fs.pc} -- layout-bypass: concrete-mutant-trace-checkpoint",
    s!"    pstate := \{ n := {fmtBool fs.pstate.n}, z := {fmtBool fs.pstate.z}, c := {fmtBool fs.pstate.c}, v := {fmtBool fs.pstate.v} }",
    "    mem :=",
    s!"      \{ lines := {linesExpr}",
    s!"        stackBase := {sbStr}",
    s!"        stackTop := {stStr} }",
    s!"    heapIvs := {fmtHeapIvs fs.heapIvs}",
    tpidrLine,
    s!"    fpsr := {fmtBv32Lit fs.fpsr}",
    brkStartLine,
    s!"    brk := {fmtBv64Lit fs.brk} -- layout-bypass: concrete-mutant-trace-checkpoint",
    s!"    physMemAvail := {physLine}",
    s!"    fs := {fmtFastFsExpr fs0.fs fs.fs}",
    "    oracle := fs0.oracle",
    s!"    oracleIdx := {fs.oracleIdx}",
    s!"    exclFails := {exclStr}",
    s!"    trace := {traceStr}",
    s!"    status := {fmtExecStatus fs.status}",
    s!"    sigAltStack := {sigAltStr} }"
  ]
  return (dirtyCount, body)

end Symbolic.BugInjection.Disproofs.Impl.CkptDump.Common
