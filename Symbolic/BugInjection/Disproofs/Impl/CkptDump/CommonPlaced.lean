/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib.Process.FastParse
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemAux
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemLine
public import Symbolic.BugInjection.Proofs.CliExec.RadixMemPlaced
public import Symbolic.BugInjection.Proofs.CliExec.TreePatch
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksRows
public import Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced
public import Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore
public import Symbolic.BugInjection.Proofs.CliExec.ElfFullSpecPlacedCore
public import Symbolic.BugInjection.Proofs.CliExec.PrebuildPlaced

/-!
# Placed Checkpoint Serializer, ELF Symbol Reader, and Adaptive Stepper

Computable serializers inverse to `CkptMacro`, raw ELF64 `.symtab` lookup (including `STB_LOCAL`
entries below `sh_info` for SPQR's `STORAGE.0` and `TOKEN` statics), a minimal `link.json` parser,
and adaptive binary-doubling chunk selection, shared by `CkptDump.BasePlaced` and
`CkptDump.RunPlaced`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Disproofs.Impl.CkptDump.CommonPlaced

open Arm64 Arm64.Process
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed (compHooks0)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (BinTree Cell FastRegs Line64 btGet btSet)
open Symbolic.BugInjection.Proofs.CliExec.TreePatch (TreePatch applyTreePatch applyLineUpdates)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksAux (FastFs)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksRows (FastState)
open Symbolic.BugInjection.Proofs.CliExec.FastHooksPlaced (MallocngCallAddrs)
open Symbolic.BugInjection.Proofs.CliExec.PlacedExecCore (PrebuiltElfPlaced StepEntryPlaced
  fastEvalInstPlaced fastRunPow2CachedPlacedCoreW fastStepPlaced fastStepPlacedSub)
open Symbolic.BugInjection.Proofs.CliExec.PrebuildPlaced (prebuildElfPlaced0)

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

def baReadU16LE (ba : ByteArray) (off : Nat) : Nat :=
  (ba.get! off).toNat + ((ba.get! (off + 1)).toNat <<< 8)

def baReadU32LE (ba : ByteArray) (off : Nat) : Nat :=
  baReadU16LE ba off + (baReadU16LE ba (off + 2) <<< 16)

def baReadU64LE (ba : ByteArray) (off : Nat) : Nat :=
  baReadU32LE ba off + (baReadU32LE ba (off + 4) <<< 32)

def baReadCString (ba : ByteArray) (start limit : Nat) : String := Id.run do
  let mut endPos := start
  while endPos < limit && ba.get! endPos != 0 do
    endPos := endPos + 1
  return String.fromUTF8! (ba.extract start endPos)

/-- Extracts all defined (`st_shndx ≠ 0`) symbols from ELF64 `SHT_SYMTAB`, including `STB_LOCAL`
entries below `sh_info` (needed for internal Rust statics `STORAGE.0` and `TOKEN`). -/
def extractAllDefinedElfSyms (ba : ByteArray) : Except String (Array (String × BitVec 64)) := do
  if ba.size < 64 then
    throw "extractAllDefinedElfSyms: ELF shorter than 64 bytes"
  let eShoff := baReadU64LE ba 40
  let eShentsize := baReadU16LE ba 58
  let eShnum := baReadU16LE ba 60
  if eShentsize != 64 || eShoff + eShnum * 64 > ba.size then
    throw s!"extractAllDefinedElfSyms: invalid section header table (shentsize={eShentsize}, shnum={eShnum})"
  let mut symShIdx? : Option Nat := none
  for i in [0:eShnum] do
    let shOff := eShoff + i * 64
    if baReadU32LE ba (shOff + 4) == 2 then
      symShIdx? := some i
  let some symIdx := symShIdx?
    | throw "extractAllDefinedElfSyms: missing SHT_SYMTAB section"
  let symSh := eShoff + symIdx * 64
  let symOff := baReadU64LE ba (symSh + 24)
  let symSize := baReadU64LE ba (symSh + 32)
  let strIdx := baReadU32LE ba (symSh + 40)
  let symEnt := baReadU64LE ba (symSh + 56)
  if symEnt != 24 || symOff + symSize > ba.size || strIdx >= eShnum then
    throw "extractAllDefinedElfSyms: malformed SHT_SYMTAB bounds"
  let strSh := eShoff + strIdx * 64
  let strOff := baReadU64LE ba (strSh + 24)
  let strSize := baReadU64LE ba (strSh + 32)
  if strOff + strSize > ba.size then
    throw "extractAllDefinedElfSyms: malformed SHT_STRTAB bounds"
  let nSyms := symSize / 24
  let mut out : Array (String × BitVec 64) := #[]
  for idx in [1:nSyms] do
    let entOff := symOff + idx * 24
    let stName := baReadU32LE ba entOff
    let stShndx := baReadU16LE ba (entOff + 6)
    let stValue := baReadU64LE ba (entOff + 8)
    if stShndx != 0 && stName < strSize then
      let nm := baReadCString ba (strOff + stName) (strOff + strSize)
      if !nm.isEmpty then
        out := out.push (nm, BitVec.ofNat 64 stValue)
  return out

def lookupUniqueSym (allSyms : Array (String × BitVec 64)) (target : String) :
    Except String (BitVec 64) := do
  let mut hits : Array (BitVec 64) := #[]
  for (nm, va) in allSyms do
    if nm == target then
      hits := hits.push va
  if hits.size == 1 then
    return hits[0]!
  else if hits.isEmpty then
    throw s!"lookupUniqueSym: symbol '{target}' not found in ELF .symtab"
  else
    throw s!"lookupUniqueSym: symbol '{target}' is ambiguous ({hits.size} definitions in .symtab)"

/-- Minimal JSON value type for parsing `link.json` and chunk plans without `Lean.Data.Json` imports. -/
inductive MiniJson where
  | null
  | bool (b : Bool)
  | nat (n : Nat)
  | str (s : String)
  | arr (xs : Array MiniJson)
  | obj (kvs : Array (String × MiniJson))
  deriving Inhabited

def skipWs (ba : ByteArray) (i : Nat) : Nat := Id.run do
  let mut p := i
  while p < ba.size do
    let b := ba.get! p
    if b == 32 || b == 9 || b == 10 || b == 13 then p := p + 1
    else break
  return p

def parseJsonStr (ba : ByteArray) (pos : Nat) : Except String (String × Nat) := do
  if pos >= ba.size || ba.get! pos != '"'.toNat.toUInt8 then
    throw s!"parseJsonStr: expected '\"' at byte {pos}"
  let mut p := pos + 1
  let mut buf := ByteArray.empty
  while p < ba.size do
    let b := ba.get! p
    if b == '"'.toNat.toUInt8 then
      return (String.fromUTF8! buf, p + 1)
    else if b == '\\'.toNat.toUInt8 then
      if p + 1 >= ba.size then throw "parseJsonStr: truncated escape"
      let esc := ba.get! (p + 1)
      if esc == '"'.toNat.toUInt8 || esc == '\\'.toNat.toUInt8 || esc == '/'.toNat.toUInt8 then
        buf := buf.push esc; p := p + 2
      else if esc == 'n'.toNat.toUInt8 then buf := buf.push 10; p := p + 2
      else if esc == 'r'.toNat.toUInt8 then buf := buf.push 13; p := p + 2
      else if esc == 't'.toNat.toUInt8 then buf := buf.push 9; p := p + 2
      else throw s!"parseJsonStr: unsupported JSON escape at byte {p}"
    else
      buf := buf.push b
      p := p + 1
  throw "parseJsonStr: unterminated string"

partial def parseMiniJsonAt (ba : ByteArray) (pos0 : Nat) : Except String (MiniJson × Nat) := do
  let pos := skipWs ba pos0
  if pos >= ba.size then
    throw "parseMiniJson: unexpected EOF"
  let b := ba.get! pos
  if b == '"'.toNat.toUInt8 then
    let (s, p') ← parseJsonStr ba pos
    return (.str s, p')
  else if b == '{'.toNat.toUInt8 then
    let mut p := skipWs ba (pos + 1)
    let mut kvs : Array (String × MiniJson) := #[]
    if p < ba.size && ba.get! p == '}'.toNat.toUInt8 then
      return (.obj kvs, p + 1)
    while p < ba.size do
      let (k, p1) ← parseJsonStr ba (skipWs ba p)
      let pColon := skipWs ba p1
      if pColon >= ba.size || ba.get! pColon != ':'.toNat.toUInt8 then
        throw s!"parseMiniJson: expected ':' after key '{k}'"
      let (v, p2) ← parseMiniJsonAt ba (pColon + 1)
      kvs := kvs.push (k, v)
      let pNext := skipWs ba p2
      if pNext < ba.size && ba.get! pNext == ','.toNat.toUInt8 then
        p := pNext + 1
      else if pNext < ba.size && ba.get! pNext == '}'.toNat.toUInt8 then
        return (.obj kvs, pNext + 1)
      else
        throw s!"parseMiniJson: expected ',' or '}}' at byte {pNext}"
    throw "parseMiniJson: unterminated object"
  else if b == '['.toNat.toUInt8 then
    let mut p := skipWs ba (pos + 1)
    let mut xs : Array MiniJson := #[]
    if p < ba.size && ba.get! p == ']'.toNat.toUInt8 then
      return (.arr xs, p + 1)
    while p < ba.size do
      let (v, p1) ← parseMiniJsonAt ba p
      xs := xs.push v
      let pNext := skipWs ba p1
      if pNext < ba.size && ba.get! pNext == ','.toNat.toUInt8 then
        p := pNext + 1
      else if pNext < ba.size && ba.get! pNext == ']'.toNat.toUInt8 then
        return (.arr xs, pNext + 1)
      else
        throw s!"parseMiniJson: expected ',' or ']' at byte {pNext}"
    throw "parseMiniJson: unterminated array"
  else if '0'.toNat.toUInt8 ≤ b && b ≤ '9'.toNat.toUInt8 then
    let mut p := pos
    let mut acc : Nat := 0
    while p < ba.size do
      let d := ba.get! p
      if '0'.toNat.toUInt8 ≤ d && d ≤ '9'.toNat.toUInt8 then
        acc := acc * 10 + (d.toNat - '0'.toNat)
        p := p + 1
      else break
    return (.nat acc, p)
  else if pos + 4 ≤ ba.size && String.fromUTF8! (ba.extract pos (pos + 4)) == "true" then
    return (.bool true, pos + 4)
  else if pos + 5 ≤ ba.size && String.fromUTF8! (ba.extract pos (pos + 5)) == "false" then
    return (.bool false, pos + 5)
  else if pos + 4 ≤ ba.size && String.fromUTF8! (ba.extract pos (pos + 4)) == "null" then
    return (.null, pos + 4)
  else
    throw s!"parseMiniJson: unexpected token at byte {pos}"

def MiniJson.field? (j : MiniJson) (key : String) : Option MiniJson :=
  match j with
  | .obj kvs => (kvs.find? (fun (k, _) => k == key)).map Prod.snd
  | _ => none

/-- Parses `link.json` bytes into `(base, stubs)`, relocating each stub entry to `(externName, base + off)`. -/
def parseLinkJsonStubs (ba : ByteArray) : Except String (Nat × List (String × Nat)) := do
  let (root, _) ← parseMiniJsonAt ba 0
  let some (.nat base) := root.field? "base"
    | throw "parseLinkJsonStubs: missing integer 'base' field in link.json"
  let some (.arr stubsArr) := root.field? "stubs"
    | throw "parseLinkJsonStubs: missing array 'stubs' field in link.json"
  let mut out : Array (String × Nat) := #[]
  for item in stubsArr do
    let some (.str ext) := item.field? "extern"
      | throw "parseLinkJsonStubs: stub entry missing string 'extern'"
    let some (.nat off) := item.field? "off"
      | throw s!"parseLinkJsonStubs: stub '{ext}' missing integer 'off'"
    out := out.push (ext, base + off)
  return (base, out.toList)

def defaultLinkJsonPath (elfPath : String) : String :=
  let p := System.FilePath.mk elfPath
  match p.parent with
  | some dir => (dir / "link.json").toString
  | none => "link.json"

def extractOptFlag (flag : String) : List String → Option String × List String
  | [] => (none, [])
  | f :: v :: rest =>
    if f == flag then (some v, rest)
    else
      let (found, tail) := extractOptFlag flag (v :: rest)
      (found, f :: tail)
  | [x] => (none, [x])

/-- Mangled `STB_LOCAL` `.symtab` name of `LibsignalSpqrV1.tokenStorageName` (`STORAGE.0`). -/
def mangledTokStorageSym : String :=
  "_RNvNtNtNtNtCs8JFVmrO4JRH_4spqr8encoding2gf17check_accelerated15use_accelerated7STORAGE.0"

/-- Mangled `STB_LOCAL` `.symtab` name of `LibsignalSpqrV1.tokenName` (`TOKEN`). -/
def mangledTokSym : String :=
  "_RNvNtNtNtCs8JFVmrO4JRH_4spqr8encoding2gf17check_accelerated5TOKEN"

/-- Loads `<elf-path>` and `<link.json>`, resolves SPQR token and `mallocng` symbol addresses, and
constructs `PrebuiltElfPlaced`. -/
def prebuildPlacedFromPaths (elfPath linkJsonPath : String) :
    IO (ElfImage × BitVec 64 × BitVec 64 × PrebuiltElfPlaced) := do
  let elfBa ← IO.FS.readBinFile elfPath
  let linkBa ← IO.FS.readBinFile linkJsonPath
  let elf ← match fastParse (byteArrayToBvList elfBa) with
    | .ok e => pure e
    | .error msg => throw (IO.userError s!"fastParse failed on {elfPath}: {msg}")
  let allSyms ← match extractAllDefinedElfSyms elfBa with
    | .ok s => pure s
    | .error msg => throw (IO.userError s!"extractAllDefinedElfSyms failed on {elfPath}: {msg}")
  let liftSym (nm : String) : IO (BitVec 64) :=
    match lookupUniqueSym allSyms nm with
    | .ok va => pure va
    | .error msg => throw (IO.userError s!"{elfPath}: {msg}")
  let tokStorageAddr ← liftSym mangledTokStorageSym
  let tokOnceAddr ← liftSym mangledTokSym
  let callocAddr ← liftSym "calloc"
  let mallocAddr ← liftSym "malloc"
  let freeAddr ← liftSym "free"
  let addrs : MallocngCallAddrs := {
    callocAddr     := callocAddr
    callocSentinel := callocAddr + 1#64
    mallocAddr     := mallocAddr
    mallocSentinel := mallocAddr + 1#64
    freeAddr       := freeAddr
    freeSentinel   := freeAddr + 1#64
  }
  let (_, stubs) ← match parseLinkJsonStubs linkBa with
    | .ok res => pure res
    | .error msg => throw (IO.userError s!"parseLinkJsonStubs failed on {linkJsonPath}: {msg}")
  let pb ← match prebuildElfPlaced0 elf tokStorageAddr tokOnceAddr addrs stubs with
    | some p => pure p
    | none =>
      throw (IO.userError s!"prebuildElfPlaced0 failed on {elfPath} ({linkJsonPath})")
  return (elf, tokStorageAddr, tokOnceAddr, pb)

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

/-- Formats a placed `MkCkpt` body (`fun pb fs0 => { ... }`) for `fs` relative to `(pb, fs0)`,
returning `(dirtyLineCount, mkCkptBody)` with `layout-bypass` annotations on concrete address literals. -/
def fmtMkCkptBody (pb : PrebuiltElfPlaced) (fs0 fs : FastState) (chunkBytes : Nat := 200) :
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

/-- Bounds and cost budget for adaptive `2^exp`-step chunk sizing (`exp ∈ [minExp .. maxExp]`). -/
structure ChunkCfg where
  minExp    : Nat := 9
  maxExp    : Nat := 12
  budget    : Nat := 5000
  maxChunks : Nat := 2048

def containsSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Estimated kernel WHNF cost of one populated `ICachePlaced` entry:
- `.instr _`: cold `Arm64.decode` + depth-62 `btSet` (`2`);
- `libcrux_hmac`: `7` uncached `mallocng` subroutine loops + SHA-256 (`4600`, capping at `exp = 9`);
- `aes_256_cbc_*`: `1–2` uncached `mallocng` subroutine loops + AES (`3200`, capping at `exp ≤ 10`);
- pure crypto (`ml_kem`, `curve25519`, `x25519`, `compress512`/`256`): `300`;
- other extern hooks: `40`. -/
def entryKernelWeight : StepEntryPlaced → Nat
  | .instr _ => 2
  | .hook nm =>
    if containsSubstr nm "libcrux_hmac" || containsSubstr nm "4hmac" then 4600
    else if containsSubstr nm "aes_256_cbc" then 3200
    else if containsSubstr nm "ml_kem" || containsSubstr nm "curve25519" ||
        containsSubstr nm "x25519" || containsSubstr nm "compress512" ||
        containsSubstr nm "compress256" then 300
    else 40
  | .unmapped => 0

def scanICacheWeight : BinTree StepEntryPlaced → Nat
  | .empty => 0
  | .twig _ e => entryKernelWeight e
  | .branch l r => scanICacheWeight l + scanICacheWeight r

def chunkMemPenalty (chunkIdx : Nat) (startFs fs : FastState) : Nat :=
  if chunkIdx ≤ 1 || fs.brk != startFs.brk || fs.heapIvs.length != startFs.heapIvs.length then
    3200
  else
    0

def chunkCandidateCost (chunkIdx e : Nat) (startFs : FastState)
    (ic : BinTree StepEntryPlaced) (fs : FastState) : Nat :=
  chunkMemPenalty chunkIdx startFs fs + (2 ^ e) + scanICacheWeight ic

partial def countExactStepsInChunk (pb : PrebuiltElfPlaced) (startFs : FastState) (maxSteps : Nat) :
    Except String Nat := Id.run do
  let mut cur := startFs
  let mut k : Nat := 0
  while k < maxSteps && cur.status == .Running do
    match fastStepPlaced pb.prog cur with
    | some nxt =>
      cur := nxt
      k := k + 1
    | none =>
      let w := cur.mem.read32 cur.pc
      return .error
        s!"step_offset={k} pc={fmtBv64Lit cur.pc} sp={fmtBv64Lit cur.sp} x8={(cur.readReg64 Reg.x8).toNat} word={fmtBv32Lit w} decoded={reprStr (Arm64.decode w)}"
  return .ok k

/-- Advances one chunk from `startFs` by binary doubling (`fastRunPow2CachedPlacedCoreW`), selecting
the largest `chosenExp ∈ [cfg.minExp .. cfg.maxExp]` within `cfg.budget` and returning
`(chosenExp, fsNext, haltedSteps?)`. -/
partial def chooseChunkPlaced (pb : PrebuiltElfPlaced) (cfg : ChunkCfg) (chunkIdx : Nat)
    (startFs : FastState) : Except String (Nat × FastState × Option Nat) := do
  if startFs.status != .Running then
    return (cfg.minExp, startFs, some 0)
  match fastRunPow2CachedPlacedCoreW compHooks0 fastEvalInstPlaced fastStepPlacedSub pb.prog
      cfg.minExp .empty startFs with
  | none =>
    match countExactStepsInChunk pb startFs (2 ^ cfg.minExp) with
    | .error diag => throw diag
    | .ok k => throw s!"fastRunPow2CachedPlacedCoreW=none at minExp={cfg.minExp} after {k} steps"
  | some (ic0, fs0) =>
    if fs0.status != .Running then
      let rem ← countExactStepsInChunk pb startFs (2 ^ cfg.minExp)
      return (cfg.minExp, fs0, some rem)
    let mut e := cfg.minExp
    let mut icW := scanICacheWeight ic0
    let mut icCur := ic0
    let mut fsCur := fs0
    let c0 := chunkMemPenalty chunkIdx startFs fsCur + (2 ^ e) + icW
    if e >= cfg.maxExp || c0 > cfg.budget then
      return (e, fsCur, none)
    while e < cfg.maxExp do
      let lbNext := chunkMemPenalty chunkIdx startFs fsCur + (2 ^ (e + 1)) + icW
      if cfg.minExp < cfg.maxExp && lbNext > cfg.budget then
        return (e, fsCur, none)
      match fastRunPow2CachedPlacedCoreW compHooks0 fastEvalInstPlaced fastStepPlacedSub pb.prog
          e icCur fsCur with
      | none =>
        match countExactStepsInChunk pb fsCur (2 ^ e) with
        | .error diag => throw s!"sub_base={2 ^ e} {diag}"
        | .ok k => throw s!"fastRunPow2CachedPlacedCoreW=none at exp={e + 1} after {(2 ^ e) + k} steps"
      | some (icNext, fsNext) =>
        let icWNext := scanICacheWeight icNext
        let cNext := chunkMemPenalty chunkIdx startFs fsNext + (2 ^ (e + 1)) + icWNext
        if fsNext.status != .Running then
          if cfg.minExp == cfg.maxExp || cNext ≤ cfg.budget then
            let remTail ← countExactStepsInChunk pb fsCur (2 ^ e)
            return (e + 1, fsNext, some ((2 ^ e) + remTail))
          else
            return (e, fsCur, none)
        if cfg.minExp < cfg.maxExp && cNext > cfg.budget then
          return (e, fsCur, none)
        e := e + 1
        icW := icWNext
        icCur := icNext
        fsCur := fsNext
    return (e, fsCur, none)

def fmtExpHist (exps : Array Nat) (minExp maxExp : Nat) : String := Id.run do
  let mut parts : Array String := #[]
  for e in [minExp : maxExp + 1] do
    let cnt := exps.foldl (fun acc x => if x == e then acc + 1 else acc) 0
    if cnt > 0 then
      parts := parts.push s!"{e}:{cnt}"
  return "[" ++ String.intercalate ", " parts.toList ++ "]"

end Symbolic.BugInjection.Disproofs.Impl.CkptDump.CommonPlaced
