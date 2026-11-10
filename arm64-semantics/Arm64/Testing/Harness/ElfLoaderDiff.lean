/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean.Data.Json
public import Arm64.Trusted.Process
public import ProofLib.Process.ByteArray
public import Arm64.Testing.Harness.TestCase

/-!
# ELF64 Process Loader vs `qemu-aarch64` Differential Comparison Harness (`Arm64.Testing.Harness.ElfLoaderDiff`)

- **Layer / Role**: Untrusted differential test harness (`Lib::Testing`, `Role::Test`).
- **Purpose & Key Exports**:
  Compares the initial process state produced by the trusted Lean ELF64 loader
  (`ElfImage.parse` via the untrusted `ByteArray` wrapper `ElfImage.parseByteArray`,
  `buildInitialStack`, `ElfImage.loadState` in `Arm64/Trusted/Process/Loader.lean`) against `qemu-aarch64` user-mode entry snapshots
  (`entry.snapshot.{json,bin}` at `pc == e_entry`, captured by `tools/proc-snapshot` with
  `ADDR_NO_RANDOMIZE` and `-seed 0`):
  1. **Every `PT_LOAD` segment and every 4 KiB page**: exact virtual start address, page count,
     `rwx` permissions, and byte-for-byte contents.
  2. **Registers at `e_entry`**: `pc == e_entry`, `sp` (16-byte aligned in top stack page),
     `x0`–`x30` (`0`), `tpidr_el0` (`0`), and `PState` / `CPSR` (checking Lean's `PState.zero`
     and QEMU TCG's documented `CPSR.Z = 1` / `0x40000000` reset value).
  3. **Whole initial stack frame (`[stackBase, stackTop)`)**: zero-filled memory below `sp`,
     `argc`, `argv[0..argc]` pointers and NUL-terminated strings, `argv[argc] == NULL`,
     `envp[0..envc]` pointers and NUL-terminated strings, `envp[envc] == NULL`, every `auxv`
     entry (`AT_PHDR`, `AT_PHENT`, `AT_PHNUM`, `AT_PAGESZ`, `AT_BASE`, `AT_FLAGS`, `AT_ENTRY`,
     `AT_UID`, `AT_EUID`, `AT_GID`, `AT_EGID`, `AT_PLATFORM`, `AT_HWCAP`, `AT_CLKTCK`,
     `AT_SECURE`, `AT_RANDOM`, `AT_HWCAP2`, `AT_EXECFN`, optional `AT_SYSINFO_EHDR`, `AT_NULL`),
     and complete byte accounting of the `[infoBase, stackTop)` string/random block.
  4. **`brk` and unmapped gaps**: `brk == brkStart == pageAlignUp(max(p_vaddr + p_memsz))`,
     unmapped null page (`0x0`), unmapped gap pages before/between/after `PT_LOAD` segments,
     unmapped `brkStart` at entry, unmapped guard page below `stackBase`, and unmapped page at
     `stackTop`.
  5. **Fail-closed rejection**: verifies that `ElfImage.parseByteArray` cleanly rejects PIE
     (`ET_DYN`), dynamic (`PT_INTERP` / `PT_DYNAMIC`), relocatable (`ET_REL`), W+X `PT_LOAD`,
     executable `PT_GNU_STACK`, and non-writable `.bss` (`p_filesz < p_memsz` without `PF_W`)
     binaries.
-/

@[expose] public section

namespace Testing.ElfLoaderDiff

open Lean (Json FromJson fromJson?)
open Arm64 Arm64.Process
open Testing.Harness (TestCase UnitTestCase runTestSuite hex64 resolveRepoFilePath missingTestFilesIO)

instance : Inhabited Snapshot.Region where
  default := { start := 0#64, perm := Perm.rw, bytes := [] }

/-! ## 1. JSON Schema for `proc-snapshot` Entry Snapshots & Differential Manifests -/

structure SnapRegion where
  start  : Nat
  size   : Nat
  perm   : String
  kind   : String
  binOff : Nat
  deriving FromJson, Repr, Inhabited

structure SnapRegs where
  x         : List Nat
  sp        : Nat
  pc        : Nat
  cpsr      : Nat
  tpidr_el0 : Option Nat
  deriving FromJson, Repr, Inhabited

structure SnapElfRef where
  path   : String
  sha256 : String
  entry  : Nat
  deriving FromJson, Repr, Inhabited

structure SnapBinRef where
  file   : String
  size   : Nat
  sha256 : String
  deriving FromJson, Repr, Inhabited

structure EntrySnapshotJson where
  schema   : String
  stop     : String
  argv     : List String
  envp     : List String
  elf      : SnapElfRef
  regions  : List SnapRegion
  brkStart : Nat
  regs     : SnapRegs
  bin      : SnapBinRef
  deriving FromJson, Repr, Inhabited

structure SparseChunk where
  offset : Nat
  hex    : String
  deriving FromJson, Repr, Inhabited

structure InitialFileSpec where
  path     : String
  utf8     : String
  deriving FromJson, Repr, Inhabited

structure PositiveDiffCase where
  id                        : String
  category                  : String
  description               : String
  elf_path                  : String
  snapshot                  : EntrySnapshotJson
  snapshot_bin_path         : Option String := none
  sparse_bin_chunks         : List SparseChunk := []
  include_vdso_in_extra_auxv : Bool := false
  stdin_utf8                : String := ""
  initial_files             : List InitialFileSpec := []
  deriving FromJson, Repr, Inhabited

structure RejectedDiffCase where
  id                    : String
  category              : String
  description           : String
  elf_path              : String
  expected_error_substr : String
  deriving FromJson, Repr, Inhabited

structure ElfLoaderDiffManifest where
  schema_version : Nat
  qemu_version   : String
  positive_cases : List PositiveDiffCase
  rejected_cases : List RejectedDiffCase
  deriving FromJson, Repr, Inhabited

/-! ## 2. Byte, Hex, and Snapshot Memory Helpers -/

def hexNibble? (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (UInt8.ofNat (c.toNat - '0'.toNat))
  else if 'a' ≤ c && c ≤ 'f' then some (UInt8.ofNat (c.toNat - 'a'.toNat + 10))
  else if 'A' ≤ c && c ≤ 'F' then some (UInt8.ofNat (c.toNat - 'A'.toNat + 10))
  else none

def decodeHexByteArray (s : String) : Except String ByteArray := do
  let chars := s.toList
  if chars.length % 2 != 0 then
    throw s!"odd-length hex string ({chars.length} chars)"
  let mut out := ByteArray.emptyWithCapacity (chars.length / 2)
  let rec loop : List Char → ByteArray → Except String ByteArray
    | [], acc => pure acc
    | c1 :: c2 :: rest, acc =>
      match hexNibble? c1, hexNibble? c2 with
      | some hi, some lo => loop rest (acc.push ((hi <<< 4) ||| lo))
      | _, _ => throw s!"invalid hex characters '{c1}{c2}'"
    | [_], _ => throw "odd-length hex string"
  loop chars out

/-- Reconstruct the full `entry.snapshot.bin` `ByteArray` from zero-initialized memory of length
    `totalSize` and a list of non-zero `SparseChunk`s. -/
def materializeSparseBin (totalSize : Nat) (chunks : List SparseChunk) :
    Except String ByteArray := do
  let mut arr := ByteArray.mk (Array.replicate totalSize 0)
  for ch in chunks do
    let bs ← decodeHexByteArray ch.hex
    if ch.offset + bs.size > totalSize then
      throw s!"sparse chunk at {ch.offset}+{bs.size} exceeds snapshot bin size {totalSize}"
    arr := ByteArray.copySlice bs 0 arr ch.offset bs.size false
  return arr

/-- Lowercase hexadecimal rendering of a `Nat` (no `0x` prefix) for diagnostics. -/
def hexNat (n : Nat) : String :=
  String.ofList (Nat.toDigits 16 n)

def permToSnapString (p : Perm) : String :=
  let r := if p.r then "r" else "-"
  let w := if p.w then "w" else "-"
  let x := if p.x then "x" else "-"
  r ++ w ++ x

def snapFindRegionFor (snap : EntrySnapshotJson) (addr : Nat) (len : Nat) :
    Option SnapRegion :=
  snap.regions.find? fun r => r.start ≤ addr && addr + len ≤ r.start + r.size

def snapReadBytes (snap : EntrySnapshotJson) (bin : ByteArray) (addr : Nat) (len : Nat) :
    Except String (List (BitVec 8)) := do
  let some r := snapFindRegionFor snap addr len
    | throw s!"address 0x{hexNat (addr)} (+{len}) not mapped in QEMU snapshot"
  let off := r.binOff + (addr - r.start)
  if off + len > bin.size then
    throw s!"snapshot bin out of bounds at offset {off}+{len}"
  return bytesOfByteArray (bin.extract off (off + len))

def snapReadU64LE (snap : EntrySnapshotJson) (bin : ByteArray) (addr : Nat) :
    Except String Nat := do
  let some r := snapFindRegionFor snap addr 8
    | throw s!"u64 address 0x{hexNat (addr)} not mapped in QEMU snapshot"
  let off := r.binOff + (addr - r.start)
  if off + 8 > bin.size then
    throw s!"snapshot bin out of bounds reading u64 at offset {off}"
  return listReadU64LE (bytesOfByteArray (bin.extract off (off + 8))) 0

def snapReadCStr (snap : EntrySnapshotJson) (bin : ByteArray) (addr : Nat) (maxLen : Nat := 4096) :
    Except String (List (BitVec 8)) := do
  let some r := snapFindRegionFor snap addr 1
    | throw s!"C-string address 0x{hexNat (addr)} not mapped in QEMU snapshot"
  let limit := Nat.min maxLen ((r.start + r.size) - addr)
  let baseOff := r.binOff + (addr - r.start)
  let mut acc : List (BitVec 8) := []
  for i in [:limit] do
    let b := bin.get! (baseOff + i)
    if b == 0 then
      return acc.reverse
    acc := BitVec.ofNat 8 b.toNat :: acc
  throw s!"unterminated C-string at 0x{hexNat (addr)} within {limit} bytes"

def memReadCStr (mem : Memory) (addr : Nat) (maxLen : Nat := 4096) :
    Except String (List (BitVec 8)) := do
  let mut acc : List (BitVec 8) := []
  for i in [:maxLen] do
    let va := BitVec.ofNat 64 (addr + i)
    if mem.perm va != some Perm.rw then
      throw s!"Lean stack C-string at 0x{hexNat ((addr + i))} is not mapped rw-"
    let b := mem.read8 va
    if b == 0#8 then
      return acc.reverse
    acc := b :: acc
  throw s!"unterminated Lean C-string at 0x{hexNat (addr)}"

def containsSubstr (haystack needle : String) : Bool :=
  needle.isEmpty || (haystack.splitOn needle).length > 1

/-- Little-endian unsigned read of `n` bytes at `off` in raw ELF file bytes (`0` past EOF). -/
def elfReadLE (bytes : ByteArray) (off n : Nat) : Nat := Id.run do
  let mut v := 0
  for i in [:n] do
    v := v ||| ((bytes.get! (off + i)).toNat <<< (8 * i))
  return v

/-- Documented Gap #4 helper: if no `PT_LOAD` *file mapping* contains the whole program header
    table `[e_phoff, e_phoff + e_phnum * 56)` and there is no `PT_PHDR`, return the `AT_PHDR`
    value `qemu-aarch64` reports in that case, `pageAlignDown(min PT_LOAD p_vaddr) + e_phoff`.
    A file mapping is page-rounded: it starts `p_vaddr % 4096` lead bytes before `p_offset`
    (when `p_filesz > 0`) and ends at `p_offset + p_filesz`, as in both `qemu-aarch64` and
    `ElfImage.parse`. Return `none` when the table is mapped (the normal case, where Lean and
    QEMU must agree exactly). -/
def qemuUncoveredPhdrAddr? (elfBytes : ByteArray) : Option Nat := Id.run do
  let ePhoff     := elfReadLE elfBytes 0x20 8
  let ePhentsize := elfReadLE elfBytes 0x36 2
  let ePhnum     := elfReadLE elfBytes 0x38 2
  let ePhBytes   := ePhnum * 56
  let mut covered := false
  let mut minVaddr : Option Nat := none
  for i in [:ePhnum] do
    let ph := ePhoff + ePhentsize * i
    let pType := elfReadLE elfBytes ph 4
    if pType == 6 then
      covered := true
    else if pType == 1 then
      let pOffset := elfReadLE elfBytes (ph + 0x08) 8
      let pVaddr  := elfReadLE elfBytes (ph + 0x10) 8
      let pFilesz := elfReadLE elfBytes (ph + 0x20) 8
      let lead    := pVaddr % 4096
      let mapStart := if pOffset ≥ lead && pFilesz > 0 then pOffset - lead else pOffset
      if mapStart ≤ ePhoff && ePhoff + ePhBytes ≤ pOffset + pFilesz then
        covered := true
      minVaddr := some (match minVaddr with
        | some m => Nat.min m pVaddr
        | none => pVaddr)
  if covered then
    return none
  return minVaddr.map fun v => (v - v % 4096) + ePhoff

/-! ## 3. Stack & `auxv` Extraction and Comparison -/

/-- Read `u64` words from `snap` starting at `baseAddr` until a `0` terminator word is reached. -/
def snapReadNullTerminatedPtrs (snap : EntrySnapshotJson) (bin : ByteArray)
    (baseAddr : Nat) (maxEntries : Nat := 256) : Except String (List Nat) := do
  let mut ptrs : List Nat := []
  for i in [:maxEntries] do
    let w ← snapReadU64LE snap bin (baseAddr + 8 * i)
    if w == 0 then
      return ptrs.reverse
    ptrs := w :: ptrs
  throw s!"pointer vector at 0x{hexNat (baseAddr)} exceeded {maxEntries} entries without NULL"

/-- Read `(a_type, a_val)` pairs from `snap` starting at `auxvBase` until `(AT_NULL = 0, 0)`. -/
def snapReadAuxv (snap : EntrySnapshotJson) (bin : ByteArray)
    (auxvBase : Nat) (maxEntries : Nat := 64) : Except String (List (Nat × Nat)) := do
  let mut pairs : List (Nat × Nat) := []
  for i in [:maxEntries] do
    let tag ← snapReadU64LE snap bin (auxvBase + 16 * i)
    let val ← snapReadU64LE snap bin (auxvBase + 16 * i + 8)
    if tag == 0 then
      if val != 0 then
        throw s!"QEMU AT_NULL (0) has non-zero value 0x{hexNat (val)}"
      return pairs.reverse
    pairs := (tag, val) :: pairs
  throw s!"QEMU auxv at 0x{hexNat (auxvBase)} exceeded {maxEntries} entries without AT_NULL"

/-- Read `(a_type, a_val)` pairs from Lean `Memory` starting at `auxvBase` until `(AT_NULL = 0, 0)`. -/
def memReadAuxv (mem : Memory) (auxvBase : Nat) (maxEntries : Nat := 64) :
    Except String (List (Nat × Nat)) := do
  let mut pairs : List (Nat × Nat) := []
  for i in [:maxEntries] do
    let tag := (mem.read64 (BitVec.ofNat 64 (auxvBase + 16 * i))).toNat
    let val := (mem.read64 (BitVec.ofNat 64 (auxvBase + 16 * i + 8))).toNat
    if tag == 0 then
      if val != 0 then
        throw s!"Lean AT_NULL (0) has non-zero value 0x{hexNat (val)}"
      return pairs.reverse
    pairs := (tag, val) :: pairs
  throw s!"Lean auxv at 0x{hexNat (auxvBase)} exceeded {maxEntries} entries without AT_NULL"

def lookupAuxv? (pairs : List (Nat × Nat)) (tag : Nat) : Option Nat :=
  (pairs.find? (fun (t, _) => t == tag)).map Prod.snd

def lookupAuxvRequired (label : String) (pairs : List (Nat × Nat)) (tag : Nat) :
    Except String Nat :=
  match lookupAuxv? pairs tag with
  | some v => pure v
  | none => throw s!"{label}: missing required auxv tag {tag}"

/-! ## 4. Full Region-by-Region, Page-by-Page, Register-by-Register, and Stack Comparator -/

/-- Compare every 4 KiB page and every byte of `PT_LOAD` segments between Lean (`img.segments` +
    `s0.mem`) and QEMU (`snap.regions` + `snapBin`). -/
def comparePtLoadRegions (img : ElfImage) (s0 : State)
    (snap : EntrySnapshotJson) (snapBin : ByteArray) : Except String Unit := do
  let qemuLoads := snap.regions.filter (·.kind == "load")
  if img.segments.length != qemuLoads.length then
    throw s!"PT_LOAD region count mismatch: Lean has {img.segments.length}, QEMU has {qemuLoads.length}"
  for (idx, (leanSeg, qemuReg)) in (img.segments.zip qemuLoads).mapIdx Prod.mk do
    let segStart := leanSeg.start.toNat
    let segSize  := leanSeg.bytes.length
    let leanPerm := permToSnapString leanSeg.perm
    if segStart != qemuReg.start then
      throw s!"PT_LOAD #{idx} start mismatch: Lean 0x{hexNat (segStart)} vs QEMU 0x{hexNat (qemuReg.start)}"
    if segSize != qemuReg.size then
      throw s!"PT_LOAD #{idx} (0x{hexNat (segStart)}) size mismatch: Lean 0x{hexNat (segSize)} vs QEMU 0x{hexNat (qemuReg.size)}"
    if leanPerm != qemuReg.perm then
      throw s!"PT_LOAD #{idx} (0x{hexNat (segStart)}) perm mismatch: Lean {leanPerm} vs QEMU {qemuReg.perm}"
    if segSize % Obj.pageSize != 0 then
      throw s!"PT_LOAD #{idx} size 0x{hexNat (segSize)} is not page-aligned"
    let leanArr := leanSeg.bytes.toArray
    let numPages := segSize / Obj.pageSize
    for pg in [:numPages] do
      let pgOff  := pg * Obj.pageSize
      let pgAddr := segStart + pgOff
      -- Verify `s0.mem` permission and boundary bytes on each page (for segments <= 64 KiB,
      -- so we do not trigger O(N^2) list walks on 1 MiB Go text segments).
      if segSize ≤ 65536 then
        let va0 := BitVec.ofNat 64 pgAddr
        let vaLast := BitVec.ofNat 64 (pgAddr + Obj.pageSize - 1)
        if s0.mem.perm va0 != some leanSeg.perm || s0.mem.perm vaLast != some leanSeg.perm then
          throw s!"PT_LOAD #{idx} page 0x{hexNat (pgAddr)}: s0.mem permission mismatch"
        let q0 := BitVec.ofNat 8 (snapBin.get! (qemuReg.binOff + pgOff)).toNat
        let qLast := BitVec.ofNat 8 (snapBin.get! (qemuReg.binOff + pgOff + Obj.pageSize - 1)).toNat
        if s0.mem.read8 va0 != q0 || s0.mem.read8 vaLast != qLast then
          throw s!"PT_LOAD #{idx} page 0x{hexNat (pgAddr)}: s0.mem boundary byte mismatch"
      -- Compare all 4096 bytes of page `pg` between `leanSeg` and `snapBin`.
      for bOff in [:Obj.pageSize] do
        let i := pgOff + bOff
        let lb := leanArr[i]!.toNat
        let qb := (snapBin.get! (qemuReg.binOff + i)).toNat
        if lb != qb then
          let va := segStart + i
          throw s!"PT_LOAD #{idx} page 0x{hexNat (pgAddr)} byte mismatch at 0x{hexNat (va)}: Lean=0x{hexNat (lb)} QEMU=0x{hexNat (qb)}"

/-- Compare all architectural registers at `e_entry` (`pc`, `sp`, `x0`–`x30`, `tpidr_el0`,
    `pstate`/`cpsr`, and `status`). -/
def compareEntryRegisters (img : ElfImage) (s0 : State) (snap : EntrySnapshotJson)
    (stackBase stackTop : Nat) : Except String Unit := do
  if s0.status != .Running then
    throw s!"expected s0.status == .Running, got {repr s0.status}"
  if s0.pc != img.entry || s0.pc.toNat != snap.regs.pc then
    throw s!"pc mismatch: Lean={hex64 s0.pc} ElfImage.entry={hex64 img.entry} QEMU=0x{hexNat (snap.regs.pc)}"
  if s0.sp.toNat % 16 != 0 || snap.regs.sp % 16 != 0 then
    throw s!"sp 16-byte alignment violated: Lean={hex64 s0.sp} QEMU=0x{hexNat (snap.regs.sp)}"
  if !(stackBase ≤ s0.sp.toNat && s0.sp.toNat < stackTop) then
    throw s!"Lean sp {hex64 s0.sp} outside stack [0x{hexNat (stackBase)}, 0x{hexNat (stackTop)})"
  if !(stackBase ≤ snap.regs.sp && snap.regs.sp < stackTop) then
    throw s!"QEMU sp 0x{hexNat (snap.regs.sp)} outside stack [0x{hexNat (stackBase)}, 0x{hexNat (stackTop)})"
  if snap.regs.x.length != 31 then
    throw s!"QEMU snapshot regs.x has {snap.regs.x.length} entries, expected 31 (x0..x30)"
  for i in [:31] do
    let lv := (s0.regs.read (BitVec.ofNat 5 i)).toNat
    let qv := snap.regs.x[i]!
    if lv != 0 || qv != 0 then
      throw s!"register x{i} mismatch at e_entry: Lean=0x{hexNat (lv)} QEMU=0x{hexNat (qv)} (expected 0)"
  if s0.tpidrEl0 != 0#64 then
    throw s!"Lean tpidr_el0 at e_entry is {hex64 s0.tpidrEl0}, expected 0"
  if snap.regs.tpidr_el0 != some 0 then
    throw s!"QEMU tpidr_el0 at e_entry is {repr snap.regs.tpidr_el0}, expected some 0"
  -- Documented Gap #1: Linux `start_thread` and Lean `loadState` initialize `PState.zero` (0),
  -- whereas QEMU TCG resets `env->ZF = 0` (`CPSR.Z = 1`, `cpsr = 0x40000000`).
  if s0.pstate != PState.zero then
    throw s!"Lean pstate at e_entry is {repr s0.pstate}, expected PState.zero"
  if snap.regs.cpsr != 0x40000000 then
    throw s!"QEMU cpsr at e_entry is 0x{hexNat (snap.regs.cpsr)}, expected 0x40000000 (TCG Z=1 reset)"

/-- Compare the entire initial stack region `[stackBase, stackTop)` (`argc`, `argv`, `envp`,
    every `auxv` entry, zeroed memory below `sp`, and info-block byte accounting). -/
def compareInitialStack (img : ElfImage) (s0 : State) (snap : EntrySnapshotJson)
    (snapBin : ByteArray) (stackReg : SnapRegion) (qemuAuxv : List (Nat × Nat))
    (qemuRandBytes : List (BitVec 8)) (includeVdso : Bool)
    (qemuUncoveredPhdr : Option Nat := none) : Except String Unit := do
  let stackBase := stackReg.start
  let stackSize := stackReg.size
  let stackTop  := stackBase + stackSize
  if stackReg.perm != "rw-" then
    throw s!"QEMU stack perm is {stackReg.perm}, expected rw-"
  -- 1. All stack bytes below `sp` (`[stackBase, sp)`) must be `0x00` in both QEMU and Lean.
  let qemuSp := snap.regs.sp
  let qemuBelowLen := qemuSp - stackBase
  for i in [:qemuBelowLen] do
    let b := snapBin.get! (stackReg.binOff + i)
    if b != 0 then
      throw s!"QEMU stack byte below sp at 0x{hexNat ((stackBase + i))} is non-zero (0x{hexNat (b.toNat)})"
  let leanSp := s0.sp.toNat
  let leanBelowLen := leanSp - stackBase
  -- Check Lean stack permissions and zero bytes below `s0.sp` at page boundaries and near `sp`.
  let mut pg := stackBase
  while pg < leanSp do
    let va := BitVec.ofNat 64 pg
    if s0.mem.perm va != some Perm.rw || s0.mem.read8 va != 0#8 then
      throw s!"Lean stack below sp at 0x{hexNat (pg)} is not zero/rw-"
    pg := pg + Obj.pageSize
  if leanBelowLen > 0 then
    let vaJustBelow := BitVec.ofNat 64 (leanSp - 1)
    if s0.mem.perm vaJustBelow != some Perm.rw || s0.mem.read8 vaJustBelow != 0#8 then
      throw s!"Lean stack byte at sp-1 ({hex64 vaJustBelow}) is not zero/rw-"

  -- 2. Compare `argc` at `sp`.
  let argc := snap.argv.length
  let qemuArgc ← snapReadU64LE snap snapBin qemuSp
  let leanArgc := (s0.mem.read64 s0.sp).toNat
  if qemuArgc != argc || leanArgc != argc then
    throw s!"argc mismatch: expected {argc}, Lean={leanArgc}, QEMU={qemuArgc}"

  -- 3. Read Lean `auxv` to locate `leanInfoBase` (the end of the `AT_NULL` entry, plus an
  -- optional 8-byte alignment word when `argc + envc + 3` is odd).
  let envc := snap.envp.length
  let leanEnvpBase := leanSp + 8 * (argc + 2)
  let leanAuxvBase := leanEnvpBase + 8 * (envc + 1)
  let leanAuxv ← memReadAuxv s0.mem leanAuxvBase
  let leanAuxvEnd := leanAuxvBase + 16 * (leanAuxv.length + 1)
  let tablePadWords := (argc + envc + 3) % 2
  if tablePadWords == 1 then
    if s0.mem.read64 (BitVec.ofNat 64 leanAuxvEnd) != 0#64 then
      throw "Lean 16-byte table alignment word after AT_NULL is non-zero"
  let leanInfoBase := leanAuxvEnd + 8 * tablePadWords

  let qemuEnvpBase := qemuSp + 8 * (argc + 2)
  let qemuAuxvBase := qemuEnvpBase + 8 * (envc + 1)
  let qemuAuxvEnd  := qemuAuxvBase + 16 * (qemuAuxv.length + 1)
  if tablePadWords == 1 then
    if (← snapReadU64LE snap snapBin qemuAuxvEnd) != 0 then
      throw "QEMU 16-byte table alignment word after AT_NULL is non-zero"
  let qemuInfoBase := qemuAuxvEnd + 8 * tablePadWords
  if leanInfoBase != qemuInfoBase then
    throw s!"infoBase mismatch: Lean=0x{hexNat leanInfoBase} QEMU=0x{hexNat qemuInfoBase}"
  let expectedSpDiff := if includeVdso then 0 else 16
  if leanSp != qemuSp + expectedSpDiff then
    throw s!"sp mismatch: Lean=0x{hexNat leanSp} QEMU=0x{hexNat qemuSp} (expected diff 0x{hexNat expectedSpDiff})"

  -- 4. Compare every `argv[0..argc]` pointer and dereferenced string, plus `argv[argc] == NULL`.
  for i in [:argc] do
    let expectedStr := bytesOfString snap.argv[i]!
    let leanPtr := (s0.mem.read64 (BitVec.ofNat 64 (leanSp + 8 * (1 + i)))).toNat
    let qemuPtr ← snapReadU64LE snap snapBin (qemuSp + 8 * (1 + i))
    if leanPtr != qemuPtr then
      throw s!"argv[{i}] ptr mismatch: Lean=0x{hexNat leanPtr} QEMU=0x{hexNat qemuPtr}"
    if !(leanInfoBase ≤ leanPtr && leanPtr < stackTop) then
      throw s!"Lean argv[{i}] ptr 0x{hexNat (leanPtr)} outside info block [0x{hexNat (leanInfoBase)}, 0x{hexNat (stackTop)})"
    let leanStr ← memReadCStr s0.mem leanPtr
    let qemuStr ← snapReadCStr snap snapBin qemuPtr
    if leanStr != expectedStr || qemuStr != expectedStr then
      throw s!"argv[{i}] string mismatch between Lean, QEMU, and expected {snap.argv[i]!}"
  let leanArgvNull := (s0.mem.read64 (BitVec.ofNat 64 (leanSp + 8 * (1 + argc)))).toNat
  let qemuArgvNull ← snapReadU64LE snap snapBin (qemuSp + 8 * (1 + argc))
  if leanArgvNull != 0 || qemuArgvNull != 0 then
    throw s!"argv[argc] NULL terminator mismatch: Lean={leanArgvNull} QEMU={qemuArgvNull}"

  -- 5. Compare every `envp[0..envc]` pointer and dereferenced string, plus `envp[envc] == NULL`.
  for i in [:envc] do
    let expectedEnv := bytesOfString snap.envp[i]!
    let leanPtr := (s0.mem.read64 (BitVec.ofNat 64 (leanEnvpBase + 8 * i))).toNat
    let qemuPtr ← snapReadU64LE snap snapBin (qemuEnvpBase + 8 * i)
    if leanPtr != qemuPtr then
      throw s!"envp[{i}] ptr mismatch: Lean=0x{hexNat leanPtr} QEMU=0x{hexNat qemuPtr}"
    if !(leanInfoBase ≤ leanPtr && leanPtr < stackTop) then
      throw s!"Lean envp[{i}] ptr 0x{hexNat (leanPtr)} outside info block"
    let leanStr ← memReadCStr s0.mem leanPtr
    let qemuStr ← snapReadCStr snap snapBin qemuPtr
    if leanStr != expectedEnv || qemuStr != expectedEnv then
      throw s!"envp[{i}] string mismatch between Lean, QEMU, and expected {snap.envp[i]!}"
  let leanEnvpNull := (s0.mem.read64 (BitVec.ofNat 64 (leanEnvpBase + 8 * envc))).toNat
  let qemuEnvpNull ← snapReadU64LE snap snapBin (qemuEnvpBase + 8 * envc)
  if leanEnvpNull != 0 || qemuEnvpNull != 0 then
    throw s!"envp[envc] NULL terminator mismatch: Lean={leanEnvpNull} QEMU={qemuEnvpNull}"

  -- 6. Compare every scalar `auxv` tag:
  -- AT_PHDR(3), AT_PHENT(4), AT_PHNUM(5), AT_PAGESZ(6), AT_BASE(7), AT_FLAGS(8), AT_ENTRY(9),
  -- AT_UID(11), AT_EUID(12), AT_GID(13), AT_EGID(14), AT_HWCAP(16), AT_CLKTCK(17),
  -- AT_SECURE(23), AT_HWCAP2(26).
  let scalarTags : List (Nat × String) :=
    [ (3, "AT_PHDR"), (4, "AT_PHENT"), (5, "AT_PHNUM"), (6, "AT_PAGESZ"),
      (7, "AT_BASE"), (8, "AT_FLAGS"), (9, "AT_ENTRY"), (11, "AT_UID"),
      (12, "AT_EUID"), (13, "AT_GID"), (14, "AT_EGID"), (16, "AT_HWCAP"),
      (17, "AT_CLKTCK"), (23, "AT_SECURE"), (26, "AT_HWCAP2") ]
  for (tag, name) in scalarTags do
    let lv ← lookupAuxvRequired s!"Lean {name}" leanAuxv tag
    let qv ← lookupAuxvRequired s!"QEMU {name}" qemuAuxv tag
    -- Documented Gap #4: when no page-rounded `PT_LOAD` file mapping contains the program
    -- header table, Lean `loadState` reports `AT_PHDR = 0` (as Linux `load_elf_binary` in
    -- `fs/binfmt_elf.c` does when no `PT_LOAD` covers `e_phoff`), whereas `qemu-aarch64`
    -- reports `pageAlignDown(min PT_LOAD p_vaddr) + e_phoff`. Both exact values are asserted.
    if tag == 3 then
      if let some qemuExpected := qemuUncoveredPhdr then
        if lv != 0 || qv != qemuExpected then
          throw s!"auxv AT_PHDR (3) Gap #4 (e_phoff not covered by any PT_LOAD) violated: Lean=0x{hexNat lv} (expected 0, Linux) QEMU=0x{hexNat qv} (expected 0x{hexNat qemuExpected})"
        continue
    if lv != qv then
      throw s!"auxv {name} ({tag}) value mismatch: Lean=0x{hexNat (lv)} QEMU=0x{hexNat (qv)}"
  -- Also check independent ELF header invariants on AT_PHDR, AT_PHENT, AT_PHNUM, AT_PAGESZ, AT_ENTRY, AT_CLKTCK.
  let atPhdr ← lookupAuxvRequired "Lean AT_PHDR" leanAuxv 3
  let atPhent ← lookupAuxvRequired "Lean AT_PHENT" leanAuxv 4
  let atPhnum ← lookupAuxvRequired "Lean AT_PHNUM" leanAuxv 5
  let atPagesz ← lookupAuxvRequired "Lean AT_PAGESZ" leanAuxv 6
  let atEntry ← lookupAuxvRequired "Lean AT_ENTRY" leanAuxv 9
  let atClktck ← lookupAuxvRequired "Lean AT_CLKTCK" leanAuxv 17
  if atPhdr != img.phdrVaddr.toNat || atPhent != 56 || atPhnum != img.phnum ||
      atPagesz != 4096 || atEntry != img.entry.toNat || atClktck != 100 then
    throw s!"auxv ELF invariant check failed: phdr=0x{hexNat (atPhdr)} phent={atPhent} phnum={atPhnum} pagesz={atPagesz} entry=0x{hexNat (atEntry)} clktck={atClktck}"

  -- 7. Compare pointer `auxv` tags: AT_PLATFORM (15), AT_RANDOM (25), AT_EXECFN (31).
  let leanPlatPtr ← lookupAuxvRequired "Lean AT_PLATFORM" leanAuxv 15
  let qemuPlatPtr ← lookupAuxvRequired "QEMU AT_PLATFORM" qemuAuxv 15
  if leanPlatPtr != qemuPlatPtr || !(leanInfoBase ≤ leanPlatPtr && leanPlatPtr < stackTop) then
    throw s!"AT_PLATFORM pointer mismatch or outside info block: Lean=0x{hexNat leanPlatPtr} QEMU=0x{hexNat qemuPlatPtr}"
  let leanPlat ← memReadCStr s0.mem leanPlatPtr
  let qemuPlat ← snapReadCStr snap snapBin qemuPlatPtr
  if leanPlat != bytesOfString "aarch64" || qemuPlat != bytesOfString "aarch64" then
    throw "AT_PLATFORM dereferenced string is not \"aarch64\""

  let leanRandPtr ← lookupAuxvRequired "Lean AT_RANDOM" leanAuxv 25
  let qemuRandPtr ← lookupAuxvRequired "QEMU AT_RANDOM" qemuAuxv 25
  if leanRandPtr != qemuRandPtr || leanRandPtr != leanInfoBase then
    throw s!"AT_RANDOM pointer mismatch: Lean=0x{hexNat leanRandPtr} QEMU=0x{hexNat qemuRandPtr} infoBase=0x{hexNat leanInfoBase}"
  let leanRandBytes := s0.mem.readBytes (BitVec.ofNat 64 leanRandPtr) 16
  if leanRandBytes != qemuRandBytes || qemuRandBytes.length != 16 then
    throw "AT_RANDOM 16-byte payload mismatch between Lean and QEMU"

  let leanExecfnPtr ← lookupAuxvRequired "Lean AT_EXECFN" leanAuxv 31
  let qemuExecfnPtr ← lookupAuxvRequired "QEMU AT_EXECFN" qemuAuxv 31
  if leanExecfnPtr != qemuExecfnPtr || !(leanInfoBase ≤ leanExecfnPtr && leanExecfnPtr < stackTop) then
    throw s!"AT_EXECFN pointer mismatch or outside info block: Lean=0x{hexNat leanExecfnPtr} QEMU=0x{hexNat qemuExecfnPtr}"
  let leanExecfn ← memReadCStr s0.mem leanExecfnPtr
  let qemuExecfn ← snapReadCStr snap snapBin qemuExecfnPtr
  if leanExecfn != bytesOfString snap.elf.path || qemuExecfn != bytesOfString snap.elf.path then
    throw "AT_EXECFN string does not match elf.path"

  -- 8. Verify complete `auxv` tag coverage (Documented Gap #2: AT_SYSINFO_EHDR = 33).
  for (lTag, _) in leanAuxv do
    if (lookupAuxv? qemuAuxv lTag).isNone then
      throw s!"Lean emitted auxv tag {lTag} not present in QEMU auxv"
  for (qTag, qVal) in qemuAuxv do
    if qTag == 33 then
      if includeVdso then
        let lVal ← lookupAuxvRequired "Lean AT_SYSINFO_EHDR" leanAuxv 33
        if lVal != qVal then
          throw s!"AT_SYSINFO_EHDR (33) mismatch: Lean=0x{hexNat (lVal)} QEMU=0x{hexNat (qVal)}"
      else if (lookupAuxv? leanAuxv 33).isSome then
        throw "Lean unexpectedly emitted AT_SYSINFO_EHDR (33) when includeVdso = false"
    else if (lookupAuxv? leanAuxv qTag).isNone then
      throw s!"QEMU emitted auxv tag {qTag} not modeled by Lean"

  -- 9. Verify that every byte in `[leanInfoBase, stackTop)` matches QEMU byte-for-byte and equals
  -- `randomBytes` (16 B) ++ `< 16` zero pad bytes ++ `"aarch64\0"` ++ `argv` strings ++ `envp`
  -- strings ++ `execfn` string ++ 8-byte top-of-stack zero sentinel word.
  let argvBlob   := (snap.argv.map (fun s => bytesOfString s ++ [0#8])).flatten
  let envpBlob   := (snap.envp.map (fun s => bytesOfString s ++ [0#8])).flatten
  let execfnBlob := bytesOfString snap.elf.path ++ [0#8]
  let platBlob   := bytesOfString "aarch64" ++ [0#8]
  let upperBlob  := platBlob ++ argvBlob ++ envpBlob ++ execfnBlob ++ List.replicate 8 0#8
  let padLen     := (stackTop - leanInfoBase) - (16 + upperBlob.length)
  if padLen ≥ 16 then
    throw s!"Lean info block padding is {padLen} bytes (expected < 16 for 16-byte sp alignment)"
  let expectedInfoBlock := qemuRandBytes ++ List.replicate padLen 0#8 ++ upperBlob
  let actualInfoBlock := s0.mem.readBytes (BitVec.ofNat 64 leanInfoBase) (stackTop - leanInfoBase)
  let qemuInfoBlock ← snapReadBytes snap snapBin qemuInfoBase (stackTop - qemuInfoBase)
  if actualInfoBlock != expectedInfoBlock || actualInfoBlock != qemuInfoBlock then
    throw "Top-of-stack [infoBase, stackTop) bytes differ between Lean, QEMU, and expected layout"

/-- Verify `brk` (`brkStart` / `brk`) and unmapped gap pages in `s0.mem` and `snap`. -/
def compareBrkAndUnmappedGaps (img : ElfImage) (s0 : State) (snap : EntrySnapshotJson)
    (stackBase stackTop : Nat) : Except String Unit := do
  -- 1. `brkStart` and `brk` at `e_entry`.
  if img.brkStart.toNat != snap.brkStart || s0.brkStart != img.brkStart || s0.brk != img.brkStart then
    throw s!"brkStart mismatch: Lean={hex64 s0.brkStart} QEMU=0x{hexNat (snap.brkStart)}"
  if snap.regions.any (·.kind == "brk") then
    throw "QEMU unexpectedly mapped a brk region at e_entry"
  if s0.mem.perm s0.brkStart != none then
    throw s!"Lean unexpectedly mapped brkStart ({hex64 s0.brkStart}) at e_entry"

  -- 2. Null page `[0x0, 0x1000)` must be unmapped.
  if s0.mem.perm 0x0#64 != none || s0.mem.perm 0xfff#64 != none then
    throw "Lean null page [0x0, 0x1000) is unexpectedly mapped"

  -- 3. Unmapped pages before, between, and after `PT_LOAD` segments.
  let segs := img.segments
  for i in [:segs.length] do
    let r : Snapshot.Region := segs[i]!
    let rStart := r.start.toNat
    let rEnd   := rStart + r.bytes.length
    let prevEnd :=
      if i == 0 then 0
      else
        let prev : Snapshot.Region := segs[i - 1]!
        prev.start.toNat + prev.bytes.length
    if prevEnd < rStart then
      let beforeByte := BitVec.ofNat 64 (rStart - 1)
      let beforePage := BitVec.ofNat 64 (rStart - Obj.pageSize)
      if s0.mem.perm beforeByte != none || s0.mem.perm beforePage != none then
        throw s!"unmapped gap before PT_LOAD #{i} (0x{hexNat (rStart)}) is mapped in Lean"
      let midGap := prevEnd + ((rStart - prevEnd) / 2)
      if s0.mem.perm (BitVec.ofNat 64 midGap) != none then
        throw s!"unmapped gap midpoint 0x{hexNat (midGap)} is mapped in Lean"
    let nextStart :=
      if i + 1 < segs.length then
        let nxt : Snapshot.Region := segs[i + 1]!
        nxt.start.toNat
      else stackBase
    if rEnd < nextStart then
      if s0.mem.perm (BitVec.ofNat 64 rEnd) != none then
        throw s!"unmapped page 0x{hexNat (rEnd)} after PT_LOAD #{i} is mapped in Lean"

  -- 4. Guard pages immediately below `stackBase` and at `stackTop` must be unmapped.
  if s0.mem.perm (BitVec.ofNat 64 (stackBase - 1)) != none ||
      s0.mem.perm (BitVec.ofNat 64 (stackBase - Obj.pageSize)) != none then
    throw s!"guard page below stackBase (0x{hexNat (stackBase)}) is mapped in Lean"
  if s0.mem.perm (BitVec.ofNat 64 stackTop) != none ||
      s0.mem.perm (BitVec.ofNat 64 (stackTop + Obj.pageSize - 1)) != none then
    throw s!"page at stackTop (0x{hexNat (stackTop)}) is mapped in Lean"

/-! ## 5. Case Evaluators (`runPositiveDiffCase`, `runRejectedDiffCase`, `runManifestIO`) -/

/-- Run the complete region-by-region, register-by-register, stack, `brk`, and unmapped-gap
    comparison for one `PositiveDiffCase`. -/
def verifyPositiveCase (elfBytes : ByteArray) (snapBin : ByteArray)
    (tc : PositiveDiffCase) : Except String Unit := do
  let snap := tc.snapshot
  if snap.schema != "arm64-proc-snapshot/1" || snap.stop != "exec-entry" then
    throw s!"unexpected snapshot header schema={snap.schema} stop={snap.stop}"
  if snapBin.size != snap.bin.size then
    throw s!"snapshot bin size {snapBin.size} != metadata size {snap.bin.size}"
  let img ← ElfImage.parseByteArray elfBytes
  if !img.WellFormed then
    throw "ElfImage.WellFormed returned false"
  let some stackReg := snap.regions.find? (·.kind == "stack")
    | throw "QEMU snapshot has no stack region"
  let stackBase := stackReg.start
  let stackSize := stackReg.size
  let stackTop  := stackBase + stackSize

  -- Parse QEMU's `auxv` and `AT_RANDOM` 16-byte seed from `snapBin`.
  let qemuSp := snap.regs.sp
  let argc := snap.argv.length
  let envc := snap.envp.length
  let qemuAuxvBase := qemuSp + 8 * (argc + 2) + 8 * (envc + 1)
  let qemuAuxv ← snapReadAuxv snap snapBin qemuAuxvBase
  let qemuRandPtr ← lookupAuxvRequired "QEMU AT_RANDOM" qemuAuxv 25
  let qemuRandBytes ← snapReadBytes snap snapBin qemuRandPtr 16
  let qemuHwcap ← lookupAuxvRequired "QEMU AT_HWCAP" qemuAuxv 16
  let qemuHwcap2 ← lookupAuxvRequired "QEMU AT_HWCAP2" qemuAuxv 26
  let qemuUid ← lookupAuxvRequired "QEMU AT_UID" qemuAuxv 11
  let qemuEuid ← lookupAuxvRequired "QEMU AT_EUID" qemuAuxv 12
  let qemuGid ← lookupAuxvRequired "QEMU AT_GID" qemuAuxv 13
  let qemuEgid ← lookupAuxvRequired "QEMU AT_EGID" qemuAuxv 14
  let extraAuxv : List (BitVec 64 × BitVec 64) ←
    if tc.include_vdso_in_extra_auxv then
      let vdso ← lookupAuxvRequired "QEMU AT_SYSINFO_EHDR" qemuAuxv 33
      pure [(33#64, BitVec.ofNat 64 vdso)]
    else
      pure []

  let stdinBytes := bytesOfString tc.stdin_utf8
  let initFiles := tc.initial_files.map fun f => (f.path, bytesOfString f.utf8)
  let inputs : ProcessInputs :=
    { argv   := snap.argv.map bytesOfString
      envp   := snap.envp.map bytesOfString
      execfn := bytesOfString snap.elf.path
      stdin  := stdinBytes
      files  := initFiles
      init   :=
        { stackTop  := BitVec.ofNat 64 stackTop
          stackSize := stackSize
          auxv      :=
            { randomBytes := qemuRandBytes
              hwcap       := BitVec.ofNat 64 qemuHwcap
              hwcap2      := BitVec.ofNat 64 qemuHwcap2
              uid         := BitVec.ofNat 64 qemuUid
              euid        := BitVec.ofNat 64 qemuEuid
              gid         := BitVec.ofNat 64 qemuGid
              egid        := BitVec.ofNat 64 qemuEgid
              extra       := extraAuxv } } }
  let s0 ← img.loadState inputs

  -- Check `State.fs` (`stdin` out-of-band stream, standard descriptors, and initial `files`).
  if s0.fs.stdin != stdinBytes ||
      s0.fs.fds 0#64 != some { path := "", accMode := .rdonly, append := false, offset := 0, kind := .stdio } ||
      s0.fs.fds 1#64 != some { path := "", accMode := .wronly, append := true, offset := 0, kind := .stdio } ||
      s0.fs.fds 2#64 != some { path := "", accMode := .wronly, append := true, offset := 0, kind := .stdio } ||
      (initFiles.all (fun (p, _) => normalizePath p != ["<stdin>"]) && s0.fs.files "<stdin>" != none) then
    throw "State.fs stdio streams do not match ProcessInputs"
  for (path, content) in initFiles do
    if s0.fs.files path != some (.file content) then
      throw s!"State.fs missing initial file {path}"

  comparePtLoadRegions img s0 snap snapBin
  compareEntryRegisters img s0 snap stackBase stackTop
  compareInitialStack img s0 snap snapBin stackReg qemuAuxv qemuRandBytes tc.include_vdso_in_extra_auxv
    (qemuUncoveredPhdrAddr? elfBytes)
  compareBrkAndUnmappedGaps img s0 snap stackBase stackTop

/-! ## 6. Human-Readable Hex Load-State Formatter & CLI Helpers -/

def hexByte2 (b : Nat) : String :=
  String.ofList [hexDigitChar (b / 16), hexDigitChar (b % 16)]
where
  hexDigitChar (n : Nat) : Char :=
    if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

def fnv1a64 (bs : List (BitVec 8)) : UInt64 :=
  bs.foldl (fun (h : UInt64) b => (h ^^^ b.toNat.toUInt64) * 0x100000001b3) 0xcbf29ce484222325

def canonicalAuxvTags : List (Nat × String) :=
  [ (3, "AT_PHDR"), (4, "AT_PHENT"), (5, "AT_PHNUM"), (6, "AT_PAGESZ")
  , (7, "AT_BASE"), (8, "AT_FLAGS"), (9, "AT_ENTRY"), (11, "AT_UID")
  , (12, "AT_EUID"), (13, "AT_GID"), (14, "AT_EGID"), (15, "AT_PLATFORM")
  , (16, "AT_HWCAP"), (17, "AT_CLKTCK"), (23, "AT_SECURE"), (25, "AT_RANDOM")
  , (26, "AT_HWCAP2"), (31, "AT_EXECFN") ]

def memReadNullTerminatedPtrs (mem : Memory) (baseAddr : Nat)
    (maxEntries : Nat := 256) : Except String (List Nat) := do
  let mut ptrs : List Nat := []
  for i in [:maxEntries] do
    let w := (mem.read64 (BitVec.ofNat 64 (baseAddr + 8 * i))).toNat
    if w == 0 then
      return ptrs.reverse
    ptrs := w :: ptrs
  throw s!"Lean pointer vector at 0x{hexNat baseAddr} exceeded {maxEntries} entries without NULL"

/-- Format the Lean initial `State` (`s0 ← img.loadState inputs`) into canonical hex text.
    `gap4PhdrAddr? = some q` prints a Lean `AT_PHDR` of `0` as `q` (Documented Gap #4, whose
    exact values `compareInitialStack` asserts separately). -/
def formatLeanLoadState (img : ElfImage) (inputs : ProcessInputs) (s0 : State)
    (extraHex : List (Nat × Nat) := []) (gap4PhdrAddr? : Option Nat := none) :
    Except String String := do
  let mut out := "regions:\n"
  for seg in img.segments do
    let start := seg.start.toNat
    let sz := seg.bytes.length
    let fnv := (fnv1a64 seg.bytes).toNat
    out := out ++ s!"  0x{hexNat start}-0x{hexNat (start + sz)} {permToSnapString seg.perm} load  size=0x{hexNat sz} fnv64=0x{hexNat fnv}\n"
  let stackTop := inputs.init.stackTop.toNat
  let stackBase := stackTop - inputs.init.stackSize
  out := out ++ s!"  0x{hexNat stackBase}-0x{hexNat stackTop} rw- stack size=0x{hexNat inputs.init.stackSize}\n"
  out := out ++ "registers & brk:\n"
  let nonZeroX := (List.range 31).filterMap fun i =>
    let v := (s0.regs.read (BitVec.ofNat 5 i)).toNat
    if v == 0 then none else some s!"x{i}=0x{hexNat v}"
  let xSummary := if nonZeroX.isEmpty then "x0..x30=0x0" else String.intercalate " " nonZeroX
  out := out ++ s!"  pc=0x{hexNat s0.pc.toNat} {xSummary} tpidr_el0=0x{hexNat s0.tpidrEl0.toNat} brk=0x{hexNat s0.brk.toNat}\n"
  out := out ++ "stack (from sp):\n"
  let sp := s0.sp.toNat
  let argc := (s0.mem.read64 s0.sp).toNat
  out := out ++ s!"  [sp+0x0] 0x{hexNat argc}  (argc={argc})\n"
  for i in [:argc] do
    let off := 8 * (1 + i)
    let ptr := (s0.mem.read64 (BitVec.ofNat 64 (sp + off))).toNat
    let s := String.fromUTF8! (byteArrayOfBytes (← memReadCStr s0.mem ptr))
    out := out ++ s!"  [sp+0x{hexNat off}] 0x{hexNat ptr} (\"{s}\")  (argv[{i}])\n"
  let argvNullOff := 8 * (1 + argc)
  let argvNull := (s0.mem.read64 (BitVec.ofNat 64 (sp + argvNullOff))).toNat
  out := out ++ s!"  [sp+0x{hexNat argvNullOff}] 0x{hexNat argvNull}  (argv[{argc}] = NULL)\n"
  let envPtrs ← memReadNullTerminatedPtrs s0.mem (sp + 8 * (argc + 2))
  let envc := envPtrs.length
  for (i, ptr) in envPtrs.mapIdx Prod.mk do
    let off := 8 * (argc + 2 + i)
    let s := String.fromUTF8! (byteArrayOfBytes (← memReadCStr s0.mem ptr))
    out := out ++ s!"  [sp+0x{hexNat off}] 0x{hexNat ptr} (\"{s}\")  (envp[{i}])\n"
  let envNullOff := 8 * (argc + 2 + envc)
  out := out ++ s!"  [sp+0x{hexNat envNullOff}] 0x0  (envp[{envc}] = NULL)\n"
  out := out ++ "  auxv:\n"
  let auxv ← memReadAuxv s0.mem (sp + 8 * (argc + 2 + envc + 1))
  for (tag, name) in canonicalAuxvTags do
    let val ← lookupAuxvRequired name auxv tag
    let val := match tag, gap4PhdrAddr? with
      | 3, some q => if val == 0 then q else val
      | _, _ => val
    if tag == 15 || tag == 31 then
      let s := String.fromUTF8! (byteArrayOfBytes (← memReadCStr s0.mem val))
      out := out ++ s!"    {name} ({tag}) = 0x{hexNat val} (\"{s}\")\n"
    else if tag == 25 then
      let hex16 := String.join ((List.range 16).map fun i => hexByte2 (s0.mem.read8 (BitVec.ofNat 64 (val + i))).toNat)
      out := out ++ s!"    {name} ({tag}) = 0x{hexNat val} (0x{hex16})\n"
    else
      out := out ++ s!"    {name} ({tag}) = 0x{hexNat val}\n"
  out := out ++ "    AT_NULL (0) = 0x0\n"
  out := out ++ "bytes:\n"
  for (vaddr, len) in (s0.pc.toNat, 32) :: extraHex do
    out := out ++ s!"  @0x{hexNat vaddr} ({len} B):\n"
    let bs : List (BitVec 8) :=
      match img.segments.find? (fun r => r.start.toNat ≤ vaddr && vaddr + len ≤ r.start.toNat + r.bytes.length) with
      | some seg => seg.bytes.drop (vaddr - seg.start.toNat) |>.take len
      | none => (List.range len).map fun j => s0.mem.read8 (BitVec.ofNat 64 (vaddr + j))
    let mut rowOff := 0
    while rowOff < len do
      let rowLen := Nat.min 16 (len - rowOff)
      let rowAddr := vaddr + rowOff
      let rowHex := String.intercalate " " ((bs.drop rowOff |>.take rowLen).map fun b => hexByte2 b.toNat)
      out := out ++ s!"    0x{hexNat rowAddr}: {rowHex}\n"
      rowOff := rowOff + 16
  return out

/-- Format a QEMU `EntrySnapshotJson` + `snapBin` into the same canonical hex text. -/
def formatQemuSnapshotState (snap : EntrySnapshotJson) (snapBin : ByteArray)
    (extraHex : List (Nat × Nat) := []) : Except String String := do
  let mut out := "regions:\n"
  for r in snap.regions do
    let endAddr := r.start + r.size
    if r.kind == "load" then
      let bs := bytesOfByteArray (snapBin.extract r.binOff (r.binOff + r.size))
      let fnv := (fnv1a64 bs).toNat
      out := out ++ s!"  0x{hexNat r.start}-0x{hexNat endAddr} {r.perm} load  size=0x{hexNat r.size} fnv64=0x{hexNat fnv}\n"
    else if r.kind == "stack" then
      out := out ++ s!"  0x{hexNat r.start}-0x{hexNat endAddr} {r.perm} stack size=0x{hexNat r.size}\n"
  out := out ++ "registers & brk:\n"
  let nonZeroX := (List.range snap.regs.x.length).filterMap fun i =>
    let v := snap.regs.x[i]!
    if v == 0 then none else some s!"x{i}=0x{hexNat v}"
  let xSummary := if nonZeroX.isEmpty then "x0..x30=0x0" else String.intercalate " " nonZeroX
  let tpidr := snap.regs.tpidr_el0.getD 0
  out := out ++ s!"  pc=0x{hexNat snap.regs.pc} {xSummary} tpidr_el0=0x{hexNat tpidr} brk=0x{hexNat snap.brkStart}\n"
  out := out ++ "stack (from sp):\n"
  let sp := snap.regs.sp
  let argc ← snapReadU64LE snap snapBin sp
  out := out ++ s!"  [sp+0x0] 0x{hexNat argc}  (argc={argc})\n"
  for i in [:argc] do
    let off := 8 * (1 + i)
    let ptr ← snapReadU64LE snap snapBin (sp + off)
    let s := String.fromUTF8! (byteArrayOfBytes (← snapReadCStr snap snapBin ptr))
    out := out ++ s!"  [sp+0x{hexNat off}] 0x{hexNat ptr} (\"{s}\")  (argv[{i}])\n"
  let argvNullOff := 8 * (1 + argc)
  let argvNull ← snapReadU64LE snap snapBin (sp + argvNullOff)
  out := out ++ s!"  [sp+0x{hexNat argvNullOff}] 0x{hexNat argvNull}  (argv[{argc}] = NULL)\n"
  let envPtrs ← snapReadNullTerminatedPtrs snap snapBin (sp + 8 * (argc + 2))
  let envc := envPtrs.length
  for (i, ptr) in envPtrs.mapIdx Prod.mk do
    let off := 8 * (argc + 2 + i)
    let s := String.fromUTF8! (byteArrayOfBytes (← snapReadCStr snap snapBin ptr))
    out := out ++ s!"  [sp+0x{hexNat off}] 0x{hexNat ptr} (\"{s}\")  (envp[{i}])\n"
  let envNullOff := 8 * (argc + 2 + envc)
  out := out ++ s!"  [sp+0x{hexNat envNullOff}] 0x0  (envp[{envc}] = NULL)\n"
  out := out ++ "  auxv:\n"
  let auxv ← snapReadAuxv snap snapBin (sp + 8 * (argc + 2 + envc + 1))
  for (tag, name) in canonicalAuxvTags do
    let val ← lookupAuxvRequired name auxv tag
    if tag == 15 || tag == 31 then
      let s := String.fromUTF8! (byteArrayOfBytes (← snapReadCStr snap snapBin val))
      out := out ++ s!"    {name} ({tag}) = 0x{hexNat val} (\"{s}\")\n"
    else if tag == 25 then
      let randBs ← snapReadBytes snap snapBin val 16
      let hex16 := String.join (randBs.map fun b => hexByte2 b.toNat)
      out := out ++ s!"    {name} ({tag}) = 0x{hexNat val} (0x{hex16})\n"
    else
      out := out ++ s!"    {name} ({tag}) = 0x{hexNat val}\n"
  out := out ++ "    AT_NULL (0) = 0x0\n"
  out := out ++ "bytes:\n"
  for (vaddr, len) in (snap.regs.pc, 32) :: extraHex do
    out := out ++ s!"  @0x{hexNat vaddr} ({len} B):\n"
    let bs ← snapReadBytes snap snapBin vaddr len
    let mut rowOff := 0
    while rowOff < len do
      let rowLen := Nat.min 16 (len - rowOff)
      let rowAddr := vaddr + rowOff
      let rowHex := String.intercalate " " ((bs.drop rowOff |>.take rowLen).map fun b => hexByte2 b.toNat)
      out := out ++ s!"    0x{hexNat rowAddr}: {rowHex}\n"
      rowOff := rowOff + 16
  return out

def extractProcessInputsFromSnapshot (snap : EntrySnapshotJson) (snapBin : ByteArray) :
    Except String ProcessInputs := do
  let some stackReg := snap.regions.find? (·.kind == "stack")
    | throw "QEMU snapshot has no stack region"
  let stackTop := stackReg.start + stackReg.size
  let argc := snap.argv.length
  let envc := snap.envp.length
  let qemuAuxv ← snapReadAuxv snap snapBin (snap.regs.sp + 8 * (argc + 2) + 8 * (envc + 1))
  let qemuRandPtr ← lookupAuxvRequired "QEMU AT_RANDOM" qemuAuxv 25
  let qemuRandBytes ← snapReadBytes snap snapBin qemuRandPtr 16
  let qemuHwcap ← lookupAuxvRequired "QEMU AT_HWCAP" qemuAuxv 16
  let qemuHwcap2 ← lookupAuxvRequired "QEMU AT_HWCAP2" qemuAuxv 26
  let qemuUid ← lookupAuxvRequired "QEMU AT_UID" qemuAuxv 11
  let qemuEuid ← lookupAuxvRequired "QEMU AT_EUID" qemuAuxv 12
  let qemuGid ← lookupAuxvRequired "QEMU AT_GID" qemuAuxv 13
  let qemuEgid ← lookupAuxvRequired "QEMU AT_EGID" qemuAuxv 14
  pure {
    argv   := snap.argv.map bytesOfString
    envp   := snap.envp.map bytesOfString
    execfn := bytesOfString snap.elf.path
    init   :=
      { stackTop  := BitVec.ofNat 64 stackTop
        stackSize := stackReg.size
        auxv      := {
          randomBytes := qemuRandBytes
          hwcap       := BitVec.ofNat 64 qemuHwcap
          hwcap2      := BitVec.ofNat 64 qemuHwcap2
          uid         := BitVec.ofNat 64 qemuUid
          euid        := BitVec.ofNat 64 qemuEuid
          gid         := BitVec.ofNat 64 qemuGid
          egid        := BitVec.ofNat 64 qemuEgid } } }

/-- Verify that `formatLeanLoadState` and `formatQemuSnapshotState` produce identical text. -/
def verifyFormattedStateSync (elfBytes : ByteArray) (snapBin : ByteArray)
    (snap : EntrySnapshotJson) : Except String Unit := do
  let img ← ElfImage.parseByteArray elfBytes
  let inputs ← extractProcessInputsFromSnapshot snap snapBin
  let s0 ← img.loadState inputs
  let leanTxt ← formatLeanLoadState img inputs s0 (gap4PhdrAddr? := qemuUncoveredPhdrAddr? elfBytes)
  let qemuTxt ← formatQemuSnapshotState snap snapBin
  if leanTxt != qemuTxt then
    throw s!"formatted load-state text mismatch:\n--- Lean ---\n{leanTxt}\n--- QEMU ---\n{qemuTxt}"

def parseNatAuto (s : String) : Except String Nat := do
  if s.startsWith "0x" || s.startsWith "0X" then
    let hex := (s.drop 2).toString
    let mut acc := 0
    for c in hex.toList do
      match hexNibble? c with
      | some v => acc := acc * 16 + v.toNat
      | none => throw s!"invalid hex integer '{s}'"
    return acc
  else
    match s.toNat? with
    | some n => return n
    | none => throw s!"invalid decimal integer '{s}'"

def parseHexRangeSpec (spec : String) : Except String (Nat × Nat) := do
  match spec.splitOn ":" with
  | [a, l] => return (← parseNatAuto a, ← parseNatAuto l)
  | _ => throw s!"expected <vaddr>:<len>, got '{spec}'"

def dumpLoadStateIO (elfPath : System.FilePath) (snapJsonPath? : Option System.FilePath)
    (hexSpecs : List String) : IO UInt32 := do
  let resolvedElf ← resolveRepoFilePath elfPath
  let elfBytes ← IO.FS.readBinFile resolvedElf
  match ElfImage.parseByteArray elfBytes with
  | .error e =>
    IO.eprintln e
    return 1
  | .ok img =>
    let inputsRes : Except String ProcessInputs ←
      match snapJsonPath? with
      | none => pure (.ok {})
      | some p =>
        let resolvedP ← resolveRepoFilePath p
        let raw ← IO.FS.readFile resolvedP
        match Json.parse raw >>= fromJson? with
        | .error e => pure (.error e)
        | .ok (snap : EntrySnapshotJson) =>
          let binPath := (resolvedP.parent.getD ".") / snap.bin.file
          let bin ← IO.FS.readBinFile binPath
          pure (extractProcessInputsFromSnapshot snap bin)
    match inputsRes with
    | .error e =>
      IO.eprintln e
      return 1
    | .ok inputs =>
      let res : Except String String := do
        let extraHex ← hexSpecs.mapM parseHexRangeSpec
        let s0 ← img.loadState inputs
        formatLeanLoadState img inputs s0 extraHex
      match res with
      | .ok txt =>
        IO.print txt
        return 0
      | .error e =>
        IO.eprintln e
        return 1

/-- Run one `PositiveDiffCase` in `IO`, returning `(passed, diagnostic)`. -/
def runPositiveCaseIO (tc : PositiveDiffCase) : IO (Bool × String) := do
  let resolvedElf ← resolveRepoFilePath tc.elf_path
  let elfBytes ← IO.FS.readBinFile resolvedElf
  let snapBinRes : Except String ByteArray ←
    match tc.snapshot_bin_path with
    | some p =>
      let resolvedSnap ← resolveRepoFilePath p
      let b ← IO.FS.readBinFile resolvedSnap
      pure (.ok b)
    | none =>
      pure (materializeSparseBin tc.snapshot.bin.size tc.sparse_bin_chunks)
  match snapBinRes with
  | .error e => return (false, s!"[{tc.id}] failed to load snapshot bin: {e}")
  | .ok snapBin =>
    match (verifyPositiveCase elfBytes snapBin tc >>= fun () =>
           verifyFormattedStateSync elfBytes snapBin tc.snapshot) with
    | .ok () => return (true, "")
    | .error e => return (false, s!"[{tc.id}] ({tc.elf_path}): {e}")

/-- Verify that `ElfImage.parseByteArray` rejects `tc.elf_path` with `tc.expected_error_substr`. -/
def runRejectedCaseIO (tc : RejectedDiffCase) : IO (Bool × String) := do
  let resolvedElf ← resolveRepoFilePath tc.elf_path
  let elfBytes ← IO.FS.readBinFile resolvedElf
  match ElfImage.parseByteArray elfBytes with
  | .ok img =>
    return (false, s!"[{tc.id}] ({tc.elf_path}): expected fail-closed rejection containing '{tc.expected_error_substr}', but parsed ok (entry={hex64 img.entry})")
  | .error err =>
    if containsSubstr err tc.expected_error_substr then
      return (true, "")
    else
      return (false, s!"[{tc.id}] ({tc.elf_path}): rejected with '{err}', which does not contain '{tc.expected_error_substr}'")

/-- Load an `ElfLoaderDiffManifest` JSON file and build parallelizable work items for all positive
    and rejected cases in deterministic manifest order. -/
def buildManifestWorkItemsIO (manifestPath : System.FilePath) :
    IO (Array (Testing.Harness.ParallelWorkItem Testing.Harness.ParallelTestBatch)) := do
  let resolvedManifest ← resolveRepoFilePath manifestPath
  let raw ← IO.FS.readFile resolvedManifest
  let j ← IO.ofExcept (Json.parse raw)
  let suite : ElfLoaderDiffManifest ← IO.ofExcept (fromJson? j)
  let mut items : Array (Testing.Harness.ParallelWorkItem Testing.Harness.ParallelTestBatch) :=
    Array.mkEmpty (suite.positive_cases.length + suite.rejected_cases.length)
  for tc in suite.positive_cases do
    let tcName := s!"ELF Loader vs QEMU [{tc.category}] {tc.id}: {tc.description}"
    items := items.push {
      label    := tcName
      priority := 400
      run      := fun () => do
        let missing ← missingTestFilesIO [← resolveRepoFilePath tc.elf_path]
        if !missing.isEmpty then
          return { cases := [UnitTestCase.skipMissingFiles tcName [tc.elf_path]] }
        let (ok, diag) ← runPositiveCaseIO tc
        let errs := if ok then #[] else #[s!"[ELF Loader Diff FAIL] {diag}"]
        return { cases := [{ name := tcName, check := ok }], stderr := errs }
    }
  for rc in suite.rejected_cases do
    let rcName := s!"ELF Loader Fail-Closed [{rc.category}] {rc.id}: {rc.description}"
    items := items.push {
      label    := rcName
      priority := 150
      run      := fun () => do
        let missing ← missingTestFilesIO [← resolveRepoFilePath rc.elf_path]
        if !missing.isEmpty then
          return { cases := [UnitTestCase.skipMissingFiles rcName [rc.elf_path]] }
        let (ok, diag) ← runRejectedCaseIO rc
        let errs := if ok then #[] else #[s!"[ELF Loader Reject FAIL] {diag}"]
        return { cases := [{ name := rcName, check := ok }], stderr := errs }
    }
  return items

/-- Load an `ElfLoaderDiffManifest` JSON file and evaluate all positive and rejected cases in parallel. -/
def runManifestPathIO (manifestPath : System.FilePath) : IO (List TestCase) := do
  let items ← buildManifestWorkItemsIO manifestPath
  Testing.Harness.runParallelTestBatchesIO items

def defaultManifestPath : System.FilePath :=
  "Arm64/Testing/ElfLoaderDiff/expected_snapshots.json"

def buildDefaultElfLoaderDiffWorkItemsIO :
    IO (Array (Testing.Harness.ParallelWorkItem Testing.Harness.ParallelTestBatch)) :=
  buildManifestWorkItemsIO defaultManifestPath

def runDefaultElfLoaderDiffIO : IO (List TestCase) :=
  runManifestPathIO defaultManifestPath

def runSingleEntryDiffIO (elfPath : System.FilePath) (snapJsonPath : System.FilePath) : IO UInt32 := do
  let raw ← IO.FS.readFile snapJsonPath
  let j ← IO.ofExcept (Json.parse raw)
  let snap : EntrySnapshotJson ← IO.ofExcept (fromJson? j)
  let binPath := (snapJsonPath.parent.getD ".") / snap.bin.file
  let tc : PositiveDiffCase := {
    id := elfPath.fileName.getD "live"
    category := "live"
    description := "Live QEMU entry snapshot vs ElfImage.loadState"
    elf_path := elfPath.toString
    snapshot := snap
    snapshot_bin_path := some binPath.toString }
  let (ok, diag) ← runPositiveCaseIO tc
  if !ok then
    IO.eprintln s!"[ELF Loader Diff FAIL] {diag}"
  return (← runTestSuite [{ name := s!"ELF Loader vs QEMU ({elfPath})", check := ok }])

end Testing.ElfLoaderDiff
