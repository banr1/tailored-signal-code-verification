/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean.Data.Json
public import Std.Data.HashMap
public import Arm64.Trusted.Process
public import ProofLib.Process
public import Arm64.Testing.Harness.FastSemantics

/-!
# Paged Fast Static-ELF Process Runner

Standalone CLI executable (`lake exe elf_run`) that executes static AArch64 Linux ELF (`ET_EXEC`)
images under `ElfImage.loadState`, `Program.fetchMem`, and `execInst` using a lazy 4 KiB paged
memory store (`Store`) backed by `ByteArray` data and 1-byte cell-permission codes. After each
memory-writing step, over-approximated write footprints (`instWriteRanges` and `syscallWriteRanges`)
patch the modified ranges back into `Store`.

Subcommands:
- `elf_run run [--trusted] <elf> <request.json> [--out <file>]`
- `elf_run selftest [<trials>] [<seed>]`
- `elf_run refcheck [--trusted] <elf> <request.json> <steps>`
- `elf_run decodescan <elf> <out.txt>`
- `elf_run decoderaw <code.bin> <out.txt>`

Request JSON schema: `{"argv": [str], "envp": [str], "stdin_hex": str,
"files": [{"path": str, "hex": str}], "dirs": [str], "max_steps": n}`.
-/

@[expose] public section

namespace Testing.ElfRun

open Lean
open Arm64 Arm64.Process Arm64.Fast ProofLib

/-! ## Cell encoding -/

/-- One memory cell, as in `Memory.cells`. -/
abbrev Cell := Option (Option Arm64.Perm × BitVec 8)

/-- Code of a cell's permission: `0` = no cell (`none`), `1` = a cell with no permission
    (`some (none, b)`, created by a raw write to an unmapped byte),
    `2 + 16·anon + 8·lazyFree + 4·r + 2·w + x` = `some (some p, b)`.
    The byte is stored separately (`0` for code `0`). -/
def encodeCode (c : Cell) : UInt8 :=
  match c with
  | none => 0
  | some (none, _) => 1
  | some (some p, _) =>
    2 + (if p.anon then 16 else 0) + (if p.lazyFree then 8 else 0) +
      (if p.r then 4 else 0) + (if p.w then 2 else 0) + (if p.x then 1 else 0)

/-- Clear the `lazyFree` bit (`8` in `code - 2`) on a mapped cell code (`code ≥ 2`). -/
@[inline] def clearLazyCode (code : UInt8) : UInt8 :=
  if code ≥ 2 then (((code - 2) &&& 23) + 2) else code

/-- `encodeCode` with `lazyFree` cleared (`Memory.write8` / `Memory.writeBytes` post-write code). -/
@[inline] def encodeCodeClearLazy (c : Cell) : UInt8 :=
  clearLazyCode (encodeCode c)

/-- The byte of a cell (`0` if there is no cell). -/
def encodeByte (c : Cell) : UInt8 :=
  match c with
  | none => 0
  | some (_, b) => b.toNat.toUInt8

/-- Inverse of `encodeCode` / `encodeByte` on codes `0..33`. -/
def decodeCell (code : Nat) (b : Nat) : Cell :=
  if code == 0 then none
  else if code == 1 then some (none, BitVec.ofNat 8 b)
  else
    let k := code - 2
    some (some { r := k / 4 % 2 == 1, w := k / 2 % 2 == 1, x := k % 2 == 1,
                 lazyFree := k / 8 % 2 == 1, anon := k / 16 % 2 == 1 },
          BitVec.ofNat 8 b)

/-- All `34 · 256` decoded cells, built once, so a lookup allocates nothing. -/
def cellTable : Array Cell :=
  Array.ofFn fun (i : Fin 8704) => decodeCell (i.val / 256) (i.val % 256)

/-- Convert `n : Nat` (`< 2 ^ 64`) to `BitVec 64` via `UInt64` without GMP `2 ^ 64` modulo. -/
@[inline] def bv64 (n : Nat) : BitVec 64 :=
  n.toUInt64.toBitVec

/-! ## Paged store -/

def pageBits : Nat := 12
def pageSize : Nat := 4096

/-- Sentinel page number (`2 ^ 60`, which is an unboxed scalar `Nat` `< 2 ^ 63` and strictly
    larger than any 64-bit page number `pn < 2 ^ 52`). -/
def tlbEmptyPn : Nat := ((1 : UInt64) <<< 60).toNat

/-- Pages written so far: `idx` maps a page number to its slot in `pages`; a page is a
    `ByteArray` of `2 · pageSize` bytes (data bytes, then cell codes). `tlbPn` and `tlbSlot`
    form a 4096-entry direct-mapped cache indexed by `pn &&& 4095` storing unboxed scalar `Nat`s;
    `hasCollision` is `false` until two distinct materialized page numbers share `pn &&& 4095`. -/
structure Store where
  idx          : Std.HashMap Nat Nat := {}
  pages        : Array ByteArray := #[]
  tlbPn        : Array Nat := Array.replicate 4096 tlbEmptyPn
  tlbSlot      : Array Nat := Array.replicate 4096 0
  hasCollision : Bool := false

/-- O(1) check whether page `pn` is in `st`. -/
@[inline] def Store.containsPage (st : Store) (pn : Nat) : Bool :=
  let k := pn &&& 4095
  if st.tlbPn[k]! == pn then true
  else if !st.hasCollision then false
  else st.idx.contains pn

/-- The memory the runner presents to `execInst`: the store's page if materialized, else the
    immutable initial memory `base`. -/
def Store.mem (base : BitVec 64 → Cell) (st : Store) : Memory :=
  ⟨fun a =>
    let n := a.toNat
    let pn := n >>> 12
    let k := pn &&& 4095
    if st.tlbPn[k]! == pn then
      let slot := st.tlbSlot[k]!
      let pg := st.pages[slot]!
      let off := n &&& 4095
      let code := (pg.get! (pageSize + off)).toNat
      let b := (pg.get! off).toNat
      cellTable[code * 256 + b]!
    else if !st.hasCollision then
      base a
    else
      match st.idx.get? pn with
      | some slot =>
        let pg := st.pages[slot]!
        let off := n &&& 4095
        let code := (pg.get! (pageSize + off)).toNat
        let b := (pg.get! off).toNat
        cellTable[code * 256 + b]!
      | none => base a⟩

/-- Fuel-bounded loop helper. -/
def loopN {α : Type} : Nat → Nat → α → (Nat → α → α) → α
  | 0, _, acc, _ => acc
  | k + 1, i, acc, f => loopN k (i + 1) (f i acc) f

/-- A page built from the cells of `m` (data bytes, then codes) in a single pass over `m`. -/
def pageOf (m : BitVec 64 → Cell) (pn : Nat) : ByteArray :=
  let start := (pn * pageSize).toUInt64
  let (bytes, codes) := loopN pageSize 0
    (ByteArray.emptyWithCapacity (2 * pageSize), ByteArray.emptyWithCapacity pageSize)
    fun i (bs, cs) =>
      let c := m (start + i.toUInt64).toBitVec
      (bs.push (encodeByte c), cs.push (encodeCode c))
  codes.copySlice 0 bytes pageSize pageSize false

/-- Cells of `m` on `[ea, ea + len)`, encoded as `len` data bytes then `len` codes in a single
    pass over `m.cells`. -/
def extractRange (m : Memory) (ea : BitVec 64) (len : Nat) : ByteArray :=
  let eaU := ea.toNat.toUInt64
  let (bytes, codes) := loopN len 0
    (ByteArray.emptyWithCapacity (2 * len), ByteArray.emptyWithCapacity len)
    fun i (bs, cs) =>
      let c := m.cells (eaU + i.toUInt64).toBitVec
      (bs.push (encodeByte c), cs.push (encodeCode c))
  codes.copySlice 0 bytes len len false

/-- A patch: the post-step cells of `[ea, ea + len)` (`extractRange`). -/
structure Patch where
  ea   : BitVec 64
  len  : Nat
  data : ByteArray

/-- Apply `f` to page `pn`, materializing it from `base` first if needed. -/
@[inline] def Store.withPage (base : BitVec 64 → Cell) (st : Store) (pn : Nat)
    (f : ByteArray → ByteArray) : Store :=
  let k := pn &&& 4095
  if st.tlbPn[k]! == pn then
    let slot := st.tlbSlot[k]!
    { st with pages := st.pages.modify slot f }
  else if !st.hasCollision && st.tlbPn[k]! == tlbEmptyPn then
    let slot := st.pages.size
    { idx := st.idx.insert pn slot
      pages := st.pages.push (f (pageOf base pn))
      tlbPn := st.tlbPn.set! k pn
      tlbSlot := st.tlbSlot.set! k slot
      hasCollision := false }
  else
    match st.idx.get? pn with
    | some slot => { st with pages := st.pages.modify slot f }
    | none =>
      let slot := st.pages.size
      let tlbEmpty := st.tlbPn[k]! == tlbEmptyPn
      { idx := st.idx.insert pn slot
        pages := st.pages.push (f (pageOf base pn))
        tlbPn := if tlbEmpty then st.tlbPn.set! k pn else st.tlbPn
        tlbSlot := if tlbEmpty then st.tlbSlot.set! k slot else st.tlbSlot
        hasCollision := if tlbEmpty then st.hasCollision else true }

/-- Clear `lazyFree` at page offset `off` if set (`Memory.write8` clears `lazyFree`). -/
@[inline] def clearLazyAt (pg : ByteArray) (off : Nat) : ByteArray :=
  let c := pg.get! (pageSize + off)
  if c ≥ 2 && ((c - 2) &&& 8) != 0 then pg.set! (pageSize + off) (((c - 2) &&& 23) + 2) else pg

/-- Unrolled in-place little-endian write of `1`, `2`, `4`, or `8` data bytes of `v` into `pg` at
    offset `off`, clearing `lazyFree` on each written byte (`Memory.write8`). -/
@[inline] def writeLeBytes8 (pg : ByteArray) (off len : Nat) (v : UInt64) : ByteArray :=
  if len == 8 then
    let pg := clearLazyAt (pg.set! off v.toUInt8) off
    let pg := clearLazyAt (pg.set! (off + 1) (v >>> 8).toUInt8) (off + 1)
    let pg := clearLazyAt (pg.set! (off + 2) (v >>> 16).toUInt8) (off + 2)
    let pg := clearLazyAt (pg.set! (off + 3) (v >>> 24).toUInt8) (off + 3)
    let pg := clearLazyAt (pg.set! (off + 4) (v >>> 32).toUInt8) (off + 4)
    let pg := clearLazyAt (pg.set! (off + 5) (v >>> 40).toUInt8) (off + 5)
    let pg := clearLazyAt (pg.set! (off + 6) (v >>> 48).toUInt8) (off + 6)
    clearLazyAt (pg.set! (off + 7) (v >>> 56).toUInt8) (off + 7)
  else if len == 4 then
    let pg := clearLazyAt (pg.set! off v.toUInt8) off
    let pg := clearLazyAt (pg.set! (off + 1) (v >>> 8).toUInt8) (off + 1)
    let pg := clearLazyAt (pg.set! (off + 2) (v >>> 16).toUInt8) (off + 2)
    clearLazyAt (pg.set! (off + 3) (v >>> 24).toUInt8) (off + 3)
  else if len == 1 then
    clearLazyAt (pg.set! off v.toUInt8) off
  else
    let pg := clearLazyAt (pg.set! off v.toUInt8) off
    clearLazyAt (pg.set! (off + 1) (v >>> 8).toUInt8) (off + 1)

/-- Direct in-place page data write for non-page-straddling stores of `1`, `2`, `4`, `8`, or `16`
    bytes (`str`, `stp`, `stnp`, `strSimd`, `stpSimd` `≤ 16` B). -/
@[inline] def Store.writeData16 (base : BitVec 64 → Cell) (st : Store) (ea : UInt64) (len : Nat)
    (bLo bHi : UInt64) : Store :=
  let pn := (ea >>> 12).toNat
  let off := (ea &&& 4095).toNat
  st.withPage base pn fun pg =>
    if len == 16 then
      let pg := writeLeBytes8 pg off 8 bLo
      writeLeBytes8 pg (off + 8) 8 bHi
    else
      writeLeBytes8 pg off len bLo

/-- Direct in-place page data write for non-page-straddling 32-byte `stpSimd .Q128` stores. -/
@[inline] def Store.writeData32 (base : BitVec 64 → Cell) (st : Store) (ea : UInt64)
    (b0 b1 b2 b3 : UInt64) : Store :=
  let pn := (ea >>> 12).toNat
  let off := (ea &&& 4095).toNat
  st.withPage base pn fun pg =>
    let pg := writeLeBytes8 pg off 8 b0
    let pg := writeLeBytes8 pg (off + 8) 8 b1
    let pg := writeLeBytes8 pg (off + 16) 8 b2
    writeLeBytes8 pg (off + 24) 8 b3

/-- Write a patch into the store, one page-bounded run at a time. -/
def Store.applyPatch (base : BitVec 64 → Cell) (st : Store) (p : Patch) : Store :=
  let eaU := p.ea.toNat.toUInt64
  let rec go : Nat → Nat → Store → Store
    | 0, _, st => st
    | fuel + 1, done, st =>
      if done ≥ p.len then st
      else
        let a := eaU + done.toUInt64
        let pn := (a >>> 12).toNat
        let off := (a &&& 4095).toNat
        let run := Nat.min (pageSize - off) (p.len - done)
        let st' := st.withPage base pn fun pg =>
          let pg := p.data.copySlice done pg off run
          p.data.copySlice (p.len + done) pg (pageSize + off) run
        go fuel (done + run) st'
  go (p.len + 1) 0 st

/-! ## Initial memory -/

/-- Packed unboxed representation of a loaded `Snapshot.Region`. -/
structure FastRegion where
  start       : Nat
  stop        : Nat
  nonAnonLen  : Nat
  codeNonAnon : UInt8
  codeAnon    : UInt8
  bytes       : ByteArray

/-- Convert `regions` into `FastRegion`s backed by `ByteArray` matching `Snapshot.loadCellAt`. -/
def mkFastRegions (regions : List Snapshot.Region) : Array FastRegion :=
  (regions.map fun r =>
    let bs := r.bytes.foldl (fun acc b => acc.push b.toNat.toUInt8)
      (ByteArray.emptyWithCapacity r.bytes.length)
    let start := r.start.toNat
    let pNonAnon : Arm64.Perm := { r := r.perm.r, w := r.perm.w, x := r.perm.x, lazyFree := false, anon := false }
    let pAnon    : Arm64.Perm := { r := r.perm.r, w := r.perm.w, x := r.perm.x, lazyFree := false, anon := r.perm.anon }
    { start
      stop        := start + bs.size
      nonAnonLen  := r.nonAnonLen
      codeNonAnon := encodeCode (some (some pNonAnon, 0#8))
      codeAnon    := encodeCode (some (some pAnon, 0#8))
      bytes       := bs }).toArray

/-- Cell code for `some (some Perm.rw, _)` (`anon = true, lazyFree = false, rw-`). -/
def rwCellCode : Nat := (encodeCode (some (some Perm.rw, 0#8))).toNat

/-- Pre-allocated cell `some (some Perm.rw, 0#8)`. -/
def rwZeroCell : Cell := cellTable[rwCellCode * 256]!

/-- Pointwise-equal lookup over `mkFastRegions (img.segments ++ [stackRegion])` +
    `mapZero stackBase stackSize`, using scalar `Nat` comparisons and `cellTable` (zero
    `BitVec.sub` / GMP / heap allocations per byte read). -/
def fastBaseCellAt (arrs : Array FastRegion) (stackBase stackStop : Nat) (a : BitVec 64) : Cell :=
  let n := a.toNat
  let rec go (i : Nat) : Cell :=
    if h : i < arrs.size then
      let r := arrs[i]
      if r.start ≤ n && n < r.stop then
        let off := n - r.start
        let b := (r.bytes.get! off).toNat
        let code := if off < r.nonAnonLen then r.codeNonAnon else r.codeAnon
        cellTable[code.toNat * 256 + b]!
      else
        go (i + 1)
    else
      if stackBase ≤ n && n < stackStop then rwZeroCell else none
  go 0

/-- Load `img` with `inputs`: `ElfImage.loadState`'s state, and its memory as a function
    (`(⟨Snapshot.cellAt (segments ++ [stack])⟩ : Memory).mapZero stackBase stackSize`, with
    `cellAt` and `mapZero` computed by the pointwise-equal `fastBaseCellAt`). -/
def load (img : ElfImage) (inputs : ProcessInputs) :
    Except String (State × (BitVec 64 → Cell)) := do
  let s0 ← img.fastLoadState inputs
  let (_, stackRegion) ← buildInitialStack img inputs
  let stackBase := inputs.init.stackTop.toNat - inputs.init.stackSize
  let stackStop := inputs.init.stackTop.toNat
  let arrs := mkFastRegions (img.segments ++ [stackRegion])
  pure (s0, fastBaseCellAt arrs stackBase stackStop)

/-! ## Write footprints -/

/-- The syscalls `execSyscall` dispatches. -/
inductive Sys
  | ioctl | openat | close | lseek | read | write | readv | writev | pread64 | ppoll | fstat
  | clockGettime | brk | munmap | mremap | mmap | mprotect | madvise | getrandom
  | exit | exitGroup | setTidAddress | schedGetaffinity
  | getpid | gettid | sigaltstack | rtSigprocmask | rtSigaction | tkill | tgkill | fcntl
  deriving DecidableEq, Repr

/-- `Sys` of a syscall number, in `execSyscall`'s dispatch order. -/
def Sys.ofNr? (nr : BitVec 64) : Option Sys :=
  if nr == SYS_IOCTL then some .ioctl
  else if nr == SYS_OPENAT then some .openat
  else if nr == SYS_CLOSE then some .close
  else if nr == SYS_LSEEK then some .lseek
  else if nr == SYS_READ then some .read
  else if nr == SYS_WRITE then some .write
  else if nr == SYS_READV then some .readv
  else if nr == SYS_WRITEV then some .writev
  else if nr == SYS_PREAD64 then some .pread64
  else if nr == SYS_PPOLL then some .ppoll
  else if nr == SYS_FSTAT then some .fstat
  else if nr == SYS_CLOCK_GETTIME then some .clockGettime
  else if nr == SYS_BRK then some .brk
  else if nr == SYS_MUNMAP then some .munmap
  else if nr == SYS_MREMAP then some .mremap
  else if nr == SYS_MMAP then some .mmap
  else if nr == SYS_MPROTECT then some .mprotect
  else if nr == SYS_MADVISE then some .madvise
  else if nr == SYS_GETRANDOM then some .getrandom
  else if nr == SYS_EXIT then some .exit
  else if nr == SYS_EXIT_GROUP then some .exitGroup
  else if nr == SYS_SET_TID_ADDRESS then some .setTidAddress
  else if nr == SYS_SCHED_GETAFFINITY then some .schedGetaffinity
  else if nr == SYS_GETPID then some .getpid
  else if nr == SYS_GETTID then some .gettid
  else if nr == SYS_SIGALTSTACK then some .sigaltstack
  else if nr == SYS_RT_SIGPROCMASK then some .rtSigprocmask
  else if nr == SYS_RT_SIGACTION then some .rtSigaction
  else if nr == SYS_TKILL then some .tkill
  else if nr == SYS_TGKILL then some .tgkill
  else if nr == SYS_FCNTL then some .fcntl
  else none

/-- Every syscall number `< 1024` that `execSyscall` dispatches (does not end in
    `.Exception "unmodeled syscall (svc)"` from the default state) is in `Sys`, and conversely. -/
def checkSysExhaustive : Bool :=
  (List.range 1024).all fun n =>
    let nr := BitVec.ofNat 64 n
    let st := (execSyscall (({} : State).writeReg64 .x8 nr)).status
    (st != .Exception "unmodeled syscall (svc)") == (Sys.ofNr? nr).isSome

/-- `(base, len)` of the first `n` iovecs (16-byte `{iov_base, iov_len}` records) at `vec` in `m`,
    with lengths clipped so that they sum to at most `budget` bytes (the bytes a vectored read
    filled, in segment order). -/
def iovFilledRanges (m : Memory) (vec : BitVec 64) : Nat → Nat → List (BitVec 64 × Nat)
  | 0, _ => []
  | _, 0 => []
  | n + 1, budget + 1 =>
    let len := min (m.read64 (vec + 8#64)).toNat (budget + 1)
    (m.read64 vec, len) :: iovFilledRanges m (vec + 16#64) n (budget + 1 - len)

/-- Ranges `execSyscall s = s'` may have written in `s'.mem` (when `s'` is `.Running`),
    over-approximated. Exhaustive over `Sys` (no wildcard). -/
def syscallWriteRanges (sc : Sys) (s s' : State) : List (BitVec 64 × Nat) :=
  let ret := s'.readReg64 .x0
  let failed := ret.slt 0#64
  match sc with
  | .read | .pread64 => if failed then [] else [(s.readReg64 .x1, ret.toNat)]
  | .readv =>
    if failed then [] else iovFilledRanges s.mem (s.readReg64 .x1) (s.readReg32 .x2).toNat ret.toNat
  | .ppoll => if failed then [] else [(s.readReg64 .x0, (s.readReg32 .x1).toNat * 8)]
  | .fstat => if failed then [] else [(s.readReg64 .x1, 128)]
  | .clockGettime => if failed then [] else [(s.readReg64 .x1, 16)]
  | .schedGetaffinity => if failed then [] else [(s.readReg64 .x2, 8)]
  | .getrandom => if failed then [] else [(s.readReg64 .x0, ret.toNat)]
  | .sigaltstack =>
    if failed || s.readReg64 .x1 == 0#64 then [] else [(s.readReg64 .x1, 24)]
  | .rtSigprocmask =>
    if failed || s.readReg64 .x2 == 0#64 then [] else [(s.readReg64 .x2, 8)]
  | .rtSigaction =>
    if failed || s.readReg64 .x2 == 0#64 then [] else [(s.readReg64 .x2, 32)]
  | .brk =>
    let oldPage := Arm64.pageAlignUp s.brk.toNat
    let newPage := Arm64.pageAlignUp s'.brk.toNat
    if oldPage < newPage then [(BitVec.ofNat 64 oldPage, newPage - oldPage)]
    else if newPage < oldPage then [(BitVec.ofNat 64 newPage, oldPage - newPage)]
    else []
  | .mmap => if failed then [] else [(ret, Arm64.pageAlignUp (s.readReg64 .x1).toNat)]
  | .mremap =>
    if failed then []
    else [(s.readReg64 .x0, Arm64.pageAlignUp (s.readReg64 .x1).toNat),
          (ret, Arm64.pageAlignUp (s.readReg64 .x2).toNat)]
  | .munmap | .mprotect | .madvise =>
    if failed then [] else [(s.readReg64 .x0, Arm64.pageAlignUp (s.readReg64 .x1).toNat)]
  | .ioctl =>
    if failed || s.readReg32 .x1 != FIONREAD_W32 then [] else [(s.readReg64 .x2, 4)]
  | .openat | .close | .lseek | .write | .writev | .exit | .exitGroup | .setTidAddress
  | .getpid | .gettid | .tkill | .tgkill | .fcntl => []

/-- Ranges `execInst inst s = s'` may have written in `s'.mem` (when `s'` is `.Running`):
    exact for scalar and SIMD single/pair stores, over-approximated (16 or 32 bytes) for
    exclusive/atomic/ldar/st1 stores from the effective address `execInst` computes.
    Exhaustive over every `Instr` constructor (no wildcard): a new constructor fails to
    compile until classified. `none` for a syscall whose number is not in `Sys`. -/
def instWriteRanges (inst : Instr) (s s' : State) : Option (List (BitVec 64 × Nat)) :=
  let ea (a : AddrMode) : BitVec 64 := (evalAddrMode s a).1
  let r (x : Reg) : BitVec 64 := s.readReg64 x
  match inst with
  -- Stores (`execStr` / `execStp` / explicit `setMem` in `execInst`).
  | .str w _ addr => some [(ea addr, w.bytes)]
  | .stp sf _ _ addr => some [(ea addr, if sf == .W64 then 16 else 8)]
  | .stnp w rn _ _ offset => some [(ea (.Offset rn offset), if w == .X64 then 16 else 8)]
  | .ldarStlr _ isLoad rn _ => some (if isLoad then [] else [(r rn, 16)])
  | .stxr _ _ _ rn _ | .cas _ _ _ _ rn _ | .atomicRmw _ _ _ _ _ rn _ => some [(r rn, 16)]
  | .stxp _ _ _ rn _ _ | .casp _ _ _ _ _ rn _ _ => some [(r rn, 32)]
  | .ldapurStlur _ opc rn _ offset =>
    some (if opc == 0#2 then [(r rn + offset, 16)] else [])
  | .stpSimd sz _ _ addr => some [(ea addr, 2 * sz.bytes)]
  | .strSimd sz _ addr => some [(ea addr, sz.bytes)]
  | .stnpSimd sz _ _ rn offset => some [(r rn + offset, 2 * sz.bytes)]
  | .st1SinglePost _ _ _ _ _ rn _ => some [(r rn, 16)]
  | .simdLdSt1Single isLoad _ _ _ _ _ _ rn _ =>
    some (if isLoad then [] else [(r rn, 16)])
  | .simdLdSt1Multi isLoad _ _ nregs rn _ _ _ =>
    some (if isLoad then [] else [(r rn, nregs * 16)])
  | .simdLdStMulti isLoad _ _ selem rn _ _ _ =>
    some (if isLoad then [] else [(r rn, selem * 16)])
  | .dcZva rt => some [(r rt &&& ~~~63#64, 64)]
  | .system isHalt imm =>
    if isHalt || imm != 0#16 then some []
    else (Sys.ofNr? (s.readReg64 .x8)).map fun sc => syscallWriteRanges sc s s'
  -- Everything else writes no memory (enumerated, no wildcard).
  | .adr .. | .addSubImm .. | .logicalImm .. | .moveWide .. | .bitfield .. | .extr ..
  | .b .. | .bl .. | .bCond .. | .cbz .. | .tbz .. | .br .. | .blr .. | .ret .. | .nop
  | .hint .. | .barrier .. | .sysReg .. | .udf ..
  | .logicalShift .. | .addSubShift .. | .addSubExt .. | .addSubCarry .. | .condCompareReg ..
  | .condCompareImm .. | .condSelect .. | .dataProc1 .. | .dataProc2 .. | .dataProc3 ..
  | .crc32 .. | .ldr .. | .ldrLit .. | .ldp .. | .ldnp .. | .ldxr .. | .ldxp .. | .ldapr ..
  | .prfm .. | .prfmLit .. | .ldrSimd .. | .ldrSimdLit .. | .ldpSimd .. | .ldnpSimd ..
  | .simdLd1r .. | .fmovGprVec .. | .fpDataProc1 .. | .fpDataProc2 .. | .fpCompare ..
  | .fpImm .. | .fpCondCompare .. | .fpCondSelect .. | .fpDataProc3 .. | .fpFixedConv ..
  | .simdImmShift .. | .simdInsDup .. | .simdThreeSame .. | .simdTwoRegMisc ..
  | .simdAcrossLanes .. | .simdPermute .. | .simdExt .. | .simdTbl .. | .simdAddpScalar ..
  | .simdDupScalar .. | .simdPmull .. | .simdThreeDiff .. | .aes .. | .cryptoSha2Reg ..
  | .cryptoSha3Reg .. | .cryptoSha512Reg2 .. | .cryptoSha512Reg3 .. | .cryptoSha3FourReg ..
  | .cryptoXar .. => some []

/-- Canonical constructor names for `instTagIdx`. -/
def instTagNames : Array String := #[
  "adr", "addSubImm", "logicalImm", "moveWide", "bitfield", "extr",
  "b", "bl", "bCond", "cbz", "tbz", "br", "blr", "ret", "nop",
  "system", "hint", "barrier", "sysReg", "dcZva", "udf",
  "logicalShift", "addSubShift", "addSubExt", "addSubCarry", "condCompareReg",
  "condCompareImm", "condSelect", "dataProc1", "dataProc2", "dataProc3", "crc32",
  "ldr", "ldrLit", "str", "ldp", "stp", "ldnp", "stnp",
  "ldarStlr", "ldxr", "stxr", "ldxp", "stxp", "cas", "casp", "atomicRmw",
  "ldapr", "ldapurStlur", "prfm", "prfmLit",
  "ldrSimd", "strSimd", "ldrSimdLit", "ldpSimd", "stpSimd", "ldnpSimd", "stnpSimd",
  "st1SinglePost", "simdLdSt1Single", "simdLdSt1Multi", "simdLdStMulti", "simdLd1r",
  "fmovGprVec", "fpDataProc1", "fpDataProc2", "fpCompare", "fpImm",
  "fpCondCompare", "fpCondSelect", "fpDataProc3", "fpFixedConv",
  "simdImmShift", "simdInsDup", "simdThreeSame", "simdTwoRegMisc", "simdAcrossLanes",
  "simdPermute", "simdExt", "simdTbl", "simdAddpScalar", "simdDupScalar",
  "simdPmull", "simdThreeDiff", "aes", "cryptoSha2Reg", "cryptoSha3Reg",
  "cryptoSha512Reg2", "cryptoSha512Reg3", "cryptoSha3FourReg", "cryptoXar"
]

/-- Fast dense index (`0 .. instTagNames.size - 1`) for dynamic instruction census. -/
def instTagIdx : Instr → Nat
  | .adr .. => 0 | .addSubImm .. => 1 | .logicalImm .. => 2 | .moveWide .. => 3
  | .bitfield .. => 4 | .extr .. => 5 | .b .. => 6 | .bl .. => 7 | .bCond .. => 8
  | .cbz .. => 9 | .tbz .. => 10 | .br .. => 11 | .blr .. => 12 | .ret .. => 13
  | .nop => 14 | .system .. => 15 | .hint .. => 16 | .barrier .. => 17
  | .sysReg .. => 18 | .dcZva .. => 19 | .udf .. => 20 | .logicalShift .. => 21
  | .addSubShift .. => 22 | .addSubExt .. => 23 | .addSubCarry .. => 24
  | .condCompareReg .. => 25 | .condCompareImm .. => 26 | .condSelect .. => 27
  | .dataProc1 .. => 28 | .dataProc2 .. => 29 | .dataProc3 .. => 30 | .crc32 .. => 31
  | .ldr .. => 32 | .ldrLit .. => 33 | .str .. => 34 | .ldp .. => 35 | .stp .. => 36
  | .ldnp .. => 37 | .stnp .. => 38 | .ldarStlr .. => 39 | .ldxr .. => 40 | .stxr .. => 41
  | .ldxp .. => 42 | .stxp .. => 43 | .cas .. => 44 | .casp .. => 45 | .atomicRmw .. => 46
  | .ldapr .. => 47 | .ldapurStlur .. => 48 | .prfm .. => 49 | .prfmLit .. => 50
  | .ldrSimd .. => 51 | .strSimd .. => 52 | .ldrSimdLit .. => 53 | .ldpSimd .. => 54
  | .stpSimd .. => 55 | .ldnpSimd .. => 56 | .stnpSimd .. => 57 | .st1SinglePost .. => 58
  | .simdLdSt1Single .. => 59 | .simdLdSt1Multi .. => 60 | .simdLdStMulti .. => 61
  | .simdLd1r .. => 62 | .fmovGprVec .. => 63 | .fpDataProc1 .. => 64 | .fpDataProc2 .. => 65
  | .fpCompare .. => 66 | .fpImm .. => 67 | .fpCondCompare .. => 68 | .fpCondSelect .. => 69
  | .fpDataProc3 .. => 70 | .fpFixedConv .. => 71 | .simdImmShift .. => 72
  | .simdInsDup .. => 73 | .simdThreeSame .. => 74 | .simdTwoRegMisc .. => 75
  | .simdAcrossLanes .. => 76 | .simdPermute .. => 77 | .simdExt .. => 78
  | .simdTbl .. => 79 | .simdAddpScalar .. => 80 | .simdDupScalar .. => 81
  | .simdPmull .. => 82 | .simdThreeDiff .. => 83 | .aes .. => 84
  | .cryptoSha2Reg .. => 85 | .cryptoSha3Reg .. => 86 | .cryptoSha512Reg2 .. => 87
  | .cryptoSha512Reg3 .. => 88 | .cryptoSha3FourReg .. => 89 | .cryptoXar .. => 90

/-! ## Stepping -/

/-- `svc #0`. -/
@[inline] def isSvc0 (inst : Instr) : Bool :=
  match inst with
  | .system isHalt imm => !isHalt && imm == 0#16
  | _ => false

/-- Fast O(1) classifier: whether `inst` can possibly write memory (exhaustive over `Instr`). -/
@[inline] def mayWriteMem (inst : Instr) : Bool :=
  match inst with
  | .str .. | .stp .. | .stnp .. | .stxr .. | .cas .. | .atomicRmw .. | .stxp .. | .casp ..
  | .stpSimd .. | .strSimd .. | .stnpSimd .. | .st1SinglePost .. | .dcZva .. => true
  | .ldarStlr _ isLoad .. | .simdLdSt1Single isLoad ..
  | .simdLdSt1Multi isLoad .. | .simdLdStMulti isLoad .. => !isLoad
  | .ldapurStlur _ opc .. => opc == 0#2
  | .system isHalt imm => !isHalt && imm == 0#16
  | .adr .. | .addSubImm .. | .logicalImm .. | .moveWide .. | .bitfield .. | .extr ..
  | .b .. | .bl .. | .bCond .. | .cbz .. | .tbz .. | .br .. | .blr .. | .ret .. | .nop
  | .hint .. | .barrier .. | .sysReg .. | .udf ..
  | .logicalShift .. | .addSubShift .. | .addSubExt .. | .addSubCarry .. | .condCompareReg ..
  | .condCompareImm .. | .condSelect .. | .dataProc1 .. | .dataProc2 .. | .dataProc3 ..
  | .crc32 .. | .ldr .. | .ldrLit .. | .ldp .. | .ldnp .. | .ldxr .. | .ldxp .. | .ldapr ..
  | .prfm .. | .prfmLit .. | .ldrSimd .. | .ldrSimdLit .. | .ldpSimd .. | .ldnpSimd ..
  | .simdLd1r .. | .fmovGprVec .. | .fpDataProc1 .. | .fpDataProc2 .. | .fpCompare ..
  | .fpImm .. | .fpCondCompare .. | .fpCondSelect .. | .fpDataProc3 .. | .fpFixedConv ..
  | .simdImmShift .. | .simdInsDup .. | .simdThreeSame .. | .simdTwoRegMisc ..
  | .simdAcrossLanes .. | .simdPermute .. | .simdExt .. | .simdTbl .. | .simdAddpScalar ..
  | .simdDupScalar .. | .simdPmull .. | .simdThreeDiff .. | .aes .. | .cryptoSha2Reg ..
  | .cryptoSha3Reg .. | .cryptoSha512Reg2 .. | .cryptoSha512Reg3 .. | .cryptoSha3FourReg ..
  | .cryptoXar .. => false

/-- Pre-state write ranges for non-`svc #0` instructions on `FastState`, computed before
    `fastExecInst inst s` so `s` is not retained across `fastExecInst` (`RC(s) = 1`).
    Exhaustive over every `Instr` constructor (no wildcard). -/
@[inline] def nonSvcWriteRanges (inst : Instr) (s : FastState) : List (BitVec 64 × Nat) :=
  let ea (a : AddrMode) : BitVec 64 := (fastEvalAddrMode s a).1.toBitVec
  let r (x : Reg) : BitVec 64 := (s.readReg64 x).toBitVec
  match inst with
  | .str w _ addr => [(ea addr, w.bytes)]
  | .stp sf _ _ addr => [(ea addr, if sf == .W64 then 16 else 8)]
  | .stnp w rn _ _ offset => [(ea (.Offset rn offset), if w == .X64 then 16 else 8)]
  | .ldarStlr _ isLoad rn _ => if isLoad then [] else [(r rn, 16)]
  | .stxr _ _ _ rn _ | .cas _ _ _ _ rn _ | .atomicRmw _ _ _ _ _ rn _ => [(r rn, 16)]
  | .stxp _ _ _ rn _ _ | .casp _ _ _ _ _ rn _ _ => [(r rn, 32)]
  | .ldapurStlur _ opc rn _ offset => if opc == 0#2 then [(r rn + offset, 16)] else []
  | .stpSimd sz _ _ addr => [(ea addr, 2 * sz.bytes)]
  | .strSimd sz _ addr => [(ea addr, sz.bytes)]
  | .stnpSimd sz _ _ rn offset => [(r rn + offset, 2 * sz.bytes)]
  | .st1SinglePost _ _ _ _ _ rn _ => [(r rn, 16)]
  | .simdLdSt1Single isLoad _ _ _ _ _ _ rn _ => if isLoad then [] else [(r rn, 16)]
  | .simdLdSt1Multi isLoad _ _ nregs rn _ _ _ => if isLoad then [] else [(r rn, nregs * 16)]
  | .simdLdStMulti isLoad _ _ selem rn _ _ _ => if isLoad then [] else [(r rn, selem * 16)]
  | .dcZva rt => [(r rt &&& ~~~63#64, 64)]
  -- Everything else (including `.system`) writes no non-syscall memory (enumerated, no wildcard).
  | .system ..
  | .adr .. | .addSubImm .. | .logicalImm .. | .moveWide .. | .bitfield .. | .extr ..
  | .b .. | .bl .. | .bCond .. | .cbz .. | .tbz .. | .br .. | .blr .. | .ret .. | .nop
  | .hint .. | .barrier .. | .sysReg .. | .udf ..
  | .logicalShift .. | .addSubShift .. | .addSubExt .. | .addSubCarry .. | .condCompareReg ..
  | .condCompareImm .. | .condSelect .. | .dataProc1 .. | .dataProc2 .. | .dataProc3 ..
  | .crc32 .. | .ldr .. | .ldrLit .. | .ldp .. | .ldnp .. | .ldxr .. | .ldxp .. | .ldapr ..
  | .prfm .. | .prfmLit .. | .ldrSimd .. | .ldrSimdLit .. | .ldpSimd .. | .ldnpSimd ..
  | .simdLd1r .. | .fmovGprVec .. | .fpDataProc1 .. | .fpDataProc2 .. | .fpCompare ..
  | .fpImm .. | .fpCondCompare .. | .fpCondSelect .. | .fpDataProc3 .. | .fpFixedConv ..
  | .simdImmShift .. | .simdInsDup .. | .simdThreeSame .. | .simdTwoRegMisc ..
  | .simdAcrossLanes .. | .simdPermute .. | .simdExt .. | .simdTbl .. | .simdAddpScalar ..
  | .simdDupScalar .. | .simdPmull .. | .simdThreeDiff .. | .aes .. | .cryptoSha2Reg ..
  | .cryptoSha3Reg .. | .cryptoSha512Reg2 .. | .cryptoSha512Reg3 .. | .cryptoSha3FourReg ..
  | .cryptoXar .. => []

/-- O(len) patch construction for `s'.mem = s.mem.writeBytes ea chunk` (`SYS_READ` / `SYS_PREAD64`),
    reading bytes from `chunk` and permissions from `s.mem` (avoiding an O(len^2) walk of the
    `write8` closure chain in `s'.mem` when `len` is multi-kilobyte). -/
def extractWriteBytesPatch (preMem : Memory) (ea : BitVec 64) (chunk : List (BitVec 8)) : Patch :=
  let len := chunk.length
  let eaU := ea.toNat.toUInt64
  let bytes := chunk.foldl (fun acc b => acc.push b.toNat.toUInt8)
    (ByteArray.emptyWithCapacity (2 * len))
  let data := loopN len 0 bytes fun i acc =>
    acc.push (encodeCodeClearLazy (preMem.cells (eaU + i.toUInt64).toBitVec))
  { ea, len, data }

/-- O(len) patch construction for `SYS_GETRANDOM`, reading bytes from `s.oracle.getrandom` and
    permissions from `s.mem`. -/
def extractGetrandomPatch (preMem : Memory) (s : State) (ea : BitVec 64) (len : Nat) : Patch :=
  let eaU := ea.toNat.toUInt64
  let bytes := loopN len 0 (ByteArray.emptyWithCapacity (2 * len)) fun i acc =>
    acc.push (s.oracle.getrandom s.oracleIdx i).toNat.toUInt8
  let data := loopN len 0 bytes fun i acc =>
    acc.push (encodeCodeClearLazy (preMem.cells (eaU + i.toUInt64).toBitVec))
  { ea, len, data }

/-- Compute the `Patch` list for `execInst inst s = s'` (when `s'.status == .Running`). -/
def stepPatches (inst : Instr) (s s' : State) : Option (List Patch) :=
  if isSvc0 inst then
    match Sys.ofNr? (s.readReg64 .x8) with
    | none => none
    | some sc =>
      let ret := s'.readReg64 .x0
      let failed := ret.slt 0#64
      match sc with
      | .read | .pread64 =>
        if failed || ret == 0#64 then some []
        else
          let fd := (s.readReg32 .x0).zeroExtend 64
          match s.fs.fds fd with
          | some desc =>
            let pos := if sc == .pread64 then (s.readReg64 .x3).toNat else desc.offset
            let chunk := ((s.fs.fdBytes desc).drop pos).take ret.toNat
            some [extractWriteBytesPatch s.mem (s.readReg64 .x1) chunk]
          | none =>
            some [{ ea := s.readReg64 .x1, len := ret.toNat,
                    data := extractRange s'.mem (s.readReg64 .x1) ret.toNat }]
      | .getrandom =>
        if failed || ret == 0#64 then some []
        else some [extractGetrandomPatch s.mem s (s.readReg64 .x0) ret.toNat]
      | _ =>
        some ((syscallWriteRanges sc s s').map fun (ea, len) =>
          { ea, len, data := extractRange s'.mem ea len })
  else
    (instWriteRanges inst s s').map fun ranges =>
      ranges.map fun (ea, len) => { ea, len, data := extractRange s'.mem ea len }

/-- Cached `Program.pureMem.fetchMem` entry for a 4-byte-aligned word in an executable segment. -/
inductive IcacheEntry
  | unknown
  | invalid
  | decoded (inst : Instr) (tagIdx : Nat)
  deriving Inhabited

/-- Lazy array-backed instruction decode cache over the executable segment. -/
structure Icache where
  start   : Nat := 0
  stop    : Nat := 0
  entries : Array IcacheEntry := #[]

/-- Build an `Icache` for the executable segment containing `img.entry`. -/
def mkIcache (img : ElfImage) : Icache :=
  match img.segments.find? (fun r => r.perm.x && r.start.toNat ≤ img.entry.toNat &&
      img.entry.toNat < r.start.toNat + r.bytes.length) with
  | some seg =>
    let start := seg.start.toNat
    let len := seg.bytes.length
    { start, stop := start + len, entries := Array.replicate (len / 4) .unknown }
  | none => {}

/-- Fetch and decode at `pc`, consulting `ic` when `pc` is 4-byte-aligned inside the cached
    executable segment and its page has not been modified in `st`. -/
@[inline] def fetchCached (pc : UInt64) (mem : Memory) (st : Store) (ic : Icache) :
    Option (Instr × Nat) × Icache :=
  let pcNat := pc.toNat
  if pcNat &&& 3 == 0 && ic.start ≤ pcNat && pcNat + 4 ≤ ic.stop &&
      !st.containsPage (pcNat >>> pageBits) then
    let idx := (pcNat - ic.start) >>> 2
    match ic.entries[idx]! with
    | .decoded inst tagIdx => (some (inst, tagIdx), ic)
    | .invalid => (none, ic)
    | .unknown =>
      match Program.pureMem.fetchMem mem pc.toBitVec with
      | none => (none, { ic with entries := ic.entries.set! idx .invalid })
      | some inst =>
        let tagIdx := instTagIdx inst
        (some (inst, tagIdx), { ic with entries := ic.entries.set! idx (.decoded inst tagIdx) })
  else
    match Program.pureMem.fetchMem mem pc.toBitVec with
    | none => (none, ic)
    | some inst => (some (inst, instTagIdx inst), ic)

/-- Runner statistics. -/
structure Stats where
  steps    : Nat := 0
  writes   : Nat := 0
  patched  : Nat := 0
  opened   : List String := []
  opCounts : Array Nat := Array.replicate instTagNames.size 0

/-- Increment `steps` and `opCounts[tagIdx]` in place, consuming `stats` so `RC(opCounts) = 1`. -/
@[inline] def Stats.bumpStep (stats : Stats) (tagIdx : Nat) : Stats :=
  match stats with
  | ⟨steps, writes, patched, opened, opCounts⟩ =>
    ⟨steps + 1, writes, patched, opened, opCounts.modify tagIdx (· + 1)⟩

/-- Increment `writes` and add `patchedBytes` in place. -/
@[inline] def Stats.bumpWrite (stats : Stats) (patchedBytes : Nat) : Stats :=
  match stats with
  | ⟨steps, writes, patched, opened, opCounts⟩ =>
    ⟨steps, writes + 1, patched + patchedBytes, opened, opCounts⟩

/-- Execute a non-`svc #0` memory-writing instruction `inst` on `s` and apply its store to `st`.
    Common non-page-straddling stores (`.str`, `.stp`, `.stnp`, `.strSimd`, `.stpSimd`) use
    `fastExecInstSkipMem` + `Store.writeData16`/`Store.writeData32` to avoid allocating `Memory.write8`
    closures. Returns `(s', st', bytesPatched)`. -/
@[inline] def execNonSvcWrite (base : BitVec 64 → Cell) (inst : Instr) (s : FastState) (st : Store) :
    FastState × Store × Nat :=
  let fallback (inst : Instr) (s : FastState) (st : Store) : FastState × Store × Nat :=
    let ranges := nonSvcWriteRanges inst s
    let s' := fastExecInst inst s
    if s'.status != .Running then (s', st, 0)
    else
      match ranges with
      | [] => (s', st, 0)
      | [(ea, len)] =>
        let p : Patch := { ea, len, data := extractRange s'.mem ea len }
        let s' := s'.setMem Memory.empty
        let st := Store.applyPatch base st p
        (s'.setMem (Store.mem base st), st, len)
      | rs =>
        let ps := rs.map fun (ea, len) => { ea, len, data := extractRange s'.mem ea len }
        let s' := s'.setMem Memory.empty
        let st := ps.foldl (Store.applyPatch base) st
        let patched := ps.foldl (· + ·.len) 0
        (s'.setMem (Store.mem base st), st, patched)
  match inst with
  | .str sz rt addr =>
    let eaU := (fastEvalAddrMode s addr).1
    let len := sz.bytes
    if (eaU.toNat &&& 4095) + len ≤ pageSize then
      let bLo := s.readReg64 rt
      let s' := fastExecStrSkipMem sz rt addr s
      if s'.status != .Running then (s', st, 0)
      else
        let st := Store.writeData16 base st eaU len bLo 0
        (s'.setMem (Store.mem base st), st, len)
    else fallback inst s st
  | .stp w rt1 rt2 addr =>
    let eaU := (fastEvalAddrMode s addr).1
    let len := if w == .W64 then 16 else 8
    if (eaU.toNat &&& 4095) + len ≤ pageSize then
      let v1 := s.readReg64 rt1
      let v2 := s.readReg64 rt2
      let bLo := match w with | .W32 => (v1 &&& (0xFFFFFFFF : UInt64)) ||| (v2 <<< 32) | .W64 => v1
      let bHi := match w with | .W32 => 0 | .W64 => v2
      let s' := fastExecStpSkipMem w rt1 rt2 addr s
      if s'.status != .Running then (s', st, 0)
      else
        let st := Store.writeData16 base st eaU len bLo bHi
        (s'.setMem (Store.mem base st), st, len)
    else fallback inst s st
  | .stnp sz rn rt1 rt2 offset =>
    let w : RegWidth := match sz with | .X64 => .W64 | _ => .W32
    let addr : AddrMode := .Offset rn offset
    let eaU := (fastEvalAddrMode s addr).1
    let len := if w == .W64 then 16 else 8
    if (eaU.toNat &&& 4095) + len ≤ pageSize then
      let v1 := s.readReg64 rt1
      let v2 := s.readReg64 rt2
      let bLo := match w with | .W32 => (v1 &&& (0xFFFFFFFF : UInt64)) ||| (v2 <<< 32) | .W64 => v1
      let bHi := match w with | .W32 => 0 | .W64 => v2
      let s' := fastExecStpSkipMem w rt1 rt2 addr s
      if s'.status != .Running then (s', st, 0)
      else
        let st := Store.writeData16 base st eaU len bLo bHi
        (s'.setMem (Store.mem base st), st, len)
    else fallback inst s st
  | .strSimd sz vt addr =>
    let eaU := (fastEvalAddrMode s addr).1
    let len := sz.bytes
    if (eaU.toNat &&& 4095) + len ≤ pageSize then
      let v := s.readVReg128 vt
      let bLo := (v.extractLsb' 0 64).toNat.toUInt64
      let bHi := (v.extractLsb' 64 64).toNat.toUInt64
      let s' := fastExecStrSimdSkipMem sz vt addr s
      if s'.status != .Running then (s', st, 0)
      else
        let st := Store.writeData16 base st eaU len bLo bHi
        (s'.setMem (Store.mem base st), st, len)
    else fallback inst s st
  | .stpSimd sz vt1 vt2 addr =>
    let eaU := (fastEvalAddrMode s addr).1
    let len := 2 * sz.bytes
    if (eaU.toNat &&& 4095) + len ≤ pageSize then
      let v1 := s.readVReg128 vt1
      let v2 := s.readVReg128 vt2
      let v1Lo := (v1.extractLsb' 0 64).toNat.toUInt64
      let v2Lo := (v2.extractLsb' 0 64).toNat.toUInt64
      let v1Hi := (v1.extractLsb' 64 64).toNat.toUInt64
      let v2Hi := (v2.extractLsb' 64 64).toNat.toUInt64
      let s' := fastExecStpSimdSkipMem sz vt1 vt2 addr s
      if s'.status != .Running then (s', st, 0)
      else
        let st :=
          match sz with
          | .B8  => Store.writeData16 base st eaU 2 ((v1Lo &&& (0xFF : UInt64)) ||| ((v2Lo &&& (0xFF : UInt64)) <<< 8)) 0
          | .H16 => Store.writeData16 base st eaU 4 ((v1Lo &&& (0xFFFF : UInt64)) ||| ((v2Lo &&& (0xFFFF : UInt64)) <<< 16)) 0
          | .S32 => Store.writeData16 base st eaU 8 ((v1Lo &&& (0xFFFFFFFF : UInt64)) ||| (v2Lo <<< 32)) 0
          | .D64 => Store.writeData16 base st eaU 16 v1Lo v2Lo
          | .Q128 => Store.writeData32 base st eaU v1Lo v1Hi v2Lo v2Hi
        (s'.setMem (Store.mem base st), st, len)
    else fallback inst s st
  | _ => fallback inst s st

/-- Run up to `fuel` steps from `s : FastState` (whose `mem` is `Store.mem base st`), refining
    `runStepsPure` via `fastExecInst_toState`. -/
def runLoop (base : BitVec 64 → Cell) :
    Nat → FastState → Store → Icache → Stats → FastState × Store × Stats
  | 0, s, st, _, stats => (s, st, stats)
  | fuel + 1, s, st, ic, stats =>
    if s.status != .Running then (s, st, stats)
    else
      let (fetched?, ic) := fetchCached s.pc s.mem st ic
      match fetched? with
      | none =>
        let stats := { stats with steps := stats.steps + 1 }
        (s.setStatus .Halted, st, stats)
      | some (inst, tagIdx) =>
        let stats := stats.bumpStep tagIdx
        if !mayWriteMem inst then
          let s' := fastExecInst inst s
          runLoop base fuel s' st ic stats
        else if !isSvc0 inst then
          let (s', st, patchedBytes) := execNonSvcWrite base inst s st
          if s'.status != .Running then (s', st, stats)
          else if patchedBytes == 0 then
            runLoop base fuel s' st ic stats
          else
            runLoop base fuel s' st ic (stats.bumpWrite patchedBytes)
        else
          let sPre := s.toState
          let s' := fastExecInst inst s
          let sPost := s'.toState
          if s'.status != .Running then
            (s', st, stats)
          else
            let opened : Option String :=
              if sPre.readReg64 .x8 == SYS_OPENAT && !(sPost.readReg64 .x0).slt 0#64 then
                (sPost.fs.fds (sPost.readReg64 .x0)).map (·.path)
              else none
            let stats := match opened with
              | some p => { stats with opened := p :: stats.opened }
              | none => stats
            match stepPatches inst sPre sPost with
            | none => (s'.setStatus (.Exception "elf_run: unclassified syscall"), st, stats)
            | some [] => runLoop base fuel s' st ic stats
            | some ps =>
              let s' := s'.setMem Memory.empty
              let st := ps.foldl (Store.applyPatch base) st
              let patchedBytes := ps.foldl (· + ·.len) 0
              runLoop base fuel (s'.setMem (Store.mem base st)) st ic (stats.bumpWrite patchedBytes)

/-- Run up to `fuel` steps from `s : State` (whose `mem` is `Store.mem base st`) using the
    trusted `Program.pureMem.fetchMem` + `Arm64.execInst` evaluator and `stepPatches` (reading
    written bytes back from `s'.mem` via `extractRange`, without `FastState`, `fastExecInst`,
    `fastExecInstSkipMem`, `Store.writeData16`/`32`, or `Icache`). -/
def runLoopTrusted (base : BitVec 64 → Cell) :
    Nat → State → Store → Stats → State × Store × Stats
  | 0, s, st, stats => (s, st, stats)
  | fuel + 1, s, st, stats =>
    if s.status != .Running then (s, st, stats)
    else
      match Program.pureMem.fetchMem s.mem s.pc with
      | none =>
        let stats := { stats with steps := stats.steps + 1 }
        ({ s with status := .Halted }, st, stats)
      | some inst =>
        let stats := stats.bumpStep (instTagIdx inst)
        let s' := execInst inst s
        if !mayWriteMem inst then
          runLoopTrusted base fuel s' st stats
        else if s'.status != .Running then
          (s', st, stats)
        else
          let opened : Option String :=
            if isSvc0 inst && s.readReg64 .x8 == SYS_OPENAT && !(s'.readReg64 .x0).slt 0#64 then
              (s'.fs.fds (s'.readReg64 .x0)).map (·.path)
            else none
          let stats := match opened with
            | some p => { stats with opened := p :: stats.opened }
            | none => stats
          match stepPatches inst s s' with
          | none => ({ s' with status := .Exception "elf_run: unclassified syscall" }, st, stats)
          | some [] => runLoopTrusted base fuel s' st stats
          | some ps =>
            let s' := { s' with mem := Memory.empty }
            let st := ps.foldl (Store.applyPatch base) st
            let patchedBytes := ps.foldl (· + ·.len) 0
            runLoopTrusted base fuel { s' with mem := Store.mem base st } st
              (stats.bumpWrite patchedBytes)

/-- Load and run `img` with `inputs` for up to `fuel` steps (`trusted = true` forces `runLoopTrusted`). -/
def runImage (fuel : Nat) (img : ElfImage) (inputs : ProcessInputs) (trusted : Bool := false) :
    Except String (State × Store × Stats) := do
  let (s0, base) ← load img inputs
  let st : Store := {}
  if trusted then
    pure (runLoopTrusted base fuel { s0 with mem := Store.mem base st } st {})
  else
    let ic := mkIcache img
    let (sf, st, stats) := runLoop base fuel (FastState.ofState { s0 with mem := Store.mem base st }) st ic {}
    pure (sf.toState, st, stats)

/-! ## JSON I/O -/

def hexChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

def bytesToHex (bs : List (BitVec 8)) : String :=
  String.ofList (bs.foldr (fun b acc => hexChar (b.toNat / 16) :: hexChar (b.toNat % 16) :: acc) [])

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

def statusJson (st : ExecStatus) : Json :=
  match st with
  | .Running => "running"
  | .Halted => "halted"
  | .Exited _ => "exited"
  | .Signaled sig => s!"signaled:{sig.toNat}"
  | .Panicked => "panicked"
  | .OutOfMemory => "out_of_memory"
  | .Exception msg => Json.str s!"exception: {msg}"

/-- Parse a request (see the module docstring) into `ProcessInputs` and `max_steps`. -/
def parseRequest (j : Json) : Except String (ProcessInputs × Nat) := do
  let argv ← (j.getObjValAs? (List String) "argv").toOption.getD ["prog"] |> pure
  let envp := (j.getObjValAs? (List String) "envp").toOption.getD []
  let stdin ← hexToBytes ((j.getObjValAs? String "stdin_hex").toOption.getD "")
  let filesJ := (j.getObjValAs? (Array Json) "files").toOption.getD #[]
  let files ← filesJ.toList.mapM fun f => do
    let p ← f.getObjValAs? String "path"
    let h ← f.getObjValAs? String "hex"
    pure (p, ← hexToBytes h)
  let dirs := (j.getObjValAs? (List String) "dirs").toOption.getD ["/", "/tmp"]
  let hwcap := (j.getObjValAs? Nat "hwcap").toOption
  let hwcap2 := (j.getObjValAs? Nat "hwcap2").toOption
  let defaultAuxv : AuxvConfig := {}
  let auxv : AuxvConfig :=
    { defaultAuxv with
      hwcap := match hwcap with | some v => BitVec.ofNat 64 v | none => defaultAuxv.hwcap
      hwcap2 := match hwcap2 with | some v => BitVec.ofNat 64 v | none => defaultAuxv.hwcap2 }
  let maxSteps := (j.getObjValAs? Nat "max_steps").toOption.getD 100000000
  pure ({ argv := argv.map bytesOfString, envp := envp.map bytesOfString, init := { auxv }, stdin, files, dirs },
    maxSteps)

/-- The final contents of every path that was an input file, an input directory, or opened. -/
def filesJson (inputs : ProcessInputs) (fs : FsState) (opened : List String) : Json :=
  let paths := (inputs.files.map (·.1) ++ opened.reverse ++ inputs.dirs).eraseDups
  Json.arr (paths.map fun p =>
    match fs.files p with
    | some (.file bs) => Json.mkObj [("path", p), ("kind", "file"), ("hex", bytesToHex bs)]
    | some .dir => Json.mkObj [("path", p), ("kind", "dir")]
    | none => Json.mkObj [("path", p), ("kind", "absent")]).toArray

def resultJson (inputs : ProcessInputs) (sf : State) (st : Store) (stats : Stats)
    (parseMs loadMs runMs : Nat) : Json :=
  let out := ProcessOutcome.ofState 0#64 sf
  let exitCode : Json := match sf.status with
    | .Exited c => toJson c.toNat
    | _ => Json.null
  let opCountsJson : Json := Json.mkObj <|
    ((List.range instTagNames.size).filterMap fun i =>
      let c := stats.opCounts.getD i 0
      if c > 0 then some (instTagNames[i]!, toJson c) else none)
  Json.mkObj [
    ("status", statusJson sf.status),
    ("exit_code", exitCode),
    ("steps", toJson stats.steps),
    ("pc", toJson sf.pc.toNat),
    ("stdout_hex", bytesToHex out.stdout),
    ("stderr_hex", bytesToHex out.stderr),
    ("files", filesJson inputs sf.fs stats.opened),
    ("brk", toJson sf.brk.toNat),
    ("oracle_idx", toJson sf.oracleIdx),
    ("mem_writes", toJson stats.writes),
    ("patched_bytes", toJson stats.patched),
    ("pages", toJson st.pages.size),
    ("op_counts", opCountsJson),
    ("parse_ms", toJson parseMs),
    ("load_ms", toJson loadMs),
    ("run_ms", toJson runMs)]

/-! ## `run` mode -/

def readRequest (elfPath reqPath : String) : IO (ElfImage × ProcessInputs × Nat × Nat) := do
  let t0 ← IO.monoMsNow
  let elfBytes ← IO.FS.readBinFile elfPath
  let img ← match fastParse (bytesOfByteArray elfBytes) with
    | .ok img => pure img
    | .error e => throw (IO.userError s!"ELF parse: {e}")
  let reqJ ← match Json.parse (← IO.FS.readFile reqPath) with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"request JSON: {e}")
  let (inputs, maxSteps) ← match parseRequest reqJ with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"request: {e}")
  -- Force the parse before timing the run.
  let nseg := img.segments.foldl (fun n r => n + r.bytes.length) 0
  let t1 ← IO.monoMsNow
  if nseg == 0 then IO.eprintln "elf_run: warning: image has no segment bytes"
  pure (img, inputs, maxSteps, t1 - t0)

def runMode (elfPath reqPath : String) (outPath : Option String) (trusted : Bool := false) : IO UInt32 := do
  if !checkSysExhaustive then
    IO.eprintln "elf_run: Sys does not match execSyscall's dispatch"; return 3
  let (img, inputs, maxSteps, parseMs) ← readRequest elfPath reqPath
  let t1 ← IO.monoMsNow
  let (s0, base) ← match load img inputs with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"load: {e}")
  let st0 : Store := {}
  let sInit0 := { s0 with mem := Store.mem base st0 }
  -- Force the load (the initial stack) before timing the run.
  let _ ← IO.lazyPure fun _ => sInit0.mem.cells sInit0.sp
  let t2 ← IO.monoMsNow
  let (sf, st, stats) ←
    if trusted then do
      let (sf, st, stats) ← IO.lazyPure fun _ => runLoopTrusted base maxSteps sInit0 st0 {}
      let _ ← IO.lazyPure fun _ => stats.steps
      pure (sf, st, stats)
    else do
      let ic0 := mkIcache img
      let sInit := FastState.ofState sInit0
      let (sfFast, st, stats) ← IO.lazyPure fun _ => runLoop base maxSteps sInit st0 ic0 {}
      let _ ← IO.lazyPure fun _ => stats.steps
      pure (sfFast.toState, st, stats)
  let t3 ← IO.monoMsNow
  let j := resultJson inputs sf st stats parseMs (t2 - t1) (t3 - t2)
  match outPath with
  | some p => IO.FS.writeFile p (j.pretty ++ "\n")
  | none => IO.println j.compress
  return 0

/-! ## `refcheck` mode -/

/-- Compare the fast runner's state after `n` steps against `runSteps Program.pureMem` (and
    `runLoopTrusted`), or against `runLoopTrusted` on full runs when `trustedLoopOnly = true`:
    control registers, `fpsr`, all general and vector registers, process fields, `stdout`/`stderr`/
    `files`, and memory across every page materialized by either runner plus the top 64 KiB of the
    stack and the first 64 KiB of `[brkStart, brk)`. -/
def refcheckMode (elfPath reqPath : String) (n : Nat) (trustedLoopOnly : Bool := false) : IO UInt32 := do
  let (img, inputs, _, _) ← readRequest elfPath reqPath
  let (s0, base) ← match load img inputs with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"load: {e}")
  let st0 : Store := {}
  let ic0 := mkIcache img
  let (sfFast, st, stats) :=
    runLoop base n (FastState.ofState { s0 with mem := Store.mem base st0 }) st0 ic0 {}
  let sf := sfFast.toState
  let (srTrusted, stTrusted, statsTrusted) :=
    runLoopTrusted base n { s0 with mem := Store.mem base st0 } st0 {}
  let sr ←
    if trustedLoopOnly then pure srTrusted
    else do
      let sRef0 ← match img.loadState inputs with
        | .ok s => pure s
        | .error e => throw (IO.userError s!"loadState: {e}")
      pure (runStepsPure n sRef0)
  let mut bad : Array String := #[]
  if stats.steps != statsTrusted.steps then bad := bad.push s!"steps {stats.steps} vs {statsTrusted.steps}"
  if sf.pc != sr.pc || sf.pc != srTrusted.pc then bad := bad.push s!"pc {sf.pc.toNat} vs {sr.pc.toNat}"
  if sf.sp != sr.sp || sf.sp != srTrusted.sp then bad := bad.push "sp"
  if sf.pstate != sr.pstate || sf.pstate != srTrusted.pstate then bad := bad.push "pstate"
  if sf.fpsr != sr.fpsr || sf.fpsr != srTrusted.fpsr then bad := bad.push "fpsr"
  if sf.status != sr.status || sf.status != srTrusted.status then bad := bad.push "status"
  if sf.brk != sr.brk || sf.brk != srTrusted.brk then bad := bad.push "brk"
  if sf.oracleIdx != sr.oracleIdx || sf.oracleIdx != srTrusted.oracleIdx then bad := bad.push "oracleIdx"
  if sf.tpidrEl0 != sr.tpidrEl0 || sf.tpidrEl0 != srTrusted.tpidrEl0 then bad := bad.push "tpidrEl0"
  if sf.trace.length != sr.trace.length || sf.trace.length != srTrusted.trace.length then
    bad := bad.push "trace length"
  let outFast := ProcessOutcome.ofState 0#64 sf
  let outRef := ProcessOutcome.ofState 0#64 sr
  if outFast.stdout != outRef.stdout then bad := bad.push "stdout"
  if outFast.stderr != outRef.stderr then bad := bad.push "stderr"
  if filesJson inputs sf.fs stats.opened != filesJson inputs sr.fs statsTrusted.opened then
    bad := bad.push "files"
  for i in [0:32] do
    let r := BitVec.ofNat 5 i
    if sf.regs.regs r != sr.regs.regs r || sf.regs.regs r != srTrusted.regs.regs r then
      bad := bad.push s!"x{i}"
    if sf.vregs.regs r != sr.vregs.regs r || sf.vregs.regs r != srTrusted.vregs.regs r then
      bad := bad.push s!"v{i}"
  let stackBase := inputs.init.stackTop.toNat - inputs.init.stackSize
  -- Pages compared: every page either runner materialized, the top 64 KiB of the stack and the
  -- first 64 KiB of `[brkStart, brk)`. Not the whole stack / brk / `mmap` area: each read of
  -- `runSteps`'s memory walks one closure per write so far, so enumerating megabytes is
  -- infeasible. A write by the reference outside these pages shows up only if a later read of
  -- it changes a register (compared above) or the run's result.
  let topPages := (List.range 16).filterMap fun i =>
    let pn := inputs.init.stackTop.toNat / pageSize - 1 - i
    if pn * pageSize ≥ stackBase then some pn else none
  let brkLen := Arm64.pageAlignUp sr.brk.toNat - sr.brkStart.toNat
  let brkPages := (List.range (min 16 (brkLen / pageSize))).map fun i =>
    sr.brkStart.toNat / pageSize + i
  let pagesToCheck :=
    (st.idx.toList.map (·.1) ++ stTrusted.idx.toList.map (·.1) ++ topPages ++ brkPages).eraseDups
  let mut checked := 0
  let mut memBad := 0
  for pn in pagesToCheck do
    for i in [0:pageSize] do
      let a := BitVec.ofNat 64 (pn * pageSize + i)
      checked := checked + 1
      if sf.mem.cells a != sr.mem.cells a || sf.mem.cells a != srTrusted.mem.cells a then
        if memBad < 5 then bad := bad.push s!"mem {a.toNat}"
        memBad := memBad + 1
  IO.println (Json.mkObj [("steps", toJson stats.steps), ("ref_status", statusJson sr.status),
    ("status", statusJson sf.status), ("bytes_checked", toJson checked),
    ("mem_mismatches", toJson memBad), ("pages", toJson st.pages.size),
    ("mismatches", toJson bad.toList)]).compress
  return (if bad.isEmpty then 0 else 1)

/-! ## `selftest` mode -/

/-- xorshift64* PRNG. -/
structure Rng where
  x : UInt64

def Rng.next (g : Rng) : UInt64 × Rng :=
  let x := g.x
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x * 0x2545F4914F6CDD1D, ⟨x⟩)

def Rng.below (g : Rng) (n : Nat) : Nat × Rng :=
  let (v, g) := g.next
  (v.toNat % n, g)

/-- Fuzz window: `[winLo, winHi)` is compared; `[rwLo, rwHi)` and `[rw2Lo, rw2Hi)` are mapped
    read-write, `[rwHi, rw2Lo)` is a hole (`mmap` target), the rest unmapped. -/
def winLo : Nat := 0x20000
def rwLo : Nat := 0x21000
def rwHi : Nat := 0x23000
def rw2Lo : Nat := 0x24000
def rw2Hi : Nat := 0x25000
def winHi : Nat := 0x26000

/-- Base memory of a trial: two read-write ranges, the path `"/tmp\0"` at `rwLo`, and random
    bytes in the first 256 bytes after it. -/
def fuzzBase (seed : Nat) : BitVec 64 → Cell :=
  let m0 := (Memory.empty.mapZero (BitVec.ofNat 64 rwLo) (rwHi - rwLo)).mapZero
    (BitVec.ofNat 64 rw2Lo) (rw2Hi - rw2Lo)
  let path := bytesOfString "/tmp" ++ [0#8]
  let m1 := m0.writeBytes (BitVec.ofNat 64 rwLo) path
  let rnd := (List.range 256).map fun i => BitVec.ofNat 8 ((seed * 2654435761 + i * 40503) % 256)
  let m2 := m1.writeBytes (BitVec.ofNat 64 (rwLo + 16)) rnd
  m2.cells

/-- Precompute `fuzzBase seed0` over `[winLo, winHi)` once at the start of `selftestMode` so
    `flatBaseArr` only updates the 256 seed-dependent bytes at `[rwLo + 16, rwLo + 272)`. -/
@[noinline] def mkFlatBaseTemplate (seed0 : Nat) : Array Cell :=
  let f := fuzzBase seed0
  Array.ofFn fun (i : Fin (winHi - winLo)) => f (BitVec.ofNat 64 (winLo + i.val))

/-- `fuzzBase seed` as a flat array over the fuzz window (`fuzzBase` has no cell outside it), so a
    lookup is O(1) instead of a walk through its ~260 `writeBytes` layers. -/
@[noinline] def flatBaseArr (tmpl : Array Cell) (seed : Nat) : Array Cell :=
  loopN 256 0 tmpl fun i arr =>
    let b := (seed * 2654435761 + i * 40503) % 256
    arr.set! (rwLo + 16 - winLo + i) cellTable[rwCellCode * 256 + b]!

/-- The cells of `flatBaseArr seed` (= `fuzzBase seed` everywhere). -/
def flatBase (arr : Array Cell) : BitVec 64 → Cell := fun a =>
  let n := a.toNat
  if winLo ≤ n && n < winHi then arr[n - winLo]! else none

/-- A random pointer into the window (mostly into mapped memory). -/
def randPtr (g : Rng) : BitVec 64 × Rng :=
  let (k, g) := g.below 10
  let (o, g) := g.below (rwHi - rwLo)
  let (o2, g) := g.below (winHi - winLo)
  let p := if k < 7 then rwLo + o else if k < 9 then rw2Lo + o % (rw2Hi - rw2Lo) else winLo + o2
  (BitVec.ofNat 64 p, g)

/-- Syscall numbers and argument shapes for the syscall trials. -/
def sysNrs : List (BitVec 64) :=
  [SYS_IOCTL, SYS_OPENAT, SYS_CLOSE, SYS_LSEEK, SYS_READ, SYS_WRITE, SYS_READV, SYS_WRITEV,
   SYS_PREAD64, SYS_PPOLL,
   SYS_FSTAT, SYS_CLOCK_GETTIME, SYS_BRK, SYS_MUNMAP, SYS_MREMAP, SYS_MMAP, SYS_MPROTECT,
   SYS_MADVISE, SYS_GETRANDOM, SYS_SET_TID_ADDRESS, SYS_SCHED_GETAFFINITY, SYS_GETPID, SYS_GETTID,
   SYS_SIGALTSTACK, SYS_RT_SIGPROCMASK, SYS_RT_SIGACTION, SYS_TKILL, SYS_TGKILL, SYS_FCNTL]

/-- A random instruction word: uniform, forced into the load/store class (`op0 = x1x0`), a
    syscall `svc #0`, or `dc zva`. -/
def randWord (g : Rng) : BitVec 32 × Rng :=
  let (k, g) := g.below 20
  let (v, g) := g.next
  let w := v.toNat % 2 ^ 32
  if k < 6 then (BitVec.ofNat 32 w, g)
  else if k < 17 then (BitVec.ofNat 32 ((w &&& 0xF5FFFFFF) ||| 0x08000000), g)
  else if k < 19 then (0xD4000001#32, g)
  else (BitVec.ofNat 32 (0xD50B7420 ||| (w % 31)), g)

/-- The `Instr` constructor name of `inst`. -/
def opName (inst : Instr) : String :=
  instTagNames[instTagIdx inst]!

/-- One trial: build a random state over the fuzz window (with some pages already in the
    store), execute `inst`, patch the store with `instWriteRanges`, and check that the store now
    agrees with `execInst`'s memory on the whole window. Returns (agrees, memory changed, still
    running). -/
def trial (tmpl : Array Cell) (seed : Nat) (g : Rng) (inst : Instr) : Bool × Bool × Bool × Rng :=
  let base := flatBase (flatBaseArr tmpl seed)
  -- Pre-materialize a random subset of the window's pages.
  let (mask, g) := g.next
  let st0 := loopN ((winHi - winLo) / pageSize) 0 ({} : Store) fun i st =>
    if (mask >>> i.toUInt64) &&& 1 == 1 then
      st.withPage base ((winLo >>> pageBits) + i) id
    else st
  let mem0 := Store.mem base st0
  -- Registers: mostly pointers into the window, small values otherwise.
  let (regs, g) := loopN 32 0 ((#[] : Array (BitVec 64)), g) fun _ (acc, g) =>
    let (k, g) := g.below 4
    let (p, g) := randPtr g
    let (v, g) := g.next
    let (sm, g) := g.below 64
    (acc.push (if k < 2 then p else if k == 2 then BitVec.ofNat 64 sm else BitVec.ofNat 64 v.toNat), g)
  let (vregs, g) := loopN 32 0 ((#[] : Array (BitVec 128)), g) fun _ (acc, g) =>
    let (a, g) := g.next
    let (b, g) := g.next
    (acc.push (BitVec.ofNat 128 (a.toNat * 2 ^ 64 + b.toNat)), g)
  let (spP, g) := randPtr g
  let (x8k, g) := g.below (sysNrs.length + 3)
  let x8 := (sysNrs[x8k]?).getD (BitVec.ofNat 64 (x8k * 7 + 500))
  let (fdk, g) := g.below 4
  let (cnt, g) := g.below 300
  let (oracleSlot, g) := g.below 2
  let (brkk, g) := g.below 3
  let (lenk, g) := g.below 3
  let regs := regs.set! 8 x8
  -- Syscall-friendly argument shapes in x0..x3 half of the time.
  let (shape, g) := g.below 2
  let regs := if shape == 0 then regs else
    let regs := regs.set! 0 (if fdk == 0 then 0#64 else if fdk == 1 then 3#64 else regs[0]!)
    let regs := regs.set! 2 (if x8 == SYS_MMAP then regs[2]! else BitVec.ofNat 64 cnt)
    let regs := if x8 == SYS_MMAP then
      let r := (regs.set! 1 (BitVec.ofNat 64 (lenk * 4096 + 1))).set! 2
        (if oracleSlot == 0 then 3#64 else 0#64)
      let r := r.set! 3 (if brkk == 0 then 0x32#64 else 0x22#64)
      let r := r.set! 0 (BitVec.ofNat 64 (rwHi + 4096 * (cnt % 2)))
      r.set! 5 0#64
    else regs
    let regs := if x8 == SYS_MUNMAP || x8 == SYS_MPROTECT || x8 == SYS_MADVISE then
      let r := regs.set! 0 (BitVec.ofNat 64 (winLo + 4096 * (cnt % 6)))
      let r := r.set! 1 (BitVec.ofNat 64 (lenk * 4096 + cnt % 3))
      r.set! 2 (if x8 == SYS_MADVISE then (if cnt % 3 == 0 then 4#64 else if cnt % 3 == 1 then 8#64 else 0#64)
        else (if cnt % 2 == 0 then 0#64 else 3#64))
    else regs
    let regs := if x8 == SYS_BRK then
      regs.set! 0 (BitVec.ofNat 64 (if brkk == 0 then rwHi + cnt * 13
        else if brkk == 1 then rwHi - 4096 + cnt else 0))
    else regs
    let regs := if x8 == SYS_PPOLL then
      let r := regs.set! 0 (BitVec.ofNat 64 (rwLo + 0x200))
      let r := r.set! 1 (BitVec.ofNat 64 (cnt % 4))
      let r := r.set! 2 (BitVec.ofNat 64 (rwLo + 0x220))
      let r := r.set! 3 0#64
      r.set! 4 8#64
    else regs
    let regs := if x8 == SYS_MREMAP then
      let r := regs.set! 0 (BitVec.ofNat 64 rwLo)
      let r := r.set! 1 4096#64
      let r := r.set! 2 (BitVec.ofNat 64 ((lenk % 2 + 1) * 4096))
      r.set! 3 1#64
    else regs
    regs
  let fuzzInputs : ProcessInputs :=
    { stdin := (List.range 200).map fun i => BitVec.ofNat 8 (i * 7)
      files := [("tmp/f", (List.range 50).map fun i => BitVec.ofNat 8 i)] }
  let fuzzOracle : Oracle :=
    { mmap := fun _ => BitVec.ofNat 64 rwHi
      getrandom := fun i j => BitVec.ofNat 8 (i + 3 * j) }
  let s : State :=
    { regs := ⟨fun i => regs[i.toNat]!⟩
      vregs := ⟨fun i => vregs[i.toNat]!⟩
      sp := spP &&& ~~~15#64
      pc := 0x10000#64
      mem := mem0
      brkStart := BitVec.ofNat 64 rwLo
      brk := BitVec.ofNat 64 rwHi
      fs := initFsState fuzzInputs
      oracle := fuzzOracle }
  let sFast := FastState.ofState s
  let sFast' := fastExecInst inst sFast
  let s' := execInst inst s  -- = Program.pureMem.evalInst inst s (`evalInst_pureMem`)
  let sf := sFast'.toState
  let regsOk := loopN 32 0
    (sf.pc == s'.pc && sf.sp == s'.sp && sf.pstate == s'.pstate &&
     sf.status == s'.status && sf.fpsr == s'.fpsr)
    fun i ok =>
      let r := BitVec.ofNat 5 i
      ok && sf.regs.regs r == s'.regs.regs r && sf.vregs.regs r == s'.vregs.regs r
  let running := s'.status == .Running
  if !running then (regsOk, false, false, g)
  else
    let st1? : Option Store :=
      if !mayWriteMem inst then some st0
      else if !isSvc0 inst then
        some (execNonSvcWrite base inst sFast st0).2.1
      else
        (stepPatches inst s sf).map fun patches =>
          patches.foldl (Store.applyPatch base) st0
    match st1? with
    | none => (false, true, true, g)
    | some st1 =>
      let mem1 := Store.mem base st1
      let (ok, changed) := loopN (winHi - winLo) 0 (regsOk, false) fun i (ok, ch) =>
        let a := BitVec.ofNat 64 (winLo + i)
        let post := s'.mem.cells a
        (ok && mem1.cells a == post, ch || post != mem0.cells a)
      (ok, changed, true, g)

def selftestMode (trials seed : Nat) : IO UInt32 := do
  if !checkSysExhaustive then
    IO.eprintln "elf_run: Sys does not match execSyscall's dispatch"; return 3
  let tmpl := mkFlatBaseTemplate seed
  let mut g : Rng := ⟨(seed.toUInt64 * 0x9E3779B97F4A7C15) ||| 1⟩
  let mut decoded := 0
  let mut running := 0
  let mut changed := 0
  let mut failures : Array String := #[]
  let mut ops : Std.HashMap String (Nat × Nat) := {}
  for t in [0:trials] do
    let (w, g1) := randWord g
    g := g1
    match decode w with
    | none => pure ()
    | some inst =>
      decoded := decoded + 1
      let (ok, ch, run, g2) := trial tmpl (seed + t) g inst
      g := g2
      if run then running := running + 1
      if ch then changed := changed + 1
      let name := opName inst
      let (a, b) := ops.getD name (0, 0)
      ops := ops.insert name (a + 1, b + (if ch then 1 else 0))
      if !ok then
        failures := failures.push s!"trial {t}: word {w.toNat} {name}"
    if (t + 1) % 500 == 0 then
      IO.eprintln s!"selftest: {t + 1}/{trials} trials, {failures.size} failures"
  let opList := ops.toList.toArray.qsort (fun a b => a.1 < b.1)
  IO.println (Json.mkObj [("trials", toJson trials), ("decoded", toJson decoded),
    ("running", toJson running), ("mem_changed", toJson changed),
    ("failures", toJson failures.size), ("first_failures", toJson (failures.toList.take 10)),
    ("distinct_ops", toJson opList.size),
    ("ops", Json.mkObj (opList.toList.map fun (n, a, b) => (n, toJson [a, b])))]).pretty
  return (if failures.isEmpty then 0 else 1)

/-! ## `decodescan` mode -/

/-- Print `{"x_bytes": n, "words": n, "undecodable": n}` on stdout and one `<addr hex> <word hex>`
    line per 4-byte-aligned word of an executable segment that `decode` rejects (the run stops
    with `.Halted` at such a `pc`: `Step.fetchFail`). Read-only; no process is run. -/
def decodescanMode (elfPath outPath : String) : IO UInt32 := do
  let elfBytes ← IO.FS.readBinFile elfPath
  let img ← match fastParse (bytesOfByteArray elfBytes) with
    | .ok img => pure img
    | .error e => throw (IO.userError s!"ELF parse: {e}")
  let h ← IO.FS.Handle.mk outPath .write
  let mut xBytes := 0
  let mut words := 0
  let mut bad := 0
  for r in img.segments do
    if r.perm.x then
      let bs := r.bytes.toArray
      xBytes := xBytes + bs.size
      let start := r.start.toNat
      let first := (4 - start % 4) % 4
      let n := (bs.size - first) / 4
      for k in [0:n] do
        let i := first + 4 * k
        let w : BitVec 32 := (bs[i]!.zeroExtend 32) ||| (bs[i+1]!.zeroExtend 32 <<< 8) |||
          (bs[i+2]!.zeroExtend 32 <<< 16) ||| (bs[i+3]!.zeroExtend 32 <<< 24)
        words := words + 1
        if (decode w).isNone then
          bad := bad + 1
          h.putStrLn s!"{String.ofList (Nat.toDigits 16 (start + i))} {String.ofList (Nat.toDigits 16 w.toNat)}"
  h.flush
  IO.println (Json.mkObj [("x_bytes", toJson xBytes), ("words", toJson words),
    ("undecodable", toJson bad)]).compress
  return 0

/-- `decodescan` on a raw AArch64 code binary (offset 0 = first byte):
    one `<offset hex> <word hex>` line per 4-byte word that `decode` rejects. -/
def decoderawMode (binPath outPath : String) : IO UInt32 := do
  let bs ← IO.FS.readBinFile binPath
  let h ← IO.FS.Handle.mk outPath .write
  let n := bs.size / 4
  let mut bad := 0
  for k in [0:n] do
    let i := 4 * k
    let w : BitVec 32 := (bs[i]!.toBitVec.zeroExtend 32) ||| (bs[i+1]!.toBitVec.zeroExtend 32 <<< 8) |||
      (bs[i+2]!.toBitVec.zeroExtend 32 <<< 16) ||| (bs[i+3]!.toBitVec.zeroExtend 32 <<< 24)
    if (decode w).isNone then
      bad := bad + 1
      h.putStrLn s!"{String.ofList (Nat.toDigits 16 i)} {String.ofList (Nat.toDigits 16 w.toNat)}"
  h.flush
  IO.println (Json.mkObj [("bytes", toJson bs.size), ("words", toJson n),
    ("undecodable", toJson bad)]).compress
  return 0

/-! ## Entry point -/

def usage : String :=
  "usage: elf_run run [--trusted] <elf> <request.json> [--out <file>] [--trusted]\n" ++
  "       elf_run selftest [<trials>] [<seed>]\n" ++
  "       elf_run refcheck [--trusted] <elf> <request.json> <steps>\n" ++
  "       elf_run decodescan <elf> <out.txt>\n" ++
  "       elf_run decoderaw <code.bin> <out.txt>"

def parseRunArgs : List String → Option String → Bool → List String →
    Option (String × String × Option String × Bool)
  | [], out, trusted, [elf, req] => some (elf, req, out, trusted)
  | [], _, _, _ => none
  | "--trusted" :: rest, out, _, pos => parseRunArgs rest out true pos
  | "--out" :: p :: rest, _, trusted, pos => parseRunArgs rest (some p) trusted pos
  | "--out" :: [], _, _, _ => none
  | a :: rest, out, trusted, pos => parseRunArgs rest out trusted (pos ++ [a])

def main (args : List String) : IO UInt32 := do
  match args with
  | "run" :: rest =>
    match parseRunArgs rest none false [] with
    | some (elf, req, out, trusted) => runMode elf req out trusted
    | none => IO.eprintln usage; return 2
  | ["selftest"] => selftestMode 20000 1
  | ["selftest", n] => selftestMode n.toNat! 1
  | ["selftest", n, seed] => selftestMode n.toNat! seed.toNat!
  | ["refcheck", elf, req, n] => refcheckMode elf req n.toNat! false
  | ["refcheck", "--trusted", elf, req, n]
  | ["refcheck", elf, req, n, "--trusted"] => refcheckMode elf req n.toNat! true
  | ["decodescan", elf, out] => decodescanMode elf out
  | ["decoderaw", bin, out] => decoderawMode bin out
  | _ => IO.eprintln usage; return 2

end Testing.ElfRun
