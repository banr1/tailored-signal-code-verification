/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import VerifiedLibraries.Mallocng.Spec.PlacedLib

/-!
# Public API Specification for `musl` 1.2.5 `mallocng`

Public separation-logic specification for unmodified `musl` 1.2.5 `mallocng` over the 24-block
`VerifiedLibraries.mallocngLib` (`Obj.MultiPlacedLib`), extracted from the Rust 1.98.1
`aarch64-unknown-linux-musl` sysroot (`lib/self-contained/libc.a`, SHA-256
`b03473b6f1efb72f700f561b4407a88885b37e0edb5cdb2a64de0df5499e813f`).

The specification is parameterized by an existential allocator interface `J : MallocngIface`,
per-symbol static addresses `A : MallocngAddrs` (with no contiguity assumptions across functions or
`.rodata` tables), a byte-cost and allocation-count budget `MallocngBudget`, and a dynamic virtual
address interval list `ivs` satisfying `MallocngNoOrphanMappings`. Contracts hold across all
`Oracle.mmap` and `Oracle.mremapFail` schedules (`MallocngSvcValid`) with no external leaf hooks,
bundling interface well-formedness (`MallocngIfaceWfStmt`) and all six exported C entry points
(`malloc`, `free`, `calloc`, `realloc`, `aligned_alloc`, `posix_memalign`) in `MallocngTopStmt`.
-/

@[expose] public section

namespace VerifiedLibraries.Mallocng

open Arm64 Arm64.CType

/-! ## Constants and Pure Size, Alignment, and Budget Predicates -/

/-- Exact `ENOMEM` request ceiling in `musl` 1.2.5 `mallocng` (`SIZE_MAX / 2 - 4097` in
    `__libc_malloc_impl` and `__libc_realloc`): requests `≤ MallocngMaxAllocSize` succeed on
    `.Running`, and requests `> MallocngMaxAllocSize` return `NULL` (`0#64`) with `errno = ENOMEM`. -/
def MallocngMaxAllocSize : Nat := 0x7fffffffffffeffe

/-- Maximum supported alignment (`2 ^ 31 = 0x80000000`) for `aligned_alloc` and `posix_memalign`
    over unmodified `musl` 1.2.5 `mallocng` (avoiding the signed
    32-bit `int reserved = end - p - n` overflow in `src/malloc/mallocng/meta.h:186`). -/
def MaxAlignedAllocAlign : Nat := 2 ^ 31

/-- Stack frame budget (`1024` bytes) sufficient for every `mallocng` C entry point (including
    depth-`≤ 3` nested `alloc_slot` -> `alloc_group` -> `alloc_slot` recursion and
    `__malloc_alloc_meta`). -/
abbrev mallocngStackBytes : Nat := 1024

/-- Fixed base overhead `a = 32 MiB` (`33,554,432` bytes) in the linear virtual-memory accounting
    bound `mappedBytes ≤ MallocngBaseOverhead + MallocngLinearFactor * b.peakCost`, covering `.data`/
    `.bss`, initial `meta_area` arenas, and bounded empty/bouncing groups across the 48 size classes. -/
def MallocngBaseOverhead : Nat := 32 * 1024 * 1024

/-- Minimum effective cost (`65536` B = `64 KiB` = 1 coarse `mmap` slab) charged per live allocation
    in `mallocngAllocBudget`, `mallocngAlignedBudget`, `mallocngFreeBudget`, and
    `mallocngReallocBudget`. Allocations with `req ≥ 65536` have `max req MallocngMinBlockCost = req`,
    and `K` simultaneously live smaller allocations add at most `64 KiB * K`. -/
abbrev MallocngMinBlockCost : Nat := 65536

/-- Multiplicative factor `k = 48` in
    `mappedBytes ≤ MallocngBaseOverhead + MallocngLinearFactor * b.peakCost` (`46` slab/coarse
    container worst-case multiplier plus `2` `meta_area` doubling reserve). -/
def MallocngLinearFactor : Nat := 48

/-- Combined byte-cost and allocation-count budget tracked across `mallocng` calls:
    - `liveCost`: sum of effective byte costs (`max req MallocngMinBlockCost + alignOver`) of
      currently live allocations;
    - `peakCost`: historical maximum of `liveCost` (monotonically non-decreasing across calls);
    - `liveCount`: number of currently live allocations;
    - `peakCount`: historical maximum of `liveCount` (monotonically non-decreasing across calls).
    Tracking `(liveCount, peakCount)` alongside `(liveCost, peakCost)` bounds the number of dynamic
    virtual-memory intervals `ivs.length` by `48 + 2 * b.peakCount` (`≤ 64 + 2 * b.peakCount`
    including static globals/TLS/auxv) independently of allocation byte sizes, while `b.peakCost`
    bounds total mapped bytes by `MallocngBaseOverhead + MallocngLinearFactor * b.peakCost`. -/
structure MallocngBudget where
  liveCost  : Nat
  peakCost  : Nat
  liveCount : Nat
  peakCount : Nat
  deriving DecidableEq, Repr

/-- Initial zero budget (`liveCost = 0, peakCost = 0, liveCount = 0, peakCount = 0`) at process
    startup. -/
def mallocngZeroBudget : MallocngBudget := ⟨0, 0, 0, 0⟩

/-- Non-zero power-of-two 64-bit alignment (`align ≠ 0` and `align & (align - 1) = 0`). -/
def IsPow2Align (align : BitVec 64) : Prop :=
  align ≠ 0#64 ∧ (align &&& (align - 1#64)) = 0#64

instance (align : BitVec 64) : Decidable (IsPow2Align align) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Boolean decision wrapper for `IsPow2Align`. -/
def isPow2Align (align : BitVec 64) : Bool :=
  decide (IsPow2Align align)

/-- Exact over-allocation request size `(len - UNIT) + max(align, UNIT)` passed to
    `__libc_malloc_impl` by `mallocng`'s `aligned_alloc(align, len)` (`UNIT = 16`):
    `len` when `align ≤ 16`, and `len + align - 16` when `align > 16`. -/
def mallocngAlignedEffSize (align len : Nat) : Nat :=
  if align ≤ 16 then len else len + align - 16

/-- `aligned_alloc(align, len)` alignment test `(align & -align) == align` in `musl`
    (`src/malloc/mallocng/aligned_alloc.c`), accepting powers of two as well as `align = 0`
    (which behaves like `align = 16`). -/
def alignedAllocAlignOk (align : BitVec 64) : Bool :=
  (align &&& (0#64 - align)) == align

/-- Under `align.toNat ≤ MaxAlignedAllocAlign`, `aligned_alloc(align, len)` succeeds on `.Running`
    in `mallocng` iff `alignedAllocAlignOk align` holds and
    `mallocngAlignedEffSize align.toNat len.toNat ≤ MallocngMaxAllocSize`. -/
def mallocngAlignedAllocOk (align len : BitVec 64) : Bool :=
  alignedAllocAlignOk align &&
    decide (mallocngAlignedEffSize align.toNat len.toNat ≤ MallocngMaxAllocSize)

/-- Under `align.toNat ≤ MaxAlignedAllocAlign`, `posix_memalign(res, align, len)` succeeds
    (`ret = 0#32`) on `.Running` iff `8 ≤ align.toNat` and `mallocngAlignedAllocOk align len`. -/
def mallocngPosixMemalignOk (align len : BitVec 64) : Bool :=
  decide (8 ≤ align.toNat) && mallocngAlignedAllocOk align len

/-- Exact return code of `posix_memalign(res, align, len)` on `.Running` (under
    `align.toNat ≤ MaxAlignedAllocAlign`):
    - `22#32` (`EINVAL`) when `align.toNat < 8` or `¬ IsPow2Align align`;
    - `0#32` (success) when `8 ≤ align.toNat ∧ IsPow2Align align ∧
      mallocngAlignedEffSize align.toNat len.toNat ≤ MallocngMaxAllocSize`;
    - `12#32` (`ENOMEM`) otherwise. -/
def mallocngPosixMemalignRet (align len : BitVec 64) : BitVec 32 :=
  if align.toNat < 8 || !isPow2Align align then 22#32
  else if mallocngAlignedEffSize align.toNat len.toNat ≤ MallocngMaxAllocSize then 0#32
  else 12#32

/-! ## Syscall Dispatch Contract and OOM / VA-Gap Predicates -/

/-- Linux AArch64 `mremap` syscall number (`__NR_mremap = 216`). -/
def MALLOCNG_SYS_MREMAP : BitVec 64 := 216#64

/-- `mremap` `flags` bit `MREMAP_MAYMOVE` (`1`). -/
def MALLOCNG_MREMAP_MAYMOVE : BitVec 64 := 1#64

/-- Move or resize a non-frozen `Perm.rw` range `[oldBase, oldBase + oldSize)` onto
    `[newBase, newBase + newSize)`: frozen bytes are preserved; `[newBase, newBase + newSize)` is
    mapped `Perm.rw` copying `min oldSize newSize` bytes from `oldBase` and zero-filling growth;
    remaining bytes in `[oldBase, oldBase + oldSize)` are unmapped; all other bytes are unchanged. -/
def mallocngRemapRw (m : Memory) (oldBase : BitVec 64) (oldSize : Nat)
    (newBase : BitVec 64) (newSize : Nat) : Memory :=
  ⟨fun a =>
    if (m.perm a).frozen then
      m.cells a
    else if (a - newBase).toNat < newSize then
      let off := (a - newBase).toNat
      let src := oldBase + BitVec.ofNat 64 off
      let b := if off < oldSize then m.read8 src else 0#8
      let p := if off < oldSize then
        { Perm.rw with lazyFree := m.isLazyFree src, anon := m.isAnon src }
      else Perm.rw
      some (some p, b)
    else if (a - oldBase).toNat < oldSize then
      none
    else
      m.cells a⟩

/-- Relational contract for a valid `mremap(oldAddr, oldLen, newLen, MREMAP_MAYMOVE)` step:
    when `oldAddr` is page-aligned, `0 < oldLen`, `0 < newLen ≤ 2 ^ 64 - PAGE_SIZE`,
    `oldAddr.toNat + pageAlignUp oldLen ≤ 2 ^ 48`, and `[oldAddr, oldAddr + pageAlignUp oldLen)` is
    uniformly anonymous `some Perm.rw` (hence non-frozen), `mremap` either:
    1. refuses with `-ENOMEM` (`s' = ((s.nextOracle).writeReg64 Reg.x0 (-ENOMEM)).advancePC`),
    2. transitions to `.OutOfMemory` when `s.physMemAvail + pageAlignUp oldLen < pageAlignUp newLen`
       (`s' = s.setStatus .OutOfMemory`), or
    3. remaps onto a page-aligned destination `newBase` (`newBase ≠ 0#64`,
      `newBase.toNat % PAGE_SIZE = 0`, `newBase.toNat + pageAlignUp newLen ≤ 2 ^ 48`,
      `(s.mem.unmapNonFrozen oldAddr (pageAlignUp oldLen)).canMap newBase (pageAlignUp newLen)`)
      via `mallocngRemapRw` and updates `physMemAvail := s.physMemAvail + pageAlignUp oldLen - pageAlignUp newLen`. -/
def MallocngMremapStep (s s' : State) : Prop :=
  let oldAddr := s.readReg64 Reg.x0
  let oldLen  := (s.readReg64 Reg.x1).toNat
  let newLen  := (s.readReg64 Reg.x2).toNat
  let flags   := s.readReg64 Reg.x3
  let oldAligned := pageAlignUp oldLen
  let newAligned := pageAlignUp newLen
  flags = MALLOCNG_MREMAP_MAYMOVE →
  oldAddr.toNat % PAGE_SIZE = 0 →
  0 < oldLen →
  0 < newLen →
  newLen ≤ 2 ^ 64 - PAGE_SIZE →
  oldAddr.toNat + oldAligned ≤ 2 ^ 48 →
  s.mem.allPerm (· == some Perm.rw) oldAddr oldAligned = true →
  s.mem.allAnon oldAddr oldAligned = true →
  s' = ((s.nextOracle).writeReg64 Reg.x0 (-ENOMEM)).advancePC ∨
  (s.physMemAvail + oldAligned < newAligned ∧ s' = s.setStatus .OutOfMemory) ∨
    ∃ newBase : BitVec 64,
      newBase ≠ 0#64 ∧
      newBase.toNat % PAGE_SIZE = 0 ∧
      newBase.toNat + newAligned ≤ 2 ^ 48 ∧
      (s.mem.unmapNonFrozen oldAddr oldAligned).canMap newBase newAligned = true ∧
      s' = ((((s.setMem (mallocngRemapRw s.mem oldAddr oldAligned newBase newAligned)).setPhysMemAvail
        (s.physMemAvail + oldAligned - newAligned)).nextOracle).writeReg64
        Reg.x0 newBase).advancePC

/-- Supervisor-call handler validity for `mallocng`: dispatches `SYS_BRK` (`214`), `SYS_MUNMAP`
    (`215`), `SYS_MMAP` (`222`), and `SYS_MPROTECT` (`226`) to their TCB handlers and satisfies
    `MallocngMremapStep` on `SYS_MREMAP` (`216`). -/
def MallocngSvcValid (svc : State → State) : Prop :=
  ∀ s : State,
    (s.readReg64 Reg.x8 = SYS_BRK → svc s = execBrk s) ∧
    (s.readReg64 Reg.x8 = SYS_MUNMAP → svc s = execMunmap s) ∧
    (s.readReg64 Reg.x8 = SYS_MMAP → svc s = execMmap s) ∧
    (s.readReg64 Reg.x8 = SYS_MPROTECT → s.readReg64 Reg.x2 = MMAP_PROT_RW → svc s = execMprotect s) ∧
    (s.readReg64 Reg.x8 = MALLOCNG_SYS_MREMAP → MallocngMremapStep s (svc s))

/-- Placed block program for block `i` of `VerifiedLibraries.mallocngLib` under multi-block placement
    `mpl` and supervisor-call handler `svc` (no external hooks or overrides). When
    `svc = Syscall.standard`, this is definitionally `VerifiedLibraries.mallocngLib.blockProgram mpl i`. -/
def mallocngBlockProg (mpl : Obj.MultiPlacement) (i : Nat) (svc : State → State) : Program :=
  VerifiedLibraries.mallocngLib.blockProgram mpl i (fun _ => none) (fun _ => none) svc

/-- `[MMAP_MIN_ADDR, 2 ^ 48)` contains an unmapped page-aligned range of `sz` bytes in `m`. -/
def MallocngHasGap (m : Memory) (sz : Nat) : Prop :=
  ∃ gap : BitVec 64,
    MMAP_MIN_ADDR ≤ gap.toNat ∧
    gap.toNat % PAGE_SIZE = 0 ∧
    gap.toNat + sz ≤ 2 ^ 48 ∧
    m.canMap gap sz = true

/-- Physical or virtual memory exhaustion witness at state `s` for a page-aligned request of `sz`
    bytes: either `[MMAP_MIN_ADDR, 2 ^ 48)` has no unmapped page-aligned gap of `sz` bytes in
    `s.mem`, or `s.physMemAvail < sz`. -/
abbrev MallocngNoGapOrPhys (s : State) (sz : Nat) : Prop :=
  ¬ MallocngHasGap s.mem sz ∨ s.physMemAvail < sz

/-- Sanitized `mmap` property: non-`MAP_FIXED` anonymous `SYS_MMAP`
    (`prot ∈ {PROT_NONE, PROT_READ | PROT_WRITE}`, `flags = MAP_PRIVATE | MAP_ANONYMOUS`, `off = 0`,
    `len ≠ 0`) transitions to `.OutOfMemory` only when either no valid unmapped gap of size
    `pageAlignUp len` exists in `[MMAP_MIN_ADDR, 2 ^ 48)` or `s.physMemAvail < pageAlignUp len`. -/
def MallocngSanitizedSvc (svc : State → State) : Prop :=
  ∀ s : State,
    s.status = .Running →
    s.readReg64 Reg.x8 = SYS_MMAP →
    (s.readReg64 Reg.x2 = MMAP_PROT_NONE ∨ s.readReg64 Reg.x2 = MMAP_PROT_RW) →
    s.readReg64 Reg.x3 = MMAP_FLAGS_PRIVATE_ANON →
    s.readReg64 Reg.x5 = 0#64 →
    s.readReg64 Reg.x1 ≠ 0#64 →
    (svc s).status = .OutOfMemory →
    MallocngNoGapOrPhys s (pageAlignUp (s.readReg64 Reg.x1).toNat)

/-- Byte `a` lies in at least one half-open interval `[iv.1, iv.1 + iv.2)` of `ivs`. -/
def MallocngInIntervals (ivs : List (BitVec 64 × Nat)) (a : BitVec 64) : Prop :=
  ∃ iv ∈ ivs, (a - iv.1).toNat < iv.2

/-- Newly mapped bytes from `m0` to `mf` are covered by at most `maxNewIntervals` intervals of
    combined byte length `≤ maxTotalBytes`. -/
def MallocngMappedDelta (maxNewIntervals maxTotalBytes : Nat) (m0 mf : Memory) : Prop :=
  ∃ ivs : List (BitVec 64 × Nat),
    ivs.length ≤ maxNewIntervals ∧
    (ivs.map Prod.snd).sum ≤ maxTotalBytes ∧
    ∀ a : BitVec 64, (mf.perm a).mapped = true →
      (m0.perm a).mapped = true ∨ MallocngInIntervals ivs a

/-- Concrete no-orphan-mapping transition law from pre-call dynamic interval list `ivs0` to
    post-call dynamic interval list `ivsf`: every byte `a` mapped in `mf` that was either newly
    mapped (`(m0.perm a).mapped = false`) or previously tracked in `ivs0`
    (`MallocngInIntervals ivs0 a`) is tracked in `ivsf` (`MallocngInIntervals ivsf a`). Because
    `ivsf` is the exact interval list indexing the post-call `J.MallocngHeap γ A tp brkStart sf.brk bf ivsf`
    (whose length and byte sum are bounded by `heap_footprint_bound`), no orphan mappings can
    accumulate across allocator loops. -/
def MallocngNoOrphanMappings (ivs0 ivsf : List (BitVec 64 × Nat)) (m0 mf : Memory) : Prop :=
  ∀ a : BitVec 64, (mf.perm a).mapped = true →
    ((m0.perm a).mapped = false ∨ MallocngInIntervals ivs0 a) →
    MallocngInIntervals ivsf a

/-- Upper bound on newly mapped bytes (and any single `mmap` request) within one `mallocng` call
    of effective payload `reqBytes` at historical peak allocation count `peakCount`:
    covers the slab/individual `mmap` request (`≤ pageAlignUp (reqBytes + 8192)`), fixed base/coarse
    slab step (`MallocngBaseOverhead = 32 MiB`), and any `meta_area` growth (`≤ 4096 * peakCount`). -/
def MallocngStepBound (reqBytes peakCount : Nat) : Nat :=
  pageAlignUp (reqBytes + 8192) + MallocngBaseOverhead + 4096 * peakCount

/-- Exact out-of-memory postcondition (`onOom`) for a `mallocng` call of effective payload
    `reqBytes` at peak allocation count `peakCount`: preserves `fs`, `trace`, and `sigActions`,
    bounds newly mapped bytes since `s0` by
    `MallocngMappedDelta 16 (MallocngStepBound reqBytes peakCount)`, and under
    `MallocngSanitizedSvc svc` witnesses a page-aligned request
    `sz ≤ MallocngStepBound reqBytes peakCount` with either no unmapped VA gap in `sf.mem` or
    `sf.physMemAvail < sz` (`MallocngNoGapOrPhys sf sz`). When the caller bounds total mapped memory,
    VMA count, and physical memory via `heap_footprint_bound`, this predicate reduces to `False`
    (`oom := fun _ => False`). -/
def MallocngOomCond (svc : State → State) (reqBytes peakCount : Nat) (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧
  sf.trace = s0.trace ∧
  sf.sigActions = s0.sigActions ∧
  MallocngMappedDelta 16 (MallocngStepBound reqBytes peakCount) s0.mem sf.mem ∧
  (MallocngSanitizedSvc svc →
    ∃ sz : Nat,
      PAGE_SIZE ≤ sz ∧
      sz % PAGE_SIZE = 0 ∧
      sz ≤ MallocngStepBound reqBytes peakCount ∧
      MallocngNoGapOrPhys sf sz)

/-- Non-allocator process state preserved across every `mallocng` subroutine call. -/
abbrev MallocngProcPreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧
  sf.trace = s0.trace ∧
  sf.tpidrEl0 = s0.tpidrEl0 ∧
  sf.brkStart = s0.brkStart ∧
  sf.oracle = s0.oracle ∧
  sf.symtab = s0.symtab ∧
  sf.sigActions = s0.sigActions

/-! ## Placement-Generic Addresses, `.rodata` Tables, and `MallocngIface` -/

/-- Stock `musl` v1.2.5 `__malloc_size_classes[0..47]` (`48` entries, in `UNIT = 16`-byte multiples). -/
def mallocngSizeClassUnits : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15,
   18, 20, 25, 31, 36, 42, 50, 63, 72, 84, 102, 127,
   146, 170, 204, 255, 292, 340, 409, 511, 584, 682, 818, 1023,
   1169, 1364, 1637, 2047, 2340, 2730, 3276, 4095, 4680, 5460, 6552, 8191]

/-- Little-endian `u16` byte encoding (`96` B) of `__malloc_size_classes`. -/
def mallocngSizeClassBytes : List (BitVec 8) :=
  mallocngSizeClassUnits.flatMap fun u => [BitVec.ofNat 8 (u % 256), BitVec.ofNat 8 (u / 256)]

/-- 32-byte De Bruijn lookup table (`debruijn32.4681` and `debruijn32.5048`) for `a_ctz_32`. -/
def mallocngDebruijn32Table : List (BitVec 8) :=
  ([0, 1, 23, 2, 29, 24, 19, 3, 30, 27, 25, 11, 20, 8, 4, 13,
    31, 22, 28, 18, 26, 10, 7, 12, 21, 17, 9, 6, 16, 5, 15, 14] : List Nat).map (BitVec.ofNat 8)

/-- 4-byte `med_cnt_tab` (`[28, 24, 20, 32]`) in `alloc_group`. -/
def mallocngMedCntTabBytes : List (BitVec 8) :=
  ([28, 24, 20, 32] : List Nat).map (BitVec.ofNat 8)

/-- 27-byte `small_cnt_tab` (`9 * 3` entries for `sc < 9`) in `alloc_group`. -/
def mallocngSmallCntTabBytes : List (BitVec 8) :=
  ([30, 30, 30, 31, 15, 15, 20, 10, 10,
    31, 15, 7, 25, 12, 6, 21, 10, 5,
    18, 8, 4, 31, 15, 7, 28, 14, 6] : List Nat).map (BitVec.ofNat 8)

/-- Exact 200-byte `.rodata` lookup-table block `[__malloc_size_classes, __malloc_size_classes + 200)`
    for stock `musl` v1.2.5 `mallocng`. -/
def mallocngRoTablesBytes : List (BitVec 8) :=
  mallocngSizeClassBytes ++
  mallocngDebruijn32Table ++
  mallocngMedCntTabBytes ++ List.replicate 4 0#8 ++
  mallocngSmallCntTabBytes ++ List.replicate 5 0#8 ++
  mallocngDebruijn32Table

/-- Placement-resolved static symbol addresses for `musl` 1.2.5 `mallocng`, with all five `.rodata`
    lookup tables resolved per symbol (no contiguity assumption):
    - `base`: nominal placement base (`mpl.base 0`).
    - `sizeClasses`: `__malloc_size_classes` (`96` B `.rodata`).
    - `debruijnFree`: `debruijn32.4681` (`32` B `.rodata`).
    - `medCntTab`: `med_cnt_tab` (`4` B `.rodata`).
    - `smallCntTab`: `small_cnt_tab` (`27` B `.rodata`).
    - `debruijnAlloc`: `debruijn32.5048` (`32` B `.rodata`).
    - `ctx`: `__malloc_context` (`928` B `.bss`).
    - `libc`: `__libc` (`+3` `need_locks`, `+8` `auxv`, `+48` `page_size`).
    - `lock`: `__malloc_lock` (`4` B `.bss`).
    - `replaced`: `__malloc_replaced` (`4` B `.bss`).
    - `aaReplaced`: `__aligned_alloc_replaced` (`4` B `.bss`). -/
structure MallocngAddrs where
  base          : BitVec 64
  sizeClasses   : BitVec 64
  debruijnFree  : BitVec 64
  medCntTab     : BitVec 64
  smallCntTab   : BitVec 64
  debruijnAlloc : BitVec 64
  ctx           : BitVec 64
  libc          : BitVec 64
  lock          : BitVec 64
  replaced      : BitVec 64
  aaReplaced    : BitVec 64
  deriving DecidableEq

/-- Resolve `MallocngAddrs` from a multi-block placement `mpl : Obj.MultiPlacement`
    (`mpl.base 0` and `mpl.ρ "<sym>"`). -/
def mallocngAddrsOfPlacement (mpl : Obj.MultiPlacement) : MallocngAddrs where
  base          := mpl.base 0
  sizeClasses   := mpl.ρ "__malloc_size_classes"
  debruijnFree  := mpl.ρ "debruijn32.4681"
  medCntTab     := mpl.ρ "med_cnt_tab"
  smallCntTab   := mpl.ρ "small_cnt_tab"
  debruijnAlloc := mpl.ρ "debruijn32.5048"
  ctx           := mpl.ρ "__malloc_context"
  libc          := mpl.ρ "__libc"
  lock          := mpl.ρ "__malloc_lock"
  replaced      := mpl.ρ "__malloc_replaced"
  aaReplaced    := mpl.ρ "__aligned_alloc_replaced"

/-- Well-formedness of the initial program break `brkStart`: page-aligned, at or above
    `MMAP_MIN_ADDR` (`0x10000`, so `execMmap`'s `MAP_FIXED` `PROT_NONE` guard page at `brkStart`
    succeeds), and within the 48-bit user virtual address space (`≤ 2 ^ 48`). Imposes zero
    alignment or offset constraints on `A.base`. -/
def MallocngBrkStartWf (brkStart : BitVec 64) : Prop :=
  MMAP_MIN_ADDR ≤ brkStart.toNat ∧ brkStart.toNat % PAGE_SIZE = 0 ∧ brkStart.toNat ≤ 2 ^ 48

/-- Valid Linux ELF auxiliary vector table at `auxvPtr` containing `AT_RANDOM` (`25#64`) before
    the `AT_NULL` (`0#64`) terminator, together with the 8-byte random secret slice at
    `randPtr + 8#64` read by `mallocng`'s `get_random_secret()`. Directly satisfied by
    `Arm64.Process.buildInitialStack` under `ProcessInputs.Valid` (`preEntries.length = 15`,
    `sufEntries.length ≤ 8`, within the 48-bit user stack region). -/
def MallocngAuxvAt (auxvPtr : BitVec 64) : SepProp :=
  ∃∗ preEntries : List (BitVec 64 × BitVec 64),
  ∃∗ sufEntries : List (BitVec 64 × BitVec 64),
  ∃∗ randPtr : BitVec 64,
  ∃∗ nullVal : BitVec 64,
  ∃∗ secretBytes : List (BitVec 8),
    ⌜(∀ e ∈ preEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
     (∀ e ∈ sufEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
     preEntries.length + sufEntries.length ≤ 64 ∧
     auxvPtr.toNat + 16 * (preEntries.length + sufEntries.length + 2) ≤ 2 ^ 48 ∧
     randPtr.toNat + 16 ≤ 2 ^ 48 ∧
     secretBytes.length = 8⌝ ∗
    (auxvPtr ↦₆₄*
      ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
        fun (t, v) => [t, v])) ∗
    ((randPtr + 8#64) ↦ₛ secretBytes)

/-- Single-threaded `musl` runtime cells at placement `A : MallocngAddrs` and thread pointer `tp`
    shared with non-allocator `libc` / `std` code between allocator calls: the thread's TLS `errno`
    slot (`*(tp - 0xa4)`), `__libc.need_locks = 0#8` (`A.libc + 3`), and
    `__libc.page_size = 4096#64` (`A.libc + 48`). -/
def MallocngRuntime (A : MallocngAddrs) (tp : BitVec 64) : SepProp :=
  (∃∗ errnoVal : BitVec 32, (tp - 0xa4#64) ↦₃₂ errnoVal) ∗
  ((A.libc + 3#64) ↦₈ 0#8) ∗
  ((A.libc + 48#64) ↦₆₄ 4096#64)

/-- Read-only `.rodata` lookup-table bundle at placement `A : MallocngAddrs` owning all 5
    per-symbol `.rodata` tables (`__malloc_size_classes`, `debruijn32.4681`, `med_cnt_tab`,
    `small_cnt_tab`, and `debruijn32.5048`) with zero contiguity assumption between them. -/
def MallocngRoTablesAt (A : MallocngAddrs) : SepProp :=
  (A.sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗
  (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
  (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
  (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
  (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table)

/-- Post-`__init_libc` separation-logic startup bundle at placement `A : MallocngAddrs` and thread
    pointer `tp`: owns the 5 per-symbol `.rodata` lookup tables (`MallocngRoTablesAt A`), the zeroed
    `.bss` allocator globals (`A.ctx`, `A.lock`, `A.replaced`, `A.aaReplaced`), `MallocngRuntime A tp`,
    `__libc.auxv` (`A.libc + 8`), and `MallocngAuxvAt auxvPtr`. -/
def MallocngStartupResources (A : MallocngAddrs) (tp : BitVec 64) : SepProp :=
  ∃∗ auxvPtr : BitVec 64,
    MallocngRoTablesAt A ∗
    (A.ctx ↦ₛ List.replicate 928 0#8) ∗
    (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗
    (A.aaReplaced ↦₃₂ 0#32) ∗
    MallocngRuntime A tp ∗
    ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
    MallocngAuxvAt auxvPtr

/-- Abstract separation-logic interface for stock `musl` v1.2.5 `mallocng`:
    - `MallocngHeap γ A tp brkStart brk b ivs` is the complete allocator and runtime invariant at
      ghost instance `γ`, symbol placement `A : MallocngAddrs`, thread pointer `tp`, initial break
      `brkStart`, current break `brk`, cost/count budget `b : MallocngBudget`, and concrete dynamic
      virtual-memory interval list `ivs : List (BitVec 64 × Nat)`.
    - `MallocngCore γ A brkStart brk b ivs` is the allocator-private part excluding
      `MallocngRuntime A tp`, allowing callers to read/write `errno` and read
      `__libc.need_locks` / `__libc.page_size` between allocator calls via `heap_split_runtime`.
    - `Block γ p n` is the zero-spatial-footprint per-allocation ownership token for a live block
      at user address `p` of requested size `n` bytes (`16 ∣ p.toNat`). -/
structure MallocngIface where
  MallocngHeap :
    GhostName → MallocngAddrs → BitVec 64 → BitVec 64 → BitVec 64 →
      MallocngBudget → List (BitVec 64 × Nat) → SepProp
  MallocngCore :
    GhostName → MallocngAddrs → BitVec 64 → BitVec 64 →
      MallocngBudget → List (BitVec 64 × Nat) → SepProp
  Block        : GhostName → BitVec 64 → Nat → SepProp
  block_noWrap : ∀ (γ : GhostName) (p : BitVec 64) (n : Nat),
    Block γ p n ⊢ ⌜p.toNat + n ≤ 2 ^ 64⌝ ∗ Block γ p n

/-- State-indexed allocator environment at state `s` with budget `b` and dynamic interval list `ivs`:
    binds `s.tpidrEl0 = tp` and `s.brkStart = brkStart`, and owns
    `J.MallocngHeap γ A tp brkStart s.brk b ivs` at `s`'s current program break `s.brk`. -/
def MallocngEnv (J : MallocngIface) (γ : GhostName) (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) (s : State) : SepProp :=
  ⌜s.tpidrEl0 = tp ∧ s.brkStart = brkStart⌝ ∗
    J.MallocngHeap γ A tp brkStart s.brk b ivs

/-- Post-call state-indexed allocator environment at exit state `sf`: existentially binds the
    post-call dynamic interval list `ivsf : List (BitVec 64 × Nat)` satisfying
    `MallocngNoOrphanMappings ivs0 ivsf s0.mem sf.mem` and `MallocngEnv J γ A tp brkStart bf ivsf sf`. -/
def MallocngPostEnv (J : MallocngIface) (γ : GhostName) (A : MallocngAddrs)
    (tp brkStart : BitVec 64) (bf : MallocngBudget) (ivs0 : List (BitVec 64 × Nat))
    (s0 sf : State) : SepProp :=
  ∃∗ ivsf : List (BitVec 64 × Nat),
    ⌜MallocngNoOrphanMappings ivs0 ivsf s0.mem sf.mem⌝ ∗
    MallocngEnv J γ A tp brkStart bf ivsf sf

/-- Combined post-call pure and step-delta accounting invariant across a `mallocng` call:
    1. `MallocngProcPreserved s0 sf` (preserves `fs`, `trace`, `tpidrEl0`, `brkStart`, `oracle`,
       `symtab`, and `sigActions`).
    2. `MallocngMappedDelta maxNewIvs maxNewBytes s0.mem sf.mem` (newly mapped bytes covered by
       `≤ maxNewIvs` intervals of total byte length `≤ maxNewBytes`). -/
def MallocngCallAccounting (maxNewIvs maxNewBytes : Nat) (s0 sf : State) : Prop :=
  MallocngProcPreserved s0 sf ∧
  MallocngMappedDelta maxNewIvs maxNewBytes s0.mem sf.mem

/-- Closed-form updated `MallocngBudget` after allocating a regular (`malloc`/`calloc`) block of
    `req` bytes (`ok = true`), or unchanged on failure (`ok = false`). -/
def mallocngAllocBudget (ok : Bool) (req : Nat) (b : MallocngBudget) : MallocngBudget :=
  if ok then
    let liveCost'  := b.liveCost + max req MallocngMinBlockCost
    let liveCount' := b.liveCount + 1
    { liveCost  := liveCost'
      peakCost  := max b.peakCost liveCost'
      liveCount := liveCount'
      peakCount := max b.peakCount liveCount' }
  else b

/-- Closed-form updated `MallocngBudget` after allocating an aligned (`aligned_alloc` /
    `posix_memalign`) block of `len` bytes at alignment `align` (`ok = true`), or unchanged on
    failure (`ok = false`). -/
def mallocngAlignedBudget (ok : Bool) (align len : Nat) (b : MallocngBudget) : MallocngBudget :=
  if ok then
    let liveCost'  := b.liveCost + max len MallocngMinBlockCost + (max align 16 - 16)
    let liveCount' := b.liveCount + 1
    { liveCost  := liveCost'
      peakCost  := max b.peakCost liveCost'
      liveCount := liveCount'
      peakCount := max b.peakCount liveCount' }
  else b

/-- Closed-form updated `MallocngBudget` after `free(p)` on a nullable block of `n` bytes. -/
def mallocngFreeBudget (isNull : Bool) (n : Nat) (b : MallocngBudget) : MallocngBudget :=
  if isNull then b
  else
    { liveCost  := b.liveCost - max n MallocngMinBlockCost
      peakCost  := b.peakCost
      liveCount := b.liveCount - 1
      peakCount := b.peakCount }

/-- Closed-form updated `MallocngBudget` after `realloc(p, newSize)` on `oldBlk`. -/
def mallocngReallocBudget (ok : Bool) (oldBlk : Option (Nat × List (BitVec 8)))
    (newSize : Nat) (b : MallocngBudget) : MallocngBudget :=
  if ok then
    let cNew := max newSize MallocngMinBlockCost
    let liveCost' :=
      match oldBlk with
      | none => b.liveCost + cNew
      | some (oldSize, _) => (b.liveCost - max oldSize MallocngMinBlockCost) + cNew
    let liveCount' :=
      match oldBlk with
      | none => b.liveCount + 1
      | some _ => b.liveCount
    { liveCost  := liveCost'
      peakCost  := max b.peakCost (b.liveCost + cNew)
      liveCount := liveCount'
      peakCount := max b.peakCount (b.liveCount + 1) }
  else b

/-- Placement-generic startup initialization statement (`mallocngInitStmt J`) over
    `VerifiedLibraries.mallocngLib.dataInit mpl`: for any multi-block placement
    `mpl : Obj.MultiPlacement` with `A = mallocngAddrsOfPlacement mpl` and any well-formed initial
    break `brkStart` (`MallocngBrkStartWf brkStart`), ghost initialization from
    `VerifiedLibraries.mallocngLib.dataInit mpl`, `MallocngRuntime A tp`, `(A.libc + 8#64) ↦₆₄ auxvPtr`,
    and `MallocngAuxvAt auxvPtr` yields an empty `MallocngHeap` at `A` with `mallocngZeroBudget` and
    `ivs = []` alongside any caller frame `R`. -/
def mallocngInitStmt (J : MallocngIface) : Prop :=
  ∀ (mpl : Obj.MultiPlacement) (tp brkStart auxvPtr : BitVec 64) (R : SepProp) (m : Memory),
    let A := mallocngAddrsOfPlacement mpl
    0xa4 ≤ tp.toNat →
    tp.toNat ≤ 2 ^ 48 →
    MallocngBrkStartWf brkStart →
    (m ⊨
      VerifiedLibraries.mallocngLib.dataInit mpl ∗
      MallocngRuntime A tp ∗
      ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
      MallocngAuxvAt auxvPtr ∗ R) →
    ∃ γ : GhostName,
      m ⊨ |==> (J.MallocngHeap γ A tp brkStart brkStart mallocngZeroBudget [] ∗ R)

/-! ## Canonical Semantic C Types (`SemType`) for `mallocng` Allocations -/

/-- Live `mallocng` allocation block of `n` uninitialized bytes aligned to `align` (`16` for
    `malloc`, `max align 16` for `aligned_alloc` / `posix_memalign`):
    owns `J.Block γ p n ∗ memRegion p n` with `p ≠ 0#64`, `align ∣ p.toNat`, and
    `p.toNat + n < 2 ^ 64`. -/
@[reducible] def MallocngBlock (J : MallocngIface) (γ : GhostName) : SemType (Nat × Nat) where
  tyName := "void * (mallocng allocated block)"
  interp := fun p (n, _) => J.Block γ p n ∗ memRegion p n
  pureWf := fun p (n, align) => p ≠ 0#64 ∧ align ∣ p.toNat ∧ p.toNat + n < 2 ^ 64

/-- Live zero-initialized `mallocng` allocation block of `n` zero bytes aligned to `align`:
    owns `J.Block γ p n ∗ (p ↦ₛ List.replicate n 0#8)` with `p ≠ 0#64`, `align ∣ p.toNat`, and
    `p.toNat + n < 2 ^ 64`. -/
@[reducible] def MallocngZeroedBlock (J : MallocngIface) (γ : GhostName) : SemType (Nat × Nat) where
  tyName := "void * (zero-initialized mallocng block)"
  interp := fun p (n, _) => J.Block γ p n ∗ (p ↦ₛ List.replicate n 0#8)
  pureWf := fun p (n, align) => p ≠ 0#64 ∧ align ∣ p.toNat ∧ p.toNat + n < 2 ^ 64

/-- Live `mallocng` allocation block of `sz` bytes at `p` whose first `bs.length ≤ sz` bytes hold
    `bs` and whose remaining `sz - bs.length` bytes are uninitialized `memRegion`. -/
@[reducible] def MallocngInitBlock (J : MallocngIface) (γ : GhostName) :
    SemType (Nat × List (BitVec 8)) where
  tyName := "void * (mallocng block with initialized prefix)"
  interp := fun p (sz, bs) =>
    J.Block γ p sz ∗ (p ↦ₛ bs) ∗
      memRegion (p + BitVec.ofNat 64 bs.length) (sz - bs.length)
  pureWf := fun p (sz, bs) =>
    p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + sz < 2 ^ 64 ∧ bs.length ≤ sz

/-- Nullable `mallocng` allocation block of `n` bytes at `p` passed to `free(p)` or
    `malloc_usable_size(p)`: `emp` when `p = 0#64`, or `J.Block γ p n ∗ memRegion p n` when
    `p ≠ 0#64`. -/
@[reducible] def MallocngFreeableBlock (J : MallocngIface) (γ : GhostName) : SemType Nat where
  tyName := "void * (nullable mallocng allocated block)"
  interp := fun p n => if p = 0#64 then emp else J.Block γ p n ∗ memRegion p n
  pureWf := fun p n => if p = 0#64 then n = 0 else 16 ∣ p.toNat ∧ p.toNat + n < 2 ^ 64

/-! ## Public C Allocator Specifications (`c_type_spec`) -/

/-- `void *malloc(size_t req)`:
    - For `req.toNat ≤ MallocngMaxAllocSize` (`0x7fffffffffffeffe`), returns a non-null
      16-byte-aligned block `MallocngBlock J γ (req.toNat, 16)` on `.Running` return and updates
      budget `b` by `mallocngAllocBudget true req.toNat b`.
    - For `req.toNat > MallocngMaxAllocSize`, returns `0#64` (`NULL`) and preserves `b`. -/
c_type_spec mallocngMallocSpec (ctx J : MallocngIface) (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (req : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost b : MallocngBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := decide (req.toNat ≤ MallocngMaxAllocSize)
  let b' := mallocngAllocBudget ok req.toNat b
  c_arg req : Val SizeT
  c_ret : Own (OptOwn (MallocngBlock J γ))
    (if ok then some (req.toNat, 16) else none)
  c_env (MallocngEnv J γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngPostEnv J γ A tp brkStart b' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting
    16 (MallocngStepBound (if ok then req.toNat else 0) b.peakCount) s0 sf
  oom_when MallocngOomCond svc (if ok then req.toNat else 0) b.peakCount s0 sf

/-- `void free(void *p)`:
    - When `p = 0#64` (`n = 0`), is a no-op preserving `MallocngEnv` and memory mappings.
    - When `p ≠ 0#64`, consumes `J.Block γ p n ∗ memRegion p n`, updates `b` via
      `mallocngFreeBudget false n b`, and adds zero new memory mappings (`MallocngMappedDelta 0 0`).
    - Never hits `.OutOfMemory` (`onOom = ⌜False⌝`). -/
c_type_spec mallocngFreeSpec (ctx J : MallocngIface) (ctx γ : GhostName)
    (ctx A : MallocngAddrs) (load_addr _b)
    (p : ptr) (sp : sp)
    (ghost n : Nat) (ghost tp brkStart : BitVec 64) (ghost b : MallocngBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) where
  let b' := mallocngFreeBudget (p == 0#64) n b
  c_arg p : Own (MallocngFreeableBlock J γ) n
  c_env (MallocngEnv J γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngPostEnv J γ A tp brkStart b' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting 0 0 s0 sf

/-- `void *calloc(size_t nmemb, size_t size)`:
    - When `total = nmemb.toNat * size.toNat ≤ MallocngMaxAllocSize`, returns a non-null
      16-byte-aligned zero-initialized block `MallocngZeroedBlock J γ (total, 16)`.
    - When `total > MallocngMaxAllocSize` (including 64-bit multiplication overflow), returns
      `0#64` (`NULL`) and preserves `b`. -/
c_type_spec mallocngCallocSpec (ctx J : MallocngIface) (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (nmemb : u64) (size : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost b : MallocngBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let total := nmemb.toNat * size.toNat
  let ok := decide (total ≤ MallocngMaxAllocSize)
  let b' := mallocngAllocBudget ok total b
  c_arg nmemb : Val SizeT
  c_arg size : Val SizeT
  c_ret : Own (OptOwn (MallocngZeroedBlock J γ))
    (if ok then some (total, 16) else none)
  c_env (MallocngEnv J γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngPostEnv J γ A tp brkStart b' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting
    16 (MallocngStepBound (if ok then total else 0) b.peakCount) s0 sf
  oom_when MallocngOomCond svc (if ok then total else 0) b.peakCount s0 sf

/-- `void *realloc(void *p, size_t newSize)`:
    - Covers `p = 0#64` (`oldBlk = none`, delegating to `malloc(newSize)`) and live blocks
      `oldBlk = some (oldSize, bs)` across in-place slab resize, `sc = 63` `mremap` (both
      succeeding and `-ENOMEM` fallback), and `malloc + memcpy + free`.
    - When `newSize.toNat ≤ MallocngMaxAllocSize`, consumes `oldBlk` and returns a non-null
      16-byte-aligned block of `newSize.toNat` bytes preserving `bs.take newSize.toNat`.
    - When `newSize.toNat > MallocngMaxAllocSize`, returns `0#64` (`NULL`) and preserves `oldBlk`. -/
c_type_spec mallocngReallocSpec (ctx J : MallocngIface) (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (p : ptr) (newSize : u64) (sp : sp)
    (ghost oldBlk : Option (Nat × List (BitVec 8)))
    (ghost tp brkStart : BitVec 64) (ghost b : MallocngBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := decide (newSize.toNat ≤ MallocngMaxAllocSize)
  let keptBs := ((oldBlk.map Prod.snd).getD []).take newSize.toNat
  let b' := mallocngReallocBudget ok oldBlk newSize.toNat b
  c_arg p : MutRef (CondOwn (OptOwn (MallocngInitBlock J γ))) (some oldBlk) ⇝
    (if ok then none else some oldBlk)
  c_arg newSize : Val SizeT
  c_ret : Own (OptOwn (MallocngInitBlock J γ))
    (if ok then some (newSize.toNat, keptBs) else none)
  c_env (MallocngEnv J γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngPostEnv J γ A tp brkStart b' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting
    16 (MallocngStepBound (if ok then newSize.toNat + MaxAlignedAllocAlign else 0) b.peakCount) s0 sf
  oom_when MallocngOomCond svc (if ok then newSize.toNat + MaxAlignedAllocAlign else 0) b.peakCount s0 sf

/-- `void *aligned_alloc(size_t align, size_t len)`:
    - Requires `align.toNat ≤ MaxAlignedAllocAlign` (`2 ^ 31`), avoiding the signed 32-bit
      `int reserved` overflow in `musl` 1.2.5 `set_size`.
    - When `mallocngAlignedAllocOk align len` holds, returns a non-null `max align.toNat 16`-aligned
      block `MallocngBlock J γ (len.toNat, max align.toNat 16)`; otherwise returns `0#64` (`NULL`). -/
c_type_spec mallocngAlignedAllocSpec (ctx J : MallocngIface) (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (align : u64) (len : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost b : MallocngBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : ptr) where
  let ok := mallocngAlignedAllocOk align len
  let eff := mallocngAlignedEffSize align.toNat len.toNat
  let b' := mallocngAlignedBudget ok align.toNat len.toNat b
  caveat [API_RESTRICTION] "align ≤ 2^31 avoids musl 1.2.5 set_size int32 reserved overflow" :
    align.toNat ≤ MaxAlignedAllocAlign
  c_arg align : Val SizeT
  c_arg len : Val SizeT
  c_ret : Own (OptOwn (MallocngBlock J γ))
    (if ok then some (len.toNat, max align.toNat 16) else none)
  c_env (MallocngEnv J γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngPostEnv J γ A tp brkStart b' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  ensures_pure MallocngCallAccounting
    16 (MallocngStepBound (if ok then eff else 0) b.peakCount) s0 sf
  oom_when MallocngOomCond svc (if ok then eff else 0) b.peakCount s0 sf

/-- `int posix_memalign(void **res, size_t align, size_t len)`:
    - Requires `align.toNat ≤ MaxAlignedAllocAlign` (`2 ^ 31`).
    - Validates `align >= 8` and power-of-two `align`, then delegates to `aligned_alloc(align, len)`.
    - Writes a non-null `max align.toNat 16`-aligned pointer into `*res` and returns `0#32` when
      `mallocngPosixMemalignOk align len` holds; otherwise leaves `memRegion res 8` untouched and
      returns `22#32` (`EINVAL`) or `12#32` (`ENOMEM`) per `mallocngPosixMemalignRet align len`. -/
c_type_spec mallocngPosixMemalignSpec (ctx J : MallocngIface) (ctx svc : State → State)
    (ctx γ : GhostName) (ctx A : MallocngAddrs) (load_addr _b)
    (res : ptr) (align : u64) (len : u64) (sp : sp)
    (ghost tp brkStart : BitVec 64) (ghost b : MallocngBudget)
    (ghost ivs0 : List (BitVec 64 × Nat)) : (ret : u32) where
  let ok := mallocngPosixMemalignOk align len
  let eff := mallocngAlignedEffSize align.toNat len.toNat
  let b' := mallocngAlignedBudget ok align.toNat len.toNat b
  caveat [API_RESTRICTION] "align ≤ 2^31 avoids musl 1.2.5 set_size int32 reserved overflow" :
    align.toNat ≤ MaxAlignedAllocAlign
  c_arg res : MutRef (OptOutPtr (MallocngBlock J γ)) none ⇝
    (if ok then some (len.toNat, max align.toNat 16) else none)
  c_arg align : Val SizeT
  c_arg len : Val SizeT
  c_env (MallocngEnv J γ A tp brkStart b ivs0 s0 ∗ stackFrameAt sp mallocngStackBytes) ⇝
        (MallocngPostEnv J γ A tp brkStart b' ivs0 s0 sf ∗ stackFrameAt sp mallocngStackBytes)
  returns mallocngPosixMemalignRet align len
  ensures_pure MallocngCallAccounting
    16 (MallocngStepBound (if ok then eff else 0) b.peakCount) s0 sf
  oom_when MallocngOomCond svc (if ok then eff else 0) b.peakCount s0 sf

/-! ## Interface Well-Formedness and Top-Level API Bundle -/

/-- Interface well-formedness, placement-generic startup initialization, runtime/RO splitting, and
    linear interval/byte footprint accounting laws (`MallocngIfaceFacts J`) for `J : MallocngIface`
    (independent of the entry-point `subroutine_ok` contracts bundled in `MallocngTopFacts`). -/
structure MallocngIfaceFacts (J : MallocngIface) : Prop where
  init : mallocngInitStmt J
  /-- Separation-logic startup entailment: any post-`__init_libc` state owning
      `MallocngStartupResources A tp` ghost-initializes to an empty `MallocngHeap` with
      `mallocngZeroBudget` and `ivs = []`. -/
  init_resources :
    ∀ (A : MallocngAddrs) (tp brkStart : BitVec 64),
      0xa4 ≤ tp.toNat →
      tp.toNat ≤ 2 ^ 48 →
      MallocngBrkStartWf brkStart →
      MallocngStartupResources A tp ⊢
        |==> (∃∗ γ : GhostName, J.MallocngHeap γ A tp brkStart brkStart mallocngZeroBudget [])
  /-- Split/rejoin law exposing `MallocngRuntime A tp` (`*(tp - 0xa4)` `errno`,
      `__libc.need_locks = 0`, `__libc.page_size = 4096`) separately from `J.MallocngCore` so
      non-allocator `libc` / `std` I/O calls can read/write `errno` and read `__libc` between
      allocator calls and rejoin `J.MallocngHeap` afterwards. -/
  heap_split_runtime :
    ∀ (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
      (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)),
      J.MallocngHeap γ A tp brkStart brk b ivs =
        (J.MallocngCore γ A brkStart brk b ivs ∗ MallocngRuntime A tp)
  /-- `J.MallocngHeap` splits into a duplicable read-only `.rodata` part `Ro` (`Ro ∗ Ro = Ro`) and
      an exclusive part `Rw` containing no `.ro` cells. -/
  heap_roSplit :
    ∀ (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
      (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)),
      ∃ Ro Rw : SepProp,
        J.MallocngHeap γ A tp brkStart brk b ivs = (Ro ∗ Rw) ∧
        (Ro ∗ Ro) = Ro ∧
        ∀ (h : Heap) (a : BitVec 64) (v : BitVec 8), SepProp.Holds Rw h → h a ≠ some (.ro v)
  block_noRO :
    ∀ (γ : GhostName) (p : BitVec 64) (n : Nat) (h : Heap) (a : BitVec 64) (v : BitVec 8),
      SepProp.Holds (J.Block γ p n) h → h a ≠ some (.ro v)
  block_nonnull :
    ∀ (γ : GhostName) (p : BitVec 64) (n : Nat),
      J.Block γ p n ⊢
        ⌜p ≠ 0#64 ∧ 16 ∣ p.toNat ∧ p.toNat + n ≤ 2 ^ 48 ∧ n ≤ MallocngMaxAllocSize⌝ ∗ J.Block γ p n
  block_exclusive :
    ∀ (γ : GhostName) (p₁ : BitVec 64) (n₁ : Nat) (p₂ : BitVec 64) (n₂ : Nat),
      J.Block γ p₁ n₁ ∗ J.Block γ p₂ n₂ ⊢
        ⌜p₁ ≠ p₂⌝ ∗ J.Block γ p₁ n₁ ∗ J.Block γ p₂ n₂
  /-- Linear interval-count and byte-count accounting bound across all `SYS_brk` and `PROT_NONE`
      `SYS_mmap` outcomes: any heap `h` satisfying `J.MallocngHeap γ A tp brkStart brk b ivs`
      satisfies:
      1. `b.liveCost ≤ b.peakCost ∧ b.liveCount ≤ b.peakCount`,
      2. `ivs.length ≤ 48 + 2 * b.peakCount`,
         `(ivs.map Prod.snd).sum ≤ MallocngBaseOverhead + MallocngLinearFactor * b.peakCost`, and
         `∀ iv ∈ ivs, iv.1.toNat + iv.2 ≤ 2 ^ 48`,
      3. `h` is covered by an interval list `allIvs` of length `≤ 64 + 2 * b.peakCount` and total
         byte length `≤ MallocngBaseOverhead + MallocngLinearFactor * b.peakCost`, and
      4. `h` has a finite byte domain `dom` of length
         `≤ MallocngBaseOverhead + MallocngLinearFactor * b.peakCost`. -/
  heap_footprint_bound :
    ∀ (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
      (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) (h : Heap),
      SepProp.Holds (J.MallocngHeap γ A tp brkStart brk b ivs) h →
      (b.liveCost ≤ b.peakCost ∧ b.liveCount ≤ b.peakCount) ∧
      (ivs.length ≤ 48 + 2 * b.peakCount ∧
        (ivs.map Prod.snd).sum ≤ MallocngBaseOverhead + MallocngLinearFactor * b.peakCost ∧
        ∀ iv ∈ ivs, iv.1.toNat + iv.2 ≤ 2 ^ 48) ∧
      (∃ allIvs : List (BitVec 64 × Nat),
        allIvs.length ≤ 64 + 2 * b.peakCount ∧
        (allIvs.map Prod.snd).sum ≤ MallocngBaseOverhead + MallocngLinearFactor * b.peakCost ∧
        ∀ a : BitVec 64, (h a ≠ none ∨ h.mapped a = true) → MallocngInIntervals allIvs a) ∧
      ∃ dom : List (BitVec 64),
        dom.length ≤ MallocngBaseOverhead + MallocngLinearFactor * b.peakCost ∧
        ∀ a : BitVec 64, (h a ≠ none ∨ h.mapped a = true) → a ∈ dom

/-- Existential interface well-formedness, startup initialization, runtime/RO splitting, and linear
    interval/byte footprint bound statement. -/
def MallocngIfaceWfStmt : Prop :=
  ∃ J : MallocngIface, MallocngIfaceFacts J

/-- Multi-block placement-generic contract for an exported function `fnName` of
    `VerifiedLibraries.mallocngLib` under `mpl : Obj.MultiPlacement` and supervisor-call handler `svc`:
    `fnName` is exported by `VerifiedLibraries.mallocngLib`, resolves via `Obj.lookupBlockSym` to some
    block `(i, off)`, and satisfies `subroutine_ok` on `mallocngBlockProg mpl i svc` at
    `VerifiedLibraries.mallocngLib.fnAddr mpl fnName` with `VerifiedLibraries.mallocngLib.withCodeLoaded mpl`
    adjoined. -/
def mallocngMultiEntryOk {S α : Type} [ToBaseSpec S α]
    (mpl : Obj.MultiPlacement) (svc : State → State) (fnName : String) (spec : S) : Prop :=
  fnName ∈ VerifiedLibraries.mallocngLib.exports ∧
  ∃ i off, Obj.lookupBlockSym fnName VerifiedLibraries.mallocngLib.blocks = some (i, off) ∧
    subroutine_ok (mallocngBlockProg mpl i svc)
      (VerifiedLibraries.mallocngLib.fnAddr mpl fnName)
      (VerifiedLibraries.mallocngLib.withCodeLoaded mpl (ToBaseSpec.toSpec spec (mpl.base i)))

/-- Joint `subroutine_ok` bundle for the six C allocator entry points (`malloc`, `free`, `calloc`,
    `realloc`, `aligned_alloc`, `posix_memalign`) exported by `VerifiedLibraries.mallocngLib`. -/
structure MallocngPlacedEntryContracts (J : MallocngIface) (mpl : Obj.MultiPlacement)
    (svc : State → State) : Prop where
  malloc_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "malloc"
      (mallocngMallocSpec J svc γ (mallocngAddrsOfPlacement mpl))
  free_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "free"
      (mallocngFreeSpec J γ (mallocngAddrsOfPlacement mpl))
  calloc_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "calloc"
      (mallocngCallocSpec J svc γ (mallocngAddrsOfPlacement mpl))
  realloc_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "realloc"
      (mallocngReallocSpec J svc γ (mallocngAddrsOfPlacement mpl))
  alignedAlloc_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "aligned_alloc"
      (mallocngAlignedAllocSpec J svc γ (mallocngAddrsOfPlacement mpl))
  posixMemalign_ok : ∀ γ : GhostName,
    mallocngMultiEntryOk mpl svc "posix_memalign"
      (mallocngPosixMemalignSpec J svc γ (mallocngAddrsOfPlacement mpl))

/-- Complete top-level correctness record (`MallocngTopFacts J`) for stock `musl` v1.2.5 `mallocng`
    at a single abstract interface `J : MallocngIface`: combines `MallocngIfaceFacts J` with
    `entries_ok`: hookless multi-block `Obj.MultiPlacedLib` contracts
    (`MallocngPlacedEntryContracts`) for all 6 C allocator exports surviving `--gc-sections` in
    stock static links (`malloc`, `free`, `calloc`, `realloc`, `aligned_alloc`, `posix_memalign`),
    with zero external leaf-helper hooks and zero `.rodata`/`.text` contiguity assumptions. -/
structure MallocngTopFacts (J : MallocngIface) : Prop extends MallocngIfaceFacts J where
  /-- Multi-block placement-generic entry-point contracts (`entries_ok`): for every multi-block
      placement `mpl : Obj.MultiPlacement` under which `VerifiedLibraries.mallocngLib` is `Placeable`
      (`Obj.MultiPlacedLib.Placeable`) and every valid supervisor-call handler `svc`
      (`MallocngSvcValid svc`), all 6 exported C entry points satisfy
      `MallocngPlacedEntryContracts J mpl svc` (with zero external hooks and zero `.rodata`
      contiguity premise; `DataDisjoint mpl` is not even needed at call time and is used only at
      startup via `MultiPlacedLib.satisfies_dataInit_of_inElf` to feed `init`). -/
  entries_ok :
    ∀ (mpl : Obj.MultiPlacement) (svc : State → State),
      VerifiedLibraries.mallocngLib.Placeable mpl →
      MallocngSvcValid svc →
      MallocngPlacedEntryContracts J mpl svc

/-- Complete top-level existential correctness statement for `mallocng`: there exists a single
    `J : MallocngIface` satisfying both `MallocngIfaceFacts J` and all placed
    entry-point contracts (`MallocngTopFacts J`). -/
def MallocngTopStmt : Prop :=
  ∃ J : MallocngIface, MallocngTopFacts J

end VerifiedLibraries.Mallocng
