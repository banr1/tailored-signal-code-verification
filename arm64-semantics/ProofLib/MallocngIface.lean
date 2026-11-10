/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Process
public import Arm64.Trusted.Syscalls.Common
public import Arm64.Trusted.Spec.Hoare
public import ProofLib.SepLogic.Stack
public import ProofLib.SepLogic.Bytes
public import ProofLib.SepLogic.Region

/-!
# Separation-Logic Interface for Static `musl` `mallocng`

Defines the two-tier separation-logic interface (`MallocngCoreIface` and `MallocngIface`) and
virtual-memory budget profile (`MallocngLimits`) for static AArch64 `ET_EXEC` binaries linked
against `musl` 1.2.5 `mallocng`. When `lim.FitsVaSpace` holds and initial memory satisfies
`MallocngInitialMemWf`, every allocation within `lim` terminates in `.Running` without panic,
exit, or OOM and returns a non-null 16-byte-aligned pointer.
-/

@[expose] public section

namespace ProofLib

open Arm64 Arm64.Process

/-! ## Budget Constants, Lookup Tables, and Link-Address Configuration -/

/-- Minimum per-block effective byte cost (`65536` B = `64 KiB` = 1 coarse `mmap` slab) charged per
    live allocation in `mallocng` virtual-memory accounting. -/
abbrev MallocngMinBlockCost : Nat := 65536

/-- Effective live byte cost of a standard (`malloc` / `calloc` / `realloc`) allocation of `req`
    user-requested bytes: `max req MallocngMinBlockCost`. -/
@[inline] def mallocngBlockCost (req : Nat) : Nat :=
  max req MallocngMinBlockCost

/-- Over-allocation request size passed to `__libc_malloc_impl` by `aligned_alloc(align, req)`
    (`req` when `align ≤ 16`, and `req + align - 16` when `align > 16`). -/
@[inline] def mallocngAlignedEffReq (align req : Nat) : Nat :=
  if align ≤ 16 then req else req + align - 16

/-- Effective live byte cost charged by `aligned_alloc(align, req)` / `posix_memalign`:
    `mallocngBlockCost req + (max align 16 - 16)`. -/
@[inline] def mallocngAlignedBlockCost (align req : Nat) : Nat :=
  mallocngBlockCost req + (max align 16 - 16)

/-- Per-binary virtual-memory budget profile for `MallocngCoreIface` and `MallocngIface`,
    bounding single-request size (`maxReq`), cumulative/peak live block cost (`maxPeakCost`),
    and peak live allocation count (`maxPeakBlocks`). -/
structure MallocngLimits where
  maxReq        : Nat := 16 * 2 ^ 30
  maxPeakCost   : Nat := 85 * 2 ^ 30
  maxPeakBlocks : Nat := 4096
  deriving DecidableEq, Repr

/-- Decidable check that `lim` leaves a guaranteed unmapped virtual-address gap in
    `[MMAP_MIN_ADDR, 2 ^ 48)` across all `MallocngCoreIface` calls (`malloc`, `free`) over a static
    ELF (`≤ 1 GiB`) and initial stack (`≤ 1 TiB`). -/
def MallocngLimits.CoreFitsVaSpace (lim : MallocngLimits) : Bool :=
  let step := ((lim.maxReq + 8192 + 4095) / 4096) * 4096 + 32 * 2 ^ 20 + 4096 * lim.maxPeakBlocks
  let mapped := (2 ^ 30 + 2 ^ 40) + (32 * 2 ^ 20 + 48 * lim.maxPeakCost) + step
  decide (lim.maxReq ≤ 0x7fffffffffffeffe ∧
    0x10000 + mapped + (67 + 2 * lim.maxPeakBlocks) * (step + 4096) ≤ 2 ^ 48)

/-- Physical memory budget (`physMemAvail`) sufficient to rule out physical-memory OOM across all
    `MallocngCoreIface` calls (`malloc`, `free`) over a static ELF (`brkBase ≤ 5 MiB`) and initial
    stack (`≤ 128 MiB`). -/
def MallocngLimits.CorePhysMem (lim : MallocngLimits) : Nat :=
  let step := ((lim.maxReq + 8192 + 4095) / 4096) * 4096 + 32 * 2 ^ 20 + 4096 * lim.maxPeakBlocks
  133 * 2 ^ 20 + (32 * 2 ^ 20 + 48 * lim.maxPeakCost) + 2 * step

/-- Decidable check that `lim` leaves a guaranteed unmapped virtual-address gap across all
    `MallocngIface` calls (including `realloc`'s `+ 2 ^ 31` step slack). -/
def MallocngLimits.FitsVaSpace (lim : MallocngLimits) : Bool :=
  let eff := lim.maxReq + 2 ^ 31
  let step := ((eff + 8192 + 4095) / 4096) * 4096 + 32 * 2 ^ 20 + 4096 * lim.maxPeakBlocks
  let mapped := (2 ^ 30 + 2 ^ 40) + (32 * 2 ^ 20 + 48 * lim.maxPeakCost) + step
  decide (eff ≤ 0x7fffffffffffeffe ∧
    0x10000 + mapped + (67 + 2 * lim.maxPeakBlocks) * (step + 4096) ≤ 2 ^ 48)

/-- Stack scratch reserve below `sp` (`4096` B = 1 page, covering nested `alloc_slot` frames). -/
abbrev MallocngStackBytes : Nat := 4096

/-- Stock `musl` v1.2.5 `__malloc_size_classes[0..47]` (`48` entries, in `UNIT = 16`-byte multiples). -/
def mallocngSizeClassUnits : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15,
   18, 20, 25, 31, 36, 42, 50, 63, 72, 84, 102, 127,
   146, 170, 204, 255, 292, 340, 409, 511, 584, 682, 818, 1023,
   1169, 1364, 1637, 2047, 2340, 2730, 3276, 4095, 4680, 5460, 6552, 8191]

/-- Exact 200-byte `.rodata` lookup-table block `[__malloc_size_classes, __malloc_size_classes + 200)`
    for stock `musl` v1.2.5 `mallocng`. -/
def mallocngRoTablesBytes : List (BitVec 8) :=
  let sizeClasses := mallocngSizeClassUnits.flatMap fun u =>
    [BitVec.ofNat 8 (u % 256), BitVec.ofNat 8 (u / 256)]
  let debruijn32 := ([0, 1, 23, 2, 29, 24, 19, 3, 30, 27, 25, 11, 20, 8, 4, 13,
    31, 22, 28, 18, 26, 10, 7, 12, 21, 17, 9, 6, 16, 5, 15, 14] : List Nat).map (BitVec.ofNat 8)
  let medCntTab := ([28, 24, 20, 32] : List Nat).map (BitVec.ofNat 8)
  let smallCntTab := ([30, 30, 30, 31, 15, 15, 20, 10, 10,
    31, 15, 7, 25, 12, 6, 21, 10, 5,
    18, 8, 4, 31, 15, 7, 28, 14, 6] : List Nat).map (BitVec.ofNat 8)
  sizeClasses ++ debruijn32 ++ medCntTab ++ List.replicate 4 0#8 ++
    smallCntTab ++ List.replicate 5 0#8 ++ debruijn32

/-- Link-address configuration for `musl` 1.2.5 `mallocng` in a static AArch64 `ET_EXEC` binary. -/
structure MallocngAddrs where
  mallocAddr               : BitVec 64
  freeAddr                 : BitVec 64
  callocAddr               : BitVec 64
  reallocAddr              : BitVec 64
  alignedAllocAddr         : BitVec 64
  posixMemalignAddr        : BitVec 64
  /-- `.rodata` start of `__malloc_size_classes` (`200` bytes through `debruijn32`). -/
  roTablesAddr             : BitVec 64
  /-- `libc.need_locks` (`1` byte, `0#8` in single-threaded processes). -/
  libcNeedLocksAddr        : BitVec 64
  /-- `libc.auxv` (`8` bytes, pointer to initial-stack `auxv` `(tag, val)` array). -/
  libcAuxvAddr             : BitVec 64
  /-- `libc.page_size` (`8` bytes, `4096#64`). -/
  libcPageSizeAddr         : BitVec 64
  /-- `__malloc_lock` (`4` bytes in `.bss`, initially `0#32`). -/
  mallocLockAddr           : BitVec 64
  /-- `__aligned_alloc_replaced` (`4` bytes in `.bss`, initially `0#32`). -/
  alignedAllocReplacedAddr : BitVec 64
  /-- `__malloc_replaced` (`4` bytes in `.bss`, initially `0#32`). -/
  mallocReplacedAddr       : BitVec 64
  /-- `__malloc_context` (`928` bytes = `0x3a0` bytes in `.bss`, initially zeroed). -/
  mallocCtxAddr            : BitVec 64
  /-- Initial program break (`img.brkStart`). -/
  brkBase                  : BitVec 64
  deriving DecidableEq, Repr

/-! ## Process-State Preservation, TLS `errno`, and Startup Preconditions -/

/-- Thread-local `errno` address (`__errno_location()` = `TPIDR_EL0 - 0xa4` on musl AArch64). -/
@[inline] def muslErrnoAddr (s : State) : BitVec 64 :=
  s.tpidrEl0 - 0xa4#64

/-- Non-allocator machine state preserved across every `mallocng` call:
    file-system state (`fs`), observable syscall/I/O trace (`trace`), signal dispositions
    (`sigActions`), thread pointer (`tpidrEl0`), and frozen RX/RO pages (`KeepsFrozen`). -/
def MallocngStatePreserved (s0 sf : State) : Prop :=
  sf.fs = s0.fs ∧
  sf.trace = s0.trace ∧
  sf.sigActions = s0.sigActions ∧
  sf.tpidrEl0 = s0.tpidrEl0 ∧
  s0.mem.KeepsFrozen sf.mem

/-- Encode a list of `(tag, val)` `auxv` pairs terminated by `(AT_NULL, 0)` as little-endian bytes. -/
def encodeAuxvBytes (pairs : List (BitVec 64 × BitVec 64)) : List (BitVec 8) :=
  ((pairs ++ [(AuxvTag.null, 0#64)]).flatMap fun (t, v) => [t, v]).flatMap fun w =>
    List.ofFn (fun i : Fin 8 => w.extractLsb' (8 * i.val) 8)

/-- Startup resources consumed by `mallocng` heap initialization after `__init_libc`:
    the 200-byte `.rodata` lookup tables (`mallocngRoTablesBytes`), `libc.need_locks = 0#8`,
    `libc.auxv = auxvAddr`, `libc.page_size = 4096#64`, the initial-stack `auxv` array containing
    `(AT_RANDOM, randomAddr)` terminated by `(AT_NULL, 0)`, the upper 8 bytes of `AT_RANDOM`,
    and the thread-local `errno` slot `muslErrnoAddr s ↦₃₂ e0`. -/
def MallocngStartupInputs (addrs : MallocngAddrs)
    (auxvAddr randomAddr : BitVec 64)
    (prePairs sufPairs : List (BitVec 64 × BitVec 64))
    (randHi8 : List (BitVec 8)) (e0 : BitVec 32) (s : State) : SepProp :=
  ⌜randHi8.length = 8 ∧
    0xa4 ≤ s.tpidrEl0.toNat ∧
    s.tpidrEl0.toNat ≤ 2 ^ 48 ∧
    prePairs.length + sufPairs.length ≤ 64 ∧
    auxvAddr.toNat % 8 = 0 ∧
    auxvAddr.toNat + 16 * (prePairs.length + sufPairs.length + 2) ≤ 2 ^ 48 ∧
    randomAddr.toNat + 16 ≤ 2 ^ 48 ∧
    (∀ e ∈ prePairs, e.1 ≠ AuxvTag.null ∧ e.1 ≠ AuxvTag.random) ∧
    (∀ e ∈ sufPairs, e.1 ≠ AuxvTag.null ∧ e.1 ≠ AuxvTag.random)⌝ ∗
  (addrs.roTablesAddr ↦ᵣ mallocngRoTablesBytes) ∗
  (addrs.libcNeedLocksAddr ↦₈ 0#8) ∗
  (addrs.libcAuxvAddr ↦₆₄ auxvAddr) ∗
  (addrs.libcPageSizeAddr ↦₆₄ 4096#64) ∗
  (auxvAddr ↦ₛ encodeAuxvBytes (prePairs ++ [(AuxvTag.random, randomAddr)] ++ sufPairs)) ∗
  ((randomAddr + 8#64) ↦ₛ randHi8) ∗
  (muslErrnoAddr s ↦₃₂ e0)

/-- Exclusive zero-initialized `.bss` globals owned by `mallocng` prior to first allocation:
    `__malloc_lock` (4 B), `__aligned_alloc_replaced` (4 B), `__malloc_replaced` (4 B), and
    `__malloc_context` (928 B). -/
def MallocngInitialBss (addrs : MallocngAddrs) : SepProp :=
  (addrs.mallocLockAddr ↦₃₂ 0#32) ∗
  (addrs.alignedAllocReplacedAddr ↦₃₂ 0#32) ∗
  (addrs.mallocReplacedAddr ↦₃₂ 0#32) ∗
  (addrs.mallocCtxAddr ↦ₛ List.replicate 928 0#8)

/-- Initial memory-map well-formedness at `main` entry: `s.brk = s.brkStart = addrs.brkBase`
    (page-aligned in `[0x10000, 1 GiB]`), and every mapped byte in `s.mem` belongs either to the
    static ELF image `[imgLo, addrs.brkBase)` or to the initial user stack `[stackBase, stackTop)`
    with `STACK_BASE_MIN ≤ stackBase` and `stackTop - stackBase ≤ 128 MiB`. -/
def MallocngInitialMemWf (addrs : MallocngAddrs) (imgLo stackBase stackTop : Nat) (s : State) : Prop :=
  s.brk = addrs.brkBase ∧
  s.brkStart = addrs.brkBase ∧
  addrs.brkBase.toNat % 4096 = 0 ∧
  0x10000 ≤ addrs.brkBase.toNat ∧
  imgLo ≤ addrs.brkBase.toNat ∧
  addrs.brkBase.toNat ≤ 2 ^ 30 ∧
  STACK_BASE_MIN ≤ stackBase ∧
  stackBase ≤ stackTop ∧
  stackTop - stackBase ≤ 128 * 2 ^ 20 ∧
  stackTop ≤ TASK_SIZE ∧
  ∀ a : BitVec 64, (s.mem.perm a).mapped = true →
    (imgLo ≤ a.toNat ∧ a.toNat < addrs.brkBase.toNat) ∨
    (stackBase ≤ a.toNat ∧ a.toNat < stackTop)

/-! ## Core Allocator Interface -/

/-- Non-zero power-of-two alignment check bounded by `2 ^ 31` (avoiding the signed 32-bit
    `int reserved` overflow in `musl` 1.2.5 `set_size` at `align ≥ 2 ^ 32`). -/
def MallocngAlignOk (align : Nat) : Prop :=
  align ≠ 0 ∧ (∃ k : Nat, align = 2 ^ k) ∧ align ≤ 2 ^ 31

/-- Core separation-logic interface for `musl` `mallocng` over a code-bearing `Program` `P`,
    link-address configuration `addrs`, and budget profile `lim`. -/
structure MallocngCoreIface (P : Program) (addrs : MallocngAddrs)
    (lim : MallocngLimits := {}) where
  /-- Abstract allocator heap assertion at ghost instance `γ`, tracking `liveCost : Nat` total
      effective live byte cost (`∑ mallocngBlockCost req`) and `liveBlocks : Nat` live allocations
      in machine state `s` (internally bounding `peakCost ≤ lim.maxPeakCost` and
      `peakCount ≤ lim.maxPeakBlocks`). -/
  Heap : GhostName → Nat → Nat → State → SepProp

  /-- Per-allocation ownership token for a live heap block at non-null pointer `p` of exact
      requested size `n : Nat` bytes (paired with caller-owned `memRegion p n`). -/
  Block : GhostName → BitVec 64 → Nat → SepProp

  /-- Every live block is non-null and fits in the 64-bit address space without wrapping. -/
  block_noWrap : ∀ (γ : GhostName) (p : BitVec 64) (n : Nat),
    Block γ p n ⊢ ⌜p ≠ 0#64 ∧ p.toNat + n < 2 ^ 64⌝ ∗ Block γ p n

  /-- Every `mallocng` block is at least 16-byte (`UNIT = 16`) aligned. -/
  block_aligned16 : ∀ (γ : GhostName) (p : BitVec 64) (n : Nat),
    Block γ p n ⊢ ⌜16 ∣ p.toNat⌝ ∗ Block γ p n

  /-- Every live block resides within the 48-bit user virtual address space (`≤ USER_VA_LIMIT`). -/
  block_userVa : ∀ (γ : GhostName) (p : BitVec 64) (n : Nat),
    Block γ p n ⊢ ⌜p.toNat + n ≤ Arm64.USER_VA_LIMIT⌝ ∗ Block γ p n

  /-- Frame-friendly state transport: CPU stores and non-VM syscalls (`openat`, `fstat`, `read`,
      `write`, `close`, `fcntl`, `ppoll`, `rt_sigaction`) preserve `brk`, `brkStart`,
      `physMemAvail`, and page permissions `mem.perm`, transporting `Heap` with zero spatial proof
      overhead. -/
  heap_transport : ∀ {γ : GhostName} {lc blk : Nat} {s1 s2 : State},
    s2.brk = s1.brk →
    s2.brkStart = s1.brkStart →
    s2.physMemAvail = s1.physMemAvail →
    (∀ a : BitVec 64, s2.mem.perm a = s1.mem.perm a) →
    Heap γ lc blk s1 ⊢ Heap γ lc blk s2

  /-- Extract `addrs.libcNeedLocksAddr ↦₈ 0#8` from `Heap` at process teardown (after the last
      allocator call) so post-`main` `libc` exit handlers can read `libc.need_locks`. -/
  heap_need_locks : ∀ (γ : GhostName) (lc blk : Nat) (s : State),
    Heap γ lc blk s ⊢ (addrs.libcNeedLocksAddr ↦₈ 0#8) ∗ ∃∗ R : SepProp, R

  /-- Empty-heap initialization after `__init_libc`: consumes `MallocngInitialBss` and
      `MallocngStartupInputs` to produce a fresh ghost instance `γ` with `liveCost = 0` and
      `liveBlocks = 0`, returning the thread-local `errno` slot to the caller. -/
  init_heap :
    ∀ {s : State} {R : SepProp} {imgLo stackBase stackTop : Nat}
      {auxvAddr randomAddr : BitVec 64}
      {prePairs sufPairs : List (BitVec 64 × BitVec 64)}
      {randHi8 : List (BitVec 8)} {e0 : BitVec 32},
      P.CodeLoaded s.mem →
      (∀ i < 200, s.mem.Frozen (addrs.roTablesAddr + BitVec.ofNat 64 i)) →
      MallocngInitialMemWf addrs imgLo stackBase stackTop s →
      lim.CorePhysMem ≤ s.physMemAvail →
      s.mem ⊨ (MallocngInitialBss addrs ∗
               MallocngStartupInputs addrs auxvAddr randomAddr prePairs sufPairs randHi8 e0 s ∗ R) →
      ∃ (γ : GhostName) (e1 : BitVec 32),
        s.mem ⊨ (Heap γ 0 0 s ∗ (muslErrnoAddr s ↦₃₂ e1) ∗ R)

  /-- `void *malloc(size_t req)` (`addrs.mallocAddr`):
      Whenever `req ≤ lim.maxReq`, `lc + mallocngBlockCost req ≤ lim.maxPeakCost`, and
      `blk + 1 ≤ lim.maxPeakBlocks` (including `req = 0`), terminates in `.Running` without
      panic/exit/OOM and returns `ret ≠ 0#64` with fresh `Block γ ret req ∗ memRegion ret req`. -/
  malloc_ok : ∀ (γ : GhostName),
    subroutine_ok P addrs.mallocAddr
      ({ pre := fun (lc, blk, req, e0) s0 =>
           ⌜req = (s0.readReg64 (.gpr 0#5)).toNat ∧
             req ≤ lim.maxReq ∧
             lc + mallocngBlockCost req ≤ lim.maxPeakCost ∧
             blk + 1 ≤ lim.maxPeakBlocks⌝ ∗
           Heap γ lc blk s0 ∗
           (muslErrnoAddr s0 ↦₃₂ e0) ∗
           stackAt s0.sp MallocngStackBytes
         post := fun (lc, blk, req, _) s0 sf =>
           let ret := sf.readReg64 (.gpr 0#5)
           ⌜MallocngStatePreserved s0 sf ∧
             ret ≠ 0#64 ∧
             16 ∣ ret.toNat ∧
             ret.toNat + req < 2 ^ 64⌝ ∗
           Heap γ (lc + mallocngBlockCost req) (blk + 1) sf ∗
           Block γ ret req ∗
           memRegion ret req ∗
           (∃∗ e1 : BitVec 32, muslErrnoAddr s0 ↦₃₂ e1) ∗
           stackAt s0.sp MallocngStackBytes } :
        Spec (Nat × Nat × Nat × BitVec 32))

  /-- `void free(void *p)` (`addrs.freeAddr`): no-op when `optReq = none` (`p = 0#64`); when
      `optReq = some req` (`p ≠ 0#64`), consumes `Block γ p req ∗ memRegion p req` and returns
      `Heap γ (lc - mallocngBlockCost req) (blk - 1) sf`. -/
  free_ok : ∀ (γ : GhostName),
    subroutine_ok P addrs.freeAddr
      ({ pre := fun (lc, blk, optReq, e0) s0 =>
           let p := s0.readReg64 (.gpr 0#5)
           Heap γ lc blk s0 ∗
           (match optReq with
            | none => ⌜p = 0#64⌝
            | some req => ⌜p ≠ 0#64⌝ ∗ Block γ p req ∗ memRegion p req) ∗
           (muslErrnoAddr s0 ↦₃₂ e0) ∗
           stackAt s0.sp MallocngStackBytes
         post := fun (lc, blk, optReq, _) s0 sf =>
           ⌜MallocngStatePreserved s0 sf⌝ ∗
           (match optReq with
            | none => Heap γ lc blk sf
            | some req => Heap γ (lc - mallocngBlockCost req) (blk - 1) sf) ∗
           (∃∗ e1 : BitVec 32, muslErrnoAddr s0 ↦₃₂ e1) ∗
           stackAt s0.sp MallocngStackBytes } :
        Spec (Nat × Nat × Option Nat × BitVec 32))

/-! ## Extended Allocator Interface -/

/-- Extended `mallocng` interface adding `calloc`, `realloc`, `aligned_alloc`, and
    `posix_memalign`. -/
structure MallocngIface (P : Program) (addrs : MallocngAddrs) (lim : MallocngLimits := {}) extends
    MallocngCoreIface P addrs lim where

  /-- `void *calloc(size_t nmemb, size_t size)` (`addrs.callocAddr`). -/
  calloc_ok : ∀ (γ : GhostName),
    subroutine_ok P addrs.callocAddr
      ({ pre := fun (lc, blk, nmemb, sz, e0) s0 =>
           let total := nmemb * sz
           ⌜nmemb = (s0.readReg64 (.gpr 0#5)).toNat ∧
             sz = (s0.readReg64 (.gpr 1#5)).toNat ∧
             total ≤ lim.maxReq ∧
             lc + mallocngBlockCost total ≤ lim.maxPeakCost ∧
             blk + 1 ≤ lim.maxPeakBlocks⌝ ∗
           Heap γ lc blk s0 ∗
           (muslErrnoAddr s0 ↦₃₂ e0) ∗
           stackAt s0.sp MallocngStackBytes
         post := fun (lc, blk, nmemb, sz, _) s0 sf =>
           let ret := sf.readReg64 (.gpr 0#5)
           let total := nmemb * sz
           ⌜MallocngStatePreserved s0 sf ∧
             ret ≠ 0#64 ∧
             16 ∣ ret.toNat ∧
             ret.toNat + total < 2 ^ 64⌝ ∗
           Heap γ (lc + mallocngBlockCost total) (blk + 1) sf ∗
           Block γ ret total ∗
           (ret ↦ₛ List.replicate total 0#8) ∗
           (∃∗ e1 : BitVec 32, muslErrnoAddr s0 ↦₃₂ e1) ∗
           stackAt s0.sp MallocngStackBytes } :
        Spec (Nat × Nat × Nat × Nat × BitVec 32))

  /-- `void *realloc(void *p, size_t newReq)` (`addrs.reallocAddr`). -/
  realloc_ok : ∀ (γ : GhostName),
    subroutine_ok P addrs.reallocAddr
      ({ pre := fun (lc, blk, oldBlk, newReq, e0) s0 =>
           let p := s0.readReg64 (.gpr 0#5)
           ⌜newReq = (s0.readReg64 (.gpr 1#5)).toNat ∧
             newReq + 2 ^ 31 ≤ lim.maxReq ∧
             lc + mallocngBlockCost newReq ≤ lim.maxPeakCost ∧
             blk + 1 ≤ lim.maxPeakBlocks⌝ ∗
           Heap γ lc blk s0 ∗
           (match oldBlk with
            | none => ⌜p = 0#64⌝
            | some (oldReq, bs) =>
                ⌜p ≠ 0#64 ∧ bs.length = oldReq⌝ ∗ Block γ p oldReq ∗ (p ↦ₛ bs)) ∗
           (muslErrnoAddr s0 ↦₃₂ e0) ∗
           stackAt s0.sp MallocngStackBytes
         post := fun (lc, blk, oldBlk, newReq, _) s0 sf =>
           let ret := sf.readReg64 (.gpr 0#5)
           let kept := match oldBlk with
             | none => []
             | some (_, bs) => bs.take newReq
           let lc' := match oldBlk with
             | none => lc + mallocngBlockCost newReq
             | some (oldReq, _) => (lc - mallocngBlockCost oldReq) + mallocngBlockCost newReq
           let blk' := match oldBlk with
             | none => blk + 1
             | some _ => blk
           ⌜MallocngStatePreserved s0 sf ∧
             ret ≠ 0#64 ∧
             16 ∣ ret.toNat ∧
             ret.toNat + newReq < 2 ^ 64⌝ ∗
           Heap γ lc' blk' sf ∗
           Block γ ret newReq ∗
           (ret ↦ₛ kept) ∗
           memRegion (ret + BitVec.ofNat 64 kept.length) (newReq - kept.length) ∗
           (∃∗ e1 : BitVec 32, muslErrnoAddr s0 ↦₃₂ e1) ∗
           stackAt s0.sp MallocngStackBytes } :
        Spec (Nat × Nat × Option (Nat × List (BitVec 8)) × Nat × BitVec 32))

  /-- `void *aligned_alloc(size_t align, size_t req)` (`addrs.alignedAllocAddr`). -/
  aligned_alloc_ok : ∀ (γ : GhostName),
    subroutine_ok P addrs.alignedAllocAddr
      ({ pre := fun (lc, blk, align, req, e0) s0 =>
           let effReq := mallocngAlignedEffReq align req
           ⌜align = (s0.readReg64 (.gpr 0#5)).toNat ∧
             req = (s0.readReg64 (.gpr 1#5)).toNat ∧
             MallocngAlignOk align ∧
             effReq ≤ lim.maxReq ∧
             lc + mallocngAlignedBlockCost align req ≤ lim.maxPeakCost ∧
             blk + 1 ≤ lim.maxPeakBlocks⌝ ∗
           Heap γ lc blk s0 ∗
           (muslErrnoAddr s0 ↦₃₂ e0) ∗
           stackAt s0.sp MallocngStackBytes
         post := fun (lc, blk, align, req, _) s0 sf =>
           let ret := sf.readReg64 (.gpr 0#5)
           ⌜MallocngStatePreserved s0 sf ∧
             ret ≠ 0#64 ∧
             max align 16 ∣ ret.toNat ∧
             ret.toNat + req < 2 ^ 64⌝ ∗
           Heap γ (lc + mallocngAlignedBlockCost align req) (blk + 1) sf ∗
           Block γ ret req ∗
           memRegion ret req ∗
           (∃∗ e1 : BitVec 32, muslErrnoAddr s0 ↦₃₂ e1) ∗
           stackAt s0.sp MallocngStackBytes } :
        Spec (Nat × Nat × Nat × Nat × BitVec 32))

  /-- `int posix_memalign(void **memptr, size_t align, size_t req)` (`addrs.posixMemalignAddr`). -/
  posix_memalign_ok : ∀ (γ : GhostName),
    subroutine_ok P addrs.posixMemalignAddr
      ({ pre := fun (lc, blk, outPtr, oldVal, align, req, e0) s0 =>
           let effReq := mallocngAlignedEffReq align req
           ⌜outPtr = s0.readReg64 (.gpr 0#5) ∧
             align = (s0.readReg64 (.gpr 1#5)).toNat ∧
             req = (s0.readReg64 (.gpr 2#5)).toNat ∧
             8 ≤ align ∧
             MallocngAlignOk align ∧
             effReq ≤ lim.maxReq ∧
             lc + mallocngAlignedBlockCost align req ≤ lim.maxPeakCost ∧
             blk + 1 ≤ lim.maxPeakBlocks⌝ ∗
           Heap γ lc blk s0 ∗
           (outPtr ↦₆₄ oldVal) ∗
           (muslErrnoAddr s0 ↦₃₂ e0) ∗
           stackAt s0.sp (MallocngStackBytes + 32)
         post := fun (lc, blk, outPtr, _, align, req, _) s0 sf =>
           ⌜MallocngStatePreserved s0 sf ∧
             (sf.readReg64 (.gpr 0#5)).truncate 32 = 0#32⌝ ∗
           (∃∗ p : BitVec 64,
             ⌜p ≠ 0#64 ∧ max align 16 ∣ p.toNat ∧ p.toNat + req < 2 ^ 64⌝ ∗
             (outPtr ↦₆₄ p) ∗
             Heap γ (lc + mallocngAlignedBlockCost align req) (blk + 1) sf ∗
             Block γ p req ∗
             memRegion p req) ∗
           (∃∗ e1 : BitVec 32, muslErrnoAddr s0 ↦₃₂ e1) ∗
           stackAt s0.sp (MallocngStackBytes + 32) } :
        Spec (Nat × Nat × BitVec 64 × BitVec 64 × Nat × Nat × BitVec 32))

end ProofLib
