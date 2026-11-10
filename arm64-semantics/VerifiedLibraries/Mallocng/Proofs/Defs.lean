/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import ProofLib.BV
public import VerifiedLibraries.Mallocng.Spec.Top
public import VerifiedLibraries.Mallocng.Proofs.Cells
public import VerifiedLibraries.Mallocng.Proofs.SizeClasses
public import VerifiedLibraries.Mallocng.Proofs.GhostToken

/-!
# Machine Struct Encodings and Abstract Heap State

Defines binary struct encodings (`CtxFields`, `GroupDesc`, `MetaAreaDesc`, `FreeMetaDesc`),
circular doubly-linked list well-formedness (`CircularDllWf`), the abstract allocator state
`MallocngSt`, and the flat byte-ownership predicates (`CarvedUserByte`, `CarvedMetaByte`,
`OwnedRwByte`, `OwnedProtNoneByte`, `OwnedMappedByte`) backing `MallocngWF`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng

/-- Layout fit condition for Rust `std` `__rdl_{alloc,alloc_zeroed,realloc}` over `mallocng`:
    `mallocngAlignedEffSize align.toNat size.toNat ≤ MallocngMaxAllocSize`. -/
def MallocngLayoutFit (size align : BitVec 64) : Prop :=
  mallocngAlignedEffSize align.toNat size.toNat ≤ MallocngMaxAllocSize

instance (size align : BitVec 64) : Decidable (MallocngLayoutFit size align) :=
  inferInstanceAs (Decidable (_ ≤ _))

end VerifiedLibraries.Mallocng

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

/-! ## Signal-action frame lemmas -/

@[simp, arm64_norm, wp_norm]
theorem sigActions_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).sigActions = s.sigActions := by cases s; cases r <;> rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_writeReg32 (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).sigActions = s.sigActions := by cases s; cases r <;> rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_writeReg (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).sigActions = s.sigActions := by cases s; cases w <;> cases r <;> rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_writeVReg128 (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_writeVReg64 (s : State) (idx : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 idx v).sigActions = s.sigActions :=
  sigActions_writeVReg128 s idx (v.zeroExtend 128)
@[simp, arm64_norm, wp_norm]
theorem sigActions_writeVReg32 (s : State) (idx : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 idx v).sigActions = s.sigActions :=
  sigActions_writeVReg128 s idx (v.zeroExtend 128)
@[simp, arm64_norm, wp_norm]
theorem sigActions_advancePC (s : State) : s.advancePC.sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_setPC (s : State) (pc : BitVec 64) : (s.setPC pc).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_setPState (s : State) (ps : PState) : (s.setPState ps).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_setMem (s : State) (m : Memory) : (s.setMem m).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_setStatus (s : State) (st : ExecStatus) : (s.setStatus st).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_setBrk (s : State) (b : BitVec 64) : (s.setBrk b).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_setFs (s : State) (f : FsState) : (s.setFs f).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_setFpsr (s : State) (f : BitVec 32) : (s.setFpsr f).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_orFpsr (s : State) (f : BitVec 32) : (s.orFpsr f).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_nextOracle (s : State) : s.nextOracle.sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_stepExclOracle (s : State) : s.stepExclOracle.sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_stepExclLoop (s : State) : s.stepExclLoop.sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_appendTrace (s : State) (evs : List TraceEvent) : (s.appendTrace evs).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_applyWriteback (s : State) (wb : Option (Reg × BitVec 64)) :
    (applyWriteback s wb).sigActions = s.sigActions := by cases wb <;> simp [applyWriteback]
@[simp, arm64_norm, wp_norm]
theorem sigActions_setTpidrEl0 (s : State) (v : BitVec 64) :
    (setTpidrEl0 s v).sigActions = s.sigActions := by cases s; rfl
@[simp, arm64_norm, wp_norm]
theorem sigActions_setPhysMemAvail (s : State) (n : Nat) :
    (s.setPhysMemAvail n).sigActions = s.sigActions := by cases s; rfl
attribute [wp_norm]
  State.brk_setPhysMemAvail State.brkStart_setPhysMemAvail
  State.oracle_setPhysMemAvail State.oracleIdx_setPhysMemAvail

/-! ## `struct malloc_context` (`928` B = `0x3a0`) encoding -/

/-- Exact field representation of `musl` 1.2.5 `struct malloc_context` (`928` bytes = `0x3a0` on
    AArch64 LP64 with compile-time omitted `pagesize` field):
    - `+0x000` (`u64`): `secret`
    - `+0x008` (`u32`): `initDone` (`0` or `1`)
    - `+0x00c` (`u32`): `mmapCounter` (`unsigned mmap_counter`)
    - `+0x010` (`u64`): `freeMetaHead` (`struct meta *`)
    - `+0x018` (`u64`): `availMeta` (`struct meta *`)
    - `+0x020` (`u64`): `availMetaCount` (`size_t`)
    - `+0x028` (`u64`): `availMetaAreaCount` (`size_t`)
    - `+0x030` (`u64`): `metaAllocShift` (`size_t`)
    - `+0x038` (`u64`): `metaAreaHead` (`struct meta_area *`)
    - `+0x040` (`u64`): `metaAreaTail` (`struct meta_area *`)
    - `+0x048` (`u64`): `availMetaAreas` (`uintptr_t`)
    - `+0x050 .. +0x1d0` (`48 × u64`): `active` (`struct meta *[48]`)
    - `+0x1d0 .. +0x350` (`48 × u64`): `usageByClass` (`size_t[48]`)
    - `+0x350 .. +0x370` (`32 × u8`): `unmapSeq` (`uint8_t[32]`)
    - `+0x370 .. +0x390` (`32 × u8`): `bounces` (`uint8_t[32]`)
    - `+0x390` (`u8`): `seq` (`uint8_t`)
    - `+0x391 .. +0x398` (`7 × u8`): `seqPad` (`7` alignment padding bytes)
    - `+0x398 .. +0x3a0` (`u64`): `brk` (`uintptr_t`). -/
structure CtxFields where
  secret             : BitVec 64
  initDone           : BitVec 32
  mmapCounter        : BitVec 32
  freeMetaHead       : BitVec 64
  availMeta          : BitVec 64
  availMetaCount     : BitVec 64
  availMetaAreaCount : BitVec 64
  metaAllocShift     : BitVec 64
  metaAreaHead       : BitVec 64
  metaAreaTail       : BitVec 64
  availMetaAreas     : BitVec 64
  active             : List (BitVec 64)
  usageByClass       : List (BitVec 64)
  unmapSeq           : List (BitVec 8)
  bounces            : List (BitVec 8)
  seq                : BitVec 8
  seqPad             : List (BitVec 8)
  brk                : BitVec 64

/-- Zero-initialized `struct malloc_context` at process startup (`.bss`). -/
def emptyCtxFields : CtxFields where
  secret             := 0#64
  initDone           := 0#32
  mmapCounter        := 0#32
  freeMetaHead       := 0#64
  availMeta          := 0#64
  availMetaCount     := 0#64
  availMetaAreaCount := 0#64
  metaAllocShift     := 0#64
  metaAreaHead       := 0#64
  metaAreaTail       := 0#64
  availMetaAreas     := 0#64
  active             := List.replicate 48 0#64
  usageByClass       := List.replicate 48 0#64
  unmapSeq           := List.replicate 32 0#8
  bounces            := List.replicate 32 0#8
  seq                := 0#8
  seqPad             := List.replicate 7 0#8
  brk                := 0#64

/-- Serialize `CtxFields` to its exact `928`-byte AArch64 little-endian representation. -/
def CtxFields.toBytes (c : CtxFields) : List (BitVec 8) :=
  unpack64 c.secret ++
  unpack32 c.initDone ++
  unpack32 c.mmapCounter ++
  unpack64 c.freeMetaHead ++
  unpack64 c.availMeta ++
  unpack64 c.availMetaCount ++
  unpack64 c.availMetaAreaCount ++
  unpack64 c.metaAllocShift ++
  unpack64 c.metaAreaHead ++
  unpack64 c.metaAreaTail ++
  unpack64 c.availMetaAreas ++
  c.active.flatMap unpack64 ++
  c.usageByClass.flatMap unpack64 ++
  c.unmapSeq ++
  c.bounces ++
  [c.seq] ++
  c.seqPad ++
  unpack64 c.brk

private theorem flatMap_unpack64_length (xs : List (BitVec 64)) :
    (xs.flatMap unpack64).length = 8 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.flatMap_cons, List.length_append, unpack64_length, ih, List.length_cons]
    omega

theorem CtxFields.toBytes_length {c : CtxFields}
    (hAct : c.active.length = 48)
    (hUse : c.usageByClass.length = 48)
    (hUnm : c.unmapSeq.length = 32)
    (hBnc : c.bounces.length = 32)
    (hPad : c.seqPad.length = 7) :
    c.toBytes.length = 928 := by
  simp only [CtxFields.toBytes, List.length_append, unpack64_length, unpack32_length,
    flatMap_unpack64_length, hAct, hUse, hUnm, hBnc, hPad, List.length_singleton]

set_option maxRecDepth 20000 in
theorem emptyCtxFields_toBytes :
    emptyCtxFields.toBytes = List.replicate 928 0#8 := by
  decide

/-! ## Slot states, group descriptors, `meta_area` pages, and circular DLLs -/

/-- State of slot `idx` inside an active `mallocng` group:
    - `.freeAvail`: bit `idx` is set in `avail_mask` (ready for `try_avail` claim).
    - `.freeInactive`: bit `idx` is set in `freed_mask` (freed or unactivated `> active_idx`).
    - `.claimed`: bit `idx` was just cleared by `alloc_slot` (`try_avail` / `alloc_group`) and is
      in-flight on the stack before `enframe` writes its `.liveNested` or `.liveUser` headers
      (`0` `.claimed` slots exist at quiescent `MallocngWF` API boundaries).
    - `.liveNested childMeta`: allocated to a nested child group whose `struct meta *` is `childMeta`.
    - `.liveUser userPtr reqSize effCost`: allocated to caller pointer `userPtr` of nominal request
      `reqSize` bytes and accounting cost `effCost` (`max reqSize 16 ≤ effCost`). -/
inductive SlotState where
  | freeAvail
  | freeInactive
  | claimed
  | liveNested (childMeta : BitVec 64)
  | liveUser (userPtr : BitVec 64) (reqSize : Nat) (effCost : Nat)
  deriving DecidableEq

/-- Descriptor for an active `struct meta` (`40` B at `metaPtr`) and its `struct group` (`mem`). -/
structure GroupDesc where
  metaPtr    : BitVec 64
  prev       : BitVec 64
  next       : BitVec 64
  mem        : BitVec 64
  availMask  : BitVec 32
  freedMask  : BitVec 32
  lastIdx    : Nat
  sc         : Nat
  /-- Page count (`0` for nested groups; `≥ 1` for `mmap`-backed root groups). -/
  maplen     : Nat
  /-- Byte `active_idx` at `mem + 8` (`activeByte &&& 0x1f#8 = BitVec.ofNat 8 activeIdx`). -/
  activeByte : BitVec 8
  /-- Parent `struct meta *` (`none` iff `0 < maplen`; `some pm` iff nested inside `pm`). -/
  parentMeta : Option (BitVec 64)
  /-- Parent slot capacity `stride_parent - 4` when nested (`0` for root groups). -/
  nestedCap  : Nat
  /-- Slot state vector of length `lastIdx + 1`. -/
  slots      : List SlotState
  /-- True iff this is a fresh individually-`mmap`ped (`IS_MMAPPED`) group whose payload bytes are
      all zero (`calloc` / `__malloc_allzerop` invariant). -/
  freshZero  : Bool
  deriving DecidableEq

/-- Number of slots `cnt = lastIdx + 1` in `g`. -/
abbrev GroupDesc.cnt (g : GroupDesc) : Nat := g.lastIdx + 1

/-- Exact `get_stride(g)` in `musl` 1.2.5 `meta.h`:
    `maplen * 4096 - 16` (`maplen * 4096 - UNIT`) when `lastIdx == 0 ∧ 0 < maplen`, else
    `slotStride sc` (`UNIT * __malloc_size_classes[sc]`). -/
def GroupDesc.stride (g : GroupDesc) : Nat :=
  if g.lastIdx == 0 && 0 < g.maplen then g.maplen * 4096 - 16
  else slotStride g.sc

/-- True iff `IS_MMAPPED(g)` holds (`sc = 63` or single-slot `mmap` group narrower than `slotStride sc`). -/
def GroupDesc.isMmapped (g : GroupDesc) : Bool :=
  g.sc == 63 || (g.lastIdx == 0 && 0 < g.maplen && g.maplen * 4096 - 16 < slotStride g.sc)

/-- Start of `g->storage` (`g.mem + 16`). -/
def GroupDesc.storage (g : GroupDesc) : BitVec 64 := g.mem + 16#64

/-- Nominal start `storage + idx * stride` of slot `idx` in `g`. -/
def GroupDesc.slotStart (g : GroupDesc) (idx : Nat) : BitVec 64 :=
  g.storage + BitVec.ofNat 64 (idx * g.stride)

/-- Nominal end `slotStart idx + stride - 4` (`IB = 4`) of slot `idx` in `g`. -/
def GroupDesc.slotEnd (g : GroupDesc) (idx : Nat) : BitVec 64 :=
  g.slotStart idx + BitVec.ofNat 64 (g.stride - 4)

/-- Total byte span of `g` starting at `g.mem`: `maplen * 4096` for root groups, `nestedCap`
    (`stride_parent - 4`) for nested groups. -/
def GroupDesc.totalBytes (g : GroupDesc) : Nat :=
  if 0 < g.maplen then g.maplen * 4096 else g.nestedCap

/-- Active `active_idx` (`0 .. 31`) decoded from `g.activeByte`. -/
def GroupDesc.activeIdx (g : GroupDesc) : Nat :=
  (g.activeByte &&& 0x1f#8).toNat

/-- Packed 64-bit bitfield word at `metaPtr + 0x20` (`freeable = 1` at bit 5). -/
def GroupDesc.packedWord (g : GroupDesc) : BitVec 64 :=
  (BitVec.ofNat 64 g.lastIdx &&& 0x1f#64) |||
  (1#64 <<< 5) |||
  ((BitVec.ofNat 64 g.sc &&& 0x3f#64) <<< 6) |||
  (BitVec.ofNat 64 g.maplen <<< 12)

/-- Exact `40`-byte serialization of `struct meta` at `g.metaPtr`. -/
def GroupDesc.metaBytes (g : GroupDesc) : List (BitVec 8) :=
  unpack64 g.prev ++
  unpack64 g.next ++
  unpack64 g.mem ++
  unpack32 g.availMask ++
  unpack32 g.freedMask ++
  unpack64 g.packedWord

@[simp] theorem GroupDesc.metaBytes_length (g : GroupDesc) : g.metaBytes.length = 40 := rfl

/-- Descriptor for an activated `4096`-byte `struct meta_area` page (`nslots = 101`). -/
structure MetaAreaDesc where
  base : BitVec 64
  next : BitVec 64
  deriving DecidableEq

/-- Address of slot `k ∈ [0..100]` (`base + 24 + 40 * k`) inside `ma : MetaAreaDesc`. -/
def MetaAreaDesc.slotAddr (ma : MetaAreaDesc) (k : Nat) : BitVec 64 :=
  ma.base + BitVec.ofNat 64 (24 + 40 * k)

/-- Descriptor for a recycled `40`-byte `struct meta` node on `ctx.free_meta_head`
    (`+0` `prev`, `+8` `next`, `+16..+40` zeroed). -/
structure FreeMetaDesc where
  ptr  : BitVec 64
  prev : BitVec 64
  next : BitVec 64
  deriving DecidableEq

/-- Exact `40`-byte serialization of a recycled `struct meta` on `ctx.free_meta_head`. -/
def FreeMetaDesc.toBytes (fm : FreeMetaDesc) : List (BitVec 8) :=
  unpack64 fm.prev ++ unpack64 fm.next ++ List.replicate 24 0#8

@[simp] theorem FreeMetaDesc.toBytes_length (fm : FreeMetaDesc) : fm.toBytes.length = 40 := rfl

/-- Reusable circular doubly-linked list invariant (`ctx.free_meta_head` and `ctx.active[0..47]`):
    - when `nodes = []`, `head = 0#64`;
    - when `nodes = d₀ :: _`, `head = d₀.ptr`, `nodes.map ptr` is duplicate-free and non-null, and
      for every index `i < nodes.length`, `next_i = ptr_{(i + 1) % n}` and
      `prev_i = ptr_{(i + n - 1) % n}`. -/
def CircularDllWf (head : BitVec 64) (nodes : List (BitVec 64 × BitVec 64 × BitVec 64)) : Prop :=
  match nodes with
  | [] => head = 0#64
  | (p0, _, _) :: _ =>
    let n := nodes.length
    head = p0 ∧
    (nodes.map Prod.fst).Nodup ∧
    (∀ x ∈ nodes, x.1 ≠ 0#64) ∧
    ∀ i : Nat, (hi : i < n) →
      let cur := nodes[i]'hi
      let nxt := nodes[(i + 1) % n]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi))
      let prv := nodes[(i + n - 1) % n]'(Nat.mod_lt _ (Nat.zero_lt_of_lt hi))
      cur.2.2 = nxt.1 ∧ cur.2.1 = prv.1

/-! ## Abstract allocator state (`MallocngSt`) and flat byte ownership -/

/-- Abstract state of `mallocng`:
    - `ctx`: `.bss.__malloc_context` (`928` B)
    - `auxvPtr`: `__libc.auxv` pointer
    - `metaAreas`: singly-linked chain of activated `4096`-byte `struct meta_area` pages
      (`ctx.metaAreaHead` .. `ctx.metaAreaTail`)
    - `guardPages`: `4096`-byte `PROT_NONE` guard pages (`brk` guard + `mmap` batch page-`0` guards)
    - `mmapGuardPages`: subset of `guardPages` allocated via `mmap` (carrying `memMapped · 4096`;
      excludes the optional `MAP_FIXED` `brk` guard page inside `[brkStart, brk)`)
    - `availMetaPages`: `ctx.availMetaAreaCount` contiguous `4096`-byte zeroed `PROT_NONE` pages
      starting at `ctx.availMetaAreas` (each carrying `memMapped · 4096`)
    - `mmapMetaAreas`: subset of `metaAreas.map (·.base)` allocated via `mmap` (carrying
      `memMapped · 4096`; excludes `brk`-backed `meta_area` pages inside `[brkStart, brk)`)
    - `freeMetas`: circular DLL at `ctx.freeMetaHead`
    - `bumpMetas`: `ctx.availMetaCount` contiguous zeroed `40`-byte slots starting at `ctx.availMeta`
    - `reservedMetas`: in-flight `40`-byte `struct meta` slots carved out during recursive `alloc_slot`
      (`[]` at quiescent API boundaries)
    - `groups`: all active `GroupDesc` nodes (both root `maplen > 0` and nested `maplen = 0`)
    - `activeLists`: `48` circular DLL node-pointer lists for `ctx.active[0..47]`
    - `masterDom`: duplicate-free finite address list covering all dynamic bytes (`metaAreas`,
      `guardPages`, `availMetaPages`, root `groups`)
    - `byteVal`: total byte valuation map (`BitVec 64 → BitVec 8`) for `ByteMap` / `ProtNoneByteMap`
    - `liveMap`: authoritative ghost map (`userPtr ↦ reqSize`, plus overhead bound `ov`). -/
structure MallocngSt where
  ctx            : CtxFields
  auxvPtr        : BitVec 64
  auxvSnap       : Option MallocngAuxvSnap := none
  metaAreas      : List MetaAreaDesc
  mmapMetaAreas  : List (BitVec 64)
  guardPages     : List (BitVec 64)
  mmapGuardPages : List (BitVec 64)
  availMetaPages : List (BitVec 64)
  freeMetas      : List FreeMetaDesc
  bumpMetas      : List (BitVec 64)
  reservedMetas  : List (BitVec 64)
  groups         : List GroupDesc
  activeLists    : List (List (BitVec 64))
  masterDom      : List (BitVec 64)
  byteVal        : BitVec 64 → BitVec 8
  liveMap        : MallocngLiveMap

/-- Empty `MallocngSt` at process startup (`init_done = 0`, zero dynamic pages or groups). -/
def emptyMallocngSt (auxvPtr : BitVec 64) : MallocngSt where
  ctx            := emptyCtxFields
  auxvPtr        := auxvPtr
  auxvSnap       := none
  metaAreas      := []
  mmapMetaAreas  := []
  guardPages     := []
  mmapGuardPages := []
  availMetaPages := []
  freeMetas      := []
  bumpMetas      := []
  reservedMetas  := []
  groups         := []
  activeLists    := List.replicate 48 []
  masterDom      := []
  byteVal        := fun _ => 0#8
  liveMap        := .empty

/-- True iff byte `a` lies inside the caller-owned payload `[userPtr, userPtr + reqSize)` of some
    `.liveUser` slot in `st.groups`. -/
def CarvedUserByte (st : MallocngSt) (a : BitVec 64) : Prop :=
  ∃ g ∈ st.groups, ∃ s ∈ g.slots,
    match s with
    | .liveUser userPtr reqSize _ => InRegion userPtr reqSize a
    | _ => False

instance (st : MallocngSt) : DecidablePred (CarvedUserByte st) := fun a =>
  decidable_of_iff
    (st.groups.any fun g => g.slots.any fun s =>
      match s with
      | .liveUser userPtr reqSize _ => decide (InRegion userPtr reqSize a)
      | _ => false)
    (by
      simp only [CarvedUserByte, List.any_eq_true]
      constructor
      · rintro ⟨g, hg, s, hs, h⟩
        refine ⟨g, hg, s, hs, ?_⟩
        cases s <;> simp_all
      · rintro ⟨g, hg, s, hs, h⟩
        refine ⟨g, hg, s, hs, ?_⟩
        cases s <;> simp_all)

/-- True iff byte `a` lies inside an in-flight `40`-byte `struct meta` slot `m ∈ st.reservedMetas`
    carved out by an active `alloc_slot` / `__libc_malloc_impl` stack frame. -/
def CarvedMetaByte (st : MallocngSt) (a : BitVec 64) : Prop :=
  ∃ m ∈ st.reservedMetas, InRegion m 40 a

instance (st : MallocngSt) : DecidablePred (CarvedMetaByte st) := fun a =>
  decidable_of_iff
    (st.reservedMetas.any fun m => decide (InRegion m 40 a))
    (by simp [CarvedMetaByte, List.any_eq_true])

/-- Dynamic `Perm.rw` byte owned by `mallocng`: lies in an activated `meta_area` page or a root
    group's `mmap` region (`0 < g.maplen`), excluding caller-carved `.liveUser` payloads and
    in-flight `reservedMetas` slots.
    Because nested groups lie inside their root ancestor's `mmap` region, creating or destroying a
    nested group leaves `OwnedRwByte` set membership invariant. -/
def OwnedRwByte (st : MallocngSt) (a : BitVec 64) : Prop :=
  ((∃ ma ∈ st.metaAreas, InRegion ma.base 4096 a) ∨
   (∃ g ∈ st.groups, 0 < g.maplen ∧ InRegion g.mem (g.maplen * 4096) a)) ∧
  ¬ CarvedUserByte st a ∧
  ¬ CarvedMetaByte st a

instance (st : MallocngSt) : DecidablePred (OwnedRwByte st) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Dynamic `Perm.protNone` byte owned by `mallocng`: lies in a guard page or an unactivated
    `avail_meta_areas` reserve page. -/
def OwnedProtNoneByte (st : MallocngSt) (a : BitVec 64) : Prop :=
  (∃ gp ∈ st.guardPages, InRegion gp 4096 a) ∨
  (∃ ap ∈ st.availMetaPages, InRegion ap 4096 a)

instance (st : MallocngSt) : DecidablePred (OwnedProtNoneByte st) := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- Dynamic `memMapped` virtual-address reservation byte owned by `mallocng`: lies in any
    `mmap`-backed `meta_area` page, `mmap`-backed guard page, `avail_meta_areas` reserve page, or
    root group `mmap` region (`0 < g.maplen`). (`brk`-backed pages in `[brkStart, brk)` are tracked
    by `s.brk` instead of `memMapped`.) -/
def OwnedMappedByte (st : MallocngSt) (a : BitVec 64) : Prop :=
  (∃ mb ∈ st.mmapMetaAreas, InRegion mb 4096 a) ∨
  (∃ mg ∈ st.mmapGuardPages, InRegion mg 4096 a) ∨
  (∃ ap ∈ st.availMetaPages, InRegion ap 4096 a) ∨
  (∃ g ∈ st.groups, 0 < g.maplen ∧ InRegion g.mem (g.maplen * 4096) a)

instance (st : MallocngSt) : DecidablePred (OwnedMappedByte st) := fun _ =>
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

end VerifiedLibraries.Mallocng.Proofs
