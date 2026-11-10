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
public import ProofLib.Hoare.SubroutineHook
public import VerifiedLibraries.Mallocng.Spec.Top
public import VerifiedLibraries.Mallocng.Proofs.Cells
public import VerifiedLibraries.Mallocng.Proofs.SizeClasses
public import VerifiedLibraries.Mallocng.Proofs.GhostToken
public import VerifiedLibraries.Mallocng.Proofs.Defs
public import VerifiedLibraries.Mallocng.Proofs.Cost.GroupTable

/-!
# Layered `mallocng` Heap Invariant and `MallocngIface` Witness

Defines the L0-L5 machine-level heap well-formedness predicates (`MallocngWFInflight`, `MallocngWF`),
the sealed separation-logic invariants (`MallocngCoreImpl`, `MallocngHeapImpl`), and the concrete
`mallocngIface : MallocngIface` witness together with its startup, runtime-split, and read-only-split
laws.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

/-! ## Helper Predicates for `MallocngWF` -/

/-- Auxiliary `svc` handler used inside `SVC #0`-free instruction segments (`SepWP.lift_noSyscalls`). -/
def mallocngFaultSvc (s : State) : State :=
  s.setStatus (.Exception "unexpected SVC")

def allMetaSlots (st : MallocngSt) : List (BitVec 64) :=
  st.metaAreas.flatMap fun ma => (List.range 101).map ma.slotAddr

def slotEffCost : SlotState → Nat
  | .liveUser _ _ effCost => effCost
  | _ => 0

def SlotState.isFree : SlotState → Bool
  | .freeAvail | .freeInactive => true
  | _ => false

def SlotState.isClaimed : SlotState → Bool
  | .claimed => true
  | _ => false

def totalClaimedSlots (st : MallocngSt) : Nat :=
  (st.groups.map fun g => (g.slots.filter SlotState.isClaimed).length).sum

def GroupDesc.isEmpty (g : GroupDesc) : Bool :=
  g.slots.all SlotState.isFree

def totalLiveEffCost (st : MallocngSt) : Nat :=
  (st.groups.map fun g => (g.slots.map slotEffCost).sum).sum

def slotLiveCount : SlotState → Nat
  | .liveUser _ _ _ => 1
  | _ => 0

def totalLiveCount (st : MallocngSt) : Nat :=
  (st.groups.map fun g => (g.slots.map slotLiveCount).sum).sum

def PairwiseDisjointRegions : List (BitVec 64 × Nat) → Prop
  | [] => True
  | (b, n) :: rest =>
    (∀ x ∈ rest, DisjointRegions b n x.1 x.2) ∧ PairwiseDisjointRegions rest

def dynamicRootRegions (st : MallocngSt) : List (BitVec 64 × Nat) :=
  st.metaAreas.map (fun ma => (ma.base, 4096)) ++
  st.guardPages.map (fun gp => (gp, 4096)) ++
  st.availMetaPages.map (fun ap => (ap, 4096)) ++
  (st.groups.filter fun g => decide (0 < g.maplen)).map (fun g => (g.mem, g.maplen * 4096))

def MallocngCountIvsWF (b : MallocngBudget) (ivs : List (BitVec 64 × Nat))
    (st : MallocngSt) : Prop :=
  b.liveCount ≤ b.peakCount ∧
  totalLiveCount st ≤ b.liveCount ∧
  ivs = dynamicRootRegions st ∧
  ivs.length ≤ 48 + 2 * b.peakCount ∧
  st.metaAreas.length ≤ 1 + (88 + 8 * b.peakCount) / 101 ∧
  Cost.GroupsGrpBound (b.peakCount + 6) st.groups

/-- Well-formedness of slot `idx` inside `g` (`L3` bitmaps and in-band `IB = 4` headers/trailers). -/
def SlotWf (st : MallocngSt) (g : GroupDesc) (idx : Nat) (s : SlotState) : Prop :=
  let start := g.slotStart idx
  let slotEnd := g.slotEnd idx
  st.byteVal (start - 4#64) = 0#8 ∧
  (g.availMask.getLsbD idx = true ↔ s = .freeAvail) ∧
  (g.freedMask.getLsbD idx = true ↔ s = .freeInactive) ∧
  (g.activeIdx < idx → s = .freeInactive) ∧
  match s with
  | .freeAvail | .freeInactive | .claimed => True
  | .liveNested cm =>
    g.sc < 48 ∧
    ∃ cg ∈ st.groups,
      cg.metaPtr = cm ∧ cg.parentMeta = some g.metaPtr ∧
      start.toNat ≤ cg.mem.toNat ∧
      (cg.mem.toNat - start.toNat) % 16 = 0 ∧
      cg.mem.toNat + cg.nestedCap ≤ slotEnd.toNat ∧
      cg.nestedCap = slotStride g.sc - 4 ∧
      let totalOffUnits := (cg.mem.toNat - g.storage.toNat) / 16
      totalOffUnits ≤ 0xffff ∧
      st.byteVal (cg.mem - 4#64) = 0#8 ∧
      st.byteVal (cg.mem - 3#64) = BitVec.ofNat 8 ((6 <<< 5) ||| idx) ∧
      readBytesFromMap st.byteVal (cg.mem - 2#64) 2 =
        unpack16 (BitVec.ofNat 16 totalOffUnits)
  | .liveUser userPtr reqSize effCost =>
    MallocngBlockWf userPtr reqSize ∧
    start.toNat ≤ userPtr.toNat ∧
    userPtr.toNat + reqSize ≤ slotEnd.toNat ∧
    let offBytes := userPtr.toNat - start.toNat
    let totalOffUnits := (userPtr.toNat - g.storage.toNat) / 16
    let reserved := slotEnd.toNat - (userPtr.toNat + reqSize)
    let r5 := min reserved 5
    max reqSize MallocngMinBlockCost ≤ effCost ∧
    (offBytes ≤ (effCost - max reqSize MallocngMinBlockCost) + 255 * 16 ∧
      effCost - max reqSize MallocngMinBlockCost ≤ MaxAlignedAllocAlign - 16 ∧
      effCost - max reqSize MallocngMinBlockCost ≤ st.liveMap.ov userPtr) ∧
    reserved < 2 ^ 31 ∧
    ((2 ≤ g.sc ∧ g.sc < 48 → nominalSlotCap (g.sc - 2) < effCost) ∧
      (g.sc < 48 → totalOffUnits < (idx + 1) * sizeClass g.sc)) ∧
    (g.sc = 63 → g.maplen * 4096 ≤ effCost + 8195) ∧
    st.byteVal (userPtr - 3#64) = BitVec.ofNat 8 ((r5 <<< 5) ||| idx) ∧
    (if totalOffUnits ≤ 0xffff then
       st.byteVal (userPtr - 4#64) = 0#8 ∧
       readBytesFromMap st.byteVal (userPtr - 2#64) 2 =
         unpack16 (BitVec.ofNat 16 totalOffUnits)
     else
       g.sc = 63 ∧ idx = 0 ∧ totalOffUnits < 2 ^ 27 ∧
       st.byteVal (userPtr - 4#64) = 1#8 ∧
       readBytesFromMap st.byteVal (userPtr - 2#64) 2 = [0#8, 0#8] ∧
       readBytesFromMap st.byteVal (userPtr - 8#64) 4 =
         unpack32 (BitVec.ofNat 32 totalOffUnits)) ∧
    (1 ≤ reserved → st.byteVal (userPtr + BitVec.ofNat 64 reqSize) = 0#8) ∧
    (5 ≤ reserved →
       st.byteVal (slotEnd - 5#64) = 0#8 ∧
       readBytesFromMap st.byteVal (slotEnd - 4#64) 4 =
         unpack32 (BitVec.ofNat 32 reserved))

/-- Well-formedness of a single active `GroupDesc` (`L2` + `L3`). -/
def GroupWf (st : MallocngSt) (g : GroupDesc) : Prop :=
  (g.sc < 48 ∨ g.sc = 63) ∧
  g.lastIdx ≤ 31 ∧
  g.slots.length = g.cnt ∧
  (g.sc = 63 → g.lastIdx = 0 ∧ 0 < g.maplen ∧ g.prev = 0#64 ∧ g.next = 0#64) ∧
  4096 ≤ g.mem.toNat ∧
  g.mem.toNat % 16 = 0 ∧
  g.mem.toNat + g.totalBytes ≤ 2 ^ 48 ∧
  12 + g.cnt * g.stride ≤ g.totalBytes ∧
  (0 < g.maplen → 12 + g.cnt * g.stride < g.totalBytes) ∧
  st.byteVal (g.slotEnd g.lastIdx) = 0#8 ∧
  (0 < g.maplen ↔ g.parentMeta = none) ∧
  (0 < g.maplen →
    g.mem.toNat % 4096 = 0 ∧ g.nestedCap = 0 ∧
    (g.sc ≤ 25 → g.maplen * 4096 ≤ 65536) ∧
    (g.sc < 48 → g.maplen * 4096 ≤ 1048576 ∧
      (g.lastIdx = 0 → g.stride ≤ slotStride g.sc ∨
        (24 ≤ g.sc ∧ g.maplen * 4096 = pageAlignUp (slotStride g.sc + 16))))) ∧
  (g.maplen = 0 →
    1 ≤ g.lastIdx ∧
    ∃ pg ∈ st.groups, ∃ pIdx : Nat, ∃ hp : pIdx < pg.slots.length,
      g.parentMeta = some pg.metaPtr ∧
      pg.sc < 48 ∧ g.sc < pg.sc ∧
      pg.sc ≤ 24 ∧
      pg.slots[pIdx]'hp = .liveNested g.metaPtr ∧
      (pg.slotStart pIdx).toNat ≤ g.mem.toNat ∧
      g.mem.toNat + g.nestedCap ≤ (pg.slotEnd pIdx).toNat ∧
      g.nestedCap = slotStride pg.sc - 4) ∧
  g.availMask &&& g.freedMask = 0#32 ∧
  (g.availMask ||| g.freedMask).toNat < 2 ^ g.cnt ∧
  g.activeIdx ≤ g.lastIdx ∧
  readBytesFromMap st.byteVal g.metaPtr 40 = g.metaBytes ∧
  readBytesFromMap st.byteVal g.mem 8 = unpack64 g.metaPtr ∧
  st.byteVal (g.mem + 8#64) = g.activeByte ∧
  ∀ idx : Nat, (hIdx : idx < g.slots.length) → SlotWf st g idx (g.slots[idx]'hIdx)

def findGroupByMeta (st : MallocngSt) (m : BitVec 64) : Option GroupDesc :=
  st.groups.find? (·.metaPtr == m)

/-- Well-formedness of `ctx.active[sc]` (`L4`) for size class `sc < 48`. -/
def ActiveClassWf (st : MallocngSt) (sc : Nat) (head : BitVec 64) (ms : List (BitVec 64)) : Prop :=
  (∀ m ∈ ms, ∃ g ∈ st.groups, g.metaPtr = m ∧ g.sc = sc) ∧
  CircularDllWf head
    (ms.filterMap fun m =>
      (findGroupByMeta st m).map fun g => (g.metaPtr, g.prev, g.next)) ∧
  (ms.filterMap fun m => (findGroupByMeta st m).map fun g => (g.metaPtr, g.prev, g.next)).length =
    ms.length ∧
  (∀ g ∈ st.groups, g.sc = sc →
    (g.metaPtr ∉ ms ↔ (g.prev = 0#64 ∧ g.next = 0#64)) ∧
    (g.metaPtr ∉ ms → g.availMask = 0#32 ∧ g.freedMask = 0#32 ∧ g.activeIdx = g.lastIdx)) ∧
  (∀ i : Nat, (hi : i < ms.length) → 0 < i →
    ∀ g ∈ st.groups, g.metaPtr = ms[i]'hi → g.availMask = 0#32 ∧ g.freedMask ≠ 0#32) ∧
  (∀ g₁ ∈ st.groups, ∀ g₂ ∈ st.groups,
    g₁.sc = sc → g₂.sc = sc →
    g₁.activeIdx < g₁.lastIdx → g₂.activeIdx < g₂.lastIdx → g₁.metaPtr = g₂.metaPtr) ∧
  (∀ g ∈ st.groups, g.sc = sc → g.activeIdx < g.lastIdx → g.metaPtr ∈ ms ∧ 0 < sc)

/-! ## Layered Heap Invariant (`MallocngWFInflight` and `MallocngWF`) -/

/-- Machine-level heap invariant (`L0`-`L5` and virtual-memory accounting) for `mallocng` loaded at
    `base` with break segment `[brkStart, brk)`, cost counters `(liveCost, peakCost)`, and at most
    `inflight` carved-out `40`-byte `struct meta` slots (`inflight = 0` at API boundaries). -/
structure MallocngWFInflight (inflight : Nat) (base brkStart brk : BitVec 64)
    (liveCost peakCost : Nat) (st : MallocngSt) : Prop where
  /-- `L0`: break segment alignment/bounds (`MallocngBrkStartWf brkStart`). -/
  base_wf : True
  brk_bounds :
    0x10000 ≤ brkStart.toNat ∧
    brkStart.toNat % 4096 = 0 ∧
    brk.toNat % 4096 = 0 ∧
    brkStart.toNat ≤ brk.toNat ∧
    brk.toNat ≤ 2 ^ 48
  /-- `L0`: fixed array lengths inside `struct malloc_context`. -/
  ctx_lens :
    st.ctx.active.length = 48 ∧
    st.ctx.usageByClass.length = 48 ∧
    st.ctx.unmapSeq.length = 32 ∧
    st.ctx.bounces.length = 32 ∧
    st.ctx.seqPad = List.replicate 7 0#8 ∧
    st.activeLists.length = 48
  /-- `L0`: `init_done ∈ {0, 1}`, and when `0` the entire dynamic state is empty. -/
  initDone_wf : st.ctx.initDone = 0#32 ∨ st.ctx.initDone = 1#32
  initZero_wf :
    st.ctx.initDone = 0#32 →
      st.ctx = { emptyCtxFields with seq := st.ctx.seq } ∧
      st.metaAreas = [] ∧ st.mmapMetaAreas = [] ∧
      st.guardPages = [] ∧ st.mmapGuardPages = [] ∧
      st.availMetaPages = [] ∧ st.freeMetas = [] ∧
      st.bumpMetas = [] ∧ st.reservedMetas = [] ∧
      st.groups = [] ∧ st.masterDom = [] ∧ brk = brkStart
  /-- `L0`: bounce counters capped at `150` and `usage_by_class[sc]` equals total slots in `sc`. -/
  bounces_wf : ∀ b ∈ st.ctx.bounces, b.toNat ≤ 150
  usage_wf :
    ∀ sc : Nat, (hsc : sc < st.ctx.usageByClass.length) →
      (st.ctx.usageByClass[sc]'hsc).toNat =
        ((st.groups.filter (·.sc == sc)).map GroupDesc.cnt).sum
  /-- `L0`/`L1`: `brk` state vs `mmap` fallback (`ctx.brk == -1`). -/
  brk_mode_wf :
    (st.ctx.initDone = 1#32 ∧ st.ctx.brk ≠ (-1#64) →
      st.ctx.brk = brk ∧
      brkStart.toNat + 8192 ≤ brk.toNat ∧
      st.ctx.availMetaAreaCount = 0#64 ∧
      st.ctx.metaAllocShift = 0#64 ∧
      st.availMetaPages = []) ∧
    st.mmapMetaAreas =
      (st.metaAreas.map (·.base)).filter (fun mb => !decide (InRegion brkStart (brk.toNat - brkStart.toNat) mb)) ∧
    st.mmapGuardPages =
      st.guardPages.filter (fun gp => !decide (InRegion brkStart (brk.toNat - brkStart.toNat) gp)) ∧
    (brkStart.toNat < brk.toNat →
      brkStart ∈ st.guardPages ∧
      ∀ k : Nat, 1 ≤ k → k < (brk.toNat - brkStart.toNat) / 4096 →
        ∃ ma ∈ st.metaAreas, ma.base = brkStart + BitVec.ofNat 64 (4096 * k))
  /-- `L1`: `meta_area` pages, chain links, headers (`check == secret`, `nslots == 101`),
      `avail_meta_areas`, `guardPages`, `freeMetas`, `bumpMetas`, `reservedMetas`, and exact
      `101`-slot partition. -/
  metaAreas_wf :
    (st.metaAreas.map (·.base)).Nodup ∧
    (∀ ma ∈ st.metaAreas,
      4096 ≤ ma.base.toNat ∧ ma.base.toNat % 4096 = 0 ∧ ma.base.toNat + 4096 ≤ 2 ^ 48 ∧
      readBytesFromMap st.byteVal ma.base 24 =
        unpack64 st.ctx.secret ++ unpack64 ma.next ++ unpack32 101#32 ++ unpack32 0#32) ∧
    (match st.metaAreas with
     | [] => st.ctx.metaAreaHead = 0#64 ∧ st.ctx.metaAreaTail = 0#64
     | hd :: _ =>
       st.ctx.metaAreaHead = hd.base ∧
       (∀ hne : st.metaAreas ≠ [],
         st.ctx.metaAreaTail = (st.metaAreas.getLast hne).base ∧
         (st.metaAreas.getLast hne).next = 0#64) ∧
       ∀ i : Nat, (hi : i + 1 < st.metaAreas.length) →
         (st.metaAreas[i]'(Nat.lt_of_succ_lt hi)).next = (st.metaAreas[i + 1]'hi).base)
  guard_avail_wf :
    st.guardPages.Nodup ∧
    (∀ gp ∈ st.guardPages, 4096 ≤ gp.toNat ∧ gp.toNat % 4096 = 0 ∧ gp.toNat + 4096 ≤ 2 ^ 48) ∧
    st.availMetaPages =
      (List.range st.ctx.availMetaAreaCount.toNat).map
        (fun i => st.ctx.availMetaAreas + BitVec.ofNat 64 (4096 * i)) ∧
    (∀ ap ∈ st.availMetaPages,
      4096 ≤ ap.toNat ∧ ap.toNat % 4096 = 0 ∧ ap.toNat + 4096 ≤ 2 ^ 48 ∧
      readBytesFromMap st.byteVal ap 4096 = List.replicate 4096 0#8)
  inflight_wf : st.reservedMetas.length + totalClaimedSlots st ≤ inflight
  free_bump_metas_wf :
    CircularDllWf st.ctx.freeMetaHead
      (st.freeMetas.map fun fm => (fm.ptr, fm.prev, fm.next)) ∧
    (∀ fm ∈ st.freeMetas, readBytesFromMap st.byteVal fm.ptr 40 = fm.toBytes) ∧
    ((st.ctx.availMetaCount = 0#64 ∧ st.bumpMetas = []) ∨
     (0 < st.ctx.availMetaCount.toNat ∧ st.ctx.availMetaCount.toNat ≤ 101 ∧
      ∃ hne : st.metaAreas ≠ [],
        let tail := st.metaAreas.getLast hne
        let k0 := 101 - st.ctx.availMetaCount.toNat
        st.ctx.availMeta = tail.slotAddr k0 ∧
        st.bumpMetas = (List.range st.ctx.availMetaCount.toNat).map (fun j => tail.slotAddr (k0 + j)))) ∧
    (∀ bm ∈ st.bumpMetas, readBytesFromMap st.byteVal bm 40 = List.replicate 40 0#8) ∧
    let usedAndFree :=
      st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr) ++ st.bumpMetas ++ st.reservedMetas
    usedAndFree.Nodup ∧
    (∀ m, m ∈ usedAndFree ↔ m ∈ allMetaSlots st)
  /-- `L2` and `L3`: active groups, nesting forest, and pairwise disjointness of root regions. -/
  groups_nodup : (st.groups.map (·.metaPtr)).Nodup ∧ (st.groups.map (·.mem)).Nodup
  groups_wf : ∀ g ∈ st.groups, GroupWf st g
  regions_disjoint :
    PairwiseDisjointRegions (dynamicRootRegions st) ∧ True
  /-- `L4`: `ctx.active[0..47]` circular DLLs. -/
  active_wf :
    ∀ sc : Nat, (h1 : sc < st.ctx.active.length) → (h2 : sc < st.activeLists.length) →
      ActiveClassWf st sc (st.ctx.active[sc]'h1) (st.activeLists[sc]'h2)
  /-- `L5`: ghost live map correspondence. -/
  liveMap_wf :
    ∀ (p : BitVec 64) (n : Nat),
      st.liveMap p = some n ↔
        ∃ g ∈ st.groups, ∃ idx : Nat, ∃ hIdx : idx < g.slots.length, ∃ effCost : Nat,
          g.slots[idx]'hIdx = .liveUser p n effCost
  /-- `L5` and accounting: cost monotonicity, `effCost` sum, structural page/empty-group bounds, and
      `masterDom` coverage within `dynamicRootRegions`. -/
  live_le_peak : liveCost ≤ peakCost
  effCost_le_live : totalLiveEffCost st ≤ liveCost
  meta_pages_bound :
    st.metaAreas.length ≤ 2 + peakCost / 655360 ∧
    (st.ctx.metaAllocShift = 0#64 → st.availMetaPages = [] ∧ st.guardPages.length ≤ 1) ∧
    (∀ m : Nat, 1 ≤ m → st.ctx.metaAllocShift.toNat = m →
      m ≤ 40 ∧ 2 ^ m - m ≤ st.metaAreas.length ∧
      2 ^ (m + 1) - 2 - m ≤ st.metaAreas.length + st.availMetaPages.length ∧
      st.guardPages.length ≤ m + 1 ∧ st.availMetaPages.length ≤ 2 ^ m - 2)
  empty_groups_bound :
    ∀ g ∈ st.groups, g.isEmpty = true →
      0 < g.maplen ∧ 7 ≤ g.sc ∧ g.sc ≤ 38 ∧ g.maplen * 4096 ≤ 1048576 ∧
      (∀ h : g.sc < st.activeLists.length, g.metaPtr ∈ st.activeLists[g.sc]'h) ∧
      (∀ g' ∈ st.groups, g'.isEmpty = true → g'.sc = g.sc → g'.metaPtr = g.metaPtr) ∧
      (g.lastIdx = 0 → slotStride g.sc + 16 ≤ g.maplen * 4096)
  masterDom_wf :
    st.masterDom.Nodup ∧
    (∀ a : BitVec 64,
      (OwnedRwByte st a ∨ OwnedProtNoneByte st a ∨ OwnedMappedByte st a) → a ∈ st.masterDom) ∧
    (∀ a ∈ st.masterDom, ∃ r ∈ dynamicRootRegions st, InRegion r.1 r.2 a)

/-- Quiescent API-boundary heap invariant (`0` in-flight carved `struct meta` slots). -/
abbrev MallocngWF := MallocngWFInflight 0

/-! ## Startup Non-Vacuity (`emptyMallocngSt_wf`) -/

def emptyMallocngStOpt (auxvPtr : BitVec 64) (snapOpt : Option MallocngAuxvSnap) : MallocngSt :=
  { emptyMallocngSt auxvPtr with auxvSnap := snapOpt }

theorem emptyMallocngStOpt_wf {base brkStart : BitVec 64} (auxvPtr : BitVec 64)
    (snapOpt : Option MallocngAuxvSnap)
    (hBrkWf : MallocngBrkStartWf brkStart) :
    MallocngWF base brkStart brkStart 0 0 (emptyMallocngStOpt auxvPtr snapOpt) where
  base_wf := trivial
  brk_bounds :=
    ⟨by simpa [MMAP_MIN_ADDR] using hBrkWf.1,
     by simpa [PAGE_SIZE] using hBrkWf.2.1,
     by simpa [PAGE_SIZE] using hBrkWf.2.1,
     Nat.le_refl _,
     hBrkWf.2.2⟩
  ctx_lens := by simp [emptyMallocngStOpt, emptyMallocngSt, emptyCtxFields]
  initDone_wf := Or.inl rfl
  initZero_wf := fun _ => by simp [emptyMallocngStOpt, emptyMallocngSt]
  bounces_wf := by
    intro b hb
    simp [emptyMallocngStOpt, emptyMallocngSt, emptyCtxFields] at hb
    subst hb; decide
  usage_wf := by
    intro sc hsc
    simp only [emptyMallocngStOpt, emptyMallocngSt, emptyCtxFields, List.getElem_replicate,
      BitVec.toNat_ofNat, Nat.zero_mod, List.filter_nil, List.map_nil, List.sum_nil]
  brk_mode_wf := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro ⟨h1, _⟩; simp [emptyMallocngStOpt, emptyMallocngSt, emptyCtxFields] at h1
    · simp [emptyMallocngStOpt, emptyMallocngSt]
    · simp [emptyMallocngStOpt, emptyMallocngSt]
    · intro hlt; omega
  metaAreas_wf := by simp [emptyMallocngStOpt, emptyMallocngSt, emptyCtxFields]
  guard_avail_wf := by
    refine ⟨List.nodup_nil, ?_, rfl, ?_⟩
    · intro _ h; cases h
    · intro _ h; cases h
  inflight_wf := by simp [emptyMallocngStOpt, emptyMallocngSt, totalClaimedSlots]
  free_bump_metas_wf := by
    refine ⟨rfl, ?_, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
    · intro fm hfm; cases hfm
    · intro bm hbm; cases hbm
    · simp [emptyMallocngStOpt, emptyMallocngSt]
    · intro m; simp [emptyMallocngStOpt, emptyMallocngSt, allMetaSlots]
  groups_nodup := ⟨List.nodup_nil, List.nodup_nil⟩
  groups_wf := fun _ hg => by cases hg
  regions_disjoint := ⟨trivial, trivial⟩
  active_wf := by
    intro sc h1 h2
    simp only [emptyMallocngStOpt, emptyMallocngSt, emptyCtxFields, List.getElem_replicate]
    refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro _ hm; cases hm
    · intro _ hg; cases hg
    · intro _ hi; cases hi
    · intro _ hg; cases hg
    · intro _ hg; cases hg
  liveMap_wf := by
    intro p n
    simp [emptyMallocngStOpt, emptyMallocngSt]
  live_le_peak := Nat.le_refl 0
  effCost_le_live := by simp [totalLiveEffCost, emptyMallocngStOpt, emptyMallocngSt]
  meta_pages_bound := by
    refine ⟨by simp [emptyMallocngStOpt, emptyMallocngSt],
      fun _ => ⟨rfl, by simp [emptyMallocngStOpt, emptyMallocngSt]⟩, ?_⟩
    intro m hm hEq
    simp [emptyMallocngStOpt, emptyMallocngSt, emptyCtxFields] at hEq
    omega
  empty_groups_bound := fun _ hg => by cases hg
  masterDom_wf := by
    refine ⟨List.nodup_nil, ?_, ?_⟩
    · intro a h
      simp [OwnedRwByte, OwnedProtNoneByte, OwnedMappedByte, emptyMallocngStOpt, emptyMallocngSt] at h
    · intro _ ha; cases ha

theorem emptyMallocngSt_wf {base brkStart : BitVec 64} (auxvPtr : BitVec 64)
    (hBrkWf : MallocngBrkStartWf brkStart) :
    MallocngWF base brkStart brkStart 0 0 (emptyMallocngSt auxvPtr) :=
  emptyMallocngStOpt_wf auxvPtr none hBrkWf

/-- No individually `mmap`ped (`isMmapped = true`) group in `st.groups` contains a free slot
    (`.freeAvail` or `.freeInactive`). -/
theorem not_isFree_of_isMmapped {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hMmap : g.isMmapped = true)
    {s : SlotState} (hs : s ∈ g.slots) :
    s.isFree = false := by
  cases hFree : s.isFree with
  | false => rfl
  | true =>
    exfalso
    have hGWf := hwf.groups_wf g hg
    have hLast0 : g.lastIdx = 0 := by
      unfold GroupDesc.isMmapped at hMmap
      rcases Bool.or_eq_true_iff.mp hMmap with h63 | hSlack
      · exact (hGWf.2.2.2.1 (beq_iff_eq.mp h63)).1
      · exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hSlack).1).1
    have hLen1 : g.slots.length = 1 := by
      have hL := hGWf.2.2.1
      unfold GroupDesc.cnt at hL
      omega
    have hSlotsEq : g.slots = [s] := by
      rcases hSlots : g.slots with _ | ⟨x, _ | _⟩
      · simp [hSlots] at hs
      · simp only [hSlots, List.mem_singleton] at hs
        rw [hs]
      · simp [hSlots] at hLen1
    have hEmpty : g.isEmpty = true := by
      simp [GroupDesc.isEmpty, hSlotsEq, hFree]
    have ⟨_, _, hScLe38, _, _, _, hNoSlack⟩ := hwf.empty_groups_bound g hg hEmpty
    have hGe := hNoSlack hLast0
    unfold GroupDesc.isMmapped at hMmap
    rcases Bool.or_eq_true_iff.mp hMmap with h63 | hSlack
    · have hEq63 := beq_iff_eq.mp h63; omega
    · have hLt : g.maplen * 4096 - 16 < slotStride g.sc :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp hSlack).2
      omega

/-! ## Sealed Separation-Logic Invariants and `mallocngIface` -/

def MallocngAuxvConcreteWf (auxvPtr : BitVec 64)
    (preEntries : List (BitVec 64 × BitVec 64)) (randPtr : BitVec 64)
    (sufEntries : List (BitVec 64 × BitVec 64)) : Prop :=
  (∀ e ∈ preEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
  (∀ e ∈ sufEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
  preEntries.length + sufEntries.length ≤ 64 ∧
  auxvPtr.toNat + 16 * (preEntries.length + sufEntries.length + 2) ≤ 2 ^ 48 ∧
  randPtr.toNat + 16 ≤ 2 ^ 48

def MallocngAuxvAuthMap (auxvPtr : BitVec 64) : Option MallocngAuxvSnap → BitVec 64 → Option Nat
  | none => fun _ => none
  | some snap => fun k => if k = 0#64 then some (encodeAuxvSnap auxvPtr snap) else none

/-- Authoritative `auxv` ghost map paired with either the untracked `MallocngAuxvAt auxvPtr`
    existential (`snap = none`) or the concrete `auxv` table and `AT_RANDOM` secret word
    (`snap = some (...)`). -/
def MallocngAuxvState (γ : GhostName) (auxvPtr : BitVec 64)
    (snap : Option MallocngAuxvSnap) : SepProp :=
  ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap auxvPtr snap) ∗
  match snap with
  | none => MallocngAuxvAt auxvPtr
  | some (preEntries, randPtr, sufEntries, nullVal, sec) =>
    ⌜MallocngAuxvConcreteWf auxvPtr preEntries randPtr sufEntries⌝ ∗
    (auxvPtr ↦₆₄*
      ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
        fun (t, v) => [t, v])) ∗
    ((randPtr + 8#64) ↦₆₄ sec)

theorem BoundedFootprint_mallocngLiveAuth (γ : GhostName) (L : MallocngLiveMap) :
    SepProp.BoundedFootprint (MallocngLiveAuth γ L) 0 :=
  BoundedFootprint_ghostMapAuth (liveGhost γ) L.enc

theorem footprintIn_mallocngLiveAuth {S : BitVec 64 → Prop}
    (γ : GhostName) (L : MallocngLiveMap) :
    SepProp.FootprintIn (MallocngLiveAuth γ L) S :=
  SepProp.FootprintIn.ghostMapAuth (liveGhost γ) L.enc

def MallocngCoreStInflightA (inflight : Nat) (γ : GhostName)
    (A : MallocngAddrs) (brkStart brk : BitVec 64) (liveCost peakCost : Nat) (st : MallocngSt) : SepProp :=
  ⌜MallocngWFInflight inflight A.base brkStart brk liveCost peakCost st⌝ ∗
  MallocngLiveAuth γ st.liveMap ∗
  (A.ctx ↦ₛ st.ctx.toBytes) ∗
  (A.lock ↦₃₂ 0#32) ∗
  (A.replaced ↦₃₂ 0#32) ∗
  (A.aaReplaced ↦₃₂ 0#32) ∗
  ((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗
  MallocngAuxvState γ st.auxvPtr st.auxvSnap ∗
  ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
  ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
  MappedSet st.masterDom (OwnedMappedByte st)

abbrev MallocngCoreStA := MallocngCoreStInflightA 0

abbrev MallocngRoTablesA (A : MallocngAddrs) : SepProp :=
  MallocngRoTablesAt A

/-- Allocator-private separation-logic invariant (`MallocngCore`). -/
@[irreducible] def MallocngCoreImpl
    (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) : SepProp :=
  MallocngRoTablesA A ∗
  ∃∗ st : MallocngSt,
    ⌜MallocngCountIvsWF b ivs st⌝ ∗
    MallocngCoreStA γ A brkStart brk b.liveCost b.peakCost st

/-- Allocator and single-threaded runtime separation-logic invariant (`MallocngHeap`). -/
@[irreducible] def MallocngHeapImpl
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) : SepProp :=
  MallocngCoreImpl γ A brkStart brk b ivs ∗ MallocngRuntime A tp

theorem MallocngCoreImpl_eq (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) :
    MallocngCoreImpl γ A brkStart brk b ivs =
      (MallocngRoTablesA A ∗
       ∃∗ st : MallocngSt,
         ⌜MallocngCountIvsWF b ivs st⌝ ∗
         MallocngCoreStA γ A brkStart brk b.liveCost b.peakCost st) := by
  unfold MallocngCoreImpl
  rfl

theorem MallocngHeapImpl_eq (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) :
    MallocngHeapImpl γ A tp brkStart brk b ivs =
      (MallocngCoreImpl γ A brkStart brk b ivs ∗ MallocngRuntime A tp) := by
  unfold MallocngHeapImpl
  rfl

/-- Concrete `MallocngIface` witness for `musl` v1.2.5 `mallocng`. -/
def mallocngIface : MallocngIface where
  MallocngHeap := MallocngHeapImpl
  MallocngCore := MallocngCoreImpl
  Block        := MallocngBlockToken
  block_noWrap := mallocngBlock_noWrap

/-! ## `MallocngIfaceFacts` Structural and Startup Laws -/

theorem mallocngHeap_split_runtime
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) :
    mallocngIface.MallocngHeap γ A tp brkStart brk b ivs =
      (mallocngIface.MallocngCore γ A brkStart brk b ivs ∗ MallocngRuntime A tp) :=
  MallocngHeapImpl_eq γ A tp brkStart brk b ivs

private theorem noRO_mallocngAuxvAt (auxvPtr : BitVec 64) :
    SepProp.NoRO (MallocngAuxvAt auxvPtr) := by
  unfold MallocngAuxvAt
  exact SepProp.NoRO.sepExists fun _ =>
    SepProp.NoRO.sepExists fun _ =>
      SepProp.NoRO.sepExists fun _ =>
        SepProp.NoRO.sepExists fun _ =>
          SepProp.NoRO.sepExists fun _ =>
            SepProp.NoRO.sepConj (SepProp.NoRO.pure _)
              (SepProp.NoRO.sepConj (SepProp.NoRO.pointsToWords64 _ _)
                (SepProp.NoRO.pointsToBytes _ _))

private theorem noRO_mallocngAuxvState (γ : GhostName) (auxvPtr : BitVec 64)
    (snap : Option MallocngAuxvSnap) :
    SepProp.NoRO (MallocngAuxvState γ auxvPtr snap) := by
  unfold MallocngAuxvState
  refine SepProp.NoRO.sepConj (SepProp.NoRO.ghostMapAuth _ _) ?_
  rcases snap with _ | ⟨preEntries, randPtr, sufEntries, nullVal, sec⟩
  · exact noRO_mallocngAuxvAt auxvPtr
  · exact SepProp.NoRO.sepConj (SepProp.NoRO.pure _)
      (SepProp.NoRO.sepConj (SepProp.NoRO.pointsToWords64 _ _)
        (SepProp.NoRO.pointsTo64 _ _))

private theorem noRO_mallocngRuntime (A : MallocngAddrs) (tp : BitVec 64) :
    SepProp.NoRO (MallocngRuntime A tp) := by
  unfold MallocngRuntime
  exact SepProp.NoRO.sepConj
    (SepProp.NoRO.sepExists fun _ => SepProp.NoRO.pointsTo32 _ _)
    (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo8 _ _) (SepProp.NoRO.pointsTo64 _ _))

private theorem noRO_mallocngCoreStA (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (liveCost peakCost : Nat) (st : MallocngSt) :
    SepProp.NoRO (MallocngCoreStA γ A brkStart brk liveCost peakCost st) := by
  unfold MallocngCoreStA MallocngCoreStInflightA
  exact SepProp.NoRO.sepConj (SepProp.NoRO.pure _)
    (SepProp.NoRO.sepConj (noRO_mallocngLiveAuth _ _)
      (SepProp.NoRO.sepConj (SepProp.NoRO.pointsToBytes _ _)
        (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo32 _ _)
          (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo32 _ _)
            (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo32 _ _)
              (SepProp.NoRO.sepConj (SepProp.NoRO.pointsTo64 _ _)
                (SepProp.NoRO.sepConj (noRO_mallocngAuxvState _ _ _)
                  (SepProp.NoRO.sepConj (ByteMap_noRO _ _ _)
                    (SepProp.NoRO.sepConj (ProtNoneByteMap_noRO _ _ _)
                      (MappedSet_noRO _ _))))))))))

private theorem mallocngRoTablesAt_dup (A : MallocngAddrs) :
    (MallocngRoTablesAt A ∗ MallocngRoTablesAt A) = MallocngRoTablesAt A := by
  unfold MallocngRoTablesAt
  have h1 := pointsToBytesRO_dup A.sizeClasses mallocngSizeClassBytes
  have h2 := pointsToBytesRO_dup A.debruijnFree mallocngDebruijn32Table
  have h3 := pointsToBytesRO_dup A.medCntTab mallocngMedCntTabBytes
  have h4 := pointsToBytesRO_dup A.smallCntTab mallocngSmallCntTabBytes
  have h5 := pointsToBytesRO_dup A.debruijnAlloc mallocngDebruijn32Table
  have hPair :
      (((A.sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗
        (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
        (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
        (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
        (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table)) ∗
       ((A.sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗
        (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
        (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
        (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
        (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table))) =
      (((A.sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗ (A.sizeClasses ↦ᵣ mallocngSizeClassBytes)) ∗
       ((A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗ (A.debruijnFree ↦ᵣ mallocngDebruijn32Table)) ∗
       ((A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗ (A.medCntTab ↦ᵣ mallocngMedCntTabBytes)) ∗
       ((A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗ (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes)) ∗
       ((A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) ∗ (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table))) := by
    generalize (A.sizeClasses ↦ᵣ mallocngSizeClassBytes) = R1
    generalize (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) = R2
    generalize (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) = R3
    generalize (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) = R4
    generalize (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) = R5
    ac_rfl
  rw [hPair, h1, h2, h3, h4, h5]

theorem mallocngHeap_roSplit
    (γ : GhostName) (A : MallocngAddrs) (tp brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) :
    ∃ Ro Rw : SepProp,
      mallocngIface.MallocngHeap γ A tp brkStart brk b ivs = (Ro ∗ Rw) ∧
      (Ro ∗ Ro) = Ro ∧
      ∀ (h : Heap) (a : BitVec 64) (v : BitVec 8), SepProp.Holds Rw h → h a ≠ some (.ro v) := by
  refine ⟨MallocngRoTablesA A,
    (∃∗ st : MallocngSt,
      ⌜MallocngCountIvsWF b ivs st⌝ ∗
      MallocngCoreStA γ A brkStart brk b.liveCost b.peakCost st) ∗
      MallocngRuntime A tp,
    ?_, mallocngRoTablesAt_dup A, ?_⟩
  · show MallocngHeapImpl γ A tp brkStart brk b ivs = _
    rw [MallocngHeapImpl_eq, MallocngCoreImpl_eq, sepConj_assoc]
  · exact SepProp.NoRO.sepConj
      (SepProp.NoRO.sepExists fun st =>
        SepProp.NoRO.sepConj (SepProp.NoRO.pure _)
          (noRO_mallocngCoreStA γ A brkStart brk b.liveCost b.peakCost st))
      (noRO_mallocngRuntime A tp)

theorem emptyMallocngStOpt_countIvs_wf (auxvPtr : BitVec 64)
    (snapOpt : Option MallocngAuxvSnap) :
    MallocngCountIvsWF mallocngZeroBudget [] (emptyMallocngStOpt auxvPtr snapOpt) := by
  refine ⟨Nat.le_refl 0, ?_, rfl, Nat.zero_le _, by simp [emptyMallocngStOpt, emptyMallocngSt], ?_⟩
  · simp [totalLiveCount, emptyMallocngStOpt, emptyMallocngSt]
  · intro g hg; simp [emptyMallocngStOpt, emptyMallocngSt] at hg

theorem emptyMallocngSt_countIvs_wf (auxvPtr : BitVec 64) :
    MallocngCountIvsWF mallocngZeroBudget [] (emptyMallocngSt auxvPtr) :=
  emptyMallocngStOpt_countIvs_wf auxvPtr none

private theorem bupd_sepExists {α : Type} (P : α → SepProp) :
    (∃∗ x : α, |==> P x) ⊢ |==> (∃∗ x : α, P x) :=
  Entails.sepExists_elim fun x => bupd_mono (Entails.sepExists_intro x)

private theorem ghostPair_init_untracked :
    emp ⊢ |==> (∃∗ γ : GhostName,
      MallocngLiveAuth γ .empty ∗
      ghostMapAuth (auxvGhost γ) (fun _ => none)) := by
  have h1 : emp ⊢ |==> (∃∗ γ1 : GhostName, ghostMapAuth γ1 (fun _ : BitVec 64 => (none : Option Nat))) :=
    ghostMap_init (fun _ => none)
  have h2 : emp ⊢ |==> (∃∗ γ2 : GhostName, ghostMapAuth γ2 (fun _ : BitVec 64 => (none : Option Nat))) :=
    ghostMap_init (fun _ => none)
  have h12 : emp ⊢ |==> ((∃∗ γ1 : GhostName, ghostMapAuth γ1 (fun _ => none)) ∗
      (∃∗ γ2 : GhostName, ghostMapAuth γ2 (fun _ => none))) := by
    conv => lhs; rw [← emp_sepConj emp]
    exact bupd_sep h1 h2
  refine Entails.trans h12 (bupd_mono ?_)
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_elim fun γ1 => ?_
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun γ2 => ?_
  have hLive : liveGhost (natPair γ1 γ2) = γ1 := by simp [liveGhost, natUnpair_natPair]
  have hAuxv : auxvGhost (natPair γ1 γ2) = γ2 := by simp [auxvGhost, natUnpair_natPair]
  refine Entails.trans ?_
    (Entails.sepExists_intro
      (P := fun γ => MallocngLiveAuth γ .empty ∗ ghostMapAuth (auxvGhost γ) (fun _ => none))
      (natPair γ1 γ2))
  unfold MallocngLiveAuth
  rw [hLive, hAuxv]
  exact Entails.refl _

theorem mallocngStartup_packA (γ : GhostName) (A : MallocngAddrs) (tp brkStart auxvPtr : BitVec 64)
    (hBrkWf : MallocngBrkStartWf brkStart) :
    (MallocngLiveAuth γ .empty ∗
     ghostMapAuth (auxvGhost γ) (fun _ => none)) ∗
    MallocngRoTablesAt A ∗
    (A.ctx ↦ₛ List.replicate 928 0#8) ∗
    (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗
    (A.aaReplaced ↦₃₂ 0#32) ∗
    MallocngRuntime A tp ∗
    ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
    MallocngAuxvAt auxvPtr ⊢
      mallocngIface.MallocngHeap γ A tp brkStart brkStart mallocngZeroBudget [] := by
  show _ ⊢ MallocngHeapImpl γ A tp brkStart brkStart mallocngZeroBudget []
  rw [MallocngHeapImpl_eq, MallocngCoreImpl_eq]
  have hWf : MallocngWF A.base brkStart brkStart 0 0 (emptyMallocngSt auxvPtr) :=
    emptyMallocngSt_wf auxvPtr hBrkWf
  have hCountIvs : MallocngCountIvsWF mallocngZeroBudget [] (emptyMallocngSt auxvPtr) :=
    emptyMallocngSt_countIvs_wf auxvPtr
  let st0 := emptyMallocngSt auxvPtr
  have hStep1 :
      (MallocngLiveAuth γ .empty ∗
       ghostMapAuth (auxvGhost γ) (fun _ => none)) ∗
      MallocngRoTablesA A ∗
      (A.ctx ↦ₛ st0.ctx.toBytes) ∗
      (A.lock ↦₃₂ 0#32) ∗
      (A.replaced ↦₃₂ 0#32) ∗
      (A.aaReplaced ↦₃₂ 0#32) ∗
      MallocngRuntime A tp ∗
      ((A.libc + 8#64) ↦₆₄ st0.auxvPtr) ∗
      MallocngAuxvAt st0.auxvPtr ⊢
      (MallocngRoTablesA A ∗
        (⌜MallocngCountIvsWF mallocngZeroBudget [] st0⌝ ∗
          MallocngCoreStA γ A brkStart brkStart 0 0 st0)) ∗ MallocngRuntime A tp := by
    rw [pure_sepConj_of_true hCountIvs]
    unfold MallocngCoreStA MallocngCoreStInflightA MallocngAuxvState ByteMap ProtNoneByteMap MappedSet SetSep
    rw [pure_sepConj_of_true hWf]
    have hDom : st0.masterDom = [] := rfl
    have hMap : st0.liveMap = .empty := rfl
    have hSnap : st0.auxvSnap = none := rfl
    rw [hDom, hMap, hSnap]
    dsimp only [MallocngAuxvAuthMap]
    simp only [BigSep_nil, sepConj_emp]
    generalize (MallocngLiveAuth γ .empty) = P1
    generalize (ghostMapAuth (auxvGhost γ) (fun _ => none)) = P1b
    generalize (MallocngRoTablesA A) = P2
    generalize (A.ctx ↦ₛ st0.ctx.toBytes) = P3
    generalize (A.lock ↦₃₂ 0#32) = P4
    generalize (A.replaced ↦₃₂ 0#32) = P5
    generalize (A.aaReplaced ↦₃₂ 0#32) = P6
    generalize (MallocngRuntime A tp) = P7
    generalize ((A.libc + 8#64) ↦₆₄ st0.auxvPtr) = P8
    generalize (MallocngAuxvAt st0.auxvPtr) = P9
    exact Entails.of_eq (by ac_rfl)
  have hEqLhs :
      (MallocngLiveAuth γ .empty ∗
       ghostMapAuth (auxvGhost γ) (fun _ => none)) ∗
      MallocngRoTablesAt A ∗
      (A.ctx ↦ₛ List.replicate 928 0#8) ∗
      (A.lock ↦₃₂ 0#32) ∗
      (A.replaced ↦₃₂ 0#32) ∗
      (A.aaReplaced ↦₃₂ 0#32) ∗
      MallocngRuntime A tp ∗
      ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
      MallocngAuxvAt auxvPtr =
      (MallocngLiveAuth γ .empty ∗
       ghostMapAuth (auxvGhost γ) (fun _ => none)) ∗
      MallocngRoTablesA A ∗
      (A.ctx ↦ₛ st0.ctx.toBytes) ∗
      (A.lock ↦₃₂ 0#32) ∗
      (A.replaced ↦₃₂ 0#32) ∗
      (A.aaReplaced ↦₃₂ 0#32) ∗
      MallocngRuntime A tp ∗
      ((A.libc + 8#64) ↦₆₄ st0.auxvPtr) ∗
      MallocngAuxvAt st0.auxvPtr := by
    simp only [MallocngRoTablesA, st0, emptyMallocngSt, emptyCtxFields_toBytes]
  rw [hEqLhs]
  refine Entails.trans hStep1 ?_
  exact sepConj_mono_left (sepConj_mono_right
    (Entails.sepExists_intro
      (P := fun st =>
        ⌜MallocngCountIvsWF mallocngZeroBudget [] st⌝ ∗
        MallocngCoreStA γ A brkStart brkStart 0 0 st)
      st0))

theorem mallocngInitResources_ok
    (A : MallocngAddrs) (tp brkStart : BitVec 64)
    (_hTpGe : 0xa4 ≤ tp.toNat)
    (_hTpLe : tp.toNat ≤ 2 ^ 48)
    (hBrkWf : MallocngBrkStartWf brkStart) :
    MallocngStartupResources A tp ⊢
      |==> (∃∗ γ : GhostName,
        mallocngIface.MallocngHeap γ A tp brkStart brkStart mallocngZeroBudget []) := by
  unfold MallocngStartupResources
  refine Entails.sepExists_elim fun auxvPtr => ?_
  let body :=
    MallocngRoTablesAt A ∗
    (A.ctx ↦ₛ List.replicate 928 0#8) ∗
    (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗
    (A.aaReplaced ↦₃₂ 0#32) ∗
    MallocngRuntime A tp ∗
    ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
    MallocngAuxvAt auxvPtr
  have h1 : body ⊢
      (|==> (∃∗ γ : GhostName,
        MallocngLiveAuth γ .empty ∗
        ghostMapAuth (auxvGhost γ) (fun _ => none))) ∗ body := by
    conv => lhs; rw [← emp_sepConj body]
    exact sepConj_mono_left ghostPair_init_untracked
  refine Entails.trans (Entails.trans h1 (bupd_frame_r _ _)) (bupd_mono ?_)
  rw [sepExists_sepConj_left]
  refine Entails.sepExists_mono fun γ => ?_
  exact mallocngStartup_packA γ A tp brkStart auxvPtr hBrkWf

set_option maxRecDepth 100000 in
private theorem mallocngMultiData_eq :
    VerifiedLibraries.mallocngMultiData = [
      { sym := "__malloc_size_classes", align := 4, readOnly := true, zeroTail := 0, bytes := mallocngSizeClassBytes },
      { sym := "debruijn32.4681", align := 1, readOnly := true, zeroTail := 0, bytes := mallocngDebruijn32Table },
      { sym := "med_cnt_tab", align := 1, readOnly := true, zeroTail := 0, bytes := mallocngMedCntTabBytes },
      { sym := "small_cnt_tab", align := 1, readOnly := true, zeroTail := 0, bytes := mallocngSmallCntTabBytes },
      { sym := "debruijn32.5048", align := 1, readOnly := true, zeroTail := 0, bytes := mallocngDebruijn32Table },
      { sym := "__malloc_lock", align := 4, readOnly := false, bytes := [], zeroTail := 4 },
      { sym := "__aligned_alloc_replaced", align := 4, readOnly := false, bytes := [], zeroTail := 4 },
      { sym := "__malloc_replaced", align := 4, readOnly := false, bytes := [], zeroTail := 4 },
      { sym := "__malloc_context", align := 8, readOnly := false, bytes := [], zeroTail := 928 }] := by
  decide +kernel

theorem mallocngLib_dataInit_eq (mpl : Obj.MultiPlacement) :
    let A := mallocngAddrsOfPlacement mpl
    VerifiedLibraries.mallocngLib.dataInit mpl =
      (MallocngRoTablesAt A ∗
       (A.ctx ↦ₛ List.replicate 928 0#8) ∗
       (A.lock ↦₃₂ 0#32) ∗
       (A.replaced ↦₃₂ 0#32) ∗
       (A.aaReplaced ↦₃₂ 0#32)) := by
  intro A
  have h32 : ∀ a : BitVec 64, (a ↦ₛ List.replicate 4 0#8) = (a ↦₃₂ 0#32) := by
    intro a; rw [pointsTo32_eq_pointsToBytes]; rfl
  have hData : VerifiedLibraries.mallocngLib.data = VerifiedLibraries.mallocngMultiData := rfl
  unfold Obj.MultiPlacedLib.dataInit
  rw [hData, mallocngMultiData_eq]
  unfold Obj.MultiPlacedLib.patchedData Obj.sepAll MallocngRoTablesAt
  simp only [List.map, List.foldl, List.append_nil, List.nil_append, List.replicate_zero, ↓reduceIte, h32]
  change
    ((A.sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗
     (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
     (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
     (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
     (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) ∗
     (A.lock ↦₃₂ 0#32) ∗
     (A.aaReplaced ↦₃₂ 0#32) ∗
     (A.replaced ↦₃₂ 0#32) ∗
     (A.ctx ↦ₛ List.replicate 928 0#8)) =
    (((A.sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗
      (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
      (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
      (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
      (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table)) ∗
     (A.ctx ↦ₛ List.replicate 928 0#8) ∗
     (A.lock ↦₃₂ 0#32) ∗
     (A.replaced ↦₃₂ 0#32) ∗
     (A.aaReplaced ↦₃₂ 0#32))
  generalize (A.sizeClasses ↦ᵣ mallocngSizeClassBytes) = D0
  generalize (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) = D1
  generalize (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) = D2
  generalize (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) = D3
  generalize (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) = D4
  generalize (A.lock ↦₃₂ 0#32) = D5
  generalize (A.aaReplaced ↦₃₂ 0#32) = D6
  generalize (A.replaced ↦₃₂ 0#32) = D7
  generalize (A.ctx ↦ₛ List.replicate 928 0#8) = D8
  ac_rfl

theorem mallocngPlacedInit_ok : mallocngInitStmt mallocngIface := by
  intro mpl tp brkStart auxvPtr R m A hTpGe hTpLe hBrkWf hSat
  have hStartup :
      (VerifiedLibraries.mallocngLib.dataInit mpl ∗
       MallocngRuntime A tp ∗
       ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
       MallocngAuxvAt auxvPtr ∗ R) ⊢
      MallocngStartupResources A tp ∗ R := by
    rw [mallocngLib_dataInit_eq mpl]
    change
      ((MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ List.replicate 928 0#8) ∗
        (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗
        (A.aaReplaced ↦₃₂ 0#32)) ∗
       MallocngRuntime A tp ∗
       ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
       MallocngAuxvAt auxvPtr ∗ R) ⊢
      MallocngStartupResources A tp ∗ R
    have hAssoc :
        ((MallocngRoTablesAt A ∗
          (A.ctx ↦ₛ List.replicate 928 0#8) ∗
          (A.lock ↦₃₂ 0#32) ∗
          (A.replaced ↦₃₂ 0#32) ∗
          (A.aaReplaced ↦₃₂ 0#32)) ∗
         MallocngRuntime A tp ∗
         ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
         MallocngAuxvAt auxvPtr ∗ R) =
        ((MallocngRoTablesAt A ∗
          (A.ctx ↦ₛ List.replicate 928 0#8) ∗
          (A.lock ↦₃₂ 0#32) ∗
          (A.replaced ↦₃₂ 0#32) ∗
          (A.aaReplaced ↦₃₂ 0#32) ∗
          MallocngRuntime A tp ∗
          ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
          MallocngAuxvAt auxvPtr) ∗ R) := by ac_rfl
    rw [hAssoc]
    refine sepConj_mono_left ?_
    unfold MallocngStartupResources
    exact Entails.sepExists_intro
      (P := fun av =>
        MallocngRoTablesAt A ∗
        (A.ctx ↦ₛ List.replicate 928 0#8) ∗
        (A.lock ↦₃₂ 0#32) ∗
        (A.replaced ↦₃₂ 0#32) ∗
        (A.aaReplaced ↦₃₂ 0#32) ∗
        MallocngRuntime A tp ∗
        ((A.libc + 8#64) ↦₆₄ av) ∗
        MallocngAuxvAt av)
      auxvPtr
  have hSatStartup := Satisfies.of_entails hSat hStartup
  have hInit :=
    Satisfies.of_bupd_frame_left
      (mallocngInitResources_ok A tp brkStart hTpGe hTpLe hBrkWf)
      hSatStartup
  rw [sepExists_sepConj_left, satisfies_sepExists] at hInit
  obtain ⟨γ, hγ⟩ := hInit
  refine ⟨γ, ?_⟩
  rw [satisfies_bupd]
  exact hγ

/-! ## Tracked Startup `auxv` Initialization and Teardown -/

private theorem ghostPair_init_tracked (auxvPtr : BitVec 64) (snap : MallocngAuxvSnap) :
    emp ⊢ |==> (∃∗ γ : GhostName,
      (MallocngLiveAuth γ .empty ∗
       ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap auxvPtr (some snap))) ∗
      MallocngAuxvTicket γ auxvPtr snap) := by
  have h1 : emp ⊢ |==> (∃∗ γ1 : GhostName, ghostMapAuth γ1 (fun _ : BitVec 64 => (none : Option Nat))) :=
    ghostMap_init (fun _ => none)
  have h2_0 : emp ⊢ |==> (∃∗ γ2 : GhostName, ghostMapAuth γ2 (fun _ : BitVec 64 => (none : Option Nat))) :=
    ghostMap_init (fun _ => none)
  have h2_step :
      (∃∗ γ2 : GhostName, ghostMapAuth γ2 (fun _ => none)) ⊢
      |==> (∃∗ γ2 : GhostName,
        ghostMapAuth γ2 (MallocngAuxvAuthMap auxvPtr (some snap)) ∗
        ghostMapElem γ2 0#64 (encodeAuxvSnap auxvPtr snap)) :=
    Entails.trans
      (Entails.sepExists_mono fun γ2 =>
        ghostMap_alloc γ2 (fun _ => none) 0#64 (encodeAuxvSnap auxvPtr snap) rfl)
      (bupd_sepExists _)
  have h2 := Entails.trans h2_0 (Entails.trans (bupd_mono h2_step) (bupd_trans _))
  have h12 : emp ⊢ |==> ((∃∗ γ1 : GhostName, ghostMapAuth γ1 (fun _ => none)) ∗
      (∃∗ γ2 : GhostName,
        ghostMapAuth γ2 (MallocngAuxvAuthMap auxvPtr (some snap)) ∗
        ghostMapElem γ2 0#64 (encodeAuxvSnap auxvPtr snap))) := by
    conv => lhs; rw [← emp_sepConj emp]
    exact bupd_sep h1 h2
  refine Entails.trans h12 (bupd_mono ?_)
  rw [sepExists_sepConj_left]; refine Entails.sepExists_elim fun γ1 => ?_
  rw [sepExists_sepConj_right]; refine Entails.sepExists_elim fun γ2 => ?_
  have hLive : liveGhost (natPair γ1 γ2) = γ1 := by simp [liveGhost, natUnpair_natPair]
  have hAuxv : auxvGhost (natPair γ1 γ2) = γ2 := by simp [auxvGhost, natUnpair_natPair]
  refine Entails.trans ?_
    (Entails.sepExists_intro
      (P := fun γ => (MallocngLiveAuth γ .empty ∗
        ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap auxvPtr (some snap))) ∗
        MallocngAuxvTicket γ auxvPtr snap)
      (natPair γ1 γ2))
  unfold MallocngLiveAuth MallocngAuxvTicket
  rw [hLive, hAuxv, sepConj_assoc]
  exact Entails.refl _

/-- Tracked startup initialization for `mallocngIface.MallocngCore`: preserves the concrete
    startup `auxv` table `(auxvPtr, preEntries, randPtr, sufEntries, nullVal, sec)` via an
    agreement ticket `MallocngAuxvTicket γ auxvPtr (...)` recoverable at teardown. -/
theorem mallocngInitCore_tracked
    (A : MallocngAddrs) (brkStart auxvPtr : BitVec 64)
    (preEntries : List (BitVec 64 × BitVec 64)) (randPtr : BitVec 64)
    (sufEntries : List (BitVec 64 × BitVec 64)) (nullVal sec : BitVec 64)
    (hBrkWf : MallocngBrkStartWf brkStart)
    (hPreTags : ∀ e ∈ preEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64)
    (hSufTags : ∀ e ∈ sufEntries, e.1 ≠ 0#64 ∧ e.1 ≠ 25#64)
    (hLen64 : preEntries.length + sufEntries.length ≤ 64)
    (hAuxvFit : auxvPtr.toNat + 16 * (preEntries.length + sufEntries.length + 2) ≤ 2 ^ 48)
    (hRandFit : randPtr.toNat + 16 ≤ 2 ^ 48) :
    MallocngRoTablesAt A ∗ (A.ctx ↦ₛ List.replicate 928 0#8) ∗ (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗ (A.aaReplaced ↦₃₂ 0#32) ∗ ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
    (auxvPtr ↦₆₄* ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
      fun (t, v) => [t, v])) ∗ ((randPtr + 8#64) ↦₆₄ sec) ⊢
      |==> (∃∗ γ : GhostName,
        mallocngIface.MallocngCore γ A brkStart brkStart mallocngZeroBudget [] ∗
        MallocngAuxvTicket γ auxvPtr (preEntries, randPtr, sufEntries, nullVal, sec)) := by
  let snap : MallocngAuxvSnap := (preEntries, randPtr, sufEntries, nullVal, sec)
  let ws := (preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap fun (t, v) => [t, v]
  let body := MallocngRoTablesAt A ∗ (A.ctx ↦ₛ List.replicate 928 0#8) ∗ (A.lock ↦₃₂ 0#32) ∗
    (A.replaced ↦₃₂ 0#32) ∗ (A.aaReplaced ↦₃₂ 0#32) ∗ ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
    (auxvPtr ↦₆₄* ws) ∗ ((randPtr + 8#64) ↦₆₄ sec)
  have h1 : body ⊢ (|==> (∃∗ γ : GhostName, (MallocngLiveAuth γ .empty ∗
      ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap auxvPtr (some snap))) ∗
      MallocngAuxvTicket γ auxvPtr snap)) ∗ body := by
    conv => lhs; rw [← emp_sepConj body]
    exact sepConj_mono_left (ghostPair_init_tracked auxvPtr snap)
  refine Entails.trans (Entails.trans h1 (bupd_frame_r _ _)) (bupd_mono ?_)
  rw [sepExists_sepConj_left]; refine Entails.sepExists_mono fun γ => ?_
  show _ ⊢ MallocngCoreImpl γ A brkStart brkStart mallocngZeroBudget [] ∗ MallocngAuxvTicket γ auxvPtr snap
  rw [MallocngCoreImpl_eq]
  let st0 := emptyMallocngStOpt auxvPtr (some snap)
  have hWf := emptyMallocngStOpt_wf (base := A.base) auxvPtr (some snap) hBrkWf
  have hCountIvs := emptyMallocngStOpt_countIvs_wf auxvPtr (some snap)
  have hAuxvWf : MallocngAuxvConcreteWf auxvPtr preEntries randPtr sufEntries :=
    ⟨hPreTags, hSufTags, hLen64, hAuxvFit, hRandFit⟩
  have hPack :
      ((MallocngLiveAuth γ .empty ∗
        ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap auxvPtr (some snap))) ∗
       MallocngAuxvTicket γ auxvPtr snap) ∗ body ⊢
      (MallocngRoTablesA A ∗ (⌜MallocngCountIvsWF mallocngZeroBudget [] st0⌝ ∗
        MallocngCoreStA γ A brkStart brkStart 0 0 st0)) ∗ MallocngAuxvTicket γ auxvPtr snap := by
    dsimp only [body]; rw [pure_sepConj_of_true hCountIvs]
    unfold MallocngCoreStA MallocngCoreStInflightA MallocngAuxvState ByteMap ProtNoneByteMap MappedSet SetSep
    rw [pure_sepConj_of_true hWf]
    have hDom : st0.masterDom = [] := rfl
    have hMap : st0.liveMap = .empty := rfl
    have hPtr : st0.auxvPtr = auxvPtr := rfl
    have hSnap : st0.auxvSnap = some snap := rfl
    have hCtx : st0.ctx.toBytes = List.replicate 928 0#8 := emptyCtxFields_toBytes
    rw [hDom, hMap, hPtr, hSnap, hCtx]; dsimp only [snap, ws]; rw [pure_sepConj_of_true hAuxvWf]
    simp only [BigSep_nil, sepConj_emp, MallocngRoTablesA]; exact Entails.of_eq (by ac_rfl)
  exact Entails.trans hPack (sepConj_mono_left (sepConj_mono_right
    (Entails.sepExists_intro (P := fun st =>
      ⌜MallocngCountIvsWF mallocngZeroBudget [] st⌝ ∗ MallocngCoreStA γ A brkStart brkStart 0 0 st) st0)))

/-- Teardown of `mallocngIface.MallocngCore` paired with `MallocngAuxvTicket`: recovers the exact
    startup `__libc.auxv` pointer, `auxv` table words, and `AT_RANDOM` secret word. -/
theorem mallocngCore_teardown_auxv
    (γ : GhostName) (A : MallocngAddrs) (brkStart brk : BitVec 64)
    (b : MallocngBudget) (ivs : List (BitVec 64 × Nat))
    (auxvPtr : BitVec 64)
    (preEntries : List (BitVec 64 × BitVec 64)) (randPtr : BitVec 64)
    (sufEntries : List (BitVec 64 × BitVec 64)) (nullVal sec : BitVec 64) :
    mallocngIface.MallocngCore γ A brkStart brk b ivs ∗
    MallocngAuxvTicket γ auxvPtr (preEntries, randPtr, sufEntries, nullVal, sec) ⊢
      ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗
      (auxvPtr ↦₆₄*
        ((preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
          fun (t, v) => [t, v])) ∗
      ((randPtr + 8#64) ↦₆₄ sec) ∗
      ∃∗ R_dead : SepProp, R_dead := by
  let snap : MallocngAuxvSnap := (preEntries, randPtr, sufEntries, nullVal, sec)
  show MallocngCoreImpl γ A brkStart brk b ivs ∗ MallocngAuxvTicket γ auxvPtr snap ⊢ _
  rw [MallocngCoreImpl_eq, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun st => ?_
  unfold MallocngCoreStA MallocngCoreStInflightA MallocngAuxvState MallocngAuxvTicket
  let auxvBody : SepProp :=
    match st.auxvSnap with
    | none => MallocngAuxvAt st.auxvPtr
    | some (pe, rp, se, nv, sc) =>
      ⌜MallocngAuxvConcreteWf st.auxvPtr pe rp se⌝ ∗
      (st.auxvPtr ↦₆₄* ((pe ++ [(25#64, rp)] ++ se ++ [(0#64, nv)]).flatMap fun (t, v) => [t, v])) ∗
      ((rp + 8#64) ↦₆₄ sc)
  let restCore : SepProp :=
    MallocngRoTablesA A ∗ ⌜MallocngCountIvsWF b ivs st⌝ ∗
    ⌜MallocngWFInflight 0 A.base brkStart brk b.liveCost b.peakCost st⌝ ∗
    MallocngLiveAuth γ st.liveMap ∗ (A.ctx ↦ₛ st.ctx.toBytes) ∗
    (A.lock ↦₃₂ 0#32) ∗ (A.replaced ↦₃₂ 0#32) ∗ (A.aaReplaced ↦₃₂ 0#32) ∗
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal ∗
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∗
    MappedSet st.masterDom (OwnedMappedByte st)
  refine Entails.trans (Q :=
      (ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap st.auxvPtr st.auxvSnap) ∗
       ghostMapElem (auxvGhost γ) 0#64 (encodeAuxvSnap auxvPtr snap)) ∗
      (((A.libc + 8#64) ↦₆₄ st.auxvPtr) ∗ auxvBody ∗ restCore))
    (Entails.of_eq (by dsimp only [auxvBody, restCore]; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left
    (ghostMap_lookup (auxvGhost γ) (MallocngAuxvAuthMap st.auxvPtr st.auxvSnap)
      0#64 (encodeAuxvSnap auxvPtr snap))) ?_
  rw [sepConj_assoc]
  refine Entails.pure_left fun hLookup => ?_
  dsimp only [auxvBody]
  rcases hSnap : st.auxvSnap with _ | ⟨pe, rp, se, nv, sc⟩
  · rw [hSnap] at hLookup
    simp [MallocngAuxvAuthMap] at hLookup
  · rw [hSnap] at hLookup
    simp only [MallocngAuxvAuthMap, ↓reduceIte, Option.some.injEq] at hLookup
    have hDec := congrArg decodeAuxvSnap hLookup
    rw [decodeAuxvSnap_encodeAuxvSnap, decodeAuxvSnap_encodeAuxvSnap] at hDec
    have ⟨hPtrEq, hSnapEq⟩ := Prod.mk.inj hDec
    dsimp only [snap] at hSnapEq
    have ⟨hPe, h1⟩ := Prod.mk.inj hSnapEq
    have ⟨hRp, h2⟩ := Prod.mk.inj h1
    have ⟨hSe, h3⟩ := Prod.mk.inj h2
    have ⟨hNv, hSc⟩ := Prod.mk.inj h3
    rw [hPtrEq, hPe, hRp, hSe, hNv, hSc]
    let ws := (preEntries ++ [(25#64, randPtr)] ++ sufEntries ++ [(0#64, nullVal)]).flatMap
      fun (t, v) => [t, v]
    let R_dead : SepProp :=
      (ghostMapAuth (auxvGhost γ) (MallocngAuxvAuthMap auxvPtr (some snap)) ∗
       ghostMapElem (auxvGhost γ) 0#64 (encodeAuxvSnap auxvPtr snap)) ∗
      ⌜MallocngAuxvConcreteWf auxvPtr preEntries randPtr sufEntries⌝ ∗ restCore
    refine Entails.trans (Q :=
        ((A.libc + 8#64) ↦₆₄ auxvPtr) ∗ (auxvPtr ↦₆₄* ws) ∗ ((randPtr + 8#64) ↦₆₄ sec) ∗ R_dead)
      (Entails.of_eq (by dsimp only [R_dead, ws, snap]; ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (Entails.sepExists_intro (P := fun R => R) R_dead)))

end VerifiedLibraries.Mallocng.Proofs
