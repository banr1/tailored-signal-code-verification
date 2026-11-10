/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Data.List.Forall2
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupProof
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotHelpers2

/-!
# Fine-Trace Definitions for Placed `alloc_group` and `alloc_slot`

Defines `allocSlotFineByteBound`, group-geometry equivalence (`GroupSameGeom`,
`SameGroupsSlotKind`), the inductive `AllocSlotFineTrace` derivation for `blk08`, recursive
cut-point contracts, and byte-delta / OOM / count-dispatch combinators.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

arm64_proof_prelude

/-! ## Byte Bounds and `AllocSlotFineTrace` -/

def allocSlotFineByteBound (sc maxMetaAreas : Nat) : Nat :=
  (allocSlotDepthBound sc + 1) * (5 * 1024 * 1024 + 32768 * maxMetaAreas)

/-- Exact equality of group geometry fields across intra-`alloc_slot` metadata transitions. -/
def GroupSameGeom (g' g : GroupDesc) : Prop :=
  g'.metaPtr = g.metaPtr ∧ g'.sc = g.sc ∧ g'.maplen = g.maplen ∧
  g'.nestedCap = g.nestedCap ∧ g'.lastIdx = g.lastIdx

/-- `List.Forall₂` group-list equivalence preserving `GroupSameGeom` and per-slot `SlotSameKind`
    (`freeAvail ↔ freeInactive` allowed; `.claimed`, `.liveNested`, `.liveUser` preserved verbatim). -/
def SameGroupsSlotKind (gs' gs : List GroupDesc) : Prop :=
  List.Forall₂ (fun g' g => GroupSameGeom g' g ∧ List.Forall₂ SlotSameKind g'.slots g.slots) gs' gs

/-- Inductive trace of compiled `alloc_slot(sc, req)` (`blk08`) from `st0` to `(st', idx)`:
    - `pop`: fastPop or `try_avail` slow-chain claims an existing free slot `(g_f, idx)` without
      creating any group (`SameGroupsSlotKind` up to setting `g_f.slots[idx] := .claimed`);
    - `rootGroup`: reaches `alloc_group` (`+0x280`) in a ring-empty state `st_ag`
      (`st_ag.ctx.active[sc] = 0#64` with `MallocngWFInflight`), selects `cnt'` (`2048 < cnt' * slotStride sc + 16`),
      and `mmap`s one new root group `cg` (`rootParamPred sc cg.cnt (cg.maplen * 4096)`);
    - `nestedGroup`: reaches `alloc_group` (`+0x280`) in a ring-empty state `st_ag`
      (`st_ag.ctx.active[sc] = 0#64` with `MallocngWFInflight`), selects `ValidNestedCnt sc cnt'`,
      recursively runs `alloc_slot(pSc, needed)` to `(st2, pIdx)`, and enframes one new nested group `cg`. -/
inductive AllocSlotFineTrace (rootParamPred : Nat → Nat → Nat → Prop)
    (base brkStart : BitVec 64) (liveCost peakCost : Nat) :
    Nat → Nat → Nat → MallocngSt → MallocngSt → Nat → Prop where
  | pop {inflight sc req : Nat} {st0 st_f st' : MallocngSt} {g_f : GroupDesc} {idx : Nat}
      (hPre : SameGroupsSlotKind st_f.groups st0.groups) (hgf : g_f ∈ st_f.groups) (hgfSc : g_f.sc = sc)
      (hIdx : idx < g_f.slots.length) (hFree : (g_f.slots[idx]'hIdx).isFree = true)
      (hClaim : SameGroupsSlotKind st'.groups (st_f.groups.map fun g =>
        if g.metaPtr == g_f.metaPtr then { g with slots := g.slots.set idx .claimed } else g)) :
      AllocSlotFineTrace rootParamPred base brkStart liveCost peakCost inflight sc req st0 st' idx
  | rootGroup {inflight sc req : Nat} {st0 st_ag st' : MallocngSt}
      {brk_ag : BitVec 64} {cnt' activeIdx : Nat} {cg : GroupDesc}
      (hPre : SameGroupsSlotKind st_ag.groups st0.groups)
      (hwfAg : MallocngWFInflight inflight base brkStart brk_ag liveCost peakCost st_ag)
      (hAct0 : ∀ h : sc < st_ag.ctx.active.length, st_ag.ctx.active[sc]'h = 0#64)
      (hCnt' : 1 ≤ cnt' ∧ cnt' ≤ 32 ∧ 2048 < cnt' * slotStride sc + 16 ∧
        cnt' * slotStride sc ≤ 1048575 ∧ (sc ≤ 25 → cnt' * slotStride sc + 20 ≤ 65536) ∧
        (sc ≤ 8 → ∃ j, j < 3 ∧ cnt' = (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat))
      (hRootP : rootParamPred sc cg.cnt (cg.maplen * 4096))
      (hCgProps : 0 < cg.maplen ∧ cg.sc = sc ∧ cg.parentMeta = none ∧ cg.nestedCap = 0 ∧
        activeIdx ≤ cg.lastIdx ∧ cg.slots = newGroupSlots cg.lastIdx activeIdx)
      (hGroups' : st'.groups = cg :: st_ag.groups) :
      AllocSlotFineTrace rootParamPred base brkStart liveCost peakCost inflight sc req st0 st' 0
  | nestedGroup {inflight sc req : Nat} {st0 st_ag st2 st' : MallocngSt}
      {brk_ag : BitVec 64} {cnt' pIdx : Nat} {pg cg : GroupDesc}
      (hPre : SameGroupsSlotKind st_ag.groups st0.groups)
      (hwfAg : MallocngWFInflight inflight base brkStart brk_ag liveCost peakCost st_ag)
      (hAct0 : ∀ h : sc < st_ag.ctx.active.length, st_ag.ctx.active[sc]'h = 0#64)
      (hv : ValidNestedCnt sc cnt')
      (hParentTrace : AllocSlotFineTrace rootParamPred base brkStart liveCost peakCost
        (inflight + 1) (sizeToClassUnits (cnt' * sizeClass sc)) (cnt' * slotStride sc + 12) st_ag st2 pIdx)
      (hPg : pg ∈ st2.groups ∧ pg.sc = sizeToClassUnits (cnt' * sizeClass sc) ∧
        ∃ hpIdx : pIdx < pg.slots.length, pg.slots[pIdx]'hpIdx = .claimed)
      (hCgProps : cg.sc = sc ∧ cg.maplen = 0 ∧ cg.parentMeta = some pg.metaPtr ∧
        cg.nestedCap = slotStride pg.sc - 4 ∧ cg.lastIdx = cnt' - 1 ∧ cg.slots = newGroupSlots (cnt' - 1) (cnt' - 1))
      (hGroups' : st'.groups = cg :: st2.groups.map (fun g =>
        if g.metaPtr == pg.metaPtr then { pg with slots := pg.slots.set pIdx (.liveNested cg.metaPtr) } else g)) :
      AllocSlotFineTrace rootParamPred base brkStart liveCost peakCost inflight sc req st0 st' 0

/-! ## Equivalence and Composition Lemmas -/

theorem slotSameKind_refl (s : SlotState) : SlotSameKind s s := Or.inl rfl

theorem slotSameKind_symm {s1 s2 : SlotState} (h : SlotSameKind s1 s2) : SlotSameKind s2 s1 := by
  rcases h with rfl | ⟨h1, h2⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨h2, h1⟩

theorem slotSameKind_trans {s1 s2 s3 : SlotState}
    (h12 : SlotSameKind s1 s2) (h23 : SlotSameKind s2 s3) : SlotSameKind s1 s3 := by
  rcases h12 with rfl | ⟨hf1, hf2⟩
  · exact h23
  · rcases h23 with rfl | ⟨_, hf3⟩
    · exact Or.inr ⟨hf1, hf2⟩
    · exact Or.inr ⟨hf1, hf3⟩

theorem list_forall2_slotSameKind_refl (ss : List SlotState) : List.Forall₂ SlotSameKind ss ss := by
  induction ss with | nil => exact .nil | cons s _ ih => exact .cons (slotSameKind_refl s) ih

theorem list_forall2_slotSameKind_symm {ss1 ss2 : List SlotState}
    (h : List.Forall₂ SlotSameKind ss1 ss2) : List.Forall₂ SlotSameKind ss2 ss1 := by
  induction h with | nil => exact .nil | cons hh _ ih => exact .cons (slotSameKind_symm hh) ih

theorem list_forall2_slotSameKind_trans {ss1 ss2 ss3 : List SlotState}
    (h12 : List.Forall₂ SlotSameKind ss1 ss2) (h23 : List.Forall₂ SlotSameKind ss2 ss3) :
    List.Forall₂ SlotSameKind ss1 ss3 := by
  induction h12 generalizing ss3 with
  | nil => cases h23; exact .nil
  | cons hh12 _ ih => cases h23 with | cons hh23 htl23 => exact .cons (slotSameKind_trans hh12 hh23) (ih htl23)

theorem GroupSameGeom.refl (g : GroupDesc) : GroupSameGeom g g :=
  ⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩

theorem GroupSameGeom.symm {g1 g2 : GroupDesc} (h : GroupSameGeom g1 g2) : GroupSameGeom g2 g1 :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

theorem GroupSameGeom.trans {g1 g2 g3 : GroupDesc}
    (h12 : GroupSameGeom g1 g2) (h23 : GroupSameGeom g2 g3) : GroupSameGeom g1 g3 :=
  ⟨h12.1.trans h23.1, h12.2.1.trans h23.2.1, h12.2.2.1.trans h23.2.2.1,
   h12.2.2.2.1.trans h23.2.2.2.1, h12.2.2.2.2.trans h23.2.2.2.2⟩

theorem SameGroupsSlotKind.refl (gs : List GroupDesc) : SameGroupsSlotKind gs gs := by
  induction gs with
  | nil => exact .nil
  | cons g _ ih => exact .cons ⟨GroupSameGeom.refl g, list_forall2_slotSameKind_refl g.slots⟩ ih

theorem SameGroupsSlotKind.symm {gs1 gs2 : List GroupDesc}
    (h : SameGroupsSlotKind gs1 gs2) : SameGroupsSlotKind gs2 gs1 := by
  induction h with | nil => exact .nil | cons hh _ ih => exact .cons ⟨hh.1.symm, list_forall2_slotSameKind_symm hh.2⟩ ih

theorem SameGroupsSlotKind.trans {gs1 gs2 gs3 : List GroupDesc}
    (h12 : SameGroupsSlotKind gs1 gs2) (h23 : SameGroupsSlotKind gs2 gs3) : SameGroupsSlotKind gs1 gs3 := by
  induction h12 generalizing gs3 with
  | nil => cases h23; exact .nil
  | cons hh12 _ ih =>
    cases h23 with | cons hh23 htl23 => exact .cons ⟨hh12.1.trans hh23.1, list_forall2_slotSameKind_trans hh12.2 hh23.2⟩ (ih htl23)

theorem SameGroupsSlotKind.length_eq {gs' gs : List GroupDesc} (h : SameGroupsSlotKind gs' gs) :
    gs'.length = gs.length := List.Forall₂.length_eq h

theorem SameGroupsSlotKind.of_map {gs : List GroupDesc} {f : GroupDesc → GroupDesc}
    (h : ∀ g ∈ gs, GroupSameGeom (f g) g ∧ List.Forall₂ SlotSameKind (f g).slots g.slots) :
    SameGroupsSlotKind (gs.map f) gs := by
  induction gs with
  | nil => exact .nil
  | cons g _ ih => exact .cons (h g (List.Mem.head _)) (ih fun x hx => h x (List.Mem.tail _ hx))

theorem SameGroupsSlotKind.of_map_map {gs : List GroupDesc} {f1 f2 : GroupDesc → GroupDesc}
    (h : ∀ g ∈ gs, GroupSameGeom (f1 g) (f2 g) ∧ List.Forall₂ SlotSameKind (f1 g).slots (f2 g).slots) :
    SameGroupsSlotKind (gs.map f1) (gs.map f2) := by
  induction gs with
  | nil => exact .nil
  | cons g _ ih => exact .cons (h g (List.Mem.head _)) (ih fun x hx => h x (List.Mem.tail _ hx))

theorem AllocSlotFineTrace.prepend_sameGroups {rootParamPred : Nat → Nat → Nat → Prop}
    {base brkStart : BitVec 64} {liveCost peakCost inflight sc req idx : Nat} {st0 st1 st' : MallocngSt}
    (h01 : SameGroupsSlotKind st1.groups st0.groups)
    (hTr : AllocSlotFineTrace rootParamPred base brkStart liveCost peakCost inflight sc req st1 st' idx) :
    AllocSlotFineTrace rootParamPred base brkStart liveCost peakCost inflight sc req st0 st' idx := by
  cases hTr with
  | pop hPre hgf hgfSc hIdx hFree hClaim => exact .pop (SameGroupsSlotKind.trans hPre h01) hgf hgfSc hIdx hFree hClaim
  | rootGroup hPre hwfAg hAct0 hCnt' hRootP hCgProps hGroups' =>
    exact .rootGroup (SameGroupsSlotKind.trans hPre h01) hwfAg hAct0 hCnt' hRootP hCgProps hGroups'
  | nestedGroup hPre hwfAg hAct0 hv hParentTrace hPg hCgProps hGroups' =>
    exact .nestedGroup (SameGroupsSlotKind.trans hPre h01) hwfAg hAct0 hv hParentTrace hPg hCgProps hGroups'

/-! ## Recursive Cut-Point Contracts -/

/-- Cross-block fine-model parameter contract for `__malloc_alloc_meta` (`blk07`). -/
def AllocMetaFineParamStmt : Prop :=
  ∀ [MallocngMultiPlacement] {P : Program}
    (inflight : Nat) (_hInflight : inflight ≤ 7) (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost maxGroups maxMetaAreas : Nat) (st : MallocngSt)
    (_hGroups : st.groups.length ≤ maxGroups) (_hMeta0 : st.metaAreas.length ≤ maxMetaAreas)
    (_hMetaStep : 1 + (7 + maxGroups) / 101 ≤ maxMetaAreas)
    (_hext : ∀ pc, P.externAt? pc = none) (_hsvc : P.svc = msvc),
    subroutine_ok P (mbase 7) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗ stackFrame s0 224 ∗
        MallocngCoreStInflightA inflight γ maddrs brkStart s0.brk liveCost peakCost st ∗ MallocngRuntime maddrs tp
      post := fun _ s0 sf =>
        ∃∗ st' : MallocngSt, ∃∗ m : BitVec 64,
          ⌜MallocngProcPreserved s0 sf ∧ sf.readReg64 .x0 = m ∧ m ≠ 0#64 ∧
           4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧ m ∉ st.reservedMetas ∧
           st'.reservedMetas = m :: st.reservedMetas ∧ st'.groups = st.groups ∧
           st'.activeLists = st.activeLists ∧ st'.liveMap = st.liveMap ∧
           totalLiveCount st' = totalLiveCount st ∧ st'.metaAreas.length ≤ maxMetaAreas ∧
           st'.ctx.active = st.ctx.active ∧ st'.ctx.usageByClass = st.ctx.usageByClass ∧
           st'.ctx.unmapSeq = st.ctx.unmapSeq ∧ st'.ctx.bounces = st.ctx.bounces ∧ st'.ctx.seq = st.ctx.seq ∧
           (∀ g ∈ st.groups, ∀ a : BitVec 64,
             (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) → st'.byteVal a = st.byteVal a) ∧
           MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem ∧
           MallocngMappedDelta 1 (32768 * maxMetaAreas) s0.mem sf.mem⌝ ∗
          stackFrame s0 224 ∗ MallocngRuntime maddrs tp ∗ (m ↦ₛ List.replicate 40 0#8) ∗
          MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st'
      onOom := fun _ s0 sf => ⌜MallocngPlacedOomCond msvc 1 (32768 * maxMetaAreas) s0 sf⌝
    })

/-- Root size-selection contract strengthened with `rootParamPred sc cnt_f len`. -/
def RootSizeSelectParamStmt (rootParamPred : Nat → Nat → Nat → Prop) : Prop :=
  ∀ [MallocngMultiPlacement] (s : State) (sc req cnt' : Nat) (use : BitVec 64) (Frame : SepProp)
    (_hw768 : Blk08HasWords768 mallocngFaultSvc) (_hsc : sc < 48) (_hReq : req ≤ nominalSlotCap sc)
    (_hlo : 1 ≤ cnt') (_hhi : cnt' ≤ 32) (_hgt2048 : 2048 < cnt' * slotStride sc + 16)
    (_hprod : cnt' * slotStride sc ≤ 1048575) (_h25 : sc ≤ 25 → cnt' * slotStride sc + 20 ≤ 65536)
    (_hcnt' : cnt' = Cost.cntSel sc use.toNat)
    (_hpc : s.pc = mbase 8 + allocSlotOff_bounces_cap) (_hrun : s.status = .Running)
    (_hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc))
    (_hx4 : s.readReg64 .x4 = 4096#64)
    (_hx6 : s.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt'))
    (_hx7 : 38 < sc → s.readReg64 .x7 = 1#64)
    (_hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt')
    (_hx21 : s.readReg64 .x21 = BitVec.ofNat 64 sc)
    (_hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc)) (_hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req)
    (_hx27 : s.readReg64 .x27 = BitVec.ofNat 64 (slotStride sc))
    (_hx25_38 : 38 < sc → (s.readReg64 .x2).toNat = use.toNat ∧ s.readReg64 .x5 = 0#64),
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc) (mbase 8 + allocSlotOff_mmap_go) s Frame
      (fun sf P_f => ∃ cnt_f len, RootMmapParamsOk sc cnt_f len ∧ rootParamPred sc cnt_f len ∧
        (cnt_f = 1 → req + 20 ≤ len) ∧ sf.status = .Running ∧ sf.sp = s.sp ∧ sf.spAligned = s.spAligned ∧
        PureStatePres s sf ∧ sf.readReg64 .x20 = BitVec.ofNat 64 cnt_f ∧ sf.readReg64 .x26 = BitVec.ofNat 64 len ∧
        (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x20 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 →
          sf.readReg64 r = s.readReg64 r) ∧ P_f = Frame)
      (fun _ => ⌜False⌝)

abbrev AllocSlotFineTracePostProp [MallocngMultiPlacement] (rootParamPred : Nat → Nat → Nat → Prop)
    (sc req inflight : Nat) (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost maxMetaAreas : Nat) (st0 : MallocngSt) (s0 sf : State) : SepProp :=
  ∃∗ st' : MallocngSt, ∃∗ idx : Nat,
    ⌜MallocngProcPreserved s0 sf ∧ st'.reservedMetas = st0.reservedMetas ∧
     st'.liveMap = st0.liveMap ∧ totalLiveEffCost st' = totalLiveEffCost st0 ∧
     totalLiveCount st' = totalLiveCount st0 ∧ st'.metaAreas.length ≤ maxMetaAreas ∧
     (∀ k : Nat, k < sc → ∀ hk1 : k < st'.ctx.active.length, ∀ hk0 : k < st0.ctx.active.length,
       st'.ctx.active[k]'hk1 = st0.ctx.active[k]'hk0) ∧
     sf.readReg32 .x0 = BitVec.ofNat 32 idx ∧ idx ≤ 31 ∧
     (∃ g ∈ st'.groups, ∃ hAct : sc < st'.ctx.active.length, ∃ hIdx : idx < g.slots.length,
       g.sc = sc ∧ req + 4 ≤ g.stride ∧ g.metaPtr = st'.ctx.active[sc]'hAct ∧ g.slots[idx]'hIdx = .claimed ∧
       (g.isMmapped = true → ∀ a : BitVec 64, InRegion (g.slotStart idx) g.stride a → st'.byteVal a = 0#8)) ∧
     AllocSlotFineTrace rootParamPred maddrs.base brkStart liveCost peakCost inflight sc req st0 st' idx ∧
     MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st') s0.mem sf.mem ∧
     MallocngMappedDelta (2 * (allocSlotDepthBound sc + 1)) (allocSlotFineByteBound sc maxMetaAreas) s0.mem sf.mem⌝ ∗
    stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) ∗
    MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp ∗
    MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st'

def AllocSlotAtDepthFineTraceStmt (rootParamPred : Nat → Nat → Nat → Prop) (sc : Nat) : Prop :=
  ∀ [MallocngMultiPlacement] (req inflight : Nat) (_hSc : sc < 48) (_hReq : req ≤ nominalSlotCap sc)
    (_hInflight : inflight + allocSlotDepthBound sc ≤ 6) (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost maxGroups maxMetaAreas : Nat) (st : MallocngSt)
    (_hGroups : st.groups.length ≤ maxGroups) (_hMeta0 : st.metaAreas.length ≤ maxMetaAreas)
    (_hMetaStep : 1 + (7 + maxGroups) / 101 ≤ maxMetaAreas),
    subroutine_ok (mallocngBlockProg mmpl 8 msvc) (mbase 8) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart ∧
         (s0.readReg32 .x0).toNat = sc ∧ (s0.readReg64 .x1).toNat = req⌝ ∗
        stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) ∗ MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightA inflight γ maddrs brkStart s0.brk liveCost peakCost st ∗ MallocngRuntime maddrs tp
      post := fun _ s0 sf =>
        AllocSlotFineTracePostProp rootParamPred sc req inflight γ tp brkStart liveCost peakCost maxMetaAreas st s0 sf
      onOom := fun _ s0 sf =>
        ⌜MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1)) (allocSlotFineByteBound sc maxMetaAreas) s0 sf⌝
    })

abbrev AllocSlotFineTracePostBody [MallocngMultiPlacement] (rootParamPred : Nat → Nat → Nat → Prop)
    (sc req inflight : Nat) (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost maxMetaAreas : Nat) (st0 : MallocngSt) (s0 sf : State) (P_f : SepProp) : Prop :=
  P_f ⊢ AllocSlotFineTracePostProp rootParamPred sc req inflight γ tp brkStart liveCost peakCost maxMetaAreas st0 s0 sf

abbrev AllocSlotFineTracePost [MallocngMultiPlacement] (rootParamPred : Nat → Nat → Nat → Prop)
    (sc req inflight : Nat) (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost maxMetaAreas : Nat) (st0 : MallocngSt) (s0 sf : State) (P_f : SepProp) : Prop :=
  AllocSlotFineTracePostBody rootParamPred sc req inflight γ tp brkStart liveCost peakCost maxMetaAreas st0 s0 sf P_f ∧
  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

def AllocGroupAtOffFineTraceStmt (rootParamPred : Nat → Nat → Nat → Prop) : Prop :=
  ∀ [MallocngMultiPlacement] (sc req inflight : Nat) (_hSc : sc < 48) (_hReq : req ≤ nominalSlotCap sc)
    (_hInflight : inflight + allocSlotDepthBound sc ≤ 6)
    (_hRec : ∀ pSc, pSc < 48 → allocSlotDepthBound pSc < allocSlotDepthBound sc →
      AllocSlotAtDepthFineTraceStmt rootParamPred pSc)
    (γ : GhostName) (tp brkStart : BitVec 64) (liveCost peakCost maxGroups maxMetaAreas : Nat) (st0 st : MallocngSt)
    (_hGroups0 : st0.groups.length ≤ maxGroups) (_hMeta0 : st0.metaAreas.length ≤ maxMetaAreas)
    (_hMetaStep : 1 + (7 + maxGroups) / 101 ≤ maxMetaAreas)
    (_hAct0 : ∀ h : sc < st.ctx.active.length, st.ctx.active[sc]'h = 0#64)
    (_hStRel : SameGroupsSlotKind st.groups st0.groups ∧ st.reservedMetas = st0.reservedMetas ∧
      st.liveMap = st0.liveMap ∧ totalLiveEffCost st = totalLiveEffCost st0 ∧ totalLiveCount st = totalLiveCount st0 ∧
      st.metaAreas = st0.metaAreas ∧ dynamicRootRegions st = dynamicRootRegions st0 ∧
      (∀ k : Nat, k < sc → ∀ hk1 : k < st.ctx.active.length, ∀ hk0 : k < st0.ctx.active.length,
        st.ctx.active[k]'hk1 = st0.ctx.active[k]'hk0))
    (s0 s : State) (_hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (_hpc : s.pc = mbase 8 + allocSlotOff_ag) (_hrun : s.status = .Running) (_hsp : s.sp = s0.sp - 96#64)
    (_hsAl : s.spAligned = true) (_htp : s0.tpidrEl0 = tp) (_hbrkS : s0.brkStart = brkStart)
    (_hpsp : PureStatePres s0 s) (_hperm : s.mem.perm = s0.mem.perm)
    (_hx22 : s.readReg64 .x22 = Obj.pageOf maddrs.ctx) (_hx23 : s.readReg64 .x23 = BitVec.ofNat 64 sc)
    (_hx21 : s.readReg64 .x21 = BitVec.ofNat 64 sc) (_hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req),
    SepWP (mallocngBlockProg mmpl 8 msvc) (s0.readReg64 .x30) s
      (AllocSlotSaved12 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x19) (s0.readReg64 .x20)
        (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25)
        (s0.readReg64 .x26) (s0.readReg64 .x27) (s0.readReg64 .x28) ∗
       stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗ MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗ MallocngRuntime maddrs tp)
      (AllocSlotFineTracePost rootParamPred sc req inflight γ tp brkStart liveCost peakCost maxMetaAreas st0 s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1)) (allocSlotFineByteBound sc maxMetaAreas) s0 sf⌝)

/-! ## Byte-Delta, OOM, and Count-Dispatch Combinators -/

theorem allocMetaFineByteBound_le_allocSlot (sc maxMetaAreas : Nat) :
    32768 * maxMetaAreas ≤ allocSlotFineByteBound sc maxMetaAreas := by
  unfold allocSlotFineByteBound
  have := Nat.mul_le_mul_right (5 * 1024 * 1024 + 32768 * maxMetaAreas) (by omega : 1 ≤ allocSlotDepthBound sc + 1)
  omega

theorem oom_from_allocMeta_fine {svc : State → State} {sc maxMetaAreas : Nat} {s0 s_call sf : State}
    (hProc : MallocngProcPreserved s0 s_call) (hperm : s_call.mem.perm = s0.mem.perm)
    (hoom : MallocngPlacedOomCond svc 1 (32768 * maxMetaAreas) s_call sf) :
    MallocngPlacedOomCond svc (2 * (allocSlotDepthBound sc + 1)) (allocSlotFineByteBound sc maxMetaAreas) s0 sf := by
  obtain ⟨hfs', htr', hsig', ivs, hivsL, hivsS, hcov, hgap⟩ := hoom
  have hb := allocMetaFineByteBound_le_allocSlot sc maxMetaAreas
  refine ⟨hfs'.trans hProc.1, htr'.trans hProc.2.1, hsig'.trans hProc.2.2.2.2.2.2,
    ivs, by omega, Nat.le_trans hivsS hb, fun a ha => ?_, fun hsan => ?_⟩
  · rw [← hperm]; exact hcov a ha
  · obtain ⟨sz, hlo, hmod, hhi, hng⟩ := hgap hsan
    exact ⟨sz, hlo, hmod, Nat.le_trans hhi hb, hng⟩

theorem oom_from_recAllocSlot_fine {svc : State → State} {sc p_sc maxMetaAreas : Nat} {s0 s_call sf : State}
    (hdepth : allocSlotDepthBound p_sc + 1 ≤ allocSlotDepthBound sc) (hProc : MallocngProcPreserved s0 s_call)
    (hd0 : MallocngMappedDelta 1 (32768 * maxMetaAreas) s0.mem s_call.mem)
    (hoom : MallocngPlacedOomCond svc (2 * (allocSlotDepthBound p_sc + 1))
      (allocSlotFineByteBound p_sc maxMetaAreas) s_call sf) :
    MallocngPlacedOomCond svc (2 * (allocSlotDepthBound sc + 1)) (allocSlotFineByteBound sc maxMetaAreas) s0 sf := by
  have hbSum : 32768 * maxMetaAreas + allocSlotFineByteBound p_sc maxMetaAreas ≤
      allocSlotFineByteBound sc maxMetaAreas := by
    unfold allocSlotFineByteBound
    calc 32768 * maxMetaAreas + (allocSlotDepthBound p_sc + 1) * (5 * 1024 * 1024 + 32768 * maxMetaAreas)
      _ ≤ (5 * 1024 * 1024 + 32768 * maxMetaAreas) +
          (allocSlotDepthBound p_sc + 1) * (5 * 1024 * 1024 + 32768 * maxMetaAreas) := by omega
      _ = (allocSlotDepthBound p_sc + 2) * (5 * 1024 * 1024 + 32768 * maxMetaAreas) := by
        rw [Nat.add_comm, ← Nat.add_one_mul]
      _ ≤ (allocSlotDepthBound sc + 1) * (5 * 1024 * 1024 + 32768 * maxMetaAreas) :=
        Nat.mul_le_mul_right _ (by omega)
  exact MallocngPlacedOomCond.mono (by omega) hbSum
    (MallocngPlacedOomCond.append_delta hProc.1 hProc.2.1 hProc.2.2.2.2.2.2 hd0 hoom)

theorem root_mappedDelta_combine_fine {sc maxMetaAreas len : Nat} {m0 m1 m2 m3 mf : Memory}
    (hd1 : MallocngMappedDelta 1 (32768 * maxMetaAreas) m0 m1) (hp12 : m2.perm = m1.perm)
    (hdMmap : MallocngMappedDelta 1 len m2 m3) (hp3f : mf.perm = m3.perm) (hlenHi : len ≤ 1048576) :
    MallocngMappedDelta (2 * (allocSlotDepthBound sc + 1)) (allocSlotFineByteBound sc maxMetaAreas) m0 mf := by
  have hsum : 32768 * maxMetaAreas + len ≤ allocSlotFineByteBound sc maxMetaAreas := by
    unfold allocSlotFineByteBound
    have := Nat.mul_le_mul_right (5 * 1024 * 1024 + 32768 * maxMetaAreas) (by omega : 1 ≤ allocSlotDepthBound sc + 1)
    omega
  exact MallocngMappedDelta.mono (by omega) hsum
    (MallocngMappedDelta.trans (mappedDelta_perm_right hd1 hp12) (mappedDelta_perm_right hdMmap hp3f))

theorem nested_mappedDelta_combine_fine {sc pSc maxMetaAreas : Nat} {m0 m1 m2 m3 mf : Memory}
    (hdepth : allocSlotDepthBound pSc + 1 ≤ allocSlotDepthBound sc)
    (hd1 : MallocngMappedDelta 1 (32768 * maxMetaAreas) m0 m1) (hp12 : m2.perm = m1.perm)
    (hdRec : MallocngMappedDelta (2 * (allocSlotDepthBound pSc + 1)) (allocSlotFineByteBound pSc maxMetaAreas) m2 m3)
    (hp3f : mf.perm = m3.perm) :
    MallocngMappedDelta (2 * (allocSlotDepthBound sc + 1)) (allocSlotFineByteBound sc maxMetaAreas) m0 mf := by
  have hsum : 32768 * maxMetaAreas + allocSlotFineByteBound pSc maxMetaAreas ≤
      allocSlotFineByteBound sc maxMetaAreas := by
    unfold allocSlotFineByteBound
    calc 32768 * maxMetaAreas + (allocSlotDepthBound pSc + 1) * (5 * 1024 * 1024 + 32768 * maxMetaAreas)
      _ ≤ (5 * 1024 * 1024 + 32768 * maxMetaAreas) +
          (allocSlotDepthBound pSc + 1) * (5 * 1024 * 1024 + 32768 * maxMetaAreas) := by omega
      _ = (allocSlotDepthBound pSc + 2) * (5 * 1024 * 1024 + 32768 * maxMetaAreas) := by
        rw [Nat.add_comm, ← Nat.add_one_mul]
      _ ≤ (allocSlotDepthBound sc + 1) * (5 * 1024 * 1024 + 32768 * maxMetaAreas) :=
        Nat.mul_le_mul_right _ (by omega)
  exact MallocngMappedDelta.mono (by omega) hsum
    (MallocngMappedDelta.trans (mappedDelta_perm_right hd1 hp12) (mappedDelta_perm_right hdRec hp3f))

theorem sepWP_extract_coreSt_wf {prog : Program} {exit_pc : BitVec 64} {s : State}
    {inflight : Nat} {γ : GhostName} {A : MallocngAddrs} {brkStart : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {Pre1 Pre2 : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : MallocngWFInflight inflight A.base brkStart s.brk liveCost peakCost st →
      SepWP prog exit_pc s (Pre1 ∗ MallocngCoreStInflightA inflight γ A brkStart s.brk liveCost peakCost st ∗ Pre2) post oom) :
    SepWP prog exit_pc s (Pre1 ∗ MallocngCoreStInflightA inflight γ A brkStart s.brk liveCost peakCost st ∗ Pre2) post oom := by
  have hSwap : (Pre1 ∗ MallocngCoreStInflightA inflight γ A brkStart s.brk liveCost peakCost st ∗ Pre2) =
      (MallocngCoreStInflightA inflight γ A brkStart s.brk liveCost peakCost st ∗ (Pre1 ∗ Pre2)) := by ac_rfl
  rw [hSwap]; conv => arg 4; simp only [MallocngCoreStInflightA, sepConj_assoc]
  apply SepWP.pure_elim; intro hwf; have hh := h hwf; rw [hSwap] at hh
  conv at hh => arg 4; simp only [MallocngCoreStInflightA, sepConj_assoc, pure_sepConj_of_true hwf]
  exact hh

private theorem wp_cnt_check_mem_fine [MallocngMultiPlacement]
    (target_pc : BitVec 64) (s : State) (sc cnt : Nat) (P : SepProp)
    {post : State → SepProp → Prop} {oom : State → SepProp} (_hw768 : Blk08HasWords768Msvc)
    (hsc : sc < 48) (hlo : 2 ≤ cnt) (hhi : cnt ≤ 32) (hprod : cnt * slotStride sc ≤ 1048575)
    (h25 : sc ≤ 25 → cnt * slotStride sc + 20 ≤ 65536)
    (hsm : sc ≤ 8 → ∃ j, j < 3 ∧ cnt = (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat)
    (hpc : s.pc = mbase 8 + allocSlotOff_cnt_check) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt) (hx28 : s.readReg64 .x28 = BitVec.ofNat 64 cnt)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc)) (hx1 : s.readReg64 .x1 = 2048#64)
    (hNested : ∀ sn : State, sn.pc = mbase 8 + allocSlotOff_nested → sn.status = .Running → sn.mem = s.mem →
      sn.sp = s.sp → sn.spAligned = s.spAligned → PureStatePres s sn → ValidNestedCnt sc cnt →
      sn.readReg64 .x0 = BitVec.ofNat 64 (cnt * slotStride sc) → sn.readReg64 .x20 = BitVec.ofNat 64 cnt →
      sn.readReg64 .x28 = BitVec.ofNat 64 cnt → (∀ r, r ≠ .x0 → r ≠ .x3 → sn.readReg64 r = s.readReg64 r) →
      SepWP (mallocngBlockProg mmpl 8 msvc) target_pc sn P post oom)
    (hRoot : ∀ sr : State, sr.pc = mbase 8 + allocSlotOff_root → sr.status = .Running → sr.mem = s.mem →
      sr.sp = s.sp → sr.spAligned = s.spAligned → PureStatePres s sr → 2048 < cnt * slotStride sc + 16 →
      cnt * slotStride sc ≤ 1048575 → (sc ≤ 25 → cnt * slotStride sc + 20 ≤ 65536) →
      sr.readReg64 .x0 = BitVec.ofNat 64 (cnt * slotStride sc) → sr.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt) →
      sr.readReg64 .x20 = BitVec.ofNat 64 cnt → sr.readReg64 .x28 = BitVec.ofNat 64 cnt →
      (∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x6 → sr.readReg64 r = s.readReg64 r) →
      SepWP (mallocngBlockProg mmpl 8 msvc) target_pc sr P post oom) :
    SepWP (mallocngBlockProg mmpl 8 msvc) target_pc s P post oom := by
  dsimp only [allocSlotOff_cnt_check] at hpc
  have ⟨_, hshi⟩ := slotStride_bounds_48 hsc; have hbd : cnt * slotStride sc ≤ 32 * 131056 := Nat.mul_le_mul hhi hshi
  have hmul_eq : BitVec.ofNat 64 (slotStride sc) * BitVec.ofNat 64 cnt = BitVec.ofNat 64 (cnt * slotStride sc) := by
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  wp_sym_steps; wp_if hls
  · have hle2048 : cnt * slotStride sc + 16 ≤ 2048 := by
      rw [BitVec.ule, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hls
      change ((cnt * slotStride sc) % (2 ^ 64) + 16) % (2 ^ 64) ≤ 2048 at hls
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hls; exact hls
    have hvnc : ValidNestedCnt sc cnt := ⟨hlo, hhi, hle2048, fun h8 => by
      obtain ⟨j, hj, rfl⟩ := hsm h8; rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> simp⟩
    exact hNested _ rfl (by simp [hrun]) rfl (by simp) (by simp [State.spAligned]) psp_rfl hvnc
      (by simp) (by simpa using hx20) (by simpa using hx28) fun r h0 h3 => by
        simp only [State.readReg64_setPC, State.readReg64_setPState,
          State.readReg64_writeReg64_ne _ _ _ _ h3, State.readReg64_writeReg64_ne _ _ _ _ h0]
  · have hgt2048 : 2048 < cnt * slotStride sc + 16 := by
      rw [BitVec.ule, decide_eq_true_eq, BitVec.toNat_add, BitVec.toNat_ofNat] at hls
      change ¬ (((cnt * slotStride sc) % (2 ^ 64) + 16) % (2 ^ 64) ≤ 2048) at hls
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hls; omega
    refine SepWP.join_same (pc_join := mbase 8 + allocSlotOff_root)
      (fun sr => sr.mem = s.mem ∧ sr.sp = s.sp ∧ sr.spAligned = s.spAligned ∧ PureStatePres s sr ∧
        sr.readReg64 .x0 = BitVec.ofNat 64 (cnt * slotStride sc) ∧ sr.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt) ∧
        sr.readReg64 .x20 = BitVec.ofNat 64 cnt ∧ sr.readReg64 .x28 = BitVec.ofNat 64 cnt ∧
        ∀ r, r ≠ .x0 → r ≠ .x3 → r ≠ .x6 → sr.readReg64 r = s.readReg64 r) ?_
      (fun sr hpcr hrunr ⟨hm, hs, ha, hp, h0, h6, h20, h28, hr⟩ =>
        hRoot sr hpcr hrunr hm hs ha hp hgt2048 hprod h25 h0 h6 h20 h28 hr)
    dsimp only [allocSlotOff_root]; wp_sym_steps
    have hb29 : (BitVec.ofNat 32 cnt)[29] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact Nat.testBit_lt_two_pow (by omega)
    refine SepWP.done rfl (by simp [hrun]) ⟨⟨rfl, by simp, by simp [State.spAligned], psp_rfl,
      by simp, ?_, by simpa using hx20, by simpa using hx28, fun r h0 h3 h6 => by
        simp only [State.readReg64_setPC, State.readReg64_setPState, State.readReg64_writeReg64_ne _ _ _ _ h6,
          State.readReg64_writeReg64_ne _ _ _ _ h3, State.readReg64_writeReg64_ne _ _ _ _ h0]⟩, by sep_entail⟩
    simp [hb29]
    have h1 : BitVec.setWidth 64 (BitVec.ofNat 32 cnt <<< 2) = BitVec.ofNat 64 (4 * cnt) := by bv_omega
    have h2 : (BitVec.ofNat 64 (4 * cnt)).ult 133#64 = true := by
      rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
      change (4 * cnt) % (2 ^ 64) < 133; rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [h1]; revert h2; bv_robdd

theorem wp_cnt_dispatch_mem_fine [MallocngMultiPlacement]
    (target_pc : BitVec 64) (s : State) (sc cnt : Nat) (P : SepProp)
    {post : State → SepProp → Prop} {oom : State → SepProp} (hw768 : Blk08HasWords768Msvc)
    (hsc : sc < 48) (hlo : 1 ≤ cnt) (hhi : cnt ≤ 32) (hprod : cnt * slotStride sc ≤ 1048575)
    (h25 : sc ≤ 25 → cnt * slotStride sc + 20 ≤ 65536)
    (hsm : sc ≤ 8 → ∃ j, j < 3 ∧ cnt = (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat)
    (hc1 : cnt = 1 → 9 ≤ sc) (hpc : s.pc = mbase 8 + allocSlotOff_cnt_join) (hrun : s.status = .Running)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 cnt)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 (slotStride sc)) (hx4 : s.readReg64 .x4 = 4096#64)
    (hNested : ∀ (cnt' : Nat) (sn : State),
      sn.pc = mbase 8 + allocSlotOff_nested → sn.status = .Running → sn.mem = s.mem → sn.sp = s.sp →
      sn.spAligned = s.spAligned → PureStatePres s sn → ValidNestedCnt sc cnt' →
      sn.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc) → sn.readReg64 .x20 = BitVec.ofNat 64 cnt' →
      sn.readReg64 .x28 = BitVec.ofNat 64 cnt' →
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x20 → r ≠ .x28 → sn.readReg64 r = s.readReg64 r) →
      SepWP (mallocngBlockProg mmpl 8 msvc) target_pc sn P post oom)
    (hRoot : ∀ (cnt' : Nat) (sr : State),
      sr.pc = mbase 8 + allocSlotOff_root → sr.status = .Running → sr.mem = s.mem → sr.sp = s.sp →
      sr.spAligned = s.spAligned → PureStatePres s sr → cnt' = Cost.cntBump sc cnt → 1 ≤ cnt' → cnt' ≤ 32 →
      2048 < cnt' * slotStride sc + 16 → cnt' * slotStride sc ≤ 1048575 →
      (sc ≤ 25 → cnt' * slotStride sc + 20 ≤ 65536) →
      (sc ≤ 8 → ∃ j, j < 3 ∧ cnt' = (smallCntTabBytes.getD (3 * sc + j) 0#8).toNat) →
      sr.readReg64 .x0 = BitVec.ofNat 64 (cnt' * slotStride sc) → sr.readReg64 .x6 = BitVec.ofNat 64 (4 * cnt') →
      sr.readReg64 .x20 = BitVec.ofNat 64 cnt' → sr.readReg64 .x28 = BitVec.ofNat 64 cnt' →
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x6 → r ≠ .x20 → r ≠ .x28 → sr.readReg64 r = s.readReg64 r) →
      SepWP (mallocngBlockProg mmpl 8 msvc) target_pc sr P post oom) :
    SepWP (mallocngBlockProg mmpl 8 msvc) target_pc s P post oom := by
  have hStepGe2 : SepWP (mallocngBlockProg mmpl 8 msvc) target_pc s (⌜2 ≤ cnt⌝ ∗ P) post oom := by
    dsimp only [allocSlotOff_cnt_join] at hpc; wp_sym_steps; wp_if heq1
    · apply SepWP.pure_elim; intro hge2
      have hw : BitVec.setWidth 32 (BitVec.ofNat 64 cnt) = BitVec.ofNat 32 cnt := by bv_omega
      have ht := congrArg BitVec.toNat (hw ▸ heq1); simp only [BitVec.toNat_ofNat] at ht
      rw [Nat.mod_eq_of_lt (by omega)] at ht; omega
    · apply SepWP.pure_elim; intro hge2
      have hb31 : (BitVec.ofNat 64 cnt)[31] = false := by
        rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact Nat.testBit_lt_two_pow (by omega)
      have hand32 : BitVec.ofNat 64 cnt &&& 4294967295#64 = BitVec.ofNat 64 cnt := by
        have hlt : (BitVec.ofNat 64 cnt).ult 33#64 = true := by
          rw [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat]
          change cnt % (2 ^ 64) < 33; rw [Nat.mod_eq_of_lt (by omega)]; omega
        revert hlt; bv_robdd
      exact wp_cnt_check_mem_fine target_pc _ sc cnt P hw768 hsc hge2 hhi hprod h25 hsm rfl (by simp [hrun])
        (by simpa using hx20) (by simp [hb31]; exact hand32) (by simpa using hx24) (by simp)
        (fun sn hp hr hm hs ha hp2 hv h0 h20 h28 hrg => hNested cnt sn hp hr hm
          (hs.trans (by simp)) (ha.trans (by simp [State.spAligned])) (PureStatePres.trans psp_rfl hp2)
          hv h0 h20 h28 fun r r0 r1 r3 _ r28 => (hrg r r0 r3).trans (by
            simp only [State.readReg64_setPC, State.readReg64_setPState,
              State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r28]))
        (fun sr hp hr hm hs ha hp2 hgt hpr h25' h0 h6 h20 h28 hrg => hRoot cnt sr hp hr hm
          (hs.trans (by simp)) (ha.trans (by simp [State.spAligned])) (PureStatePres.trans psp_rfl hp2)
          (by simp only [Cost.cntBump]; split <;> omega) (by omega) hhi hgt hpr h25' hsm h0 h6 h20 h28
          fun r r0 r1 r3 r6 _ r28 => (hrg r r0 r3 r6).trans (by
            simp only [State.readReg64_setPC, State.readReg64_setPState,
              State.readReg64_writeReg64_ne _ _ _ _ r1, State.readReg64_writeReg64_ne _ _ _ _ r28]))
  by_cases hc : cnt = 1
  · have hsc9 : 9 ≤ sc := hc1 hc
    exact wp_cnt_dispatch_mem target_pc s sc cnt P hw768 hsc hlo hhi hprod h25 hsm hc1 hpc hrun hx20 hx24 hx4 hNested
      (fun cnt' sr hp hr hm hs ha hp2 hbump hlo' hhi' hgt' hpr' h25' =>
        hRoot cnt' sr hp hr hm hs ha hp2 hbump hlo' hhi' hgt' hpr' h25' (fun h8 => absurd h8 (by omega)))
  · exact SepWP.weaken_pre (Entails.of_eq (pure_sepConj_of_true (P := P) (by omega : 2 ≤ cnt)).symm) hStepGe2

end LibsignalBinary.Heap.Fine
