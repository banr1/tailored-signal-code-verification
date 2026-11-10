/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupProof
import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotStage2

/-!
# Placed Outer `alloc_slot` Proof

Composes the `blk08` stage symbolic execution lemmas with placed `alloc_group` by bounded recursion
on `allocSlotDepthBound sc <= 3` to prove `placed_allocSlot_full_ok` and `placed_allocSlot_ok`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

arm64_proof_prelude

/-! ## Stack Frame Opening, Active Head Lookup, and Exit Glue -/

private theorem setWidth32_zeroExtend64 (w : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 w) = w := by
  bv_robdd

private theorem pointsToWords64_12_eq_slotSaved
    (sp0 : BitVec 64) (ws : List (BitVec 64)) (hLen : ws.length = 12) :
    ∃ u29 u30 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 : BitVec 64,
      ((sp0 - BitVec.ofNat 64 (8 * 12)) ↦₆₄* ws) =
        (SlotSaved8 sp0 u29 u30 u21 u22 u23 u24 u25 u26 ∗
         SlotSaved4 sp0 u19 u20 u27 u28) := by
  rcases ws with _ | ⟨u29, _ | ⟨u30, _ | ⟨u19, _ | ⟨u20, _ | ⟨u21, _ | ⟨u22,
    _ | ⟨u23, _ | ⟨u24, _ | ⟨u25, _ | ⟨u26, _ | ⟨u27, _ | ⟨u28, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try simp at hLen
  refine ⟨u29, u30, u19, u20, u21, u22, u23, u24, u25, u26, u27, u28, ?_⟩
  rw [sepConj_comm (SlotSaved8 _ _ _ _ _ _ _ _ _), ← slotSaved12_eq_8_4]
  simp only [SlotSaved12, pointsToWords64_cons, pointsToWords64_nil, sepConj_emp]
  have h1 : sp0 - 96#64 + 8#64 = sp0 - 88#64 := by bv_omega
  have h2 : sp0 - 88#64 + 8#64 = sp0 - 80#64 := by bv_omega
  have h3 : sp0 - 80#64 + 8#64 = sp0 - 72#64 := by bv_omega
  have h4 : sp0 - 72#64 + 8#64 = sp0 - 64#64 := by bv_omega
  have h5 : sp0 - 64#64 + 8#64 = sp0 - 56#64 := by bv_omega
  have h6 : sp0 - 56#64 + 8#64 = sp0 - 48#64 := by bv_omega
  have h7 : sp0 - 48#64 + 8#64 = sp0 - 40#64 := by bv_omega
  have h8 : sp0 - 40#64 + 8#64 = sp0 - 32#64 := by bv_omega
  have h9 : sp0 - 32#64 + 8#64 = sp0 - 24#64 := by bv_omega
  have h10 : sp0 - 24#64 + 8#64 = sp0 - 16#64 := by bv_omega
  have h11 : sp0 - 16#64 + 8#64 = sp0 - 8#64 := by bv_omega
  have h96 : BitVec.ofNat 64 (8 * 12) = 96#64 := rfl
  rw [h96, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

private theorem stackFrame_open_allocSlot (s0 : State) (sc : Nat) :
    stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) =
      (∃∗ ws : List (BitVec 64), ⌜ws.length = 12⌝ ∗
        ((s0.sp - BitVec.ofNat 64 (8 * 12)) ↦₆₄* ws) ∗
        stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224)) := by
  have hd : allocSlotDepthBound sc ≤ 3 := by
    unfold allocSlotDepthBound; repeat (first | split | omega)
  unfold stackFrame
  rw [← solver_stackFrameAt_eq_memRegion s0.sp ((allocSlotDepthBound sc + 1) * 96 + 224) (by omega),
      stackFrameAt_split_top s0.sp 96 ((allocSlotDepthBound sc + 1) * 96 + 224) (by omega) (by omega),
      show (allocSlotDepthBound sc + 1) * 96 + 224 - 96 = allocSlotDepthBound sc * 96 + 224 by omega,
      show (96 : Nat) = 8 * 12 from rfl,
      stackFrameAt_eq_exists_pointsToWords64 s0.sp 12]
  simp only [sepExists_sepConj_left, sepConj_assoc]

private theorem allocSlot_head_group_of_nonzero {inflight sc : Nat}
    {base brkStart brk : BitVec 64} {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    (hsc : sc < 48) {h1 : sc < st.ctx.active.length} (hNe0 : st.ctx.active[sc]'h1 ≠ 0#64) :
    ∃ g ∈ st.groups, g.sc = sc ∧
      ∀ h1' : sc < st.ctx.active.length, st.ctx.active[sc]'h1' = g.metaPtr := by
  have h2 : sc < st.activeLists.length := hwf.ctx_lens.2.2.2.2.2 ▸ hsc
  have hAct : ActiveClassWf st sc (st.ctx.active[sc]'h1) (st.activeLists[sc]'h2) :=
    hwf.active_wf sc h1 h2
  cases hMs : st.activeLists[sc]'h2 with
  | nil =>
    have h0 : st.ctx.active[sc]'h1 = 0#64 := by simpa [hMs, CircularDllWf] using hAct.2.1
    exact False.elim (hNe0 h0)
  | cons m0 tl =>
    obtain ⟨g, hg, rfl, hgSc⟩ := hAct.1 m0 (hMs ▸ List.mem_cons_self ..)
    have hF0 := slot_findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hg
    have hDll0 := hAct.2.1
    rw [hMs] at hDll0
    simp only [List.filterMap_cons, hF0, Option.map_some, CircularDllWf] at hDll0
    exact ⟨g, hg, hgSc, fun _ => hDll0.1⟩

private theorem fastPop_finish_post [MallocngMultiPlacement]
    (hw348 : Blk08HasWords348 mallocngFaultSvc) (hr348 : Blk08Range348)
    (hw564 : Blk08HasWords564 mallocngFaultSvc) (hr564 : Blk08Range564)
    {sc req inflight : Nat} (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc)
    {γ : GhostName} {tp brkStart v19 v20 v27 v28 : BitVec 64}
    {liveCost peakCost peakCount : Nat}
    {st0 st : MallocngSt} {g : GroupDesc}
    (hg : g ∈ st.groups) (hScEq : g.sc = sc)
    (hHead : ∀ h1 : sc < st.ctx.active.length, st.ctx.active[sc]'h1 = g.metaPtr)
    (hAvNe : g.availMask ≠ 0#32) (hPres : AllocSlotStPres sc st0 st)
    (s0 s : State)
    (hpc : s.pc = mbase 8 + allocSlotOff_fast_pop) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hsAl : s.spAligned = true)
    (hpsp : PureStatePres s0 s) (hperm : s.mem.perm = s0.mem.perm)
    (hw0 : s.readReg32 .x0 = g.availMask) (hx2 : s.readReg64 .x2 = g.metaPtr)
    (hx19 : s.readReg64 .x19 = s0.readReg64 .x19) (hx20 : s.readReg64 .x20 = s0.readReg64 .x20)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27) (hx28 : s.readReg64 .x28 = s0.readReg64 .x28) :
    SepWP (mallocngBlockProg mmpl 8 msvc) (s0.readReg64 .x30) s
      (SlotSaved8 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
        (s0.readReg64 .x25) (s0.readReg64 .x26) ∗
       MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
       (SlotSaved4 s0.sp v19 v20 v27 v28 ∗
        stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗
        MallocngRuntime maddrs tp))
      (AllocSlotFullPost sc req inflight γ tp brkStart liveCost peakCost peakCount st0 s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1))
                   (allocSlotPlacedByteBound sc peakCount) s0 sf⌝) := by
  apply sepWP_of_noSyscalls_block
  refine SepWP.mono
    (wp_allocSlot_fast_pop_ret hw348 hr348 hw564 hr564 hsc hReq hg hScEq hHead hAvNe s _
      hpc hrun hsp hsAl hw0 hx2) ?_
  rintro sf P_f _ _ ⟨st1, idx, _, hsp_f, _, hpsp_f, hRes1, hLive1, hEff1, hCnt1, hMa1, hDyn1,
    hAct1, hGM1, hx0_f, hIdxLe, hGrpEx, h19f, h20f, h21f, h22f, h23f, h24f, h25f, h26f, h27f, h28f,
    h29f, _, hPf⟩ hperm_f
  have hpsp0 : PureStatePres s0 sf := hpsp.trans hpsp_f
  have hperm0 : sf.mem.perm = s0.mem.perm := hperm_f.trans hperm
  refine ⟨?_, hsp_f, calleeSaved_of_epilogue (h19f.trans hx19) (h20f.trans hx20)
    h21f h22f h23f h24f h25f h26f (h27f.trans hx27) (h28f.trans hx28) h29f hpsp0.2.2⟩
  subst hPf
  refine Entails.trans ?_ (Entails.sepExists_intro st1)
  refine Entails.trans ?_ (Entails.sepExists_intro idx)
  have hPure :
      MallocngProcPreserved s0 sf ∧ st1.reservedMetas = st0.reservedMetas ∧
      st1.liveMap = st0.liveMap ∧ totalLiveEffCost st1 = totalLiveEffCost st0 ∧
      totalLiveCount st1 = totalLiveCount st0 ∧
      st1.metaAreas.length ≤ max st0.metaAreas.length (1 + (88 + 8 * peakCount) / 101) ∧
      (∀ k : Nat, k < sc → ∀ hk1 : k < st1.ctx.active.length, ∀ hk0 : k < st0.ctx.active.length,
        st1.ctx.active[k]'hk1 = st0.ctx.active[k]'hk0) ∧
      sf.readReg32 .x0 = BitVec.ofNat 32 idx ∧ idx ≤ 31 ∧
      (∃ g' ∈ st1.groups, ∃ hAct : sc < st1.ctx.active.length, ∃ hIdx : idx < g'.slots.length,
        g'.sc = sc ∧ req + 4 ≤ g'.stride ∧ g'.metaPtr = st1.ctx.active[sc]'hAct ∧
        g'.slots[idx]'hIdx = .claimed ∧
        (g'.isMmapped = true → ∀ a : BitVec 64, InRegion (g'.slotStart idx) g'.stride a → st1.byteVal a = 0#8)) ∧
      MallocngNoOrphanMappings (dynamicRootRegions st0) (dynamicRootRegions st1) s0.mem sf.mem ∧
      MallocngMappedDelta (2 * (allocSlotDepthBound sc + 1)) (allocSlotPlacedByteBound sc peakCount) s0.mem sf.mem ∧
      (totalClaimedSlots st0 = 0 → ∀ U : Nat, peakCount ≤ U →
        Cost.GroupsGrpBound U st0.groups → Cost.GroupsGrpBound U st1.groups) := by
    refine ⟨hpsp0.1, hRes1.trans hPres.1, hLive1.trans hPres.2.1, hEff1.trans hPres.2.2.1,
      hCnt1.trans hPres.2.2.2.1,
      by rw [hMa1, hPres.2.2.2.2.1]; exact Nat.le_max_left _ _,
      fun k hk hk1 hk0 => ?_, hx0_f, hIdxLe, hGrpEx,
      mallocngNoOrphanMappings_of_perm_eq (hDyn1.trans hPres.2.2.2.2.2.1) hperm0,
      mappedDelta_of_perm_eq hperm0,
      fun _ U _ hU => hGM1 U (hPres.2.2.2.2.2.2.2.2 U hU)⟩
    have hk_st : k < st.ctx.active.length := hAct1 ▸ hk1
    simpa [hAct1] using hPres.2.2.2.2.2.2.2.1 k hk hk_st hk0
  rw [pure_sepConj_of_true hPure]
  have hJoin := saved12_rejoin_stackFrame s0 sc
    (s0.readReg64 .x29) (s0.readReg64 .x30) v19 v20
    (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
    (s0.readReg64 .x25) (s0.readReg64 .x26) v27 v28
  have hS12 :
      (SlotSaved8 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
        (s0.readReg64 .x25) (s0.readReg64 .x26) ∗
       SlotSaved4 s0.sp v19 v20 v27 v28) =
      AllocSlotSaved12 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        v19 v20 (s0.readReg64 .x21) (s0.readReg64 .x22)
        (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
        v27 v28 := by
    rw [sepConj_comm (SlotSaved8 _ _ _ _ _ _ _ _ _), ← slotSaved12_eq_8_4]; rfl
  refine Entails.trans (Entails.of_eq ?_) (sepConj_mono_left hJoin)
  rw [← hS12]
  generalize SlotSaved8 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
    (s0.readReg64 .x25) (s0.readReg64 .x26) = S8
  generalize SlotSaved4 s0.sp v19 v20 v27 v28 = S4
  generalize stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) = ST
  generalize MallocngRoTablesA maddrs = RO
  generalize MallocngRuntime maddrs tp = RT
  generalize MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st1 = CS1
  ac_rfl

private theorem ag_finish_post [MallocngMultiPlacement]
    (hMeta : AllocMetaPlacedFullStmt)
    {sc req inflight : Nat} (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc)
    (hInflight : inflight + allocSlotDepthBound sc ≤ 6)
    (hRec : ∀ pSc, pSc < 48 → allocSlotDepthBound pSc < allocSlotDepthBound sc →
      AllocSlotAtDepthFullStmt pSc)
    {γ : GhostName} {tp brkStart : BitVec 64} {liveCost peakCost peakCount : Nat}
    {st0 st : MallocngSt} (hCount0 : totalLiveCount st0 ≤ peakCount)
    (hPres : AllocSlotStPres sc st0 st)
    (hClaimRel : totalClaimedSlots st0 = 0 → totalClaimedSlots st = 0)
    (hAct0 : ∀ h : sc < st.ctx.active.length, st.ctx.active[sc]'h = 0#64)
    (s0 s : State) (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hpc : s.pc = mbase 8 + allocSlotOff_ag) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 96#64) (hsAl : s.spAligned = true)
    (htp : s0.tpidrEl0 = tp) (hbrkS : s0.brkStart = brkStart)
    (hpsp : PureStatePres s0 s) (hperm : s.mem.perm = s0.mem.perm)
    (hx22 : s.readReg64 .x22 = Obj.pageOf maddrs.ctx)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 sc)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 sc)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 req) :
    SepWP (mallocngBlockProg mmpl 8 msvc) (s0.readReg64 .x30) s
      (SlotSaved4 s0.sp (s0.readReg64 .x19) (s0.readReg64 .x20)
        (s0.readReg64 .x27) (s0.readReg64 .x28) ∗
       MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
       (SlotSaved8 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
          (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
          (s0.readReg64 .x25) (s0.readReg64 .x26) ∗
        stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) ∗
        MallocngRoTablesA maddrs ∗
        MallocngRuntime maddrs tp))
      (AllocSlotFullPost sc req inflight γ tp brkStart liveCost peakCost peakCount st0 s0)
      (fun sf => ⌜MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1))
                   (allocSlotPlacedByteBound sc peakCount) s0 sf⌝) := by
  have hS12 :
      (SlotSaved8 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
        (s0.readReg64 .x25) (s0.readReg64 .x26) ∗
       SlotSaved4 s0.sp (s0.readReg64 .x19) (s0.readReg64 .x20)
        (s0.readReg64 .x27) (s0.readReg64 .x28)) =
      AllocSlotSaved12 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
        (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
        (s0.readReg64 .x27) (s0.readReg64 .x28) := by
    rw [sepConj_comm (SlotSaved8 _ _ _ _ _ _ _ _ _), ← slotSaved12_eq_8_4]; rfl
  refine SepWP.weaken_pre (Entails.of_eq ?_)
    (wp_placed_allocGroup hMeta sc req inflight hsc hReq hInflight hRec γ tp brkStart
      liveCost peakCost peakCount st0 st (hPres.2.2.2.1.symm ▸ hCount0) hAct0
      ⟨hPres.1, hPres.2.1, hPres.2.2.1, hPres.2.2.2.1, hPres.2.2.2.2.1, hPres.2.2.2.2.2.1,
       hPres.2.2.2.2.2.2.2.1, hPres.2.2.2.2.2.2.2.2, hClaimRel⟩
      s0 s hcl hpc hrun hsp hsAl htp hbrkS hpsp hperm hx22 hx23 hx21 hx25)
  rw [← hS12]
  generalize SlotSaved8 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
    (s0.readReg64 .x25) (s0.readReg64 .x26) = S8
  generalize SlotSaved4 s0.sp (s0.readReg64 .x19) (s0.readReg64 .x20)
    (s0.readReg64 .x27) (s0.readReg64 .x28) = S4
  generalize stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) = ST
  generalize MallocngRoTablesA maddrs = RO
  generalize MallocngRuntime maddrs tp = RT
  generalize MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st = CS
  ac_rfl

/-! ## Slow-Path `mallocngFaultSvc` Chain -/

private theorem wp_allocSlot_slow_chain_to_208 [MallocngMultiPlacement]
    (hw0 : Blk08HasWords0 mallocngFaultSvc) (hr0 : Blk08Range0)
    (hw348 : Blk08HasWords348 mallocngFaultSvc) (hr348 : Blk08Range348)
    (hw564 : Blk08HasWords564 mallocngFaultSvc) (hr564 : Blk08Range564)
    {inflight sc : Nat} (hsc : sc < 48) {γ : GhostName}
    {sp0 u19 u20 u27 u28 brkStart : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt} {g : GroupDesc}
    (hg : g ∈ st.groups) (hScEq : g.sc = sc)
    (hHead : ∀ h1 : sc < st.ctx.active.length, st.ctx.active[sc]'h1 = g.metaPtr)
    (hAv0 : g.availMask = 0#32) (hSlow : g.freedMask ≠ 0#32 ∨ g.next ≠ g.metaPtr)
    (s : State) (Rest : SepProp)
    (hpc : s.pc = mbase 8 + allocSlotOff_030) (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64) (hsAl : s.spAligned = true)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 sc + 10#64)
    (hx2 : s.readReg64 .x2 = g.metaPtr)
    (hx3 : s.readReg64 .x3 = maddrs.ctx)
    (hx22 : s.readReg64 .x22 = Obj.pageOf maddrs.ctx)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 sc) :
    SepWP ((mallocngBlockProg mmpl 8 msvc).withSvc mallocngFaultSvc)
      (mbase 8 + allocSlotOff_fast_pop) s
      (SlotSaved4 sp0 u19 u20 u27 u28 ∗
       MallocngCoreStInflightA inflight γ maddrs brkStart s.brk liveCost peakCost st ∗
       (MallocngRoTablesA maddrs ∗ Rest))
      (fun sf P_f =>
        ∃ st_f : MallocngSt, ∃ g_f ∈ st_f.groups,
          sf.status = .Running ∧ sf.sp = sp0 - 96#64 ∧ sf.spAligned = true ∧
          PureStatePres s sf ∧
          AllocSlotStPres sc st st_f ∧
          g_f.sc = sc ∧ g_f.availMask ≠ 0#32 ∧
          (∀ h1' : sc < st_f.ctx.active.length, st_f.ctx.active[sc]'h1' = g_f.metaPtr) ∧
          sf.readReg32 .x0 = g_f.availMask ∧ sf.readReg64 .x2 = g_f.metaPtr ∧
          sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
          sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
          P_f = (SlotSaved4 sp0 (s.readReg64 .x19) (s.readReg64 .x20)
            (s.readReg64 .x27) (s.readReg64 .x28) ∗
            MallocngCoreStInflightA inflight γ maddrs brkStart sf.brk liveCost peakCost st_f ∗
            (MallocngRoTablesA maddrs ∗ Rest)))
      (fun _ => ⌜False⌝) := by
  let S4 := SlotSaved4 sp0 (s.readReg64 .x19) (s.readReg64 .x20)
    (s.readReg64 .x27) (s.readReg64 .x28)
  refine SepWP.seq
    (wp_allocSlot_030_slow_to_a8 hw0 hr0 hsc hg hScEq hHead hAv0 hSlow s
      (MallocngRoTablesA maddrs ∗ Rest) hpc hrun hsp hsAl hx1 hx2 hx3 hx22 hx23) ?_
  rintro s2 P2 hpc2 hrun2 ⟨st2, g2, hg2, _, hsp2, hal2, hpsp2, hPres2, hg2Sc, hg2Av0, hg2FrNe,
    hHead2, hs2_x2, hr2, rfl⟩
  have hs2_22 : s2.readReg64 .x22 = Obj.pageOf maddrs.ctx :=
    (hr2 .x22 (by decide) (by decide) (by decide) (by decide)).trans hx22
  have hs2_23 : s2.readReg64 .x23 = BitVec.ofNat 64 sc :=
    (hr2 .x23 (by decide) (by decide) (by decide) (by decide)).trans hx23
  have hSwap2 :
      (S4 ∗ MallocngCoreStInflightA inflight γ maddrs brkStart s2.brk liveCost peakCost st2 ∗
        (MallocngRoTablesA maddrs ∗ Rest)) =
      (MallocngCoreStInflightA inflight γ maddrs brkStart s2.brk liveCost peakCost st2 ∗
        (MallocngRoTablesA maddrs ∗ (S4 ∗ Rest))) := by
    dsimp only [S4]
    generalize SlotSaved4 sp0 (s.readReg64 .x19) (s.readReg64 .x20)
      (s.readReg64 .x27) (s.readReg64 .x28) = A
    generalize MallocngCoreStInflightA inflight γ maddrs brkStart s2.brk liveCost peakCost st2 = B
    generalize MallocngRoTablesA maddrs = C
    ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hSwap2) ?_
  refine SepWP.seq
    (wp_allocSlot_a8_to_c8 hw0 hr0 hsc hg2 hg2Sc hHead2 hg2Av0 hg2FrNe s2
      (MallocngRoTablesA maddrs ∗ (S4 ∗ Rest)) hpc2 hrun2 hs2_x2 hs2_22 hs2_23) ?_
  rintro s3 P3 hpc3 hrun3 ⟨st3, g3, hg3, _, hsp3, hal3, hpsp3, hPres3, hg3Sc, hg3Av0, hg3FrNe,
    hHead3, hs3_x2, hs3_w4, hr3, rfl⟩
  have hs3_22 : s3.readReg64 .x22 = Obj.pageOf maddrs.ctx :=
    (hr3 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs2_22
  have hs3_23 : s3.readReg64 .x23 = BitVec.ofNat 64 sc :=
    (hr3 .x23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs2_23
  refine SepWP.seq
    (wp_allocSlot_c8_to_activate hw0 hr0 hw348 hr348 hsc hg3 hg3Sc hHead3 hg3Av0 hg3FrNe s3
      (S4 ∗ Rest) hpc3 hrun3 hs3_x2 hs3_w4 hs3_22 hs3_23) ?_
  rintro s4 P4 hpc4 hrun4 ⟨st4, g4, hg4, _, hsp4, hal4, hpsp4, hPres4, hg4Sc, hg4Av0,
    hg4ActFrNe, hHead4, hs4_x2, hs4_22, _, rfl⟩
  refine SepWP.seq
    (wp_allocSlot_activate hw0 hr0 hw348 hr348 hsc hg4 hg4Sc hHead4 hg4Av0 hg4ActFrNe s4
      (MallocngRoTablesA maddrs ∗ (S4 ∗ Rest)) hpc4 hrun4 hs4_x2) ?_
  rintro s5 P5 hpc5 hrun5 ⟨st5, g5, hg5, _, hsp5, hal5, hpsp5, hPres5, _, hg5Sc, hg5AvNe,
    hHead5, hs5_x2, hs5_x0, hr5, rfl⟩
  have hs5_22 : s5.readReg64 .x22 = Obj.pageOf maddrs.ctx :=
    (hr5 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs4_22
  have hsp5_0 : s5.sp = sp0 - 96#64 := hsp5.trans (hsp4.trans (hsp3.trans hsp2))
  have hal5_0 : s5.spAligned = true := hal5.trans (hal4.trans (hal3.trans hal2))
  have hSwap5 :
      (MallocngCoreStInflightA inflight γ maddrs brkStart s5.brk liveCost peakCost st5 ∗
        (MallocngRoTablesA maddrs ∗ (S4 ∗ Rest))) =
      (S4 ∗ MallocngCoreStInflightA inflight γ maddrs brkStart s5.brk liveCost peakCost st5 ∗
        (MallocngRoTablesA maddrs ∗ Rest)) := by
    dsimp only [S4]
    generalize SlotSaved4 sp0 (s.readReg64 .x19) (s.readReg64 .x20)
      (s.readReg64 .x27) (s.readReg64 .x28) = A
    generalize MallocngCoreStInflightA inflight γ maddrs brkStart s5.brk liveCost peakCost st5 = B
    generalize MallocngRoTablesA maddrs = C
    ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hSwap5) ?_
  refine SepWP.mono
    (wp_allocSlot_bounces_tail hw348 hr348 hw564 hr564 hsc hg5 hg5Sc s5
      (MallocngRoTablesA maddrs ∗ Rest) hpc5 hrun5 hsp5_0 hal5_0 hs5_x2 hs5_22) ?_
  rintro sf P_f _ _ ⟨st6, hrun6, hsp6, hal6, hpsp6, hPres6, hGrp6, hAct6, hs6_x0, hs6_x2,
    hs6_19, hs6_20, hs6_27, hs6_28, hPf⟩
  refine ⟨st6, g5, hGrp6 ▸ hg5, hrun6, hsp6, hal6,
    hpsp2.trans (hpsp3.trans (hpsp4.trans (hpsp5.trans hpsp6))),
    hPres2.trans (hPres3.trans (hPres4.trans (hPres5.trans hPres6))),
    hg5Sc, hg5AvNe, fun h1' => by simpa [hAct6] using hHead5 (hAct6 ▸ h1'),
    by rw [State.readReg32, hs6_x0, hs5_x0, setWidth32_zeroExtend64],
    hs6_x2, hs6_19, hs6_20, hs6_27, hs6_28, hPf⟩

/-! ## Single-Step and Bounded-Depth Induction -/

private theorem allocSlot_step_full_ok
    (hMeta : AllocMetaPlacedFullStmt) {sc : Nat}
    (hRec : ∀ pSc, pSc < 48 → allocSlotDepthBound pSc < allocSlotDepthBound sc →
      AllocSlotAtDepthFullStmt pSc) :
    AllocSlotAtDepthFullStmt sc := by
  intro _ req inflight hsc hReq hInflight γ tp brkStart liveCost peakCost peakCount st hCount
  refine subroutine_ok_withCL_of_cl fun m0 hcl0 => ?_
  obtain ⟨⟨hw0, hr0⟩, ⟨hw348, hr348⟩, ⟨hw564, hr564⟩, _, _⟩ := blk08_segments_noSyscalls
  apply subroutine_ok_of_sepWP_init; intro _ R s0 hPc0 hRun0 hPre0 hSp0
  refine ⟨_, hPre0, ?_⟩; dsimp only
  refine SepWP.mono ?_
    (fun sf P_f _ _ (hPost : AllocSlotFullPost sc req inflight γ tp brkStart
        liveCost peakCost peakCount st s0 sf P_f) =>
      ⟨fun hmf => Satisfies.mono (sepConj_mono_left hPost.1) hmf, hPost.2.1, hPost.2.2⟩)
  apply SepWP.pure_elim; rintro rfl
  apply SepWP.pure_elim; rintro ⟨hTp0, hBs0, hw0_sc, hx1_req⟩
  rw [stackFrame_open_allocSlot s0 sc]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply SepWP.exists_elim; intro ws
  apply SepWP.pure_elim; intro hWsLen
  obtain ⟨u29, u30, u19, u20, u21, u22, u23, u24, u25, u26, u27, u28, hWsEq⟩ :=
    pointsToWords64_12_eq_slotSaved s0.sp ws hWsLen
  rw [hWsEq]
  let StkRest := stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224)
  let EntryFrame := SlotSaved4 s0.sp u19 u20 u27 u28 ∗ StkRest ∗
    MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp
  have hEntryEq :
      ((SlotSaved8 s0.sp u29 u30 u21 u22 u23 u24 u25 u26 ∗
        SlotSaved4 s0.sp u19 u20 u27 u28) ∗
       StkRest ∗ MallocngRoTablesA maddrs ∗
       MallocngCoreStInflightA inflight γ maddrs brkStart s0.brk liveCost peakCost st ∗
       MallocngRuntime maddrs tp) =
      (SlotSaved8 s0.sp u29 u30 u21 u22 u23 u24 u25 u26 ∗
       MallocngCoreStInflightA inflight γ maddrs brkStart s0.brk liveCost peakCost st ∗
       EntryFrame) := by
    dsimp only [EntryFrame, StkRest]
    generalize SlotSaved8 s0.sp u29 u30 u21 u22 u23 u24 u25 u26 = S8
    generalize SlotSaved4 s0.sp u19 u20 u27 u28 = S4
    generalize stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) = ST
    generalize MallocngRoTablesA maddrs = RO
    generalize MallocngCoreStInflightA inflight γ maddrs brkStart s0.brk liveCost peakCost st = CS
    generalize MallocngRuntime maddrs tp = RT
    ac_rfl
  refine SepWP.weaken_pre (Entails.of_eq hEntryEq) ?_
  refine sepWP_seq_noSyscalls_cl (mid_pc := mbase 8 + allocSlotOff_030) hcl0
    (SepWP.mono
      (wp_allocSlot_entry_to_030 hw0 hr0 hsc s0 EntryFrame hPc0 hRun0 hSp0 hw0_sc hx1_req) ?_)
  rintro s1 P1 hpc1 hrun1 ⟨h1, _, hsp1, hal1, hpsp1, hs1_1, hs1_2, hs1_3,
    hs1_21, hs1_22, hs1_23, hs1_25, hs1_19, hs1_20, hs1_27, hs1_28, _, rfl⟩ hperm1 hcl1
  let S8_0 := SlotSaved8 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
    (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
    (s0.readReg64 .x25) (s0.readReg64 .x26)
  let S4_0 := SlotSaved4 s0.sp (s0.readReg64 .x19) (s0.readReg64 .x20)
    (s0.readReg64 .x27) (s0.readReg64 .x28)
  by_cases hActZ : st.ctx.active[sc]'h1 = 0#64
  · have hPreZ :
        (S8_0 ∗ MallocngCoreStInflightA inflight γ maddrs brkStart s1.brk liveCost peakCost st ∗
          EntryFrame) =
        (SlotSaved4 s0.sp u19 u20 u27 u28 ∗
         (MallocngCoreStInflightA inflight γ maddrs brkStart s1.brk liveCost peakCost st ∗
          (S8_0 ∗ StkRest ∗ MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp))) := by
      dsimp only [EntryFrame, S8_0, StkRest]
      generalize SlotSaved8 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
        (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
        (s0.readReg64 .x25) (s0.readReg64 .x26) = A
      generalize SlotSaved4 s0.sp u19 u20 u27 u28 = B
      generalize MallocngCoreStInflightA inflight γ maddrs brkStart s1.brk liveCost peakCost st = C
      generalize stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) = D
      generalize MallocngRoTablesA maddrs = E
      generalize MallocngRuntime maddrs tp = F
      ac_rfl
    refine SepWP.weaken_pre (Entails.of_eq hPreZ) ?_
    refine sepWP_seq_noSyscalls_cl (mid_pc := mbase 8 + allocSlotOff_ag) hcl1
      (SepWP.mono
        (wp_allocSlot_030_zero_to_ag hw0 hr0 hw564 hr564 s1 _ hpc1 hrun1 hsp1 hal1
          (hs1_2.trans hActZ)) ?_)
    rintro s2 P2 hpc2 hrun2 ⟨_, hsp2, hal2, hpsp2, hr2, rfl⟩ hperm2 hcl2
    rw [hs1_19, hs1_20, hs1_27, hs1_28, ← hpsp2.2.1]
    exact ag_finish_post hMeta hsc hReq hInflight hRec hCount AllocSlotStPres.rfl id
      (fun _ => hActZ) s0 s2 hcl2 hpc2 hrun2 hsp2 hal2 hTp0 hBs0
      (hpsp1.trans hpsp2) (hperm2.trans hperm1)
      ((hr2 .x22).trans hs1_22) ((hr2 .x23).trans hs1_23)
      ((hr2 .x21).trans hs1_21) ((hr2 .x25).trans hs1_25)
  ·
    have hPreWf :
        (S8_0 ∗ MallocngCoreStInflightA inflight γ maddrs brkStart s1.brk liveCost peakCost st ∗
          EntryFrame) =
        (MallocngCoreStInflightA inflight γ maddrs brkStart s1.brk liveCost peakCost st ∗
          (S8_0 ∗ EntryFrame)) := by
      rw [← sepConj_assoc, sepConj_comm S8_0, sepConj_assoc]
    refine SepWP.weaken_pre (Entails.of_eq hPreWf) ?_
    apply sepWP_coreSt_wf; intro hwf
    obtain ⟨g, hg, hScEq, hHead⟩ := allocSlot_head_group_of_nonzero hwf hsc hActZ
    have hs1_2g : s1.readReg64 .x2 = g.metaPtr := hs1_2.trans (hHead h1)
    by_cases hAv0 : g.availMask = 0#32
    · by_cases hDeqSing : g.freedMask = 0#32 ∧ g.next = g.metaPtr
      ·
        have hPreSing :
            (MallocngCoreStInflightA inflight γ maddrs brkStart s1.brk liveCost peakCost st ∗
              (S8_0 ∗ EntryFrame)) =
            (SlotSaved4 s0.sp u19 u20 u27 u28 ∗
              MallocngCoreStInflightA inflight γ maddrs brkStart s1.brk liveCost peakCost st ∗
              (S8_0 ∗ StkRest ∗ MallocngRoTablesA maddrs ∗ MallocngRuntime maddrs tp)) := by
          dsimp only [EntryFrame, S8_0, StkRest]
          generalize SlotSaved8 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
            (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
            (s0.readReg64 .x25) (s0.readReg64 .x26) = A
          generalize SlotSaved4 s0.sp u19 u20 u27 u28 = B
          generalize MallocngCoreStInflightA inflight γ maddrs brkStart s1.brk liveCost peakCost st = C
          generalize stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) = D
          generalize MallocngRoTablesA maddrs = E
          generalize MallocngRuntime maddrs tp = F
          ac_rfl
        refine SepWP.weaken_pre (Entails.of_eq hPreSing) ?_
        refine sepWP_seq_noSyscalls_cl (mid_pc := mbase 8 + allocSlotOff_ag) hcl1
          (SepWP.mono
            (wp_allocSlot_030_deq_singleton_to_ag hw0 hr0 hsc hg hScEq hHead hAv0
              hDeqSing.1 hDeqSing.2 s1 _ hpc1 hrun1 hsp1 hal1
              hs1_1 hs1_2g hs1_3 hs1_22 hs1_23) ?_)
        rintro s2 P2 hpc2 hrun2 ⟨st2, _, hsp2, hal2, hpsp2, hPres2, hClaim2, hAct0_2, hr2, rfl⟩ hperm2 hcl2
        rw [hs1_19, hs1_20, hs1_27, hs1_28]
        exact ag_finish_post hMeta hsc hReq hInflight hRec hCount hPres2 (fun h => hClaim2.trans h) hAct0_2
          s0 s2 hcl2 hpc2 hrun2 hsp2 hal2 hTp0 hBs0
          (hpsp1.trans hpsp2) (hperm2.trans hperm1)
          ((hr2 .x22 (by decide) (by decide) (by decide) (by decide)).trans hs1_22)
          ((hr2 .x23 (by decide) (by decide) (by decide) (by decide)).trans hs1_23)
          ((hr2 .x21 (by decide) (by decide) (by decide) (by decide)).trans hs1_21)
          ((hr2 .x25 (by decide) (by decide) (by decide) (by decide)).trans hs1_25)
      ·
        have hSlow : g.freedMask ≠ 0#32 ∨ g.next ≠ g.metaPtr := by
          by_cases hFr : g.freedMask = 0#32
          · exact Or.inr fun hNx => hDeqSing ⟨hFr, hNx⟩
          · exact Or.inl hFr
        have hPreSlow :
            (MallocngCoreStInflightA inflight γ maddrs brkStart s1.brk liveCost peakCost st ∗
              (S8_0 ∗ EntryFrame)) =
            (SlotSaved4 s0.sp u19 u20 u27 u28 ∗
              MallocngCoreStInflightA inflight γ maddrs brkStart s1.brk liveCost peakCost st ∗
              (MallocngRoTablesA maddrs ∗ (S8_0 ∗ StkRest ∗ MallocngRuntime maddrs tp))) := by
          dsimp only [EntryFrame, S8_0, StkRest]
          generalize SlotSaved8 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
            (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
            (s0.readReg64 .x25) (s0.readReg64 .x26) = A
          generalize SlotSaved4 s0.sp u19 u20 u27 u28 = B
          generalize MallocngCoreStInflightA inflight γ maddrs brkStart s1.brk liveCost peakCost st = C
          generalize stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) = D
          generalize MallocngRoTablesA maddrs = E
          generalize MallocngRuntime maddrs tp = F
          ac_rfl
        refine SepWP.weaken_pre (Entails.of_eq hPreSlow) ?_
        refine sepWP_seq_noSyscalls_cl (mid_pc := mbase 8 + allocSlotOff_fast_pop) hcl1
          (SepWP.mono
            (wp_allocSlot_slow_chain_to_208 hw0 hr0 hw348 hr348 hw564 hr564 hsc hg hScEq hHead
              hAv0 hSlow s1 (S8_0 ∗ StkRest ∗ MallocngRuntime maddrs tp)
              hpc1 hrun1 hsp1 hal1 hs1_1 hs1_2g hs1_3 hs1_22 hs1_23) ?_)
        rintro sf P_f hpcf hrunf ⟨st_f, g_f, hg_f, _, hspf, half, hpspf, hPresf,
          hgfSc, hgfAvNe, hHeadf, hw0f, hx2f, h19f, h20f, h27f, h28f, rfl⟩ hpermf _
        have hPostPerm :
            (SlotSaved4 s0.sp (s1.readReg64 .x19) (s1.readReg64 .x20)
              (s1.readReg64 .x27) (s1.readReg64 .x28) ∗
              MallocngCoreStInflightA inflight γ maddrs brkStart sf.brk liveCost peakCost st_f ∗
              (MallocngRoTablesA maddrs ∗ (S8_0 ∗ StkRest ∗ MallocngRuntime maddrs tp))) =
            (S8_0 ∗ MallocngRoTablesA maddrs ∗
              MallocngCoreStInflightA inflight γ maddrs brkStart sf.brk liveCost peakCost st_f ∗
              (S4_0 ∗ StkRest ∗ MallocngRuntime maddrs tp)) := by
          dsimp only [S8_0, S4_0, StkRest]
          rw [hs1_19, hs1_20, hs1_27, hs1_28]
          generalize SlotSaved8 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
            (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
            (s0.readReg64 .x25) (s0.readReg64 .x26) = A
          generalize SlotSaved4 s0.sp (s0.readReg64 .x19) (s0.readReg64 .x20)
            (s0.readReg64 .x27) (s0.readReg64 .x28) = B
          generalize MallocngCoreStInflightA inflight γ maddrs brkStart sf.brk liveCost peakCost st_f = C
          generalize stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) = D
          generalize MallocngRoTablesA maddrs = E
          generalize MallocngRuntime maddrs tp = F
          ac_rfl
        refine SepWP.weaken_pre (Entails.of_eq hPostPerm) ?_
        exact fastPop_finish_post hw348 hr348 hw564 hr564 hsc hReq hg_f hgfSc hHeadf hgfAvNe hPresf
          s0 sf hpcf hrunf hspf half (hpsp1.trans hpspf) (hpermf.trans hperm1) hw0f hx2f
          (h19f.trans hs1_19) (h20f.trans hs1_20) (h27f.trans hs1_27) (h28f.trans hs1_28)
    ·
      refine sepWP_seq_noSyscalls_cl (mid_pc := mbase 8 + allocSlotOff_fast_pop) hcl1
        (SepWP.mono
          (wp_allocSlot_030_fast_to_208 hw0 hr0 hg hAv0 s1 (S8_0 ∗ EntryFrame)
            hpc1 hrun1 hs1_2g) ?_)
      rintro s2 P2 hpc2 hrun2 ⟨_, hsp2, hal2, hpsp2, _, hw0_2, hx2_2, hr2, rfl⟩ hperm2 _
      have hFastPerm :
          (MallocngCoreStInflightA inflight γ maddrs brkStart s2.brk liveCost peakCost st ∗
            (S8_0 ∗ EntryFrame)) =
          (S8_0 ∗ MallocngRoTablesA maddrs ∗
            MallocngCoreStInflightA inflight γ maddrs brkStart s2.brk liveCost peakCost st ∗
            (SlotSaved4 s0.sp u19 u20 u27 u28 ∗ StkRest ∗ MallocngRuntime maddrs tp)) := by
        dsimp only [EntryFrame, S8_0, StkRest]
        generalize SlotSaved8 s0.sp (s0.readReg64 .x29) (s0.readReg64 .x30)
          (s0.readReg64 .x21) (s0.readReg64 .x22) (s0.readReg64 .x23) (s0.readReg64 .x24)
          (s0.readReg64 .x25) (s0.readReg64 .x26) = A
        generalize SlotSaved4 s0.sp u19 u20 u27 u28 = B
        generalize MallocngCoreStInflightA inflight γ maddrs brkStart s2.brk liveCost peakCost st = C
        generalize stackFrameAt (s0.sp - 96#64) (allocSlotDepthBound sc * 96 + 224) = D
        generalize MallocngRoTablesA maddrs = E
        generalize MallocngRuntime maddrs tp = F
        ac_rfl
      refine SepWP.weaken_pre (Entails.of_eq hFastPerm) ?_
      exact fastPop_finish_post hw348 hr348 hw564 hr564 hsc hReq hg hScEq hHead hAv0
        AllocSlotStPres.rfl s0 s2 hpc2 hrun2 (hsp2.trans hsp1) (hal2.trans hal1)
        (hpsp1.trans hpsp2) (hperm2.trans hperm1) hw0_2 hx2_2
        ((hr2 .x19 (by decide)).trans hs1_19) ((hr2 .x20 (by decide)).trans hs1_20)
        ((hr2 .x27 (by decide)).trans hs1_27) ((hr2 .x28 (by decide)).trans hs1_28)

private theorem allocSlot_by_depth (hMeta : AllocMetaPlacedFullStmt) :
    ∀ (d sc : Nat), sc < 48 → allocSlotDepthBound sc ≤ d → AllocSlotAtDepthFullStmt sc
  | 0, _, _, hd => allocSlot_step_full_ok hMeta fun _ _ hlt => by omega
  | d + 1, _, _, hd =>
    allocSlot_step_full_ok hMeta fun pSc hpSc hlt =>
      allocSlot_by_depth hMeta d pSc hpSc (by omega)

theorem allocSlot_at_depth_full_ok (hMeta : AllocMetaPlacedFullStmt) {sc : Nat} :
    AllocSlotAtDepthFullStmt sc := by
  by_cases hsc : sc < 48
  · have hd3 : allocSlotDepthBound sc ≤ 3 := by
      unfold allocSlotDepthBound; repeat (first | split | omega)
    exact allocSlot_by_depth hMeta 3 sc hsc hd3
  · intros; contradiction

/-! ## Public Placed `alloc_slot` Contracts and Caller Lifts -/

private theorem pure_sepConj_mono {φ ψ : Prop} {Q : SepProp} (h : φ → ψ) :
    (⌜φ⌝ ∗ Q) ⊢ (⌜ψ⌝ ∗ Q) := by
  refine Entails.pure_left fun hφ => ?_
  rw [pure_sepConj_of_true (h hφ)]
  exact Entails.refl Q

theorem placed_allocSlot_full_ok (hMeta : AllocMetaPlacedFullStmt) : AllocSlotPlacedFullStmt := by
  intro _ sc req inflight hsc hReq hInflight γ tp brkStart liveCost peakCost peakCount st hCount
  refine subroutine_ok_mono_sp
    (allocSlot_at_depth_full_ok hMeta req inflight hsc hReq hInflight γ tp brkStart
      liveCost peakCost peakCount st hCount)
    (fun _ _ => Entails.refl _)
    (fun _ _ _ _ => ?_)
  dsimp only [withCL]
  refine sepConj_mono_left ?_
  refine Entails.sepExists_elim fun st' => Entails.sepExists_elim fun idx => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro st')
  refine Entails.trans ?_ (Entails.sepExists_intro idx)
  refine pure_sepConj_mono fun h => ?_
  obtain ⟨hProc, hRes, hLive, hEff, hCnt, hMa, _, hx0, hIdxLe, hGrp, hOrph, hDelta, hGrpB⟩ := h
  exact ⟨hProc, hRes, hLive, hEff, hCnt, hMa, hx0, hIdxLe, hGrp, hOrph, hDelta, hGrpB⟩

theorem placed_allocSlot_ok (hMeta : AllocMetaPlacedFullStmt) : AllocSlotPlacedStmt := by
  intro _ sc req inflight hsc hReq hInflight γ tp brkStart liveCost peakCost peakCount st hCount
  refine subroutine_ok_mono_sp
    (placed_allocSlot_full_ok hMeta sc req inflight hsc hReq hInflight γ tp brkStart
      liveCost peakCost peakCount st hCount)
    (fun _ _ => Entails.refl _)
    (fun _ _ _ _ => ?_)
  dsimp only [withCL]
  refine sepConj_mono_left ?_
  refine Entails.sepExists_elim fun st' => Entails.sepExists_elim fun idx => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro st')
  refine Entails.trans ?_ (Entails.sepExists_intro idx)
  refine pure_sepConj_mono fun h => ?_
  obtain ⟨hProc, hRes, hLive, hEff, hCnt, _, hx0, hIdxLe,
    ⟨g, hg, hAct, hIdx, hScG, _, hMetaEq, hClaimed, hZero⟩, _, hDelta, _⟩ := h
  exact ⟨hProc, hRes, hLive, hEff, hCnt, hx0, hIdxLe,
    ⟨g, hg, hAct, hIdx, hScG, hMetaEq, hClaimed, hZero⟩, hDelta⟩

theorem call_placed_allocSlot [MallocngMultiPlacement] {P : Program}
    (hMeta : AllocMetaPlacedFullStmt)
    (sc req inflight : Nat) (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc)
    (hInflight : inflight + allocSlotDepthBound sc ≤ 6)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat) (st : MallocngSt)
    (hCount : totalLiveCount st ≤ peakCount)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 8) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart ∧
         (s0.readReg32 .x0).toNat = sc ∧
         (s0.readReg64 .x1).toNat = req⌝ ∗
        stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightA inflight γ maddrs brkStart s0.brk liveCost peakCost st ∗
        MallocngRuntime maddrs tp
      post := fun _ s0 sf =>
        ∃∗ st' : MallocngSt,
        ∃∗ idx : Nat,
          ⌜MallocngProcPreserved s0 sf ∧
           st'.reservedMetas = st.reservedMetas ∧
           st'.liveMap = st.liveMap ∧
           totalLiveEffCost st' = totalLiveEffCost st ∧
           totalLiveCount st' = totalLiveCount st ∧
           sf.readReg32 .x0 = BitVec.ofNat 32 idx ∧ idx ≤ 31 ∧
           (∃ g ∈ st'.groups, ∃ hAct : sc < st'.ctx.active.length, ∃ hIdx : idx < g.slots.length,
             g.sc = sc ∧
             g.metaPtr = st'.ctx.active[sc]'hAct ∧
             g.slots[idx]'hIdx = .claimed ∧
             (g.isMmapped = true →
               ∀ a : BitVec 64, InRegion (g.slotStart idx) g.stride a → st'.byteVal a = 0#8)) ∧
           MallocngMappedDelta (2 * (allocSlotDepthBound sc + 1))
             (allocSlotPlacedByteBound sc peakCount) s0.mem sf.mem⌝ ∗
          stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) ∗
          MallocngRoTablesA maddrs ∗
          MallocngRuntime maddrs tp ∗
          MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st'
      onOom := fun _ s0 sf =>
        ⌜MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1))
           (allocSlotPlacedByteBound sc peakCount) s0 sf⌝
    }) :=
  subroutine_ok_block_to_block (j := 8) (by decide)
    (placed_allocSlot_ok hMeta sc req inflight hsc hReq hInflight γ tp brkStart
      liveCost peakCost peakCount st hCount) hext hsvc

theorem call_placed_allocSlot_full [MallocngMultiPlacement] {P : Program}
    (hMeta : AllocMetaPlacedFullStmt)
    (sc req inflight : Nat) (hsc : sc < 48) (hReq : req ≤ nominalSlotCap sc)
    (hInflight : inflight + allocSlotDepthBound sc ≤ 6)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat) (st : MallocngSt)
    (hCount : totalLiveCount st ≤ peakCount)
    (hext : ∀ pc, P.externAt? pc = none := by
      intro pc; simp [Program.rebase, PlacedLib.program, Program.externAt?, Program.hookAtOff?])
    (hsvc : P.svc = msvc := by rfl) :
    subroutine_ok P (mbase 8) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart ∧
         (s0.readReg32 .x0).toNat = sc ∧
         (s0.readReg64 .x1).toNat = req⌝ ∗
        stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) ∗
        MallocngRoTablesA maddrs ∗
        MallocngCoreStInflightA inflight γ maddrs brkStart s0.brk liveCost peakCost st ∗
        MallocngRuntime maddrs tp
      post := fun _ s0 sf =>
        ∃∗ st' : MallocngSt,
        ∃∗ idx : Nat,
          ⌜MallocngProcPreserved s0 sf ∧
           st'.reservedMetas = st.reservedMetas ∧
           st'.liveMap = st.liveMap ∧
           totalLiveEffCost st' = totalLiveEffCost st ∧
           totalLiveCount st' = totalLiveCount st ∧
           st'.metaAreas.length ≤ max st.metaAreas.length (1 + (88 + 8 * peakCount) / 101) ∧
           sf.readReg32 .x0 = BitVec.ofNat 32 idx ∧ idx ≤ 31 ∧
           (∃ g ∈ st'.groups, ∃ hAct : sc < st'.ctx.active.length, ∃ hIdx : idx < g.slots.length,
             g.sc = sc ∧
             req + 4 ≤ g.stride ∧
             g.metaPtr = st'.ctx.active[sc]'hAct ∧
             g.slots[idx]'hIdx = .claimed ∧
             (g.isMmapped = true →
               ∀ a : BitVec 64, InRegion (g.slotStart idx) g.stride a → st'.byteVal a = 0#8)) ∧
           MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem ∧
           MallocngMappedDelta (2 * (allocSlotDepthBound sc + 1))
             (allocSlotPlacedByteBound sc peakCount) s0.mem sf.mem ∧
           (totalClaimedSlots st = 0 → ∀ U : Nat, peakCount ≤ U →
             Cost.GroupsGrpBound U st.groups → Cost.GroupsGrpBound U st'.groups)⌝ ∗
          stackFrame s0 ((allocSlotDepthBound sc + 1) * 96 + 224) ∗
          MallocngRoTablesA maddrs ∗
          MallocngRuntime maddrs tp ∗
          MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st'
      onOom := fun _ s0 sf =>
        ⌜MallocngPlacedOomCond msvc (2 * (allocSlotDepthBound sc + 1))
           (allocSlotPlacedByteBound sc peakCount) s0 sf⌝
    }) :=
  subroutine_ok_block_to_block (j := 8) (by decide)
    (placed_allocSlot_full_ok hMeta sc req inflight hsc hReq hInflight γ tp brkStart
      liveCost peakCost peakCount st hCount) hext hsvc

end VerifiedLibraries.Mallocng.Proofs
