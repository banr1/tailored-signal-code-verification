/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplStage2b
public import LibsignalBinary.Heap.Fine.AllocMetaFine
public import LibsignalBinary.Heap.Fine.RootMmapParamsFine
public import LibsignalBinary.Heap.Fine.AllocSlotTraceRaw
public import LibsignalBinary.Heap.Fine.AllocSlotFine
public import LibsignalBinary.Heap.Fine.Footprint
public import LibsignalBinary.Heap.Fine.FineSpecs
public import LibsignalBinary.Heap.Fine.MallocImplEnframeSteps
public import VerifiedLibraries.Mallocng.Proofs.PlacedFetch2

/-!
# Fine-Grained `__libc_malloc_impl` Trace Fold and Join Epilogue

Folds `AllocSlotFineTrace` and inline `try_avail` claims into `AllocSlotInvPres`, and verifies the
`__libc_malloc_impl` (`blk09`) join epilogue (`miOff_call_unlock → ret`) producing
`MallocImplFineRawRel` without committing `FineBudget`.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic
open VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

arm64_proof_prelude

/-! ## Trace Fold (`AllocSlotFineTrace → AllocSlotInvPres`) and OOM Bounds -/

theorem allocMeta_fine_param_ok : AllocMetaFineParamStmt :=
  fun inflight hInflight γ tp brkStart liveCost peakCost maxGroups maxMetaAreas st
    hGroups hMeta0 hMetaStep hext hsvc =>
    call_placed_allocMeta_fine inflight hInflight γ tp brkStart liveCost peakCost
      maxGroups maxMetaAreas st hGroups hMeta0 hMetaStep hext hsvc

theorem rootSizeSelect_fine_param_ok : RootSizeSelectParamStmt RootMmapParamsFine := by
  intro _ s sc req cnt' use Frame hw768 hsc hReq hlo hhi hgt2048 hprod h25 hcnt' hpc hrun hx0 hx4 hx6 hx7 hx20 hx21 hx24 hx25 hx27 hx25_38
  refine SepWP.mono
    (wp_root_size_select_req_fine s sc req cnt' use Frame hw768 hsc hReq hlo hhi hgt2048 hprod h25
      hcnt' hpc hrun hx0 hx4 hx6 hx7 hx20 hx21 hx24 hx25 hx27 hx25_38)
    ?_
  rintro sf P_f _ _ ⟨cnt_f, len, hFine, hc1, hrunf, hspf, hspAf, hPsp, hx20f, hx26f, hRegs, hPf⟩
  exact ⟨cnt_f, len, hFine.1, hFine, hc1, hrunf, hspf, hspAf, hPsp, hx20f, hx26f, hRegs, hPf⟩

theorem allocSlotInvPres_of_sameGroups {sc : Nat} {pk : List Nat}
    {alignMap : BitVec 64 → Option Nat} {st0 st_ag : MallocngSt}
    (hInit : AllocSlotInvPres sc pk alignMap st0 st0)
    (hLiveAll : ∀ k < 48, liveSlotsInClass st0 k ≤ pk.getD k 0)
    (hPre : SameGroupsSlotKind st_ag.groups st0.groups) :
    (∀ sc', AllocSlotInvPres sc' pk alignMap st_ag st_ag) ∧
    (∀ k < 48, liveSlotsInClass st_ag k ≤ pk.getD k 0) := by
  have hP := fineSameGroupsSlotKind_preserves_all (alignMap := alignMap) hPre
  refine ⟨fun sc' => AllocSlotInvPres.refl
    (hP.1 hInit.groups_geom)
    (hP.2.1 hInit.user_slots_wf)
    (fun k hk => by rw [hP.2.2.2.1 k]; exact hInit.groups_le k hk)
    (fun ch hch q hq => by rw [hP.2.2.2.2.1 ch q]; exact hInit.edges_le ch hch q hq)
    (fun k hk => by rw [hP.2.2.2.2.2.1 k]; exact hInit.roots_le k hk),
    fun k hk => by rw [hP.2.2.1 k]; exact hLiveAll k hk⟩

/-- Structural induction folding `AllocSlotFineTrace RootMmapParamsFine` into `AllocSlotInvPres`. -/
theorem allocSlotInvPres_of_trace {base brkStart : BitVec 64} {liveCost peakCost : Nat}
    {pk : List Nat} {alignMap : BitVec 64 → Option Nat}
    {inflight sc req : Nat} {st_in st_out : MallocngSt} {idx : Nat}
    (hTrace : AllocSlotFineTrace RootMmapParamsFine base brkStart liveCost peakCost inflight sc req st_in st_out idx)
    (hsc : sc < 48)
    (hInfDepth : inflight + allocSlotDepthBound sc ≤ 4)
    (hInit : AllocSlotInvPres sc pk alignMap st_in st_in)
    (hLiveAll : ∀ k < 48, liveSlotsInClass st_in k ≤ pk.getD k 0)
    (hNodupOut : (st_out.groups.map GroupDesc.metaPtr).Nodup) :
    AllocSlotInvPres sc pk alignMap st_in st_out := by
  induction hTrace with
  | @pop infl sc' req' st0 st_f st' g_f idx' hPre hgf _hgfSc hIdx hFree hClaim =>
    exact allocSlotInvPres_pop hInit hPre hgf hIdx hFree hClaim hNodupOut
  | @rootGroup infl sc' req' st0 st_ag st' brk_ag cnt' activeIdx cg
      hPre hwfAg hAct0 hCnt' hRootP hCgProps hGroups' =>
    exact allocSlotInvPres_rootGroup hsc (by omega) hInit (hLiveAll sc' hsc)
      hPre hwfAg hAct0 hCnt'.2.2.2.2.2 hCnt'.2.2.1
      hRootP.1 hRootP.2.1 hRootP.2.2.1 hRootP.2.2.2
      ⟨hCgProps.1, hCgProps.2.1, hCgProps.2.2.2.1, hCgProps.2.2.2.2.2⟩ hGroups'
  | @nestedGroup infl sc' req' st0 st_ag st2 st' brk_ag cnt' pIdx pg cg
      hPre hwfAg hAct0 hv _hParentTrace hPg hCgProps hGroups' ih =>
    have hpScLt : sizeToClassUnits (cnt' * sizeClass sc') < 48 :=
      (validNestedCnt_bounds hsc hv).2.1
    have hDepthStep := allocSlotDepthBound_nested_lt hsc hv
    obtain ⟨hInitAg, hLiveAg⟩ := allocSlotInvPres_of_sameGroups hInit hLiveAll hPre
    have hNodup2 := nestedGroup_parent_nodup hGroups' hNodupOut
    have hParentPres := ih hpScLt (by omega)
      (hInitAg (sizeToClassUnits (cnt' * sizeClass sc'))) hLiveAg hNodup2
    obtain ⟨hpIdx, hClaimed⟩ := hPg.2.2
    exact allocSlotInvPres_nestedGroup hsc (by omega) hInit (hLiveAll sc' hsc)
      hPre hwfAg hAct0 hv hParentPres hPg.1 hPg.2.1 hpIdx hClaimed
      ⟨hCgProps.1, hCgProps.2.1, hCgProps.2.2.2.1, hCgProps.2.2.2.2.1, hCgProps.2.2.2.2.2⟩
      hGroups' hNodupOut

/-- Inline `try_avail` fast-path claim (`mkReplaceSlotSt st0 g idx newAvail .claimed`) preserves
    `AllocSlotInvPres sc pk alignMap st0 st1`. -/
theorem claimFreeAvail_allocSlotInvPres {base brkStart brk : BitVec 64}
    {liveCost peakCost sc : Nat} {pk : List Nat}
    {alignMap : BitVec 64 → Option Nat} {st0 : MallocngSt} {g : GroupDesc}
    (hwf0 : MallocngWF base brkStart brk liveCost peakCost st0)
    (hInit : AllocSlotInvPres sc pk alignMap st0 st0)
    (hg : g ∈ st0.groups) (hAvailNe : g.availMask ≠ 0#32) :
    let idx := ctz32DeBruijn g.availMask
    let newAvail := g.availMask - ((-g.availMask) &&& g.availMask)
    let g' := mkReplaceSlotGroup g idx newAvail .claimed
    let val' := writeBytesToMap st0.byteVal g.metaPtr g'.metaBytes
    let st1 := mkReplaceSlotSt st0 g idx newAvail .claimed val' st0.liveMap
    AllocSlotInvPres sc pk alignMap st0 st1 := by
  intro idx newAvail g' val' st1
  obtain ⟨hIdxSlots, hIdx32, _, _, _, _, hwf1, _, _, _, _, _⟩ :=
    claimFreeAvail_absorb hwf0 hg hAvailNe
  have hgw := hwf0.groups_wf g hg
  obtain ⟨_, _, _, hIso, _, hSet, _, _⟩ := ctz32DeBruijn_spec hAvailNe
  obtain ⟨hBitTrue, _, _, _, _⟩ := bit32_sub_pow2_props idx hIdx32 g.availMask hIso hSet
  have hsw := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdxSlots
  have hFree : (g.slots[idx]'hIdxSlots).isFree = true := by
    rw [hsw.2.1.mp hBitTrue]; rfl
  have hClaim : FineSameGroupsSlotKind st1.groups
      (st0.groups.map fun h =>
        if h.metaPtr == g.metaPtr then { h with slots := h.slots.set idx .claimed } else h) := by
    dsimp only [st1, mkReplaceSlotSt, replaceGroup, g', mkReplaceSlotGroup]
    exact SameGroupsSlotKind.of_map_map fun h _ => by
      by_cases hEq : (h.metaPtr == g.metaPtr) = true
      · have hhEq : h = g := nodup_metaPtr_eq hwf0.groups_nodup.1 ‹h ∈ st0.groups› hg (beq_iff_eq.mp hEq)
        subst hhEq
        simp only [hEq, ↓reduceIte]
        exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, list_forall2_slotSameKind_refl _⟩
      · simp only [Bool.not_eq_true] at hEq
        simp only [hEq, Bool.false_eq_true, ↓reduceIte]
        exact ⟨GroupSameGeom.refl h, list_forall2_slotSameKind_refl _⟩
  exact allocSlotInvPres_pop hInit (FineSameGroupsSlotKind.refl st0.groups)
    hg hIdxSlots hFree hClaim hwf1.groups_nodup.1

theorem allocSlotFineByteBound_le_stepReserve (sc req : Nat) (b : FineBudget) :
    2 * (allocSlotDepthBound sc + 1) ≤ 16 ∧
    allocSlotFineByteBound sc (fineMaxMetaAreas b) ≤ fineStepReserve (.alloc req) b := by
  have hDepth := allocSlotDepthBound_le_three sc
  refine ⟨by omega, ?_⟩
  dsimp only [allocSlotFineByteBound, fineStepReserve, FineStepBound]
  have hMul : (allocSlotDepthBound sc + 1) * (5 * 1024 * 1024 + 32768 * fineMaxMetaAreas b) ≤
      4 * (5 * 1024 * 1024 + 32768 * fineMaxMetaAreas b) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem fineStepOomCond_of_allocSlot {svc : State → State}
    {sc req : Nat} {b : FineBudget} {s0 s sf : State}
    (hProc : MallocngProcPreserved s0 s)
    (hPerm0 : s.mem.perm = s0.mem.perm)
    (hOom : MallocngPlacedOomCond svc (2 * (allocSlotDepthBound sc + 1))
      (allocSlotFineByteBound sc (fineMaxMetaAreas b)) s sf) :
    FineStepOomCond svc (fineStepReserve (.alloc req) b) s0 sf := by
  obtain ⟨hCntLe, hByteLe⟩ := allocSlotFineByteBound_le_stepReserve sc req b
  obtain ⟨hfs, htr, hsig, ivs, hLen, hSum, hCov, hgap⟩ := hOom
  refine ⟨hfs.trans hProc.1, htr.trans hProc.2.1, hsig.trans hProc.2.2.2.2.2.2,
    ⟨ivs, Nat.le_trans hLen hCntLe, Nat.le_trans hSum hByteLe,
      fun a ha => (hCov a ha).imp (fun h => hPerm0 ▸ h) id⟩, ?_⟩
  intro hsan
  obtain ⟨sz, hlo, hmod, hhi, hng⟩ := hgap hsan
  exact ⟨sz, hlo, hmod, Nat.le_trans (Nat.le_add_left _ _) (Nat.le_trans hhi hByteLe), hng⟩

theorem coarseBump_choice_to_coarseAlt {req sc : Nat}
    (hChoice :
      let sc0 := sizeToClassUnits ((req + 3) / 16)
      sc = sc0 ∨ (4 ≤ sc0 ∧ sc0 ≤ 31 ∧ sc0 ≠ 6 ∧ sc0 % 2 = 0 ∧ sc = sc0 + 1)) :
    sc = sizeToClassUnits ((req + 3) / 16) ∨
    sc = coarseAlt (sizeToClassUnits ((req + 3) / 16)) := by
  dsimp only at hChoice
  rcases hChoice with hEq | ⟨hlo, hhi, hne6, hpar, hEq⟩
  · exact Or.inl hEq
  · right
    unfold coarseAlt coarseBumpable
    rw [decide_eq_true ⟨hlo, hhi, hne6, hpar⟩]
    simpa using hEq

/-! ## Raw Join Epilogue -/

/-- Success postcondition body of `libcMallocImplFineRawSpec` when `req ≤ MallocngMaxAllocSize`
    (before prepending `⌜MallocngProcPreserved s0 sf ∧ MallocngMappedDelta ...⌝`). -/
def MallocImplFineRawSuccessBody [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat) (s0 sf : State) : SepProp :=
  stackFrame s0 704 ∗
  ∃∗ p : BitVec 64,
  ∃∗ bs : List (BitVec 8),
  ∃∗ st0 : MallocngSt,
  ∃∗ alignMap0 : BitVec 64 → Option Nat,
  ∃∗ st' : MallocngSt,
  ∃∗ g' : GroupDesc,
  ∃∗ idx : Nat,
  ∃∗ bCoarse : MallocngBudget,
    ⌜sf.readReg64 .x0 = p ∧
     sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
     MallocngBlockWf p req ∧
     bs.length = req ∧
     MallocngNoOrphanMappings ivs0 (dynamicRootRegions st') s0.mem sf.mem ∧
     MallocngWF maddrs.base brkStart sf.brk bCoarse.liveCost bCoarse.peakCost st' ∧
     MallocngCountIvsWF bCoarse (dynamicRootRegions st') st' ∧
     MallocImplFineRawRel maddrs.base brkStart b ivs0 alignMap0 st0 st' g' idx req p ∧
     (g'.isMmapped = true → bs = List.replicate req 0#8)⌝ ∗
    MallocngRoTablesA maddrs ∗
    ghostMapAuth (fineAlignGam γ) alignMap0 ∗
    MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk
      bCoarse.liveCost bCoarse.peakCost st' ∗
    MallocngRuntime maddrs tp ∗
    (p ↦ₛ bs) ∗
    MallocngBlockToken (fineBaseGam γ) p req

/-- Full success postcondition of `libcMallocImplFineRawSpec` when `req ≤ MallocngMaxAllocSize`. -/
def MallocImplFineRawSuccessPost [MallocngMultiPlacement]
    (γ : GhostName) (tp brkStart : BitVec 64) (b : FineBudget)
    (ivs0 : List (BitVec 64 × Nat)) (req : Nat) (s0 sf : State) : SepProp :=
  ⌜MallocngProcPreserved s0 sf ∧
   MallocngMappedDelta 16 (fineStepReserve (.alloc req) b) s0.mem sf.mem⌝ ∗
  MallocImplFineRawSuccessBody γ tp brkStart b ivs0 req s0 sf

set_option maxHeartbeats 400000 in
theorem mallocImpl_enframe_finish_raw_fine [MallocngMultiPlacement]
    {γ : GhostName} {tp brkStart : BitVec 64} {b : FineBudget} {bud : MallocngBudget}
    {ivs0 : List (BitVec 64 × Nat)} {alignMap0 : BitVec 64 → Option Nat}
    {req idx off : Nat} {st0 st1 : MallocngSt} {g : GroupDesc} {s0 s : State}
    {oom : State → SepProp}
    (hInv0 : MallocngFineInv 0 b ivs0 alignMap0 st0)
    (hLiveMap1 : st1.liveMap = st0.liveMap)
    (hMetaLe1 : st1.metaAreas.length ≤ fineMaxMetaAreas b)
    (hNoOrph1 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st1) s0.mem s.mem)
    (hwf1 : MallocngWFInflight 1 maddrs.base brkStart s.brk bud.liveCost bud.peakCost st1)
    (hNoRes : st1.reservedMetas = [])
    (hg : g ∈ st1.groups) (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hReqMax : req ≤ MallocngMaxAllocSize)
    (hFit0 : req + 4 ≤ g.stride) (hOff255 : off ≤ 255) (hFit : 16 * off + req ≤ g.stride - 4)
    (hSc2 : 2 ≤ g.sc ∧ g.sc < 48 → nominalSlotCap (g.sc - 2) < max req 16)
    (hSc24 : g.sc = 24 → nominalSlotCap 23 < req)
    (hSc63 : g.sc = 63 → g.maplen * 4096 ≤ max req MallocngMinBlockCost + 8195)
    (hSc63_4115 : g.sc = 63 → g.maplen * 4096 ≤ req + 4115)
    (hZeroMm : g.isMmapped = true → ∀ a : BitVec 64, InRegion (g.slotStart idx) g.stride a → st1.byteVal a = 0#8)
    (hRawBranch : ∀ (p : BitVec 64) (val' : BitVec 64 → BitVec 8) (liveMap' : MallocngLiveMap),
      let effCost := max req MallocngMinBlockCost
      let g' := mkReplaceSlotGroup g idx g.availMask (.liveUser p req effCost)
      let st2 := mkReplaceSlotSt st1 g idx g.availMask (.liveUser p req effCost) val' liveMap'
      if hSmall : req ≤ MmapThresholdReq then
        ∃ (sc : Nat) (pk : List Nat) (pkSC pkSB : Nat)
          (st1_w : MallocngSt) (g1_w : GroupDesc)
          (brk1 : BitVec 64) (live1 peak1 : Nat),
          let _ := hSmall
          sc < 48 ∧
          (sc = sizeToClassUnits ((req + 3) / 16) ∨
           sc = coarseAlt (sizeToClassUnits ((req + 3) / 16))) ∧
          (pk.length = 48 ∧
           (∀ k < 48, liveSlotsInClass st0 k ≤ pk.getD k 0) ∧
           (∀ k < 48, (allGroups st0 k).length ≤ gBound pk k) ∧
           (∀ ch < 48, ∀ pSc < 48, (nestedEdge st0 ch pSc).length ≤ edgeBound pk ch pSc) ∧
           (∀ k < 48, rootBytes st0 k ≤ rBound pk k) ∧
           (straddle63Groups st0).length ≤ pkSC ∧
           straddle63Bytes st0 ≤ pkSB ∧
           linForm grpWtS pk + FineScale * pkSC ≤ b.cumSmallGroupsS ∧
           linForm slotWt pk + pkSB ≤ b.cumSmallBytes) ∧
          AllocSlotInvPres sc pk alignMap0 st0 st1_w ∧
          MallocngWFInflight 1 maddrs.base brkStart brk1 live1 peak1 st1_w ∧
          g1_w ∈ st1_w.groups ∧ g1_w.sc = sc ∧
          (∃ hIdx1 : idx < g1_w.slots.length, g1_w.slots[idx]'hIdx1 = .claimed) ∧
          FineGroupSameGeom g' g1_w ∧
          g'.slots = g1_w.slots.set idx (.liveUser p req effCost) ∧
          st2.groups = st1_w.groups.map (fun h => if h.metaPtr == g1_w.metaPtr then g' else h)
      else
        ∃ st1_w : MallocngSt,
          idx = 0 ∧
          FineSameGroupsSlotKind st1_w.groups st0.groups ∧
          st2.groups = g' :: st1_w.groups ∧
          g'.sc = 63 ∧
          g'.slots = [.liveUser p req effCost] ∧
          g'.maplen * 4096 ≤ req + 4115)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hpc : s.pc = mbase 9 + miOff_enframe_c4) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx0 : s.readReg64 (.gpr 0#5) = g.slotStart idx)
    (hx1 : s.readReg64 (.gpr 1#5) = BitVec.ofNat 64 off)
    (hx2 : s.readReg64 (.gpr 2#5) = g.storage)
    (hx4 : s.readReg64 (.gpr 4#5) = 0#64)
    (hx6 : s.readReg64 (.gpr 6#5) = g.slotEnd idx)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx22 : s.readReg64 (.gpr 22#5) = g.metaPtr)
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (mallocngBlockProg mmpl 9 msvc) (s0.readReg64 (.gpr 30#5)) s
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       ghostMapAuth (fineAlignGam γ) alignMap0 ∗
       MallocngCoreStInflightA 1 (fineBaseGam γ) maddrs brkStart s.brk bud.liveCost bud.peakCost st1 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        sf.sp = s0.sp ∧ sf.brk = s.brk ∧ sf.mem.perm = s.mem.perm ∧
        MallocngProcPreserved s0 sf ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ MallocImplFineRawSuccessBody γ tp brkStart b ivs0 req s0 sf))
      oom := by
  rw [mallocngBlockProg_eq_b09]
  have hb : BlkBase 9 (mbase 9) := rfl
  generalize mbase 9 = b9 at hpc hb ⊢
  have hgw := hwf1.groups_wf g hg
  have hTot48 : g.mem.toNat + g.totalBytes ≤ 2 ^ 48 := hgw.2.2.2.2.2.2.1
  obtain ⟨hIdxCnt, _, hStartNat, _, hEndNat, hEndLe, h48G, _, _⟩ := group_slot_bounds hgw hIdx
  have hIdx31 : idx ≤ 31 := by have := hgw.2.1; dsimp [GroupDesc.cnt] at hIdxCnt; omega
  let start := g.slotStart idx
  let p := start + BitVec.ofNat 64 (16 * off)
  let slotBs := readBytesFromMap st1.byteVal (start - 4#64) g.stride
  let totOff16 := (p.toNat - g.storage.toNat) / 16
  let res := (g.slotEnd idx).toNat - (p.toNat + req)
  have hStartEq : start.toNat = g.mem.toNat + 16 + idx * g.stride := hStartNat
  have hFit4 : 16 * off + 4 ≤ g.stride :=
    Nat.le_trans (Nat.add_le_add_right (Nat.le_trans (Nat.le_add_right _ req) hFit) 4)
      (Nat.le_of_eq (Nat.sub_add_cancel (Nat.le_trans (Nat.le_add_left 4 req) hFit0)))
  have hResEq : res = g.stride - 4 - (16 * off + req) := by
    have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
    have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
    have hPNat : p.toNat = start.toNat + 16 * off := bv64_add_toNat (by omega)
    dsimp only [res]; omega
  obtain ⟨hBs1L, hBs2L, hBs3L, hNewL, hBs3Idx, hB0, hBP4, hBP3, hBP2, hBR1, hBR5, hZeroU⟩ :=
    enframe_slotBytes_props hgw hIdx hClaimed hOff255 hFit hZeroMm
  obtain ⟨hBlkWf, hFresh1, hPOffLe, hSc24_26, hwf2, hg'Mem, _hCntEq, hDynEq, hExtSlot, hAbsSlot, hPnEq, hMpEq⟩ :=
    enframeClaimed_absorb (b := bud) hwf1 hg hIdx hClaimed hReqMax hOff255 hFit hSc2 hSc24 hSc63
      hNewL hB0 hBP4 hBP3 hBP2 hBR1 hBR5
  obtain ⟨hSlackLt, _, _, _, _, _, hOffProps⟩ := enframe_bv_props hgw hIdx hFit0 hSc63
  have hResLt : res < 1048576 :=
    Nat.lt_of_le_of_lt (by rw [hResEq]; exact Nat.sub_le_sub_left (Nat.le_add_left _ _) _) hSlackLt
  obtain ⟨hOffSE, _, hPS4, _, _, _, hSub32, _, hNegAddr, hSle4, _, _, hR5Or⟩ := hOffProps off hOff255 hFit
  have hExtMeta := meta_and_slot_extract hwf1 hNoRes hg hIdx hClaimed
  let liveMap' : MallocngLiveMap := st1.liveMap.insert p req 0
  let newSlotBs := ByteSlice.write8 (enframeB3 (enframeB2 (enframeB1 slotBs off) off idx totOff16) off req g.stride res)
    (16 * off + 1) (BitVec.ofNat 8 ((min res 5 <<< 5) ||| idx))
  let val' := writeBytesToMap st1.byteVal (start - 4#64) newSlotBs
  let rwTail := ByteMap st1.masterDom
    (fun a => (OwnedRwByte st1 a ∧ ¬ InRegion (start - 4#64) g.stride a) ∧ ¬ InRegion g.metaPtr 40 a) st1.byteVal
  let coreStatic := (maddrs.ctx ↦ₛ st1.ctx.toBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗
    (maddrs.aaReplaced ↦₃₂ 0#32) ∗ ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) ∗
    MallocngAuxvState (fineBaseGam γ) st1.auxvPtr st1.auxvSnap ∗
    ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗ MappedSet st1.masterDom (OwnedMappedByte st1)
  let envTail := stackFrameAt (s0.sp - 80#64) 624 ∗ MallocngRoTablesA maddrs ∗
    ghostMapAuth (fineAlignGam γ) alignMap0 ∗ MallocngRuntime maddrs tp ∗
    MallocngBlockToken (fineBaseGam γ) p req ∗ MallocngLiveAuth (fineBaseGam γ) liveMap' ∗ coreStatic ∗ rwTail
  dsimp only [MallocngCoreStInflightA]
  rw [hExtSlot, hExtMeta]
  wp_conv_pre => simp only [hwf1, pure_true, emp_sepConj]
  refine sepWP_bupd_focus (mallocngBlock_alloc_bupd (fineBaseGam γ) st1.liveMap p req 0 hBlkWf hFresh1) (h := ?_)
  have hPre1 : ((MallocngLiveAuth (fineBaseGam γ) liveMap' ∗ MallocngBlockToken (fineBaseGam γ) p req) ∗
      MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗ MallocngRoTablesA maddrs ∗
      ghostMapAuth (fineAlignGam γ) alignMap0 ∗
      (maddrs.ctx ↦ₛ st1.ctx.toBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗
      (maddrs.aaReplaced ↦₃₂ 0#32) ∗ ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) ∗
      MallocngAuxvState (fineBaseGam γ) st1.auxvPtr st1.auxvSnap ∗
      ((start - 4#64) ↦ₛ slotBs) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗ rwTail ∗
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
      MappedSet st1.masterDom (OwnedMappedByte st1) ∗ MallocngRuntime maddrs tp) =
      (((start - 4#64) ↦ₛ slotBs) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗
        (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ envTail)) := by
    dsimp only [envTail, coreStatic]
    generalize MallocngBlockToken (fineBaseGam γ) p req = tok,
      MallocngLiveAuth (fineBaseGam γ) liveMap' = gm,
      ghostMapAuth (fineAlignGam γ) alignMap0 = ga,
      ((start - 4#64) ↦ₛ slotBs) = sA, (g.metaPtr ↦ₛ g.metaBytes) = mA, rwTail = rT,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = svA, stackFrameAt (s0.sp - 80#64) 624 = sfA,
      MallocngRoTablesA maddrs = roA, MallocngRuntime maddrs tp = rtA,
      (maddrs.ctx ↦ₛ st1.ctx.toBytes) = cA, (maddrs.lock ↦₃₂ 0#32) = lkA,
      (maddrs.replaced ↦₃₂ 0#32) = rpA, (maddrs.aaReplaced ↦₃₂ 0#32) = aaA,
      ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) = lbA,
      MallocngAuxvState (fineBaseGam γ) st1.auxvPtr st1.auxvSnap = axA,
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pnA,
      MappedSet st1.masterDom (OwnedMappedByte st1) = mpA
    ac_rfl
  rw [hPre1]
  refine SepWP.seq_entails_emp
    (enframe_step1_fine hb hFit0 hFit hOff255 (readBytesFromMap_length ..) (by simp [GroupDesc.metaBytes])
      (by rw [(metaBytes_ops g 0 0#32 .claimed).1]; rfl) hOffSE hpc hrun hsp hProc hcsHi
      hx0 hx1 hx2 hx4 hx6 hx20 hx22 hx23) ?_
  rintro s1 hpc1 hrun1 ⟨hsp1, hbrk1, hperm1, hProc1, hcs1, hx0_1, hx2_1, hx4_1, hx6_1, hx20_1, hx23_1⟩
  have hPre2 : (((start - 4#64) ↦ₛ enframeB1 slotBs off) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ envTail)) =
      (((start - 4#64) ↦ₛ enframeB1 slotBs off) ∗
        (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗ envTail)) := by
    generalize ((start - 4#64) ↦ₛ enframeB1 slotBs off) = sA, (g.metaPtr ↦ₛ g.metaBytes) = mA,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = svA, envTail = eT
    ac_rfl
  rw [hPre2]
  refine SepWP.seq_entails_emp
    (enframe_step2_fine hb hFit0 hFit hIdx31 hResEq hResLt hBs1L hBs2L hBs3L hBs3Idx
      hPS4 hSub32 hNegAddr hSle4 hpc1 hrun1 hProc1 hcs1 hx0_1 hx2_1 hx4_1 hx6_1 hx20_1 hx23_1) ?_
  rintro s2 hpc2 hrun2 ⟨hsp2, hbrk2, hperm2, hProc2, hcs2, hx0_2, hx1_2, hx4_2⟩
  have hPre3 : (((start - 4#64) ↦ₛ enframeB3 (enframeB2 (enframeB1 slotBs off) off idx totOff16) off req g.stride res) ∗
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗ envTail)) =
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
        ((start - 4#64) ↦ₛ enframeB3 (enframeB2 (enframeB1 slotBs off) off idx totOff16) off req g.stride res) ∗
        ((g.metaPtr ↦ₛ g.metaBytes) ∗ envTail)) := by
    generalize ((start - 4#64) ↦ₛ enframeB3 (enframeB2 (enframeB1 slotBs off) off idx totOff16) off req g.stride res) = sA,
      (g.metaPtr ↦ₛ g.metaBytes) = mA, MallocImplSavedRegs s0 (s0.sp - 80#64) = svA, envTail = eT
    ac_rfl
  rw [hPre3]
  refine SepWP.mono
    (enframe_step3_fine hb hFit4 hIdx31 hBs3L hR5Or hpc2 hrun2 (hsp2.trans hsp1) hsp_align
      hProc2 hcs2 hx0_2 hx1_2 hx4_2) ?_
  rintro sf P_f _ _ ⟨hsf_sp, hsf_brk, hsf_perm, hsf_proc, hsf_cs, hsf_x0, hPf⟩
  have hBrkEq : sf.brk = s.brk := hsf_brk.trans (hbrk2.trans hbrk1)
  have hPermEq : sf.mem.perm = s.mem.perm := hsf_perm.trans (hperm2.trans hperm1)
  refine ⟨hsf_sp, hBrkEq, hPermEq, hsf_proc, hsf_cs, Entails.trans hPf ?_⟩
  let effCost := max req MallocngMinBlockCost
  let st2 := mkReplaceSlotSt st1 g idx g.availMask (.liveUser p req effCost) val' liveMap'
  let g' := mkReplaceSlotGroup g idx g.availMask (.liveUser p req effCost)
  let bf := mallocngAllocBudget true req bud
  let bCoarse := synthCoarseBudget bf.liveCost bf.peakCost st2
  have hReasm : (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ ((start - 4#64) ↦ₛ newSlotBs) ∗
      ((g.metaPtr ↦ₛ g.metaBytes) ∗ envTail)) =
      ((MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624) ∗
       (MallocngRoTablesA maddrs ∗
        ghostMapAuth (fineAlignGam γ) alignMap0 ∗
        (MallocngLiveAuth (fineBaseGam γ) st2.liveMap ∗ (maddrs.ctx ↦ₛ st2.ctx.toBytes) ∗
         (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
         ((maddrs.libc + 8#64) ↦₆₄ st2.auxvPtr) ∗
         MallocngAuxvState (fineBaseGam γ) st2.auxvPtr st2.auxvSnap ∗
         ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal ∗
         ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal ∗
         MappedSet st2.masterDom (OwnedMappedByte st2)) ∗
        MallocngRuntime maddrs tp ∗ (p ↦ₛ readBytesFromMap val' p req) ∗
        MallocngBlockToken (fineBaseGam γ) p req)) := by
    have hM1 : ((start - 4#64) ↦ₛ newSlotBs) ∗ ((g.metaPtr ↦ₛ g.metaBytes) ∗ rwTail) =
        (p ↦ₛ readBytesFromMap val' p req) ∗ ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal := by
      dsimp only [rwTail]; rw [← hExtMeta]; exact hAbsSlot
    have hLAdj : (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ ((start - 4#64) ↦ₛ newSlotBs) ∗
        ((g.metaPtr ↦ₛ g.metaBytes) ∗ envTail)) =
        (((start - 4#64) ↦ₛ newSlotBs) ∗ ((g.metaPtr ↦ₛ g.metaBytes) ∗ rwTail)) ∗
        (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
         MallocngRuntime maddrs tp ∗ MallocngBlockToken (fineBaseGam γ) p req ∗
         MallocngLiveAuth (fineBaseGam γ) liveMap' ∗ coreStatic) := by
      dsimp only [envTail]
      generalize MallocImplSavedRegs s0 (s0.sp - 80#64) = svA, ((start - 4#64) ↦ₛ newSlotBs) = nA,
        (g.metaPtr ↦ₛ g.metaBytes) = mA, stackFrameAt (s0.sp - 80#64) 624 = sfA,
        MallocngRoTablesA maddrs = roA, ghostMapAuth (fineAlignGam γ) alignMap0 = ga,
        MallocngRuntime maddrs tp = rtA, MallocngBlockToken (fineBaseGam γ) p req = tok,
        MallocngLiveAuth (fineBaseGam γ) liveMap' = gm, coreStatic = cS, rwTail = rT
      ac_rfl
    have hSt2F : st2.liveMap = liveMap' ∧ st2.ctx = st1.ctx ∧ st2.auxvPtr = st1.auxvPtr ∧ st2.auxvSnap = st1.auxvSnap :=
      ⟨rfl, rfl, rfl, rfl⟩
    rw [hLAdj, hM1]; dsimp only [coreStatic]
    rw [hPnEq, hMpEq, hSt2F.1, hSt2F.2.1, hSt2F.2.2.1, hSt2F.2.2.2]
    generalize (p ↦ₛ readBytesFromMap val' p req) = uA,
      ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal = rw2A,
      MallocngLiveAuth (fineBaseGam γ) liveMap' = gm,
      ghostMapAuth (fineAlignGam γ) alignMap0 = ga,
      MallocngBlockToken (fineBaseGam γ) p req = tok,
      MallocImplSavedRegs s0 (s0.sp - 80#64) = svA, stackFrameAt (s0.sp - 80#64) 624 = sfA,
      MallocngRoTablesA maddrs = roA, MallocngRuntime maddrs tp = rtA,
      (maddrs.ctx ↦ₛ st1.ctx.toBytes) = cA, (maddrs.lock ↦₃₂ 0#32) = lkA,
      (maddrs.replaced ↦₃₂ 0#32) = rpA, (maddrs.aaReplaced ↦₃₂ 0#32) = aaA,
      ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) = lbA,
      MallocngAuxvState (fineBaseGam γ) st1.auxvPtr st1.auxvSnap = axA,
      ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal = pnA,
      MappedSet st2.masterDom (OwnedMappedByte st2) = mpA
    ac_rfl
  change _ ⊢ MallocImplFineRawSuccessBody γ tp brkStart b ivs0 req s0 sf
  rw [hReasm]; unfold MallocImplFineRawSuccessBody
  refine sepConj_mono (savedRegs_entails_stackFrame s0) ?_
  refine Entails.trans ?_ (Entails.sepExists_intro p)
  refine Entails.trans ?_ (Entails.sepExists_intro (readBytesFromMap val' p req))
  refine Entails.trans ?_ (Entails.sepExists_intro st0)
  refine Entails.trans ?_ (Entails.sepExists_intro alignMap0)
  refine Entails.trans ?_ (Entails.sepExists_intro st2)
  refine Entails.trans ?_ (Entails.sepExists_intro g')
  refine Entails.trans ?_ (Entails.sepExists_intro idx)
  refine Entails.trans ?_ (Entails.sepExists_intro bCoarse)
  have hNoOrph2 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st2) s0.mem sf.mem :=
    mallocngNoOrphanMappings_congr_perm rfl hDynEq rfl hPermEq hNoOrph1
  have hwf2_sf : MallocngWF maddrs.base brkStart sf.brk bCoarse.liveCost bCoarse.peakCost st2 := by
    rw [hBrkEq]; exact hwf2
  have hGrp2 : Cost.GroupsGrpBound 128 st2.groups := by
    have hBr := hRawBranch p val' liveMap'
    dsimp only at hBr
    by_cases hSm : req ≤ MmapThresholdReq
    · rw [dite_eq_left hSm] at hBr
      obtain ⟨sc, pk, pkSC, pkSB, st1_w, g1_w, brk1, live1, peak1,
        _hSc48, _hScAlt, _hPk, hPres, _hwf1, hg1Mem, _hg1Sc, _hCl,
        hg1Same, _hg'Slots, hGs2⟩ := hBr
      have hG1 := groupsGrpBound_128_of_geom hPres.groups_geom
      rw [hGs2]
      exact hG1.map_ite g1_w.metaPtr fun hm hs => by
        rw [hg1Same.2.2.1] at hm ⊢; rw [hg1Same.2.1] at hs ⊢
        exact hG1 g1_w hg1Mem hm hs
    · rw [dite_eq_right hSm] at hBr
      obtain ⟨st1_w, _hIdx0, hSame1, hGs2, hg'Sc, _hg'Slots, _hg'Map⟩ := hBr
      have hG1 := groupsGrpBound_128_of_geom
        ((fineSameGroupsSlotKind_preserves_all (alignMap := alignMap0) hSame1).1 hInv0.groups_geom)
      rw [hGs2]
      exact hG1.cons fun _ hs => by rw [hg'Sc] at hs; omega
  have hCountIvs2 : MallocngCountIvsWF bCoarse (dynamicRootRegions st2) st2 :=
    synthCoarseBudget_countIvsWF st2 hGrp2
  have hFresh0 : st0.liveMap p = none := hLiveMap1 ▸ hFresh1
  have hLiveMap2 : st2.liveMap = st0.liveMap.insert p req 0 := by
    dsimp only [st2, mkReplaceSlotSt, liveMap']; rw [hLiveMap1]
  have hRawRel : MallocImplFineRawRel maddrs.base brkStart b ivs0 alignMap0 st0 st2 g' idx req p :=
    ⟨hInv0, hFresh0, hLiveMap2, hMetaLe1, hg'Mem,
      ⟨by simpa [g', mkReplaceSlotGroup] using hIdx,
       by dsimp [g', mkReplaceSlotGroup]; exact List.getElem_set_self _⟩,
      hPOffLe, hSc24_26,
      by simpa [g', mkReplaceSlotGroup] using hSc63_4115,
      hRawBranch p val' liveMap'⟩
  have hPure :
      sf.readReg64 .x0 = p ∧
      sf.tpidrEl0 = tp ∧ sf.brkStart = brkStart ∧
      MallocngBlockWf p req ∧
      (readBytesFromMap val' p req).length = req ∧
      MallocngNoOrphanMappings ivs0 (dynamicRootRegions st2) s0.mem sf.mem ∧
      MallocngWF maddrs.base brkStart sf.brk bCoarse.liveCost bCoarse.peakCost st2 ∧
      MallocngCountIvsWF bCoarse (dynamicRootRegions st2) st2 ∧
      MallocImplFineRawRel maddrs.base brkStart b ivs0 alignMap0 st0 st2 g' idx req p ∧
      (g'.isMmapped = true → readBytesFromMap val' p req = List.replicate req 0#8) :=
    ⟨hsf_x0, hsf_proc.2.2.1.trans htp0, hsf_proc.2.2.2.1.trans hbrkS0,
      hBlkWf, readBytesFromMap_length .., hNoOrph2, hwf2_sf, hCountIvs2, hRawRel, hZeroU⟩
  have hCoreEq :
      MallocngCoreStA (fineBaseGam γ) maddrs brkStart sf.brk bCoarse.liveCost bCoarse.peakCost st2 =
      (MallocngLiveAuth (fineBaseGam γ) st2.liveMap ∗ (maddrs.ctx ↦ₛ st2.ctx.toBytes) ∗
       (maddrs.lock ↦₃₂ 0#32) ∗ (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗
       ((maddrs.libc + 8#64) ↦₆₄ st2.auxvPtr) ∗
       MallocngAuxvState (fineBaseGam γ) st2.auxvPtr st2.auxvSnap ∗
       ByteMap st2.masterDom (OwnedRwByte st2) st2.byteVal ∗
       ProtNoneByteMap st2.masterDom (OwnedProtNoneByte st2) st2.byteVal ∗
       MappedSet st2.masterDom (OwnedMappedByte st2)) := by
    have hwf2' : MallocngWFInflight 0 maddrs.base brkStart sf.brk bCoarse.liveCost bCoarse.peakCost st2 := hwf2_sf
    dsimp only [MallocngCoreStA, MallocngCoreStInflightA]
    rw [propext ⟨fun _ => trivial, fun _ => hwf2'⟩, pure_true, emp_sepConj]
  rw [propext ⟨fun _ => trivial, fun _ => hPure⟩, pure_true, emp_sepConj, hCoreEq]
  exact Entails.refl _

set_option maxHeartbeats 400000 in
theorem mallocImpl_join_epilogue_raw_fine [MallocngMultiPlacement]
    {γ : GhostName} {tp brkStart : BitVec 64} {b : FineBudget} {bud : MallocngBudget}
    {ivs0 : List (BitVec 64 × Nat)} {alignMap0 : BitVec 64 → Option Nat}
    {req idx : Nat} {cycVal : BitVec 64}
    {st0 st1 : MallocngSt} {g : GroupDesc} {s0 s : State} {oom : State → SepProp}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s.mem)
    (hInv0 : MallocngFineInv 0 b ivs0 alignMap0 st0)
    (hLiveMap1 : st1.liveMap = st0.liveMap)
    (hMetaLe1 : st1.metaAreas.length ≤ fineMaxMetaAreas b)
    (hNoOrph1 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st1) s0.mem s.mem)
    (hwf1 : MallocngWFInflight 1 maddrs.base brkStart s.brk bud.liveCost bud.peakCost st1)
    (hNoRes : st1.reservedMetas = [])
    (hg : g ∈ st1.groups) (hIdx : idx < g.slots.length) (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hReqMax : req ≤ MallocngMaxAllocSize) (hFit0 : req + 4 ≤ g.stride)
    (hSc2 : 2 ≤ g.sc ∧ g.sc < 48 → nominalSlotCap (g.sc - 2) < max req 16)
    (hSc24 : g.sc = 24 → nominalSlotCap 23 < req)
    (hSc63 : g.sc = 63 → g.maplen * 4096 ≤ max req MallocngMinBlockCost + 8195)
    (hSc63_4115 : g.sc = 63 → g.maplen * 4096 ≤ req + 4115)
    (hZeroMm : g.isMmapped = true → ∀ a : BitVec 64, InRegion (g.slotStart idx) g.stride a → st1.byteVal a = 0#8)
    (hRawBranch : ∀ (p : BitVec 64) (val' : BitVec 64 → BitVec 8) (liveMap' : MallocngLiveMap),
      let effCost := max req MallocngMinBlockCost
      let g' := mkReplaceSlotGroup g idx g.availMask (.liveUser p req effCost)
      let st2 := mkReplaceSlotSt st1 g idx g.availMask (.liveUser p req effCost) val' liveMap'
      if hSmall : req ≤ MmapThresholdReq then
        ∃ (sc : Nat) (pk : List Nat) (pkSC pkSB : Nat)
          (st1_w : MallocngSt) (g1_w : GroupDesc)
          (brk1 : BitVec 64) (live1 peak1 : Nat),
          let _ := hSmall
          sc < 48 ∧
          (sc = sizeToClassUnits ((req + 3) / 16) ∨
           sc = coarseAlt (sizeToClassUnits ((req + 3) / 16))) ∧
          (pk.length = 48 ∧
           (∀ k < 48, liveSlotsInClass st0 k ≤ pk.getD k 0) ∧
           (∀ k < 48, (allGroups st0 k).length ≤ gBound pk k) ∧
           (∀ ch < 48, ∀ pSc < 48, (nestedEdge st0 ch pSc).length ≤ edgeBound pk ch pSc) ∧
           (∀ k < 48, rootBytes st0 k ≤ rBound pk k) ∧
           (straddle63Groups st0).length ≤ pkSC ∧
           straddle63Bytes st0 ≤ pkSB ∧
           linForm grpWtS pk + FineScale * pkSC ≤ b.cumSmallGroupsS ∧
           linForm slotWt pk + pkSB ≤ b.cumSmallBytes) ∧
          AllocSlotInvPres sc pk alignMap0 st0 st1_w ∧
          MallocngWFInflight 1 maddrs.base brkStart brk1 live1 peak1 st1_w ∧
          g1_w ∈ st1_w.groups ∧ g1_w.sc = sc ∧
          (∃ hIdx1 : idx < g1_w.slots.length, g1_w.slots[idx]'hIdx1 = .claimed) ∧
          FineGroupSameGeom g' g1_w ∧
          g'.slots = g1_w.slots.set idx (.liveUser p req effCost) ∧
          st2.groups = st1_w.groups.map (fun h => if h.metaPtr == g1_w.metaPtr then g' else h)
      else
        ∃ st1_w : MallocngSt,
          idx = 0 ∧
          FineSameGroupsSlotKind st1_w.groups st0.groups ∧
          st2.groups = g' :: st1_w.groups ∧
          g'.sc = 63 ∧
          g'.slots = [.liveUser p req effCost] ∧
          g'.maplen * 4096 ≤ req + 4115)
    (htp0 : s0.tpidrEl0 = tp) (hbrkS0 : s0.brkStart = brkStart)
    (hDelta : MallocngMappedDelta 16 (fineStepReserve (.alloc req) b) s0.mem s.mem)
    (hpc : s.pc = mbase 9 + miOff_call_unlock) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 80#64) (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hProc : MallocngProcPreserved s0 s) (hcsHi : MallocImplUntouchedCS s0 s)
    (hx0 : s.readReg64 (.gpr 0#5) = maddrs.lock)
    (hx19 : s.readReg64 (.gpr 19#5) = cycVal)
    (hx20 : s.readReg64 (.gpr 20#5) = BitVec.ofNat 64 req)
    (hx21 : s.readReg64 (.gpr 21#5) = BitVec.ofNat 64 idx)
    (hx22 : s.readReg64 (.gpr 22#5) = g.metaPtr)
    (hx23 : s.readReg64 (.gpr 23#5) = BitVec.ofNat 64 idx) :
    SepWP (mallocngBlockProg mmpl 9 msvc) (s0.readReg64 (.gpr 30#5)) s
      (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
       MallocngRoTablesA maddrs ∗
       ghostMapAuth (fineAlignGam γ) alignMap0 ∗
       MallocngCoreStInflightA 1 (fineBaseGam γ) maddrs brkStart s.brk bud.liveCost bud.peakCost st1 ∗
       MallocngRuntime maddrs tp)
      (fun sf P_f =>
        (P_f ⊢ MallocImplFineRawSuccessPost γ tp brkStart b ivs0 req s0 sf) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      oom := by
  rw [mallocngBlockProg_eq_b09]
  generalize hb_eq : mbase 9 = b9 at hpc ⊢
  have hb : BlkBase 9 b9 := hb_eq.symm
  refine SepWP.mono (oom := fun _ => ⌜False⌝) (post := fun sf P_f =>
    sf.sp = s0.sp ∧ sf.brk = s.brk ∧ sf.mem.perm = s.mem.perm ∧
    MallocngProcPreserved s0 sf ∧ CalleeSavedPreserved s0 sf ∧
    (P_f ⊢ MallocImplFineRawSuccessBody γ tp brkStart b ivs0 req s0 sf)) ?_ ?_
  · have hgw := hwf1.groups_wf g hg
    obtain ⟨hTst0, hZ, hNZ⟩ := getStride_props hgw
    obtain ⟨_, hStrSubReq, hStrSub4, hShr4, hMadd, hW1Fit, _⟩ := enframe_bv_props hgw hIdx hFit0 hSc63
    have hSlot0 : ((readBytesFromMap st1.byteVal (g.slotStart idx - 4#64) g.stride)[0]?).getD 0#8 = 0#8 := by
      have hSW := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx
      have h0lt : 0 < (readBytesFromMap st1.byteVal (g.slotStart idx - 4#64) g.stride).length := by
        rw [readBytesFromMap_length]; have := (group_stride_pos_and_align hgw).1; omega
      rw [List.getElem?_eq_getElem h0lt, Option.getD_some, readBytesFromMap_getElem _ _ _ 0 h0lt]
      simpa using hSW.1
    obtain ⟨hMemMeta, _, _, _, _, hPkMeta, _⟩ := metaBytes_ops g 0 0#32 .claimed
    have hExtSlot := slot_extract hwf1 hNoRes hg hIdx hClaimed
    have hExtMeta := meta_and_slot_extract hwf1 hNoRes hg hIdx hClaimed
    let start := g.slotStart idx
    let slotBs := readBytesFromMap st1.byteVal (start - 4#64) g.stride
    let rwTail := ByteMap st1.masterDom
      (fun a => (OwnedRwByte st1 a ∧ ¬ InRegion (start - 4#64) g.stride a) ∧ ¬ InRegion g.metaPtr 40 a) st1.byteVal
    let roTail := (maddrs.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
      (maddrs.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
      (maddrs.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
      (maddrs.debruijnAlloc ↦ᵣ mallocngDebruijn32Table)
    let coreRest := MallocngLiveAuth (fineBaseGam γ) st1.liveMap ∗ (maddrs.ctx ↦ₛ st1.ctx.toBytes) ∗
      (maddrs.replaced ↦₃₂ 0#32) ∗ (maddrs.aaReplaced ↦₃₂ 0#32) ∗ ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) ∗
      MallocngAuxvState (fineBaseGam γ) st1.auxvPtr st1.auxvSnap ∗ rwTail ∗
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∗
      MappedSet st1.masterDom (OwnedMappedByte st1)
    let unlockFrame := MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
      (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ roTail ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
      ((start - 4#64) ↦ₛ slotBs) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗
      coreRest ∗ MallocngRuntime maddrs tp
    have hRoSplit : MallocngRoTablesA maddrs = ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ roTail) := rfl
    have hPreInit : (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
        MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
        MallocngCoreStInflightA 1 (fineBaseGam γ) maddrs brkStart s.brk bud.liveCost bud.peakCost st1 ∗
        MallocngRuntime maddrs tp) = ((maddrs.lock ↦₃₂ 0#32) ∗ unlockFrame) := by
      rw [hRoSplit]
      dsimp only [MallocngCoreStInflightA, unlockFrame, coreRest, start, slotBs, rwTail]
      rw [propext ⟨fun _ => trivial, fun _ => hwf1⟩, pure_true, emp_sepConj, hExtSlot, hExtMeta]
      generalize ((g.slotStart idx - 4#64) ↦ₛ readBytesFromMap st1.byteVal (g.slotStart idx - 4#64) g.stride) = pS,
        (g.metaPtr ↦ₛ g.metaBytes) = pM,
        ByteMap st1.masterDom (fun a => (OwnedRwByte st1 a ∧ ¬ InRegion (g.slotStart idx - 4#64) g.stride a) ∧ ¬ InRegion g.metaPtr 40 a) st1.byteVal = pRw,
        (maddrs.ctx ↦ₛ st1.ctx.toBytes) = pCtx,
        (maddrs.lock ↦₃₂ 0#32) = pLk,
        (maddrs.replaced ↦₃₂ 0#32) = pRp,
        (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
        ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) = pLb,
        (maddrs.sizeClasses ↦ᵣ sizeClassBytes) = pSc,
        roTail = pRo, ghostMapAuth (fineAlignGam γ) alignMap0 = pGa,
        MallocngLiveAuth (fineBaseGam γ) st1.liveMap = pGm,
        MallocngAuxvState (fineBaseGam γ) st1.auxvPtr st1.auxvSnap = pAx,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pPn,
        MappedSet st1.masterDom (OwnedMappedByte st1) = pMp,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
        MallocngRuntime maddrs tp = pRt
      ac_rfl
    rw [hPreInit]
    have hSpAl : s.spAligned = true := by
      dsimp [State.spAligned]; rw [hsp]; exact sp_sub_80_aligned hsp_align
    wp_step
    have hunlock := placed_unlockNoop_perm_ok (P := blkPC_b09.rebase b9 (fun _ => none)) maddrs.lock
    have hBl23 : mbase 23 = b9 + miOff_call_unlock + (mbase 23 - b9 - miOff_call_unlock) := by bv_arith
    rw [hBl23] at hunlock
    refine SepWP.call_subroutine_frame (F := unlockFrame) (x := ()) (ret_pc := b9 + miOff_after_unlock)
      hunlock rfl (by simp [arm64_norm, hrun]) (by simpa [State.spAligned, arm64_norm] using hSpAl)
      (by dsimp only [miOff_call_unlock, miOff_after_unlock, Reg.lr]; simp [arm64_norm])
      (fun R' hm => by
        rw [sepConj_assoc] at hm
        refine Satisfies.mono (sepConj_mono_left ?_) hm
        dsimp only [withCL]
        rw [sepConj_comm]
        exact Entails.pure_right hcl (Entails.pure_right (by simpa [arm64_norm] using hx0) (Entails.refl _)))
      (fun R' sf _ hp => by dsimp only [withCL] at hp; exact not_satisfies_false_sepConj hp)
      (fun R' code sf _ he => by dsimp only [withCL] at he; exact not_satisfies_false_sepConj he)
      (fun su hpc_u hrun_u hsp_u hcs_u => ?_)
    dsimp only [withCL]
    rw [sepConj_assoc, sepConj_assoc]
    apply SepWP.pure_elim; rintro ⟨hProc_u0, hbrk_u, hperm_u⟩
    apply SepWP.weaken_pre (sepConj_mono_right (Entails.pure_left fun _ => Entails.refl unlockFrame))
    have hProc_u : MallocngProcPreserved s su :=
      ⟨hProc_u0.1, hProc_u0.2.1, hProc_u0.2.2.1, hProc_u0.2.2.2.1,
       hProc_u0.2.2.2.2.1, hProc_u0.2.2.2.2.2.1,
       by simpa [sigActions_setPC, sigActions_writeReg64] using hProc_u0.2.2.2.2.2.2⟩
    have hsp_su : su.sp = s0.sp - 80#64 := hsp_u.trans hsp
    have hProc_su : MallocngProcPreserved s0 su := procPres_trans hProc hProc_u
    have hcs_su : MallocImplUntouchedCS s0 su :=
      untouchedCS_step hcsHi (hcs_u.2.2.2.2.2.2.2.1.trans (by simp))
        (hcs_u.2.2.2.2.2.2.2.2.1.trans (by simp)) (hcs_u.2.2.2.2.2.2.2.2.2.1.trans (by simp))
        (by simpa [calleeSavedVRegs] using hcs_u.2.2.2.2.2.2.2.2.2.2.2)
    have hPreG : ((maddrs.lock ↦₃₂ 0#32) ∗ unlockFrame) =
        ((g.metaPtr ↦ₛ g.metaBytes) ∗ (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗
         (((start - 4#64) ↦ₛ slotBs) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
          stackFrameAt (s0.sp - 80#64) 624 ∗ roTail ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
          coreRest ∗ MallocngRuntime maddrs tp)) := by
      dsimp only [unlockFrame]
      generalize ((start - 4#64) ↦ₛ slotBs) = pS, (g.metaPtr ↦ₛ g.metaBytes) = pM,
        (maddrs.lock ↦₃₂ 0#32) = pLk, (maddrs.sizeClasses ↦ᵣ sizeClassBytes) = pSc, roTail = pRo,
        ghostMapAuth (fineAlignGam γ) alignMap0 = pGa, coreRest = pCr,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv, MallocngRuntime maddrs tp = pRt
      ac_rfl
    rw [hPreG]
    refine SepWP.seq_entails_emp
      (getStride_step_fine hb (by simp [GroupDesc.metaBytes]) hPkMeta hTst0
        (fun h => ⟨(hZ h).2.1, (hZ h).2.2⟩) hNZ hpc_u hrun_u hsp_su hProc_su hcs_su
        (hcs_u.1.trans (by simpa using hx19)) (hcs_u.2.1.trans (by simpa using hx20))
        (hcs_u.2.2.1.trans (by simpa using hx21)) (hcs_u.2.2.2.1.trans (by simpa using hx22))
        (hcs_u.2.2.2.2.1.trans (by simpa using hx23))) ?_
    rintro s1 hpc1 hrun1 ⟨hsp1, hbrk1, hperm1, hProc1, hcs1, hx4_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1⟩
    have hPreH : ((g.metaPtr ↦ₛ g.metaBytes) ∗ (maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗
        (((start - 4#64) ↦ₛ slotBs) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
         stackFrameAt (s0.sp - 80#64) 624 ∗ roTail ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
         coreRest ∗ MallocngRuntime maddrs tp)) =
        (((start - 4#64) ↦ₛ slotBs) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗
         ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
          stackFrameAt (s0.sp - 80#64) 624 ∗ roTail ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
          coreRest ∗ MallocngRuntime maddrs tp)) := by
      generalize ((start - 4#64) ↦ₛ slotBs) = pS, (g.metaPtr ↦ₛ g.metaBytes) = pM,
        (maddrs.lock ↦₃₂ 0#32) = pLk, (maddrs.sizeClasses ↦ᵣ sizeClassBytes) = pSc, roTail = pRo,
        ghostMapAuth (fineAlignGam γ) alignMap0 = pGa, coreRest = pCr,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv, MallocngRuntime maddrs tp = pRt
      ac_rfl
    rw [hPreH]
    refine SepWP.seq_entails_emp
      (enframe_head_step_fine hb hFit0 (readBytesFromMap_length ..) (by simp [GroupDesc.metaBytes])
        (by rw [hMemMeta]; rfl) hSlot0 hStrSubReq hStrSub4 hMadd
        hpc1 hrun1 hsp1 hProc1 hcs1 hx4_1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1) ?_
    rintro s2 hpc2 hrun2 ⟨hsp2, hbrk2, hperm2, hProc2, hcs2, hx0_2, hx1_2, hx2_2, hx3_2, hx4_2, hx5_2, hx6_2, hx20_2, hx22_2, hx23_2⟩
    refine SepWP.seq_entails_emp
      (enframe_mask_step_fine hb hShr4 hW1Fit hpc2 hrun2 hsp2 hProc2 hcs2
        hx0_2 hx1_2 hx2_2 hx3_2 hx4_2 hx5_2 hx6_2 hx20_2 hx22_2 hx23_2) ?_
    rintro s3 hpc3 hrun3 ⟨off, hOff255, hFit, hsp3, hbrk3, hperm3, hProc3, hcs3, hx0_3, hx1_3, hx2_3, hx4_3, hx6_3, hx20_3, hx22_3, hx23_3⟩
    have hBrk3 : s3.brk = s.brk := hbrk3.trans (hbrk2.trans (hbrk1.trans hbrk_u))
    have hPerm3 : s3.mem.perm = s.mem.perm := hperm3.trans (hperm2.trans (hperm1.trans hperm_u))
    have hwf3 : MallocngWFInflight 1 maddrs.base brkStart s3.brk bud.liveCost bud.peakCost st1 := hBrk3 ▸ hwf1
    have hNoOrph3 : MallocngNoOrphanMappings ivs0 (dynamicRootRegions st1) s0.mem s3.mem :=
      mallocngNoOrphanMappings_congr_perm rfl rfl rfl hPerm3 hNoOrph1
    have hPreF : (((start - 4#64) ↦ₛ slotBs) ∗ (g.metaPtr ↦ₛ g.metaBytes) ∗
        ((maddrs.sizeClasses ↦ᵣ sizeClassBytes) ∗ (maddrs.lock ↦₃₂ 0#32) ∗ MallocImplSavedRegs s0 (s0.sp - 80#64) ∗
         stackFrameAt (s0.sp - 80#64) 624 ∗ roTail ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
         coreRest ∗ MallocngRuntime maddrs tp)) =
        (MallocImplSavedRegs s0 (s0.sp - 80#64) ∗ stackFrameAt (s0.sp - 80#64) 624 ∗
         MallocngRoTablesA maddrs ∗ ghostMapAuth (fineAlignGam γ) alignMap0 ∗
         MallocngCoreStInflightA 1 (fineBaseGam γ) maddrs brkStart s3.brk bud.liveCost bud.peakCost st1 ∗
         MallocngRuntime maddrs tp) := by
      rw [hRoSplit]
      dsimp only [MallocngCoreStInflightA, coreRest, start, slotBs, rwTail]
      rw [propext ⟨fun _ => trivial, fun _ => hwf3⟩, pure_true, emp_sepConj, hExtSlot, hExtMeta]
      generalize ((g.slotStart idx - 4#64) ↦ₛ readBytesFromMap st1.byteVal (g.slotStart idx - 4#64) g.stride) = pS,
        (g.metaPtr ↦ₛ g.metaBytes) = pM,
        ByteMap st1.masterDom (fun a => (OwnedRwByte st1 a ∧ ¬ InRegion (g.slotStart idx - 4#64) g.stride a) ∧ ¬ InRegion g.metaPtr 40 a) st1.byteVal = pRw,
        (maddrs.ctx ↦ₛ st1.ctx.toBytes) = pCtx,
        (maddrs.lock ↦₃₂ 0#32) = pLk,
        (maddrs.replaced ↦₃₂ 0#32) = pRp,
        (maddrs.aaReplaced ↦₃₂ 0#32) = pAa,
        ((maddrs.libc + 8#64) ↦₆₄ st1.auxvPtr) = pLb,
        (maddrs.sizeClasses ↦ᵣ sizeClassBytes) = pSc,
        roTail = pRo, ghostMapAuth (fineAlignGam γ) alignMap0 = pGa,
        MallocngLiveAuth (fineBaseGam γ) st1.liveMap = pGm,
        MallocngAuxvState (fineBaseGam γ) st1.auxvPtr st1.auxvSnap = pAx,
        stackFrameAt (s0.sp - 80#64) 624 = pSf,
        ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal = pPn,
        MappedSet st1.masterDom (OwnedMappedByte st1) = pMp,
        MallocImplSavedRegs s0 (s0.sp - 80#64) = pSv,
        MallocngRuntime maddrs tp = pRt
      ac_rfl
    rw [hPreF]
    subst hb_eq
    rw [← mallocngBlockProg_eq_b09]
    exact SepWP.mono (mallocImpl_enframe_finish_raw_fine hInv0 hLiveMap1 hMetaLe1 hNoOrph3 hwf3 hNoRes
      hg hIdx hClaimed hReqMax hFit0 hOff255 hFit hSc2 hSc24 hSc63 hSc63_4115 hZeroMm hRawBranch htp0 hbrkS0
      hpc3 hrun3 hsp3 hsp_align hProc3 hcs3 hx0_3 hx1_3 hx2_3 hx4_3 hx6_3 hx20_3 hx22_3 hx23_3)
      (fun _ _ _ _ ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2.trans hBrk3, h3.trans hPerm3, h4, h5, h6⟩)
  · rintro sf P_f _ _ ⟨hsf_sp, _, hsf_perm, hsf_proc, hsf_cs, hPf⟩
    have hDeltaF : MallocngMappedDelta 16 (fineStepReserve (.alloc req) b) s0.mem sf.mem :=
      mappedDelta_congr_perm_right hDelta hsf_perm
    refine ⟨Entails.trans hPf ?_, hsf_sp, hsf_cs⟩
    dsimp only [MallocImplFineRawSuccessPost]
    exact Entails.pure_right ⟨hsf_proc, hDeltaF⟩ (Entails.refl _)

end LibsignalBinary.Heap.Fine
