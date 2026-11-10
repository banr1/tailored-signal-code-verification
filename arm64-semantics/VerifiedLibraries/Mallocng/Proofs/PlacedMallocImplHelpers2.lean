/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedMallocImplHelpers1
public import VerifiedLibraries.Mallocng.Proofs.InternalPlaced
public import VerifiedLibraries.Mallocng.Proofs.LiveUserBandHelpers

/-!
# Slot-Replacement and Accounting Helpers for Placed Malloc

Internal contracts (`AllocMetaPlacedFullStmt`, `AllocSlotPlacedFullStmt`, `MallocngMetaCountInv`),
`MallocngNoOrphanMappings` and `MallocngCountIvsWF` accounting lemmas, and slot-replacement
well-formedness (`replaceSlot_wf_core`, `claimFreeAvail_absorb`).
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

/-! ## Internal Contracts and Accounting Bridges -/

/-- Bounds `st.metaAreas.length` by `1 + (88 + 8 * b.peakCount) / 101` under `MallocngCountIvsWF`. -/
def MallocngMetaCountInv : Prop :=
  ∀ (b : MallocngBudget) (ivs : List (BitVec 64 × Nat)) (st : MallocngSt),
    MallocngCountIvsWF b ivs st →
      st.metaAreas.length ≤ 1 + (88 + 8 * b.peakCount) / 101

theorem mallocngMetaCountInv_holds : MallocngMetaCountInv :=
  fun _ _ _ h => h.2.2.2.2.1

/-- Internal contract for placed `__malloc_alloc_meta()` (`blk07`). -/
def AllocMetaPlacedFullStmt : Prop :=
  ∀ [MallocngMultiPlacement]
    (inflight : Nat) (_hInflight : inflight ≤ 7)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat) (st : MallocngSt)
    (_hCount : totalLiveCount st ≤ peakCount),
    subroutine_ok (mallocngBlockProg mmpl 7 msvc) (mbase 7) (withCL mmpl {
      pre := fun (_ : Unit) s0 =>
        ⌜s0.tpidrEl0 = tp ∧ s0.brkStart = brkStart⌝ ∗
        stackFrame s0 224 ∗
        MallocngCoreStInflightA inflight γ maddrs brkStart s0.brk liveCost peakCost st ∗
        MallocngRuntime maddrs tp
      post := fun _ s0 sf =>
        ∃∗ st' : MallocngSt,
        ∃∗ m : BitVec 64,
          ⌜MallocngProcPreserved s0 sf ∧
           sf.readReg64 .x0 = m ∧ m ≠ 0#64 ∧
           4096 ≤ m.toNat ∧ m.toNat % 8 = 0 ∧ m.toNat + 40 ≤ 2 ^ 48 ∧
           m ∉ st.reservedMetas ∧
           st'.reservedMetas = m :: st.reservedMetas ∧
           st'.groups = st.groups ∧
           st'.activeLists = st.activeLists ∧
           st'.liveMap = st.liveMap ∧
           totalLiveCount st' = totalLiveCount st ∧
           st'.metaAreas.length ≤ max st.metaAreas.length (1 + (88 + 8 * peakCount) / 101) ∧
           st'.ctx.active = st.ctx.active ∧
           st'.ctx.usageByClass = st.ctx.usageByClass ∧
           st'.ctx.unmapSeq = st.ctx.unmapSeq ∧
           st'.ctx.bounces = st.ctx.bounces ∧
           st'.ctx.seq = st.ctx.seq ∧
           (∀ g ∈ st.groups, ∀ a : BitVec 64,
             (InRegion g.metaPtr 40 a ∨ InRegion g.mem g.totalBytes a) →
               st'.byteVal a = st.byteVal a) ∧
           MallocngNoOrphanMappings (dynamicRootRegions st) (dynamicRootRegions st') s0.mem sf.mem ∧
           MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) s0.mem sf.mem⌝ ∗
          stackFrame s0 224 ∗
          MallocngRuntime maddrs tp ∗
          (m ↦ₛ List.replicate 40 0#8) ∗
          MallocngCoreStInflightA (inflight + 1) γ maddrs brkStart sf.brk liveCost peakCost st'
      onOom := fun _ s0 sf =>
        ⌜MallocngPlacedOomCond msvc 1 (allocMetaPlacedByteBound peakCount) s0 sf⌝
    })

/-- Internal contract for placed `alloc_slot(sc, req)` (`blk08`). -/
def AllocSlotPlacedFullStmt : Prop :=
  ∀ [MallocngMultiPlacement]
    (sc req inflight : Nat)
    (_hSc : sc < 48)
    (_hReq : req ≤ nominalSlotCap sc)
    (_hInflight : inflight + allocSlotDepthBound sc ≤ 6)
    (γ : GhostName) (tp brkStart : BitVec 64)
    (liveCost peakCost peakCount : Nat) (st : MallocngSt)
    (_hCount : totalLiveCount st ≤ peakCount),
    subroutine_ok (mallocngBlockProg mmpl 8 msvc) (mbase 8) (withCL mmpl {
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
    })

theorem mallocngNoOrphanMappings_of_perm_eq {ivs0 ivsf : List (BitVec 64 × Nat)}
    {m0 mf : Memory} (hIvs : ivsf = ivs0) (hPerm : mf.perm = m0.perm) :
    MallocngNoOrphanMappings ivs0 ivsf m0 mf := by
  subst hIvs
  intro a hm hsrc
  rcases hsrc with hf | hin
  · rw [hPerm, hf] at hm; cases hm
  · exact hin

theorem mallocngNoOrphanMappings_congr_perm {ivs0 ivs0' ivsf ivsf' : List (BitVec 64 × Nat)}
    {m0 m0' mf mf' : Memory}
    (hi0 : ivs0' = ivs0) (hif : ivsf = ivsf')
    (h0 : m0'.perm = m0.perm) (hf : mf.perm = mf'.perm)
    (hno : MallocngNoOrphanMappings ivs0' ivsf' m0' mf') :
    MallocngNoOrphanMappings ivs0 ivsf m0 mf := by
  subst hi0; subst hif
  intro a ha hsrc
  rw [hf] at ha
  rw [← h0] at hsrc
  exact hno a ha hsrc

theorem mallocngNoOrphanMappings_large_mmap {ivs0 ivs1 : List (BitVec 64 × Nat)}
    {mb : BitVec 64} {len : Nat} {m0 m1 m2 m3 mf : Memory}
    (hMmap : ∀ a : BitVec 64, (m1.perm a).mapped = true →
      (m0.perm a).mapped = true ∨ InRegion mb len a)
    (h12 : m2.perm = m1.perm)
    (hMeta : MallocngNoOrphanMappings ivs0 ivs1 m2 m3)
    (h3f : mf.perm = m3.perm)
    {ivsf : List (BitVec 64 × Nat)}
    (hSub1 : ∀ iv ∈ ivs1, iv ∈ ivsf)
    (hMbIn : (mb, len) ∈ ivsf) :
    MallocngNoOrphanMappings ivs0 ivsf m0 mf := by
  intro a hmf hsrc
  have hm3 : (m3.perm a).mapped = true := by rwa [← h3f]
  by_cases hm2 : (m2.perm a).mapped = false
  · obtain ⟨iv, hiv, haIv⟩ := hMeta a hm3 (Or.inl hm2)
    exact ⟨iv, hSub1 iv hiv, haIv⟩
  · have hm2t : (m2.perm a).mapped = true := by cases h : (m2.perm a).mapped <;> simp_all
    have hm1t : (m1.perm a).mapped = true := by rwa [← h12]
    rcases hsrc with hm0f | hIn0
    · rcases hMmap a hm1t with hm0t | hInMb
      · rw [hm0t] at hm0f; cases hm0f
      · exact ⟨(mb, len), hMbIn, hInMb⟩
    · obtain ⟨iv, hiv, haIv⟩ := hMeta a hm3 (Or.inr hIn0)
      exact ⟨iv, hSub1 iv hiv, haIv⟩

private theorem pow2_sub_ge_twelve : ∀ m : Nat, 4 ≤ m → 12 ≤ 2 ^ m - m := by
  intro m hm
  obtain ⟨d, rfl⟩ : ∃ d, m = 4 + d := ⟨m - 4, by omega⟩
  clear hm
  induction d with
  | zero => decide
  | succ k ih =>
    have hPow : 2 ^ (4 + (k + 1)) = 2 * 2 ^ (4 + k) := by
      rw [← Nat.add_assoc, Nat.pow_succ, Nat.mul_comm]
    omega

theorem dynamicRootRegions_length_le_of_metaBound {base brkStart brk : BitVec 64}
    {liveCost peakCost peakCount : Nat} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    (hLiveCnt : totalLiveCount st ≤ peakCount)
    (hMetaLe : st.metaAreas.length ≤ 1 + (88 + 8 * peakCount) / 101) :
    (dynamicRootRegions st).length ≤ 48 + 2 * peakCount := by
  let rootGs := st.groups.filter (fun g => decide (0 < g.maplen))
  have hDynLen :
      (dynamicRootRegions st).length =
      (st.metaAreas.length + st.guardPages.length + st.availMetaPages.length) +
      rootGs.length := by
    unfold dynamicRootRegions
    dsimp only [rootGs]
    simp only [List.length_append, List.length_map]
  let empRootGs := rootGs.filter GroupDesc.isEmpty
  let nonEmpRootGs := rootGs.filter (fun g => !GroupDesc.isEmpty g)
  have hRootSplit : rootGs.length = empRootGs.length + nonEmpRootGs.length := by
    dsimp only [empRootGs, nonEmpRootGs]
    induction rootGs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.filter]
      cases GroupDesc.isEmpty x <;> simp only [Bool.not_false, Bool.not_true, List.length_cons] <;> omega
  have hSubEmp : ∀ m ∈ empRootGs.map (·.metaPtr),
      m ∈ (st.groups.filter (·.isEmpty)).map (·.metaPtr) := by
    intro m hm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm
    have ⟨hgRoot, hE⟩ := List.mem_filter.mp hg
    exact List.mem_map_of_mem (List.mem_filter.mpr ⟨(List.mem_filter.mp hgRoot).1, hE⟩)
  have hEmpNd : (empRootGs.map (·.metaPtr)).Nodup :=
    (((List.filter_sublist.trans List.filter_sublist).map _)).nodup hwf.groups_nodup.1
  have hEmpRootLen : empRootGs.length ≤ 32 := by
    have h1 := nodup_length_le_of_subset hEmpNd hSubEmp
    have h2 := emptyGroups_length_le hwf
    simp only [List.length_map] at h1
    omega
  let rootMeta : GroupDesc → BitVec 64 := fun h => iterParentMeta st 7 h.metaPtr
  let groupCnt : GroupDesc → Nat := fun h => (h.slots.map slotLiveCount).sum
  have hClaim0 : totalClaimedSlots st = 0 := by have h := hwf.inflight_wf; omega
  have hEachNonEmp : ∀ g ∈ nonEmpRootGs,
      1 ≤ ((st.groups.filter fun h => rootMeta h == g.metaPtr).map groupCnt).sum := by
    intro g hg
    have ⟨hgRoot, hgNotEB⟩ := List.mem_filter.mp hg
    have ⟨hgIn, hgMapPosB⟩ := List.mem_filter.mp hgRoot
    have hgMapPos : 0 < g.maplen := of_decide_eq_true hgMapPosB
    have hgNotE : g.isEmpty = false := by simpa using hgNotEB
    have hParNone : g.parentMeta = none := (hwf.groups_wf g hgIn).2.2.2.2.2.2.2.2.2.2.1.mp hgMapPos
    have hFixG : parentMetaStep st g.metaPtr = g.metaPtr := by
      simp [parentMetaStep, findGroupByMeta_of_mem hwf.groups_nodup.1 hgIn, hParNone]
    obtain ⟨leaf, hleaf, d, hdLt8, hLeafDir, hIterD, _⟩ :=
      descend_nonempty_group hwf hgIn hgNotE
    have hRootEq : rootMeta leaf = g.metaPtr := by
      show iterParentMeta st 7 leaf.metaPtr = g.metaPtr
      have hdEq : 7 = d + (7 - d) := by omega
      rw [hdEq, iterParentMeta_add, hIterD]
      exact iterParentMeta_fixed hFixG (7 - d)
    unfold GroupDesc.hasDirectLeaf at hLeafDir
    obtain ⟨s, hsMem, hsDir⟩ := List.any_eq_true.mp hLeafDir
    have hLeSum : ∀ {n : Nat} {ns : List Nat}, n ∈ ns → n ≤ ns.sum := by
      intro n ns hMem; obtain ⟨as, bs, rfl⟩ := List.append_of_mem hMem; simp; omega
    have hsNotClaimed : s ≠ .claimed := by
      intro hEq; subst hEq
      have hIn : SlotState.claimed ∈ leaf.slots.filter SlotState.isClaimed :=
        List.mem_filter.mpr ⟨hsMem, rfl⟩
      obtain ⟨as, bs, hEqL⟩ := List.append_of_mem hIn
      have h1 : 1 ≤ (leaf.slots.filter SlotState.isClaimed).length := by rw [hEqL]; simp; omega
      have h2 : (leaf.slots.filter SlotState.isClaimed).length ≤ totalClaimedSlots st :=
        hLeSum (List.mem_map_of_mem hleaf)
      omega
    rcases hS : s with _ | _ | _ | _ | ⟨userPtr, reqSize, effCost⟩
    · simp [hS] at hsDir
    · simp [hS] at hsDir
    · exact False.elim (hsNotClaimed hS)
    · simp [hS] at hsDir
    · have h1InLeaf : 1 ≤ groupCnt leaf := by
        have hMem1 : 1 ∈ leaf.slots.map slotLiveCount := by
          rw [hS] at hsMem
          exact List.mem_map.mpr ⟨.liveUser userPtr reqSize effCost, hsMem, rfl⟩
        exact hLeSum hMem1
      have hLeafInFiber : groupCnt leaf ∈
          (st.groups.filter fun h => rootMeta h == g.metaPtr).map groupCnt :=
        List.mem_map_of_mem (List.mem_filter.mpr ⟨hleaf, beq_iff_eq.mpr hRootEq⟩)
      exact Nat.le_trans h1InLeaf (hLeSum hLeafInFiber)
  have hNonEmpMetaNd : (nonEmpRootGs.map (·.metaPtr)).Nodup :=
    (((List.filter_sublist.trans List.filter_sublist).map _)).nodup hwf.groups_nodup.1
  have hFiberBound :
      (nonEmpRootGs.map fun g =>
        ((st.groups.filter fun h => rootMeta h == g.metaPtr).map groupCnt).sum).sum ≤
      (st.groups.map groupCnt).sum := by
    have hMapEq :
        (nonEmpRootGs.map fun g =>
          ((st.groups.filter fun h => rootMeta h == g.metaPtr).map groupCnt).sum) =
        ((nonEmpRootGs.map (·.metaPtr)).map fun m =>
          ((st.groups.filter fun h => rootMeta h == m).map groupCnt).sum) := by
      rw [List.map_map]; rfl
    rw [hMapEq]
    exact sum_filter_beq_le_of_nodup rootMeta groupCnt st.groups hNonEmpMetaNd
  have hCntTotal : (st.groups.map groupCnt).sum = totalLiveCount st := rfl
  have hNonEmpLenLe : nonEmpRootGs.length ≤ totalLiveCount st := by
    have hMinSum : (nonEmpRootGs.map fun _ => 1).sum ≤
        (nonEmpRootGs.map fun g =>
          ((st.groups.filter fun h => rootMeta h == g.metaPtr).map groupCnt).sum).sum := by
      have hGen : ∀ (xs : List GroupDesc), (∀ g ∈ xs,
          1 ≤ ((st.groups.filter fun h => rootMeta h == g.metaPtr).map groupCnt).sum) →
          (xs.map fun _ => 1).sum ≤
            (xs.map fun g =>
              ((st.groups.filter fun h => rootMeta h == g.metaPtr).map groupCnt).sum).sum := by
        intro xs hxs
        induction xs with
        | nil => simp
        | cons x rest ih =>
          simp only [List.map_cons, List.sum_cons]
          have hx := hxs x List.mem_cons_self
          have hr := ih (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
          omega
      exact hGen nonEmpRootGs hEachNonEmp
    have hConst1 : (nonEmpRootGs.map fun _ => 1).sum = nonEmpRootGs.length := by
      clear hMinSum
      induction nonEmpRootGs with
      | nil => rfl
      | cons _ rest ih => simp [ih]; omega
    omega
  by_cases hShift0 : st.ctx.metaAllocShift = 0#64
  · obtain ⟨hAv0, hGp1⟩ := hwf.meta_pages_bound.2.1 hShift0
    have hAvLen : st.availMetaPages.length = 0 := by simp [hAv0]
    omega
  · have hShiftPos : 1 ≤ st.ctx.metaAllocShift.toNat := by
      rcases Nat.eq_zero_or_pos st.ctx.metaAllocShift.toNat with h0 | hPos
      · exact False.elim (hShift0 (BitVec.eq_of_toNat_eq h0))
      · exact hPos
    let m := st.ctx.metaAllocShift.toNat
    obtain ⟨hm40, hMaGe, _, hGpLe, hAvLe⟩ := hwf.meta_pages_bound.2.2 m hShiftPos rfl
    by_cases hm4 : m < 4
    · have hmCases : m = 1 ∨ m = 2 ∨ m = 3 := by omega
      rcases hmCases with hm1 | hm2 | hm3
      · rw [hm1] at hGpLe hAvLe; omega
      · rw [hm2] at hGpLe hAvLe; omega
      · rw [hm3] at hGpLe hAvLe; omega
    · have hGe12 : 12 ≤ 2 ^ m - m := pow2_sub_ge_twelve m (by omega)
      omega

theorem mallocngCountIvsWF_after_alloc {base brkStart brk : BitVec 64}
    {req : Nat} {b : MallocngBudget} {st0 st' : MallocngSt} {ivs0 : List (BitVec 64 × Nat)}
    (hCount0 : MallocngCountIvsWF b ivs0 st0)
    (hLiveCnt : totalLiveCount st' = totalLiveCount st0 + 1)
    (hMetaLe : st'.metaAreas.length ≤ 1 + (88 + 8 * (mallocngAllocBudget true req b).peakCount) / 101)
    (hwf' : MallocngWF base brkStart brk
      (mallocngAllocBudget true req b).liveCost (mallocngAllocBudget true req b).peakCost st')
    (hGrp : Cost.GroupsGrpBound ((mallocngAllocBudget true req b).peakCount + 6) st'.groups) :
    let bf := mallocngAllocBudget true req b
    MallocngCountIvsWF bf (dynamicRootRegions st') st' := by
  intro bf
  have hBfLive : bf.liveCount = b.liveCount + 1 := rfl
  have hBfPeak : bf.peakCount = max b.peakCount (b.liveCount + 1) := rfl
  have hCntLe : totalLiveCount st' ≤ bf.liveCount := by have := hCount0.2.1; omega
  have hLiveLePeak : bf.liveCount ≤ bf.peakCount := by omega
  exact ⟨hLiveLePeak, hCntLe, rfl,
    dynamicRootRegions_length_le_of_metaBound hwf' (by omega) hMetaLe, hMetaLe, hGrp⟩

/-! ## Slot Replacement and Spatial Absorption -/

theorem replaceSlot_wf_core {inflight inflight' : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost liveCost' peakCost' : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hNotN : ∀ cm, g.slots[idx]'hIdx ≠ .liveNested cm)
    (hNotU : ∀ u r c, g.slots[idx]'hIdx ≠ .liveUser u r c)
    {newAvail : BitVec 32} {sNew : SlotState}
    {val' : BitVec 64 → BitVec 8} {liveMap' : MallocngLiveMap}
    (hNewNotN : ∀ cm, sNew ≠ .liveNested cm) (hNewNotFree : sNew.isFree = false)
    (hMaskAnd : newAvail &&& g.freedMask = 0#32)
    (hMaskOr : (newAvail ||| g.freedMask).toNat < 2 ^ g.cnt)
    (hMaskOther : ∀ j, j ≠ idx → newAvail.getLsbD j = g.availMask.getLsbD j)
    (hMaskAct : newAvail = g.availMask ∨ g.availMask ≠ 0#32)
    (hOutMod : ∀ a, ¬ SlotWriteMod g idx a → val' a = st.byteVal a)
    (hMetaBytes : readBytesFromMap val' g.metaPtr 40 =
      (mkReplaceSlotGroup g idx newAvail sNew).metaBytes)
    (hTargetSlotWf : SlotWf (mkReplaceSlotSt st g idx newAvail sNew val' liveMap')
      (mkReplaceSlotGroup g idx newAvail sNew) idx sNew)
    (hInflight : st.reservedMetas.length + totalClaimedSlots st +
        (if sNew.isClaimed then 1 else 0) ≤
      inflight' + (if (g.slots[idx]'hIdx).isClaimed then 1 else 0))
    (hLiveMap : ∀ p n, liveMap' p = some n ↔
      ((∃ ef, sNew = .liveUser p n ef) ∨ st.liveMap p = some n))
    (hLiveOv : ∀ u r, st.liveMap u = some r → liveMap'.ov u = st.liveMap.ov u)
    (hLiveLePeak : liveCost' ≤ peakCost')
    (hEffLeLive : totalLiveEffCost st + slotEffCost sNew ≤ liveCost')
    (hPeakMono : peakCost ≤ peakCost') :
    let g' := mkReplaceSlotGroup g idx newAvail sNew
    let st' := mkReplaceSlotSt st g idx newAvail sNew val' liveMap'
    MallocngWFInflight inflight' base brkStart brk liveCost' peakCost' st' ∧
    g' ∈ st'.groups ∧
    totalLiveEffCost st' = totalLiveEffCost st + slotEffCost sNew ∧
    totalLiveCount st' = totalLiveCount st + slotLiveCount sNew ∧
    dynamicRootRegions st' = dynamicRootRegions st ∧
    (∀ a, OwnedMappedByte st' a ↔ OwnedMappedByte st a) ∧
    (∀ a, CarvedUserByte st' a ↔
      ((∃ u r c, sNew = .liveUser u r c ∧ InRegion u r a) ∨ CarvedUserByte st a)) := by
  intro g' st'
  have hgw := hwf.groups_wf g hg
  have hIdx' : idx < g'.slots.length := by simp [g', mkReplaceSlotGroup, hIdx]
  have hSlotNew : g'.slots[idx]'hIdx' = sNew := by simp [g', mkReplaceSlotGroup]
  obtain ⟨hg'Mem, hGsCases, hGsKeep, hGsMeta, hGsMem, hGsRoot, hGsCnt, hGsFind, hGsSum⟩ :=
    replaceGroup_props st.groups g g' hg hwf.groups_nodup.1 rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨hSetCl, hSetEff, hSetCnt, hSetLive⟩ := list_set_slot_props g.slots idx hIdx sNew
  have hOldEff0 : slotEffCost (g.slots[idx]'hIdx) = 0 := by
    cases hS : g.slots[idx]'hIdx with
    | liveUser u r c => exact False.elim (hNotU u r c hS)
    | _ => rfl
  have hOldCnt0 : slotLiveCount (g.slots[idx]'hIdx) = 0 := by
    cases hS : g.slots[idx]'hIdx with
    | liveUser u r c => exact False.elim (hNotU u r c hS)
    | _ => rfl
  obtain ⟨hmDisjMa, hmDisjMeta, hmDisjGrpHdr, hmDisjOther⟩ :=
    slotWriteMod_disjoint hwf hg hIdx hNotN
  obtain ⟨hmDisjAp, _⟩ := protNone_disjoint_slotWriteMod hwf hg hIdx
  have hOutRead : ∀ (b : BitVec 64) (n : Nat), n ≤ 2 ^ 64 →
      (∀ a, InRegion b n a → ¬ SlotWriteMod g idx a) →
      readBytesFromMap st'.byteVal b n = readBytesFromMap st.byteVal b n :=
    fun b n hn hD => (readBytesFromMap_congr_pred (W := SlotWriteMod g idx) hn hD
      (fun a hN => (hOutMod a hN).symm)).symm
  have hDynEq : dynamicRootRegions st' = dynamicRootRegions st := by
    dsimp only [dynamicRootRegions, st', mkReplaceSlotSt, g', mkReplaceSlotGroup] at hGsRoot ⊢
    rw [hGsRoot]
  have hEffEq : totalLiveEffCost st' = totalLiveEffCost st + slotEffCost sNew := by
    have hS := hGsSum (fun x => (x.slots.map slotEffCost).sum)
    rw [hOldEff0, Nat.add_zero] at hSetEff
    unfold totalLiveEffCost
    dsimp only [st', mkReplaceSlotSt, g', mkReplaceSlotGroup] at hS ⊢
    omega
  have hCntEqTot : totalLiveCount st' = totalLiveCount st + slotLiveCount sNew := by
    have hS := hGsSum (fun x => (x.slots.map slotLiveCount).sum)
    rw [hOldCnt0, Nat.add_zero] at hSetCnt
    unfold totalLiveCount
    dsimp only [st', mkReplaceSlotSt, g', mkReplaceSlotGroup] at hS ⊢
    omega
  have hCarvedIff : ∀ a, CarvedUserByte st' a ↔
      ((∃ u r c, sNew = .liveUser u r c ∧ InRegion u r a) ∨ CarvedUserByte st a) := by
    intro a; unfold CarvedUserByte
    constructor
    · rintro ⟨x, hx, s, hs, hSub⟩
      cases s with
      | freeAvail | freeInactive | claimed | liveNested _ => simp at hSub
      | liveUser u r c =>
        rcases hGsCases x hx with ⟨_, rfl⟩ | ⟨_, hxOld⟩
        · rcases (hSetLive u r c hNotU).mp hs with hEq | hM
          · exact Or.inl ⟨u, r, c, hEq, hSub⟩
          · exact Or.inr ⟨g, hg, .liveUser u r c, hM, hSub⟩
        · exact Or.inr ⟨x, hxOld, .liveUser u r c, hs, hSub⟩
    · rintro (⟨u, r, c, rfl, hSub⟩ | ⟨x, hx, s, hs, hSub⟩)
      · exact ⟨g', hg'Mem, .liveUser u r c, (hSetLive u r c hNotU).mpr (Or.inl rfl), hSub⟩
      · cases s with
        | freeAvail | freeInactive | claimed | liveNested _ => simp at hSub
        | liveUser u r c =>
          by_cases hEqM : x.metaPtr = g.metaPtr
          · have rflX := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hEqM; subst rflX
            exact ⟨g', hg'Mem, .liveUser u r c, (hSetLive u r c hNotU).mpr (Or.inr hs), hSub⟩
          · exact ⟨x, hGsKeep x hx hEqM, .liveUser u r c, hs, hSub⟩
  have hMpEq : ∀ a, OwnedMappedByte st' a ↔ OwnedMappedByte st a := by
    intro a; unfold OwnedMappedByte
    have hGrpMp : (∃ x ∈ st'.groups, 0 < x.maplen ∧ InRegion x.mem (x.maplen * 4096) a) ↔
        (∃ x ∈ st.groups, 0 < x.maplen ∧ InRegion x.mem (x.maplen * 4096) a) := by
      constructor
      · rintro ⟨x, hx, hMp, hIn⟩
        rcases hGsCases x hx with ⟨_, rfl⟩ | ⟨_, hxO⟩
        · exact ⟨g, hg, hMp, hIn⟩
        · exact ⟨x, hxO, hMp, hIn⟩
      · rintro ⟨x, hx, hMp, hIn⟩
        by_cases hE : x.metaPtr = g.metaPtr
        · have rflX := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE; subst rflX
          exact ⟨g', hg'Mem, hMp, hIn⟩
        · exact ⟨x, hGsKeep x hx hE, hMp, hIn⟩
    dsimp only [st', mkReplaceSlotSt] at hGrpMp ⊢
    rw [hGrpMp]
  have hRwImp : ∀ a, OwnedRwByte st' a → OwnedRwByte st a := by
    intro a ⟨hDom, hNotC, hNotM⟩
    refine ⟨?_, fun hc => hNotC ((hCarvedIff a).mpr (Or.inr hc)), hNotM⟩
    rcases hDom with hMa | ⟨x, hx, hMp, hIn⟩
    · exact Or.inl hMa
    · rcases hGsCases x hx with ⟨_, rfl⟩ | ⟨_, hxO⟩
      · exact Or.inr ⟨g, hg, hMp, hIn⟩
      · exact Or.inr ⟨x, hxO, hMp, hIn⟩
  have hGroupsMap : ∀ cg ∈ st.groups, ∃ cg' ∈ st'.groups,
      cg'.metaPtr = cg.metaPtr ∧ cg'.parentMeta = cg.parentMeta ∧
      cg'.mem = cg.mem ∧ cg'.nestedCap = cg.nestedCap := fun cg hcg => by
    by_cases hE : cg.metaPtr = g.metaPtr
    · have rflC := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg hg hE; subst rflC
      exact ⟨g', hg'Mem, rfl, rfl, rfl, rfl⟩
    · exact ⟨cg, hGsKeep cg hcg hE, rfl, rfl, rfl, rfl⟩
  refine ⟨?_, hg'Mem, hEffEq, hCntEqTot, hDynEq, hMpEq, hCarvedIff⟩
  have hMemOut : ∀ x ∈ st.groups,
      st'.byteVal (x.slotEnd x.lastIdx) = st.byteVal (x.slotEnd x.lastIdx) ∧
      readBytesFromMap st'.byteVal x.mem 8 = readBytesFromMap st.byteVal x.mem 8 ∧
      st'.byteVal (x.mem + 8#64) = st.byteVal (x.mem + 8#64) := fun x hx => by
    obtain ⟨hMem9, hEnd⟩ := hmDisjGrpHdr x hx
    have hMem8 : ∀ a, InRegion x.mem 8 a → ¬ SlotWriteMod g idx a :=
      fun a ha => hMem9 a (by unfold InRegion at ha ⊢; omega)
    have hAct8 : ¬ SlotWriteMod g idx (x.mem + 8#64) :=
      hMem9 (x.mem + 8#64) (by unfold InRegion; bv_omega)
    exact ⟨hOutMod _ hEnd, hOutRead x.mem 8 (by decide) hMem8, hOutMod _ hAct8⟩
  have hParLift : ∀ x ∈ st.groups, x.maplen = 0 →
      1 ≤ x.lastIdx ∧ ∃ pg ∈ st'.groups, ∃ pIdx : Nat, ∃ hp : pIdx < pg.slots.length,
        x.parentMeta = some pg.metaPtr ∧ pg.sc < 48 ∧ x.sc < pg.sc ∧ pg.sc ≤ 24 ∧
        pg.slots[pIdx]'hp = .liveNested x.metaPtr ∧
        (pg.slotStart pIdx).toNat ≤ x.mem.toNat ∧
        x.mem.toNat + x.nestedCap ≤ (pg.slotEnd pIdx).toNat ∧
        x.nestedCap = slotStride pg.sc - 4 := fun x hx hMp0 => by
    obtain ⟨h1, pg, hpg, pIdx, hp, hPar, hSc48, hScLt, hSc24, hSl, hLo, hHi, hCap⟩ :=
      (hwf.groups_wf x hx).2.2.2.2.2.2.2.2.2.2.2.2.1 hMp0
    refine ⟨h1, ?_⟩
    by_cases hE : pg.metaPtr = g.metaPtr
    · have rflP := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg hg hE; subst rflP
      have hpNe : pIdx ≠ idx := fun hI => by subst hI; exact hNotN x.metaPtr hSl
      refine ⟨g', hg'Mem, pIdx, by simp [g', mkReplaceSlotGroup, hp], hPar, hSc48, hScLt, hSc24, ?_,
        hLo, hHi, hCap⟩
      simp [g', mkReplaceSlotGroup, List.getElem_set_ne (Ne.symm hpNe), hSl]
    · exact ⟨pg, hGsKeep pg hpg hE, pIdx, hp, hPar, hSc48, hScLt, hSc24, hSl, hLo, hHi, hCap⟩
  refine {
    base_wf := hwf.base_wf
    brk_bounds := hwf.brk_bounds
    ctx_lens := hwf.ctx_lens
    initDone_wf := hwf.initDone_wf
    initZero_wf := fun h0 => by exfalso; rw [(hwf.initZero_wf h0).2.2.2.2.2.2.2.2.2.1] at hg; cases hg
    bounces_wf := hwf.bounces_wf
    usage_wf := fun sc hsc => by dsimp only [st', mkReplaceSlotSt]; rw [hGsCnt sc]; exact hwf.usage_wf sc hsc
    brk_mode_wf := hwf.brk_mode_wf
    metaAreas_wf := ⟨hwf.metaAreas_wf.1, fun ma hma => by
      obtain ⟨h1, h2, h3, h4⟩ := hwf.metaAreas_wf.2.1 ma hma
      exact ⟨h1, h2, h3, (hOutRead ma.base 24 (by decide) (hmDisjMa ma hma)).trans h4⟩,
      hwf.metaAreas_wf.2.2⟩
    guard_avail_wf := ⟨hwf.guard_avail_wf.1, hwf.guard_avail_wf.2.1, hwf.guard_avail_wf.2.2.1,
      fun ap hap => by
        obtain ⟨h1, h2, h3, h4⟩ := hwf.guard_avail_wf.2.2.2 ap hap
        exact ⟨h1, h2, h3, (hOutRead ap 4096 (by decide) (hmDisjAp ap hap)).trans h4⟩⟩
    inflight_wf := by
      have hS := hGsSum (fun x => (x.slots.filter SlotState.isClaimed).length)
      unfold totalClaimedSlots at hInflight ⊢
      dsimp only [st', mkReplaceSlotSt, g', mkReplaceSlotGroup] at hS ⊢
      omega
    free_bump_metas_wf := by
      obtain ⟨hDll, hFmB, hBumpC, hBmB, hUFNd, hUFIff⟩ := hwf.free_bump_metas_wf
      have hNd12 := (List.nodup_append.mp hUFNd).1
      have hNd1 := (List.nodup_append.mp hNd12).1
      refine ⟨hDll, fun fm hfm => ?_, hBumpC, fun bm hbm => ?_,
        by dsimp only [st', mkReplaceSlotSt]; rw [hGsMeta]; exact hUFNd,
        fun m => by dsimp only [st', mkReplaceSlotSt, allMetaSlots]; rw [hGsMeta]; exact hUFIff m⟩
      · have hNe : fm.ptr ≠ g.metaPtr := fun hE =>
          (List.nodup_append.mp hNd1).2.2 g.metaPtr (List.mem_map_of_mem hg) fm.ptr
            (List.mem_map_of_mem hfm) hE.symm
        have hAll : fm.ptr ∈ allMetaSlots st :=
          (hUFIff fm.ptr).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hfm))))
        exact (hOutRead fm.ptr 40 (by decide) (hmDisjMeta fm.ptr hAll hNe)).trans (hFmB fm hfm)
      · have hNe : bm ≠ g.metaPtr := fun hE =>
          (List.nodup_append.mp hNd12).2.2 g.metaPtr
            (List.mem_append_left _ (List.mem_map_of_mem hg)) bm hbm hE.symm
        have hAll : bm ∈ allMetaSlots st :=
          (hUFIff bm).mp (List.mem_append_left _ (List.mem_append_right _ hbm))
        exact (hOutRead bm 40 (by decide) (hmDisjMeta bm hAll hNe)).trans (hBmB bm hbm)
    groups_nodup := by
      dsimp only [st', mkReplaceSlotSt]; rw [hGsMeta, hGsMem]; exact hwf.groups_nodup
    groups_wf := fun x' hx' => by
      rcases hGsCases x' hx' with ⟨_, rfl⟩ | ⟨hNeM, hxOld⟩
      · obtain ⟨hEndEq, hMem8Eq, hAct8Eq⟩ := hMemOut g hg
        refine ⟨hgw.1, hgw.2.1, by simp [g', mkReplaceSlotGroup, GroupDesc.cnt, hgw.2.2.1],
          hgw.2.2.2.1, hgw.2.2.2.2.1, hgw.2.2.2.2.2.1, hgw.2.2.2.2.2.2.1, hgw.2.2.2.2.2.2.2.1,
          hgw.2.2.2.2.2.2.2.2.1, hEndEq.trans hgw.2.2.2.2.2.2.2.2.2.1, hgw.2.2.2.2.2.2.2.2.2.2.1,
          hgw.2.2.2.2.2.2.2.2.2.2.2.1, hParLift g hg,
          hMaskAnd, hMaskOr, hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hMetaBytes, hMem8Eq.trans hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hAct8Eq.trans hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, fun j hj => ?_⟩
        by_cases hji : j = idx
        · subst hji; simpa [hSlotNew] using hTargetSlotWf
        · have hjO : j < g.slots.length := by simpa [g', mkReplaceSlotGroup] using hj
          have hSlEq : g'.slots[j]'hj = g.slots[j]'hjO := by
            simp [g', mkReplaceSlotGroup, List.getElem_set_ne (Ne.symm hji)]
          rw [hSlEq]
          obtain ⟨hNonN, hNest⟩ := hmDisjOther g hg j hjO (Or.inr hji)
          exact slotWf_congr_local hwf hg hjO rfl rfl rfl rfl rfl rfl (hMaskOther j hji) rfl hGroupsMap
            (fun hNN a ha => hOutMod a (hNonN hNN a ha))
            (fun cm cg hS hcg hCm hPm => ⟨hOutMod _ (hNest cm cg hS hcg hCm hPm).1,
              fun a ha => hOutMod a ((hNest cm cg hS hcg hCm hPm).2 a ha)⟩)
            (fun u r e hS => hLiveOv u r ((hwf.liveMap_wf u r).mpr ⟨g, hg, j, hjO, e, hS⟩))
      · have hxw := hwf.groups_wf x' hxOld
        obtain ⟨hEndEq, hMem8Eq, hAct8Eq⟩ := hMemOut x' hxOld
        have hAll := (hwf.free_bump_metas_wf.2.2.2.2.2 x'.metaPtr).mp
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hxOld))))
        refine ⟨hxw.1, hxw.2.1, hxw.2.2.1, hxw.2.2.2.1, hxw.2.2.2.2.1, hxw.2.2.2.2.2.1,
          hxw.2.2.2.2.2.2.1, hxw.2.2.2.2.2.2.2.1, hxw.2.2.2.2.2.2.2.2.1,
          hEndEq.trans hxw.2.2.2.2.2.2.2.2.2.1, hxw.2.2.2.2.2.2.2.2.2.2.1,
          hxw.2.2.2.2.2.2.2.2.2.2.2.1, hParLift x' hxOld,
          hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          (hOutRead x'.metaPtr 40 (by decide) (hmDisjMeta x'.metaPtr hAll hNeM)).trans
            hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hMem8Eq.trans hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hAct8Eq.trans hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, fun j hj => ?_⟩
        obtain ⟨hNonN, hNest⟩ := hmDisjOther x' hxOld j hj (Or.inl hNeM)
        exact slotWf_congr_local hwf hxOld hj rfl rfl rfl rfl rfl rfl rfl rfl hGroupsMap
          (fun hNN a ha => hOutMod a (hNonN hNN a ha))
          (fun cm cg hS hcg hCm hPm => ⟨hOutMod _ (hNest cm cg hS hcg hCm hPm).1,
            fun a ha => hOutMod a ((hNest cm cg hS hcg hCm hPm).2 a ha)⟩)
          (fun u r e hS => hLiveOv u r ((hwf.liveMap_wf u r).mpr ⟨x', hxOld, j, hj, e, hS⟩))
    regions_disjoint := by rw [hDynEq]; exact hwf.regions_disjoint
    active_wf := fun sc h1 h2 => by
      have haw := hwf.active_wf sc h1 h2
      have hFmEq : ∀ ms : List (BitVec 64),
          ms.filterMap (fun m => (findGroupByMeta st' m).map fun x => (x.metaPtr, x.prev, x.next)) =
          ms.filterMap (fun m => (findGroupByMeta st m).map fun x => (x.metaPtr, x.prev, x.next)) := by
        intro ms; induction ms with
        | nil => rfl
        | cons m tl ih =>
          dsimp only [List.filterMap, findGroupByMeta, st', mkReplaceSlotSt, g', mkReplaceSlotGroup] at hGsFind ih ⊢
          rw [hGsFind m, ih]
      have hToOld : ∀ x ∈ st'.groups, ∃ y ∈ st.groups,
          y.metaPtr = x.metaPtr ∧ y.sc = x.sc ∧ y.activeIdx = x.activeIdx ∧ y.lastIdx = x.lastIdx := fun x hx =>
        (hGsCases x hx).elim (fun ⟨_, hE⟩ => by subst hE; exact ⟨g, hg, rfl, rfl, rfl, rfl⟩)
          (fun ⟨_, hxO⟩ => ⟨x, hxO, rfl, rfl, rfl, rfl⟩)
      refine ⟨fun m hm => ?_, by rw [hFmEq]; exact haw.2.1, by rw [hFmEq]; exact haw.2.2.1,
        fun x hx hSc => ?_, fun i hi hPos x hx hM => ?_,
        fun x1 hx1 x2 hx2 hS1 hS2 hA1 hA2 => ?_, fun x hx hSc hA => ?_⟩
      · obtain ⟨x, hx, rfl, rfl⟩ := haw.1 m hm
        exact if hE : x.metaPtr = g.metaPtr then
          ⟨g', hg'Mem, (congrArg GroupDesc.metaPtr (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE)).symm,
            (congrArg GroupDesc.sc (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE)).symm⟩
        else ⟨x, hGsKeep x hx hE, rfl, rfl⟩
      · exact (hGsCases x hx).elim (fun ⟨_, hE⟩ => by
          subst hE; have hOld := haw.2.2.2.1 g hg hSc
          exact ⟨hOld.1, fun hNot => hMaskAct.elim (fun hEq => ⟨hEq.trans (hOld.2 hNot).1, (hOld.2 hNot).2⟩)
            (fun hAv => False.elim (hAv (hOld.2 hNot).1))⟩) (fun ⟨_, hxO⟩ => haw.2.2.2.1 x hxO hSc)
      · exact (hGsCases x hx).elim (fun ⟨_, hE⟩ => by
          subst hE; have hOld := haw.2.2.2.2.1 i hi hPos g hg hM
          exact hMaskAct.elim (fun hEq => ⟨hEq.trans hOld.1, hOld.2⟩) (fun hAv => False.elim (hAv hOld.1)))
          (fun ⟨_, hxO⟩ => haw.2.2.2.2.1 i hi hPos x hxO hM)
      · obtain ⟨y1, hy1, hM1, hY1S, hY1A, hY1L⟩ := hToOld x1 hx1
        obtain ⟨y2, hy2, hM2, hY2S, hY2A, hY2L⟩ := hToOld x2 hx2
        exact hM1.symm.trans ((haw.2.2.2.2.2.1 y1 hy1 y2 hy2 (hY1S.trans hS1) (hY2S.trans hS2)
          (by omega) (by omega)).trans hM2)
      · obtain ⟨y, hy, hM, hYS, hYA, hYL⟩ := hToOld x hx
        rw [← hM]; exact haw.2.2.2.2.2.2 y hy (hYS.trans hSc) (by omega)
    liveMap_wf := fun p n => by
      dsimp only [st', mkReplaceSlotSt]; rw [hLiveMap p n, hwf.liveMap_wf p n]; constructor
      · rintro (⟨ef, hSN⟩ | ⟨x, hx, j, hj, ef, hSl⟩)
        · exact ⟨g', hg'Mem, idx, hIdx', ef, hSlotNew.trans hSN⟩
        · by_cases hE : x.metaPtr = g.metaPtr
          · have rflX := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE; subst rflX
            have hjNe : j ≠ idx := fun hI => by subst hI; exact hNotU p n ef hSl
            exact ⟨g', hg'Mem, j, by simp [g', mkReplaceSlotGroup, hj], ef,
              by simp [g', mkReplaceSlotGroup, List.getElem_set_ne (Ne.symm hjNe), hSl]⟩
          · exact ⟨x, hGsKeep x hx hE, j, hj, ef, hSl⟩
      · rintro ⟨x, hx, j, hj, ef, hSl⟩
        rcases hGsCases x hx with ⟨_, rfl⟩ | ⟨_, hxOld⟩
        · by_cases hji : j = idx
          · subst hji; exact Or.inl ⟨ef, hSlotNew.symm.trans hSl⟩
          · have hjO : j < g.slots.length := by simpa [g', mkReplaceSlotGroup] using hj
            simp only [g', mkReplaceSlotGroup, List.getElem_set_ne (Ne.symm hji)] at hSl
            exact Or.inr ⟨g, hg, j, hjO, ef, hSl⟩
        · exact Or.inr ⟨x, hxOld, j, hj, ef, hSl⟩
    live_le_peak := hLiveLePeak
    effCost_le_live := by rw [hEffEq]; exact hEffLeLive
    meta_pages_bound := ⟨Nat.le_trans hwf.meta_pages_bound.1
      (Nat.add_le_add_left (Nat.div_le_div_right hPeakMono) 2),
      hwf.meta_pages_bound.2.1, hwf.meta_pages_bound.2.2⟩
    empty_groups_bound := fun x hx hEmp =>
      (hGsCases x hx).elim (fun ⟨_, hE⟩ => by
          subst hE; exfalso
          have hAll := List.all_eq_true.mp hEmp (g'.slots[idx]'hIdx') (List.getElem_mem hIdx')
          rw [hSlotNew, hNewNotFree] at hAll; cases hAll)
        (fun ⟨_, hxO⟩ => by
          obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hwf.empty_groups_bound x hxO hEmp
          refine ⟨e1, e2, e3, e4, e5, fun y hy hEmpY hScY => (hGsCases y hy).elim
            (fun ⟨_, hEY⟩ => by
              subst hEY; exfalso
              have hAll := List.all_eq_true.mp hEmpY (g'.slots[idx]'hIdx') (List.getElem_mem hIdx')
              rw [hSlotNew, hNewNotFree] at hAll; cases hAll)
            (fun ⟨_, hyO⟩ => e6 y hyO hEmpY hScY), e7⟩)
    masterDom_wf := ⟨hwf.masterDom_wf.1,
      fun a h => hwf.masterDom_wf.2.1 a (h.elim (fun h1 => Or.inl (hRwImp a h1))
        (fun h23 => h23.elim (fun h2 => Or.inr (Or.inl h2))
          (fun h3 => Or.inr (Or.inr ((hMpEq a).mp h3))))),
      fun a ha => by rw [hDynEq]; exact hwf.masterDom_wf.2.2 a ha⟩
  }

theorem claimFreeAvail_absorb {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hAvailNe : g.availMask ≠ 0#32) :
    let idx := ctz32DeBruijn g.availMask
    let newAvail := g.availMask - ((-g.availMask) &&& g.availMask)
    let g' := mkReplaceSlotGroup g idx newAvail .claimed
    let val' := writeBytesToMap st.byteVal g.metaPtr g'.metaBytes
    let st1 := mkReplaceSlotSt st g idx newAvail .claimed val' st.liveMap
    idx < g.slots.length ∧
    idx < 32 ∧
    g'.isMmapped = false ∧
    st1.metaAreas.length = st.metaAreas.length ∧
    totalLiveCount st1 = totalLiveCount st ∧
    dynamicRootRegions st1 = dynamicRootRegions st ∧
    MallocngWFInflight 1 base brkStart brk liveCost peakCost st1 ∧
    g' ∈ st1.groups ∧
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
      ((g.metaPtr ↦ₛ g.metaBytes) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal) ∧
    ((g.metaPtr ↦ₛ g'.metaBytes) ∗
      ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal) =
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal ∧
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∧
    MappedSet st.masterDom (OwnedMappedByte st) =
      MappedSet st1.masterDom (OwnedMappedByte st1) := by
  intro idx newAvail g' val' st1
  have hgw := hwf.groups_wf g hg
  have hRes0 : st.reservedMetas = [] := by
    have hInf := hwf.inflight_wf; cases hR : st.reservedMetas with | nil => rfl | cons _ _ => simp [hR] at hInf
  obtain ⟨_, hIdx32, _, hIso, _, hSet, _, _⟩ := ctz32DeBruijn_spec hAvailNe
  obtain ⟨hBitTrue, _, hRemBit, hRemAnd, hRemOr⟩ := bit32_sub_pow2_props idx hIdx32 g.availMask hIso hSet
  have hIdxCnt : idx < g.cnt := Classical.byContradiction fun hGe => by
    have hPowLe : 2 ^ g.cnt ≤ 2 ^ idx := Nat.pow_le_pow_right (n := 2) (by omega) (Nat.le_of_not_lt hGe)
    have hShiftNat : (1#32 <<< idx).toNat = 2 ^ idx := by
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 32),
        Nat.one_shiftLeft, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (a := 2) (by omega) hIdx32)]
    have hAndLe : (g.availMask &&& (1#32 <<< idx)).toNat ≤ g.availMask.toNat := by
      rw [BitVec.toNat_and]; exact Nat.and_le_left
    have hOrGe : g.availMask.toNat ≤ (g.availMask ||| g.freedMask).toNat :=
      BitVec.le_def.mp (by bv_bits : g.availMask ≤ g.availMask ||| g.freedMask)
    rw [hSet, hShiftNat] at hAndLe
    have hOrLt := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  have hIdx : idx < g.slots.length := by rw [hgw.2.2.1]; exact hIdxCnt
  have hsw := hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx
  have hFreeAvail : g.slots[idx]'hIdx = .freeAvail := hsw.2.1.mp hBitTrue
  have hNotMmap : g'.isMmapped = false := by
    change g.isMmapped = false
    cases hMm : g.isMmapped with
    | false => rfl
    | true =>
      have hNF := not_isFree_of_isMmapped hwf hg hMm (hFreeAvail ▸ List.getElem_mem hIdx)
      simp [SlotState.isFree] at hNF
  obtain ⟨hMetaOwn, hSlotOwn⟩ := group_meta_and_claimed_ownedRw hwf hRes0 hg
  have hNotN : ∀ cm, g.slots[idx]'hIdx ≠ .liveNested cm := by rw [hFreeAvail]; intro _ h; cases h
  have hNotU : ∀ u r c, g.slots[idx]'hIdx ≠ .liveUser u r c := by rw [hFreeAvail]; intro _ _ _ h; cases h
  have hStartOutMeta : ¬ InRegion g.metaPtr 40 (g.slotStart idx - 4#64) := by
    obtain ⟨_, _, _, hSub4, hEnd, hEndLe, h48G, _, _⟩ := group_slot_bounds hgw hIdx
    have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
    have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
    refine (hSlotOwn idx hIdx hNotN hNotU _ ?_).2.2
    exact (inRegion_iff_toNat (n := g.stride) (by omega) _).mpr
      ⟨by omega, by have := (group_stride_pos_and_align hgw).1; omega⟩
  have hMetaLen : g'.metaBytes.length = 40 := GroupDesc.metaBytes_length g'
  have hTargetSw : SlotWf st1 g' idx .claimed := by
    refine ⟨?_, ?_, ?_, ?_, trivial⟩
    · change writeBytesToMap st.byteVal g.metaPtr g'.metaBytes (g.slotStart idx - 4#64) = 0#8
      rw [writeBytesToMap_out _ _ _ (by rwa [hMetaLen])]; exact hsw.1
    · have hBF : newAvail.getLsbD idx = false := by simpa using hRemBit idx
      simp [g', mkReplaceSlotGroup, hBF]
    · simp only [g', mkReplaceSlotGroup, reduceCtorEq, iff_false, Bool.not_eq_true]
      cases hF : g.freedMask.getLsbD idx with
      | false => rfl
      | true => have hFI := hsw.2.2.1.mp hF; rw [hFreeAvail] at hFI; cases hFI
    · intro hLt; exfalso; have hFI := hsw.2.2.2.1 hLt; rw [hFreeAvail] at hFI; cases hFI
  obtain ⟨hwf1, hg'Mem, _, hCntEq, hDynEq, hMpIff, hCarvIff⟩ := replaceSlot_wf_core (inflight' := 1)
    hwf hg hIdx hNotN hNotU (fun _ h => by cases h) rfl
    (hRemAnd g.freedMask hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (Nat.lt_of_le_of_lt (hRemOr g.freedMask) hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (fun j hj => by rw [hRemBit j]; simp [hj])
    (Or.inr hAvailNe)
    (fun a hNotMod => writeBytesToMap_out _ _ _ (fun hIn => hNotMod (Or.inl (by rwa [hMetaLen] at hIn))))
    (readBytesFromMap_writeBytesToMap st.byteVal g.metaPtr g'.metaBytes (by rw [hMetaLen]; decide))
    hTargetSw
    (by have := hwf.inflight_wf; simp [SlotState.isClaimed]; omega)
    (fun p n => ⟨fun h => Or.inr h, fun h => h.elim (fun ⟨_, hE⟩ => by cases hE) id⟩)
    (fun _ _ _ => rfl)
    hwf.live_le_peak (by simp [slotEffCost, hwf.effCost_le_live]) (Nat.le_refl _)
  have hExt := ByteMap_extract_slice hwf.masterDom_wf.1 (keep := OwnedRwByte st)
    st.byteVal g.metaPtr (n := 40) (by decide)
    (fun a ha => (hMetaOwn a ha).2) (fun a ha => (hMetaOwn a ha).1)
  have hReadMeta : readBytesFromMap st.byteVal g.metaPtr 40 = g.metaBytes :=
    hgw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hReadMeta] at hExt
  have hAbs := ByteMap_absorb_slice hwf.masterDom_wf.1
    (keep := fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a)
    st.byteVal g.metaPtr g'.metaBytes (by rw [hMetaLen]; decide)
    (fun a ha => (hMetaOwn a (by rwa [hMetaLen] at ha)).2)
    (fun a ha hK => hK.2 (by rwa [hMetaLen] at ha))
  have hRwEq : ByteMap st.masterDom
      (fun a => (OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) ∨ InRegion g.metaPtr g'.metaBytes.length a) val' =
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal := by
    unfold ByteMap; refine SetSep_congr (fun a _ => ?_) (fun _ _ _ => rfl)
    rw [hMetaLen]
    have hOwnEq : OwnedRwByte st1 a ↔ OwnedRwByte st a := by
      obtain ⟨_, hGsCases, hGsKeep, _, _, _, _, _, _⟩ :=
        replaceGroup_props st.groups g g' hg hwf.groups_nodup.1 rfl rfl rfl rfl rfl rfl rfl
      unfold OwnedRwByte
      refine ⟨fun ⟨hD, hNC, hNM⟩ => ⟨?_, fun hc => hNC ((hCarvIff a).mpr (Or.inr hc)), hNM⟩,
        fun ⟨hD, hNC, hNM⟩ => ⟨?_, fun hc => hNC (((hCarvIff a).mp hc).elim (fun ⟨_, _, _, hE, _⟩ => by cases hE) id), hNM⟩⟩
      · exact hD.elim Or.inl (fun ⟨x, hx, hp, hi⟩ => (hGsCases x hx).elim
          (fun ⟨_, hE⟩ => by subst hE; exact Or.inr ⟨g, hg, hp, hi⟩) (fun ⟨_, hxO⟩ => Or.inr ⟨x, hxO, hp, hi⟩))
      · exact hD.elim Or.inl (fun ⟨x, hx, hp, hi⟩ =>
          if hE : x.metaPtr = g.metaPtr then
            by have rflX := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE; subst rflX; exact Or.inr ⟨g', hg'Mem, hp, hi⟩
          else Or.inr ⟨x, hGsKeep x hx hE, hp, hi⟩)
    rw [hOwnEq]
    exact ⟨fun h => h.elim (fun h1 => h1.1) (fun h2 => (hMetaOwn a h2).1),
      fun h => if hM : InRegion g.metaPtr 40 a then Or.inr hM else Or.inl ⟨h, hM⟩⟩
  have hPnEq : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal := by
    unfold ProtNoneByteMap; refine SetSep_congr (fun _ _ => Iff.rfl) (fun a _ hPn => ?_)
    obtain ⟨hDisjAp, hDisjGp⟩ := protNone_disjoint_slotWriteMod hwf hg hIdx
    have hOut : ¬ InRegion g.metaPtr 40 a := fun hM =>
      hPn.elim (fun ⟨gp, hgp, ha⟩ => hDisjGp gp hgp a ha (Or.inl hM))
        (fun ⟨ap, hap, ha⟩ => hDisjAp ap hap a ha (Or.inl hM))
    congr 1; exact (writeBytesToMap_out st.byteVal g.metaPtr g'.metaBytes (by rwa [hMetaLen])).symm
  have hMpEq : MappedSet st.masterDom (OwnedMappedByte st) = MappedSet st1.masterDom (OwnedMappedByte st1) := by
    unfold MappedSet; exact SetSep_congr (fun a _ => (hMpIff a).symm) (fun _ _ _ => rfl)
  exact ⟨hIdx, hIdx32, hNotMmap, rfl, by simpa [slotLiveCount] using hCntEq, hDynEq,
    hwf1, hg'Mem, hExt, hAbs.trans hRwEq, hPnEq, hMpEq⟩

end VerifiedLibraries.Mallocng.Proofs
