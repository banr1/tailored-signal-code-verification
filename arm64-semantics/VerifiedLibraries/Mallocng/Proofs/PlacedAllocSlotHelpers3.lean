/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocSlotHelpers2

/-!
# Pure Invariant Helpers for Placed `alloc_slot` (Part 3)

Proves pure `MallocngWFInflight` and `ByteMap` transition and absorption lemmas for outer
`alloc_slot`: `unique_partial_active_next_eq_lastIdx`, `tryAvail_dequeue_multi_absorb`, and
`tryAvail_bump_activeIdx_absorb`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

theorem unique_partial_active_next_eq_lastIdx {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {sc : Nat} (hsc : sc < 48) {g gNext : GroupDesc}
    (hg : g ∈ st.groups) (hgNext : gNext ∈ st.groups)
    (hScG : g.sc = sc) (hScNx : gNext.sc = sc)
    (hLt : g.activeIdx < g.lastIdx) (hNe : gNext ≠ g) :
    gNext.activeIdx = gNext.lastIdx := by
  have h1 : sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hsc
  have h2 : sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hsc
  have hAct := hwf.active_wf sc h1 h2
  have hLe : gNext.activeIdx ≤ gNext.lastIdx :=
    (hwf.groups_wf gNext hgNext).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact Classical.byContradiction fun hNeIdx => by
    have hLtNx : gNext.activeIdx < gNext.lastIdx := by omega
    have hEqM := hAct.2.2.2.2.2.1 gNext hgNext g hg hScNx hScG hLtNx hLt
    exact hNe (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hgNext hg hEqM)

set_option maxHeartbeats 800000 in
theorem tryAvail_dequeue_multi_absorb {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {sc : Nat} (hsc : sc < 48) {g : GroupDesc} (hg : g ∈ st.groups) (hScEq : g.sc = sc)
    (hHead : st.ctx.active[sc]'(by rw [hwf.ctx_lens.1]; exact hsc) = g.metaPtr)
    (hAv0 : g.availMask = 0#32) (hFr0 : g.freedMask = 0#32) (hNxNe : g.next ≠ g.metaPtr) :
    let fG : GroupDesc → GroupDesc := fun u =>
      if u.metaPtr == g.metaPtr then { u with prev := 0#64, next := 0#64 }
      else { u with
        prev := if u.metaPtr == g.next then g.prev else u.prev
        next := if u.metaPtr == g.prev then g.next else u.next }
    let h2 : sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hsc
    ∃ gNext gPrev : GroupDesc, ∃ msTl : List (BitVec 64),
      gNext ∈ st.groups ∧ gNext.metaPtr = g.next ∧ gNext ≠ g ∧
      gPrev ∈ st.groups ∧ gPrev.metaPtr = g.prev ∧ gPrev ≠ g ∧
      g.next ≠ 0#64 ∧ g.prev ≠ 0#64 ∧
      st.activeLists[sc]'h2 = g.metaPtr :: g.next :: msTl ∧
      let bv1 :=
        if g.prev = g.next then
          writeBytesToMap (writeBytesToMap st.byteVal gNext.metaPtr (fG gNext).metaBytes)
            g.metaPtr (fG g).metaBytes
        else
          writeBytesToMap
            (writeBytesToMap (writeBytesToMap st.byteVal gPrev.metaPtr (fG gPrev).metaBytes)
              gNext.metaPtr (fG gNext).metaBytes)
            g.metaPtr (fG g).metaBytes
      let st1 : MallocngSt :=
        { st with
          ctx := { st.ctx with active := st.ctx.active.set sc g.next }
          groups := st.groups.map fG
          activeLists := st.activeLists.set sc (g.next :: msTl)
          byteVal := bv1 }
      let P1 := fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a
      let P2 := fun a => P1 a ∧ ¬ InRegion gNext.metaPtr 40 a
      let Rest2 := ByteMap st.masterDom P2 st.byteVal
      let Rest3 := ByteMap st.masterDom (fun a => P2 a ∧ ¬ InRegion gPrev.metaPtr 40 a) st.byteVal
      (fG gNext) ∈ st1.groups ∧ (fG gNext).metaPtr = g.next ∧ (fG gNext).sc = sc ∧
      (fG gNext).availMask = 0#32 ∧ (fG gNext).freedMask ≠ 0#32 ∧
      MallocngWFInflight inflight base brkStart brk liveCost peakCost st1 ∧
      totalLiveCount st1 = totalLiveCount st ∧
      totalLiveEffCost st1 = totalLiveEffCost st ∧
      dynamicRootRegions st1 = dynamicRootRegions st ∧
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
        ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∧
      MappedSet st.masterDom (OwnedMappedByte st) =
        MappedSet st1.masterDom (OwnedMappedByte st1) ∧
      (g.prev = g.next →
        gPrev = gNext ∧
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
          ((g.metaPtr ↦ₛ g.metaBytes) ∗ ((gNext.metaPtr ↦ₛ gNext.metaBytes) ∗ Rest2)) ∧
        (((g.metaPtr ↦ₛ (fG g).metaBytes) ∗ ((gNext.metaPtr ↦ₛ (fG gNext).metaBytes) ∗ Rest2)) =
          ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal)) ∧
      (g.prev ≠ g.next →
        gPrev ≠ gNext ∧
        ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
          ((g.metaPtr ↦ₛ g.metaBytes) ∗
            ((gNext.metaPtr ↦ₛ gNext.metaBytes) ∗ ((gPrev.metaPtr ↦ₛ gPrev.metaBytes) ∗ Rest3))) ∧
        (((g.metaPtr ↦ₛ (fG g).metaBytes) ∗
          ((gNext.metaPtr ↦ₛ (fG gNext).metaBytes) ∗ ((gPrev.metaPtr ↦ₛ (fG gPrev).metaBytes) ∗ Rest3))) =
          ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal)) := by
  intro fG h2
  have h1 : sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hsc
  have hActOld := hwf.active_wf sc h1 h2
  obtain ⟨hActEqG, hNotEmpG⟩ := freed0_eq_lastIdx_not_empty hwf hg hAv0 hFr0
  obtain ⟨gMin, _, hMBoundG, hMReadG, hMOwnG⟩ := meta_ownedRw_of_mem_groups hwf hg
  have hHeadNe0 : st.ctx.active[sc]'h1 ≠ 0#64 := by
    rw [hHead]; intro h0; rw [h0] at gMin; simp at gMin
  obtain ⟨g0, _, hG0M, _, tail0, hMsCons0⟩ := active_head_group_of_nonzero hwf h1 h2 hHeadNe0
  have hMs0 : st.activeLists[sc]'h2 = g.metaPtr :: tail0 := by rw [hMsCons0, hG0M, hHead]
  have hDll0 := hActOld.2.1
  have hMapFst0 := activeList_nodes_map_fst hwf.groups_nodup.1
    (fun m hm => let ⟨x, hx, hmX, _⟩ := hActOld.1 m hm; ⟨x, hx, hmX⟩)
  cases tail0 with
  | nil =>
    rw [hMs0] at hDll0
    simp only [List.filterMap_cons, List.filterMap_nil,
      slot_findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hg, Option.map_some] at hDll0
    exact False.elim (hNxNe ((CircularDllWf.singleton_iff_next_eq hDll0).2 rfl).2)
  | cons m1 msTl =>
    have hMs1 : st.activeLists[sc]'h2 = g.metaPtr :: m1 :: msTl := hMs0
    obtain ⟨gNext, hgNext, hGNxM, hGNxSc⟩ := hActOld.1 m1 (by rw [hMs1]; simp)
    let tlNodes := msTl.filterMap fun m => (findGroupByMeta st m).map fun x => (x.metaPtr, x.prev, x.next)
    have hNodesEq : ((st.activeLists[sc]'h2).filterMap fun m =>
        (findGroupByMeta st m).map fun x => (x.metaPtr, x.prev, x.next)) =
        (g.metaPtr, g.prev, g.next) :: (gNext.metaPtr, gNext.prev, gNext.next) :: tlNodes := by
      rw [hMs1, ← hGNxM]
      simp [tlNodes, slot_findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hg,
        slot_findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hgNext]
    rw [hNodesEq, hHead] at hDll0
    obtain ⟨hNxEqGNext, hDll1⟩ := CircularDllWf.dequeue_head hDll0
    have hGNxMeta : gNext.metaPtr = g.next := hNxEqGNext.symm
    have hNxEqM1 : g.next = m1 := hNxEqGNext.trans hGNxM
    have hMapFst1 : (((g.metaPtr, g.prev, g.next) :: (gNext.metaPtr, gNext.prev, gNext.next) :: tlNodes).map Prod.fst) =
        g.metaPtr :: m1 :: msTl := by
      calc (((g.metaPtr, g.prev, g.next) :: (gNext.metaPtr, gNext.prev, gNext.next) :: tlNodes).map Prod.fst)
          = (((st.activeLists[sc]'h2).filterMap fun m =>
              (findGroupByMeta st m).map fun x => (x.metaPtr, x.prev, x.next)).map Prod.fst) := by rw [hNodesEq]
        _ = st.activeLists[sc]'h2 := hMapFst0
        _ = g.metaPtr :: m1 :: msTl := hMs1
    have hTlMapFst : (((gNext.metaPtr, gNext.prev, gNext.next) :: tlNodes).map Prod.fst) = m1 :: msTl := by
      simpa using hMapFst1
    have hNdMs : (g.metaPtr :: m1 :: msTl).Nodup := hMapFst1 ▸ hDll0.2.1
    have hGNxNeG : gNext ≠ g := fun hE => (List.nodup_cons.mp hNdMs).1 (by rw [← hE, hGNxM]; simp)
    have hPvLink := (hDll0.2.2.2 0 (by simp)).2
    have hModLast : (0 + ((g.metaPtr, g.prev, g.next) :: (gNext.metaPtr, gNext.prev, gNext.next) :: tlNodes).length - 1) %
        ((g.metaPtr, g.prev, g.next) :: (gNext.metaPtr, gNext.prev, gNext.next) :: tlNodes).length =
        tlNodes.length + 1 := by
      simp only [List.length_cons, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [hModLast, List.getElem_cons_zero, List.getElem_cons_succ] at hPvLink
    have hPvInTail : g.prev ∈ m1 :: msTl := by
      have hMemFst : (((gNext.metaPtr, gNext.prev, gNext.next) :: tlNodes)[tlNodes.length]'(by simp)).1 ∈
          (((gNext.metaPtr, gNext.prev, gNext.next) :: tlNodes).map Prod.fst) :=
        List.mem_map_of_mem (List.getElem_mem (by simp))
      rw [hTlMapFst] at hMemFst; exact hPvLink ▸ hMemFst
    obtain ⟨gPrev, hgPrev, hGPvM, hGPvSc⟩ := hActOld.1 g.prev (by rw [hMs1]; exact List.mem_cons_of_mem _ hPvInTail)
    have hGPvNeG : gPrev ≠ g := fun hE => (List.nodup_cons.mp hNdMs).1 (hE ▸ hGPvM ▸ hPvInTail)
    obtain ⟨hLoNx, _, hMBoundNx, hMReadNx, hMOwnNx⟩ := meta_ownedRw_of_mem_groups hwf hgNext
    obtain ⟨hLoPv, _, hMBoundPv, hMReadPv, hMOwnPv⟩ := meta_ownedRw_of_mem_groups hwf hgPrev
    have hNxNe0 : g.next ≠ 0#64 := by intro h0; rw [hGNxMeta, h0] at hLoNx; simp at hLoNx
    have hPvNe0 : g.prev ≠ 0#64 := by intro h0; rw [hGPvM, h0] at hLoPv; simp at hLoPv
    have hNextIdx1 := hActOld.2.2.2.2.1 1 (by rw [hMs1]; simp) (by omega) gNext hgNext
      (by simp [hMs1, hGNxM])
    refine ⟨gNext, gPrev, msTl, hgNext, hGNxMeta, hGNxNeG, hgPrev, hGPvM, hGPvNeG,
      hNxNe0, hPvNe0, hNxEqM1 ▸ hMs1, ?_⟩
    intro bv1 st1 P1 P2 Rest2 Rest3
    have hDisjOfNe : ∀ {x y : GroupDesc}, x ∈ st.groups → y ∈ st.groups → x ≠ y →
        DisjointRegions x.metaPtr 40 y.metaPtr 40 := fun {x y} hx hy hne => by
      have hneM : x.metaPtr ≠ y.metaPtr := fun hM => hne (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hy hM)
      exact (allMetaSlots_info hwf ((hwf.free_bump_metas_wf.2.2.2.2.2 x.metaPtr).mp
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hx)))))).2.2.2.2
        y.metaPtr ((hwf.free_bump_metas_wf.2.2.2.2.2 y.metaPtr).mp
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hy))))) hneM.symm
    have hLenFG : ∀ x : GroupDesc, (fG x).metaBytes.length = 40 := fun x => by simp [GroupDesc.metaBytes]
    obtain ⟨hWO_G, hWR_G⟩ := writeBytes40_props (bv := writeBytesToMap st.byteVal gNext.metaPtr (fG gNext).metaBytes)
      (hLenFG g) hMBoundG
    obtain ⟨hWO_Nx2, hWR_Nx2⟩ := writeBytes40_props (bv := st.byteVal) (hLenFG gNext) hMBoundNx
    obtain ⟨hWO_Pv3, hWR_Pv3⟩ := writeBytes40_props (bv := st.byteVal) (hLenFG gPrev) hMBoundPv
    obtain ⟨hWO_Nx3, hWR_Nx3⟩ := writeBytes40_props
      (bv := writeBytesToMap st.byteVal gPrev.metaPtr (fG gPrev).metaBytes) (hLenFG gNext) hMBoundNx
    obtain ⟨hWO_G3, hWR_G3⟩ := writeBytes40_props
      (bv := writeBytesToMap (writeBytesToMap st.byteVal gPrev.metaPtr (fG gPrev).metaBytes)
        gNext.metaPtr (fG gNext).metaBytes) (hLenFG g) hMBoundG
    have hSubF : ∀ u ∈ st.groups, (fG u).metaPtr = u.metaPtr ∧ (fG u).mem = u.mem ∧
        (fG u).lastIdx = u.lastIdx ∧ (fG u).sc = u.sc ∧ (fG u).maplen = u.maplen ∧
        (fG u).activeByte = u.activeByte ∧ (fG u).parentMeta = u.parentMeta ∧
        (fG u).nestedCap = u.nestedCap ∧ (fG u).slots = u.slots ∧
        (fG u).availMask = u.availMask ∧ (fG u).freedMask = u.freedMask ∧
        (fG u).freshZero = u.freshZero ∧ (fG u).activeIdx = u.activeIdx := fun u _ => by
      dsimp only [fG]; split <;> simp [GroupDesc.activeIdx]
    have hNd1 : ((st.groups.map fG).map (·.metaPtr)).Nodup := by
      have hMapEq : (st.groups.map fG).map (·.metaPtr) = st.groups.map (·.metaPtr) := by
        rw [List.map_map]; exact List.map_congr_left fun u hu => (hSubF u hu).1
      rw [hMapEq]; exact hwf.groups_nodup.1
    have hOutBv1 : ∀ a : BitVec 64, (∀ u ∈ st.groups, ¬ InRegion u.metaPtr 40 a) → bv1 a = st.byteVal a := by
      intro a hOut; dsimp only [bv1]; split
      · exact (hWO_G a (hOut g hg)).trans (hWO_Nx2 a (hOut gNext hgNext))
      · exact (hWO_G3 a (hOut g hg)).trans ((hWO_Nx3 a (hOut gNext hgNext)).trans (hWO_Pv3 a (hOut gPrev hgPrev)))
    have hMetaBv1 : ∀ u ∈ st.groups, readBytesFromMap bv1 u.metaPtr 40 = (fG u).metaBytes := by
      intro u hu
      by_cases hEG : u = g
      · rw [hEG]; dsimp only [bv1]; split
        · exact hWR_G
        · exact hWR_G3
      · have hDisjUG := hDisjOfNe hu hg hEG
        by_cases hENx : u = gNext
        · rw [hENx]; dsimp only [bv1]; split
          · exact (readBytesFromMap_congr (by decide) fun a ha =>
              hWO_G a (fun hIn => DisjointRegions.not_both (hDisjOfNe hgNext hg hGNxNeG) ha hIn)).trans hWR_Nx2
          · exact (readBytesFromMap_congr (by decide) fun a ha =>
              hWO_G3 a (fun hIn => DisjointRegions.not_both (hDisjOfNe hgNext hg hGNxNeG) ha hIn)).trans hWR_Nx3
        · have hDisjUNx := hDisjOfNe hu hgNext hENx
          dsimp only [bv1]; split
          · rename_i hPN
            have hFuId : fG u = u := by
              have h1' : (u.metaPtr == g.metaPtr) = false := beq_false_of_ne fun hM =>
                hEG (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg hM)
              have h2' : (u.metaPtr == g.next) = false := beq_false_of_ne fun hM =>
                hENx (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hgNext (hM.trans hGNxMeta.symm))
              dsimp only [fG]; rw [h1', h2', hPN, h2']; simp
            rw [hFuId]
            exact (readBytesFromMap_congr (by decide) fun a ha =>
              (hWO_G a (fun hIn => DisjointRegions.not_both hDisjUG ha hIn)).trans
                (hWO_Nx2 a (fun hIn => DisjointRegions.not_both hDisjUNx ha hIn))).trans
              (meta_ownedRw_of_mem_groups hwf hu).2.2.2.1
          · rename_i hPN
            by_cases hEPv : u = gPrev
            · rw [hEPv]
              have hPvNeNx : gPrev ≠ gNext := fun hE => hPN (hGPvM.symm.trans (hE ▸ hGNxMeta))
              exact (readBytesFromMap_congr (by decide) fun a ha =>
                (hWO_G3 a (fun hIn => DisjointRegions.not_both (hDisjOfNe hgPrev hg hGPvNeG) ha hIn)).trans
                  (hWO_Nx3 a (fun hIn => DisjointRegions.not_both (hDisjOfNe hgPrev hgNext hPvNeNx) ha hIn))).trans
                hWR_Pv3
            · have hDisjUPv := hDisjOfNe hu hgPrev hEPv
              have hFuId : fG u = u := by
                have h1' : (u.metaPtr == g.metaPtr) = false := beq_false_of_ne fun hM =>
                  hEG (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg hM)
                have h2' : (u.metaPtr == g.next) = false := beq_false_of_ne fun hM =>
                  hENx (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hgNext (hM.trans hGNxMeta.symm))
                have h3' : (u.metaPtr == g.prev) = false := beq_false_of_ne fun hM =>
                  hEPv (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hgPrev (hM.trans hGPvM.symm))
                dsimp only [fG]; rw [h1', h2', h3']; simp
              rw [hFuId]
              exact (readBytesFromMap_congr (by decide) fun a ha =>
                (hWO_G3 a (fun hIn => DisjointRegions.not_both hDisjUG ha hIn)).trans
                  ((hWO_Nx3 a (fun hIn => DisjointRegions.not_both hDisjUNx ha hIn)).trans
                    (hWO_Pv3 a (fun hIn => DisjointRegions.not_both hDisjUPv ha hIn)))).trans
                (meta_ownedRw_of_mem_groups hwf hu).2.2.2.1
    have hMain := metaOnly_map_wf hwf hsc hg (newHead := g.next) (newMs := g.next :: msTl)
      (fG := fG) (bv1 := bv1)
      (fun u hu => by
        obtain ⟨hm, hmem, hlast, hsc', hmap, hab, hp, hnc, hsl, _, _, _, _⟩ := hSubF u hu
        refine ⟨hm, hmem, hlast, hsc', hmap, hab, hp, hnc, hsl ▸ rfl, fun hNeSc => ?_⟩
        have h1' : (u.metaPtr == g.metaPtr) = false := beq_false_of_ne fun hM =>
          hNeSc ((mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg hM) ▸ hScEq)
        have h2' : (u.metaPtr == g.next) = false := beq_false_of_ne fun hM =>
          hNeSc ((mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hgNext (hM.trans hGNxMeta.symm)) ▸ hGNxSc)
        have h3' : (u.metaPtr == g.prev) = false := beq_false_of_ne fun hM =>
          hNeSc ((mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hgPrev (hM.trans hGPvM.symm)) ▸ hGPvSc)
        dsimp only [fG]; rw [h1', h2', h3']; simp)
      (fun u hu => by
        have huWf := hwf.groups_wf u hu
        obtain ⟨_, _, hlast, hsc', _, _, _, _, _, hav, hfr, _, _⟩ := hSubF u hu
        rw [hav, hfr, hsc']
        refine ⟨huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1, huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, fun h63 => ?_⟩
        have hNeG : (u.metaPtr == g.metaPtr) = false := beq_false_of_ne fun hM => by
          have := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg hM; subst this; omega
        have hNeNx : (u.metaPtr == g.next) = false := beq_false_of_ne fun hM => by
          have := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hgNext (hM.trans hGNxMeta.symm); subst this; omega
        have hNePv : (u.metaPtr == g.prev) = false := beq_false_of_ne fun hM => by
          have := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hgPrev (hM.trans hGPvM.symm); subst this; omega
        dsimp only [fG]; rw [hNeG, hNeNx, hNePv]; simp only [Bool.false_eq_true, ↓reduceIte]
        exact (huWf.2.2.2.1 h63).2.2)
      (fun u hu j hj1 hj2 => by
        have hsw := (hwf.groups_wf u hu).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj2
        obtain ⟨_, _, _, _, _, _, _, _, hsl, hav, hfr, _, _⟩ := hSubF u hu
        have hGetEq : (fG u).slots[j]'hj1 = u.slots[j]'hj2 := by simp [hsl]
        dsimp only; rw [hGetEq, hav, hfr]
        exact ⟨Or.inl rfl, hsw.2.1, hsw.2.2.1, hsw.2.2.2.1⟩)
      hOutBv1 hMetaBv1
      (by
        have hTailSub : ∀ m ∈ g.next :: msTl, m ∈ m1 :: msTl := fun m hm => by simpa [hNxEqM1] using hm
        have hNodes1 : ((g.next :: msTl).filterMap fun m =>
            (findGroupByMeta st1 m).map fun x => (x.metaPtr, x.prev, x.next)) =
            (((gNext.metaPtr, gNext.prev, gNext.next) :: tlNodes).map fun d =>
              (d.1, if d.1 == g.next then g.prev else d.2.1, if d.1 == g.prev then g.next else d.2.2)) := by
          have hStep1 : ((g.next :: msTl).filterMap fun m =>
              (findGroupByMeta st1 m).map fun x => (x.metaPtr, x.prev, x.next)) =
              ((m1 :: msTl).filterMap fun m =>
                (findGroupByMeta st m).map fun u =>
                  (u.metaPtr, if u.metaPtr == g.next then g.prev else u.prev,
                    if u.metaPtr == g.prev then g.next else u.next)) := by
            rw [hNxEqM1]
            exact filterMap_congr_mem fun m hm => by
              obtain ⟨u, hu, rfl, _⟩ := hActOld.1 m (by rw [hMs1]; exact List.mem_cons_of_mem _ hm)
              have hNeGM : (u.metaPtr == g.metaPtr) = false := beq_false_of_ne fun hM =>
                (List.nodup_cons.mp hNdMs).1 (hM ▸ hm)
              have hu1 : fG u ∈ st.groups.map fG := List.mem_map_of_mem hu
              have hmU := (hSubF u hu).1
              have hFind1 : findGroupByMeta st1 u.metaPtr = some (fG u) := by
                rw [← hmU]; exact slot_findGroupByMeta_eq_of_mem (st := st1) hNd1 hu1
              rw [hFind1, slot_findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hu]
              dsimp only [fG]; rw [hNeGM]; simp only [Bool.false_eq_true, ↓reduceIte, Option.map_some, hNxEqM1]
          rw [hStep1, List.filterMap_cons, ← hGNxM, slot_findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hgNext]
          simp only [Option.map_some, List.map_cons, tlNodes]
          congr 1
          have hFmMap : ∀ l : List (BitVec 64),
              (l.filterMap fun m =>
                (findGroupByMeta st m).map fun u =>
                  (u.metaPtr, if u.metaPtr == g.next then g.prev else u.prev,
                    if u.metaPtr == g.prev then g.next else u.next)) =
              ((l.filterMap fun m => (findGroupByMeta st m).map fun x => (x.metaPtr, x.prev, x.next)).map
                fun d => (d.1, if d.1 == g.next then g.prev else d.2.1,
                  if d.1 == g.prev then g.next else d.2.2)) := fun l => by
            induction l with
            | nil => rfl
            | cons x xt ih =>
              simp only [List.filterMap_cons]
              cases findGroupByMeta st x with
              | none => exact ih
              | some ux => simp only [Option.map_some, List.map_cons]; exact congrArg _ ih
          exact hFmMap msTl
        refine ⟨fun m hm => ?_, hNodes1 ▸ hDll1, ?_, ?_, ?_, ?_, ?_⟩
        · obtain ⟨u, hu, rfl, hScU⟩ := hActOld.1 m (by rw [hMs1]; exact List.mem_cons_of_mem _ (hTailSub m hm))
          exact ⟨fG u, List.mem_map_of_mem hu, (hSubF u hu).1, (hSubF u hu).2.2.2.1.trans hScU⟩
        · have hLen0 := hActOld.2.2.1
          rw [hNodesEq, hMs1] at hLen0
          rw [hNodes1]; simp at hLen0 ⊢; omega
        · simp only [List.mem_map]; rintro _ ⟨u, hu, rfl⟩ hScF
          obtain ⟨hm, _, hlast, hsc', _, _, _, _, _, hav, hfr, _, hact⟩ := hSubF u hu
          have hOff := hActOld.2.2.2.1 u hu (hsc' ▸ hScF)
          by_cases hEG : u = g
          · rw [hEG]
            have hNotTail : g.metaPtr ∉ g.next :: msTl := fun hIn =>
              (List.nodup_cons.mp hNdMs).1 (hTailSub g.metaPtr hIn)
            dsimp only [fG]; simp [hNotTail, hAv0, hFr0, GroupDesc.activeIdx]
            exact hActEqG
          · have hNeGM : (u.metaPtr == g.metaPtr) = false := beq_false_of_ne fun hM =>
              hEG (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg hM)
            have hMemEquiv : u.metaPtr ∈ g.next :: msTl ↔ u.metaPtr ∈ st.activeLists[sc]'h2 := by
              rw [hMs1, hNxEqM1]; exact ⟨fun h => List.mem_cons_of_mem _ h, fun h => by
                rcases List.mem_cons.mp h with hEqG | hTl
                · exact False.elim (hEG (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg hEqG))
                · exact hTl⟩
            rw [hm, hav, hfr, hact, hlast, hMemEquiv]
            refine ⟨⟨fun hNot => ?_, fun ⟨hp0, _⟩ hIn => ?_⟩, hOff.2⟩
            · have hpv0 := (hOff.1.mp hNot).1; have hnx0 := (hOff.1.mp hNot).2
              have hNeNxM : (u.metaPtr == g.next) = false := beq_false_of_ne fun hM =>
                hNot (hMemEquiv.mp (hM ▸ List.mem_cons_self ..))
              have hNePvM : (u.metaPtr == g.prev) = false := beq_false_of_ne fun hM =>
                hNot (by rw [hMs1]; exact List.mem_cons_of_mem _ (hM ▸ hPvInTail))
              dsimp only [fG]; rw [hNeGM, hNeNxM, hNePvM]; simp [hpv0, hnx0]
            · dsimp only [fG] at hp0; rw [hNeGM] at hp0; simp only [Bool.false_eq_true, ↓reduceIte] at hp0
              split at hp0
              · exact hPvNe0 hp0
              · let allNodes := (g.metaPtr, g.prev, g.next) :: (gNext.metaPtr, gNext.prev, gNext.next) :: tlNodes
                have hMemNode : (u.metaPtr, u.prev, u.next) ∈ allNodes := by
                  dsimp only [allNodes]; rw [← hNodesEq]
                  exact List.mem_filterMap.mpr ⟨u.metaPtr, hIn, by
                    simp [slot_findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hu]⟩
                obtain ⟨k, hk, hGetK⟩ := List.getElem_of_mem hMemNode
                have hPrvEq := (hDll0.2.2.2 k hk).2
                have hCurPv : (allNodes[k]'hk).2.1 = u.prev := by rw [hGetK]
                rw [hCurPv] at hPrvEq
                have hModLt : (k + allNodes.length - 1) % allNodes.length < allNodes.length :=
                  Nat.mod_lt _ (by dsimp only [allNodes]; simp)
                have hNzPrv := hDll0.2.2.1 _ (List.getElem_mem hModLt)
                exact hNzPrv (hPrvEq ▸ hp0)
        · intro i hi hiPos _ hMemF hMF
          simp only [List.mem_map] at hMemF; obtain ⟨u, hu, rfl⟩ := hMemF
          obtain ⟨hm, _, _, _, _, _, _, _, _, hav, hfr, _, _⟩ := hSubF u hu
          rw [hm] at hMF; rw [hav, hfr]
          have hiOld : i + 1 < (st.activeLists[sc]'h2).length := by rw [hMs1]; simp at hi ⊢; omega
          have hMFOld : u.metaPtr = (st.activeLists[sc]'h2)[i + 1]'hiOld := by
            cases i with
            | zero => omega
            | succ k => simp [hMs1] at hi hMF ⊢; exact hMF
          exact hActOld.2.2.2.2.1 (i + 1) hiOld (by omega) u hu hMFOld
        · simp only [List.mem_map]
          rintro _ ⟨u₁, hu₁, rfl⟩ _ ⟨u₂, hu₂, rfl⟩ hs₁ hs₂ hl₁ hl₂
          obtain ⟨hm1, _, hl1', hsc1, _, _, _, _, _, _, _, _, ha1⟩ := hSubF u₁ hu₁
          obtain ⟨hm2, _, hl2', hsc2, _, _, _, _, _, _, _, _, ha2⟩ := hSubF u₂ hu₂
          rw [hm1, hm2]
          exact hActOld.2.2.2.2.2.1 u₁ hu₁ u₂ hu₂ (hsc1 ▸ hs₁) (hsc2 ▸ hs₂)
            (by rw [← ha1, ← hl1']; exact hl₁) (by rw [← ha2, ← hl2']; exact hl₂)
        · simp only [List.mem_map]; rintro _ ⟨u, hu, rfl⟩ hsF hlF
          obtain ⟨hm, _, hl', hsc', _, _, _, _, _, _, _, _, ha⟩ := hSubF u hu
          have hActLt : u.activeIdx < u.lastIdx := by rw [← ha, ← hl']; exact hlF
          have hPair := hActOld.2.2.2.2.2.2 u hu (hsc' ▸ hsF) hActLt
          have hNeG : u ≠ g := fun hE => by rw [hE] at hActLt; omega
          rw [hm]
          refine ⟨?_, hPair.2⟩
          have hInOld := hPair.1; rw [hMs1, hNxEqM1.symm] at hInOld
          rcases List.mem_cons.mp hInOld with hEqM | hTl
          · exact False.elim (hNeG (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg hEqM))
          · exact hTl)
      (fun u hu hScU hEmpU => by
        have hInOld : u.metaPtr ∈ st.activeLists[sc]'h2 := by
          subst hScU; exact (hwf.empty_groups_bound u hu hEmpU).2.2.2.2.1 h2
        rw [hMs1, hNxEqM1.symm] at hInOld
        rcases List.mem_cons.mp hInOld with hEqM | hTl
        · have rflU := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg hEqM
          rw [rflU, hNotEmpG] at hEmpU; cases hEmpU
        · exact hTl)
    obtain ⟨hWf1, hCnt1, hEff1, hDyn1, hOwn1, hPn1, hMp1⟩ := hMain
    have hBmCongr : ByteMap st.masterDom (OwnedRwByte st) bv1 =
        ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal :=
      SetSep_congr (fun a _ => (hOwn1 a).symm) (fun _ _ _ => rfl)
    have hUpdG := slot_byteMap_update40 hwf.masterDom_wf.1 (P := OwnedRwByte st) st.byteVal (hLenFG g) hMOwnG
    have hMOwnNxP1 : ∀ a : BitVec 64, InRegion gNext.metaPtr 40 a → P1 a ∧ a ∈ st.masterDom := fun a ha =>
      ⟨⟨(hMOwnNx a ha).1, fun hInG => DisjointRegions.not_both (hDisjOfNe hgNext hg hGNxNeG) ha hInG⟩,
        (hMOwnNx a ha).2⟩
    have hUpdNx := slot_byteMap_update40 hwf.masterDom_wf.1 (P := P1) st.byteVal (hLenFG gNext) hMOwnNxP1
    have hExtrG : ByteMap st.masterDom (OwnedRwByte st) st.byteVal =
        ((g.metaPtr ↦ₛ g.metaBytes) ∗ ByteMap st.masterDom P1 st.byteVal) := by
      rw [hUpdG.1, hMReadG]
    have hExtrNx : ByteMap st.masterDom P1 st.byteVal =
        ((gNext.metaPtr ↦ₛ gNext.metaBytes) ∗ Rest2) := by
      rw [hUpdNx.1, hMReadNx]
    refine ⟨List.mem_map_of_mem hgNext, (hSubF gNext hgNext).1.trans hGNxMeta,
      (hSubF gNext hgNext).2.2.2.1.trans hGNxSc,
      (hSubF gNext hgNext).2.2.2.2.2.2.2.2.2.1.trans hNextIdx1.1,
      (hSubF gNext hgNext).2.2.2.2.2.2.2.2.2.2.1 ▸ hNextIdx1.2,
      hWf1, hCnt1, hEff1, hDyn1, hPn1, hMp1, fun hPN => ?_, fun hPN => ?_⟩
    · have hPvEqNx : gPrev = gNext :=
        mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hgPrev hgNext (hGPvM.trans (hPN.trans hGNxMeta.symm))
      have hUpdG2 := slot_byteMap_update40 hwf.masterDom_wf.1 (P := OwnedRwByte st)
        (writeBytesToMap st.byteVal gNext.metaPtr (fG gNext).metaBytes) (hLenFG g) hMOwnG
      have hBv1Eq : bv1 = writeBytesToMap (writeBytesToMap st.byteVal gNext.metaPtr (fG gNext).metaBytes)
          g.metaPtr (fG g).metaBytes := by simp [bv1, hPN]
      refine ⟨hPvEqNx, by rw [hExtrG, hExtrNx], ?_⟩
      rw [hUpdNx.2, hUpdG2.2, ← hBv1Eq]; exact hBmCongr
    · have hPvNeNx : gPrev ≠ gNext := fun hE => hPN (hGPvM.symm.trans (hE ▸ hGNxMeta))
      have hMOwnPvP2 : ∀ a : BitVec 64, InRegion gPrev.metaPtr 40 a → P2 a ∧ a ∈ st.masterDom := fun a ha =>
        ⟨⟨⟨(hMOwnPv a ha).1, fun hInG => DisjointRegions.not_both (hDisjOfNe hgPrev hg hGPvNeG) ha hInG⟩,
          fun hInNx => DisjointRegions.not_both (hDisjOfNe hgPrev hgNext hPvNeNx) ha hInNx⟩, (hMOwnPv a ha).2⟩
      have hUpdPv := slot_byteMap_update40 hwf.masterDom_wf.1 (P := P2) st.byteVal (hLenFG gPrev) hMOwnPvP2
      have hExtrPv : Rest2 = ((gPrev.metaPtr ↦ₛ gPrev.metaBytes) ∗ Rest3) := by
        dsimp only [Rest2]; rw [hUpdPv.1, hMReadPv]
      have hUpdNx3 := slot_byteMap_update40 hwf.masterDom_wf.1 (P := P1)
        (writeBytesToMap st.byteVal gPrev.metaPtr (fG gPrev).metaBytes) (hLenFG gNext) hMOwnNxP1
      have hUpdG3 := slot_byteMap_update40 hwf.masterDom_wf.1 (P := OwnedRwByte st)
        (writeBytesToMap (writeBytesToMap st.byteVal gPrev.metaPtr (fG gPrev).metaBytes)
          gNext.metaPtr (fG gNext).metaBytes) (hLenFG g) hMOwnG
      have hBv1Eq : bv1 = writeBytesToMap
          (writeBytesToMap (writeBytesToMap st.byteVal gPrev.metaPtr (fG gPrev).metaBytes)
            gNext.metaPtr (fG gNext).metaBytes) g.metaPtr (fG g).metaBytes := by simp [bv1, hPN]
      refine ⟨hPvNeNx, by rw [hExtrG, hExtrNx, hExtrPv], ?_⟩
      rw [hUpdPv.2, hUpdNx3.2, hUpdG3.2, ← hBv1Eq]; exact hBmCongr

set_option maxHeartbeats 1200000 in
theorem tryAvail_bump_activeIdx_absorb {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {sc : Nat} (hsc : sc < 48) {g : GroupDesc} (hg : g ∈ st.groups) (hScEq : g.sc = sc)
    (hHead : st.ctx.active[sc]'(by rw [hwf.ctx_lens.1]; exact hsc) = g.metaPtr)
    (hLt : g.activeIdx < g.lastIdx)
    {newActByte : BitVec 8}
    (hLo : g.activeIdx + 1 ≤ ({ g with activeByte := newActByte } : GroupDesc).activeIdx)
    (hHi : ({ g with activeByte := newActByte } : GroupDesc).activeIdx ≤ g.lastIdx) :
    let g' : GroupDesc := { g with activeByte := newActByte }
    let fG : GroupDesc → GroupDesc := fun u => if u.metaPtr == g.metaPtr then g' else u
    let bv1 := writeBytesToMap st.byteVal (g.mem + 8#64) [newActByte]
    let st1 : MallocngSt := { st with groups := st.groups.map fG, byteVal := bv1 }
    let Rest := ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion (g.mem + 8#64) 1 a) st.byteVal
    g' ∈ st1.groups ∧
    ((2#32 <<< g'.activeIdx) - 1#32) &&& g'.freedMask ≠ 0#32 ∧
    MallocngWFInflight inflight base brkStart brk liveCost peakCost st1 ∧
    totalLiveCount st1 = totalLiveCount st ∧
    totalLiveEffCost st1 = totalLiveEffCost st ∧
    dynamicRootRegions st1 = dynamicRootRegions st ∧
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∧
    MappedSet st.masterDom (OwnedMappedByte st) =
      MappedSet st1.masterDom (OwnedMappedByte st1) ∧
    ByteMap st.masterDom (OwnedRwByte st) st.byteVal = (((g.mem + 8#64) ↦ₛ [g.activeByte]) ∗ Rest) ∧
    ((((g.mem + 8#64) ↦ₛ [newActByte]) ∗ Rest) = ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal) := by
  intro g' fG bv1 st1 Rest
  have hgWf := hwf.groups_wf g hg
  have hLast : g.lastIdx ≤ 31 := hgWf.2.1
  have hGsG := group_slot_toNat hgWf
  have hMem4096 : 4096 ≤ g.mem.toNat := hgWf.2.2.2.2.1
  have hEndLimG : (g.slotEnd g.lastIdx).toNat ≤ 2 ^ 48 := by
    obtain ⟨gr, hgr, hgrPos, _, hEndLe, _⟩ := group_root_containment hwf hg
    have hGrBnd := (hwf.groups_wf gr hgr).2.2.2.2.2.2.1
    have hTot : gr.totalBytes = gr.maplen * 4096 := by simp [GroupDesc.totalBytes, hgrPos]
    omega
  have hEndGe28 : g.mem.toNat + 28 ≤ (g.slotEnd g.lastIdx).toNat := by
    rw [hGsG.2.2.2.1]; have := Nat.mul_le_mul hGsG.2.1 hGsG.1; omega
  let a₀ : BitVec 64 := g.mem + 8#64
  have ha₀Nat : a₀.toNat = g.mem.toNat + 8 := add_ofNat_toNat (by omega)
  have hgCont0 : GroupContains g a₀.toNat := ⟨by omega, by omega⟩
  obtain ⟨_, hActRead0, hHdrOwn⟩ := group_header_ownedRw hwf hg
  have ha₀InHdr : InRegion g.mem 16 a₀ := (inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩
  obtain ⟨hOwn0, hDom0⟩ := hHdrOwn a₀ ha₀InHdr
  have hOutBv1 : ∀ a : BitVec 64, a ≠ a₀ → bv1 a = st.byteVal a := fun a hNe =>
    writeBytesToMap_out st.byteVal a₀ [newActByte] fun hIn => by
      have hb := (inRegion_bounds (by simp; omega)).mp hIn
      simp only [List.length_singleton] at hb
      exact hNe (BitVec.eq_of_toNat_eq (by omega))
  have hAtBv1 : bv1 a₀ = newActByte := by
    simpa using writeBytesToMap_in st.byteVal a₀ [newActByte] (i := 0) (by simp) (by simp)
  obtain ⟨grG, hgrG, hgrGPos, hGrGLo, _, hGrGHi⟩ := group_root_containment hwf hg
  have hGrGBnd := (hwf.groups_wf grG hgrG).2.2.2.2.2.2.1
  have hGrGTot : grG.totalBytes = grG.maplen * 4096 := by simp [GroupDesc.totalBytes, hgrGPos]
  have ha₀InGrG : InRegion grG.mem (grG.maplen * 4096) a₀ :=
    (inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩
  have hNotInMeta : ∀ mr ∈ allMetaSlots st, ∀ a, InRegion mr 40 a → a ≠ a₀ := by
    intro mr hmr a ha hEq
    obtain ⟨_, _, _, ⟨ma, hma, hInMa⟩, _⟩ := allMetaSlots_info hwf hmr
    exact DisjointRegions.not_both (metaArea_disjoint_rootGroup hwf hma hgrG hgrGPos)
      (hInMa a₀ (hEq ▸ ha)) ha₀InGrG
  have hFuEq : ∀ u ∈ st.groups, fG u = if u = g then g' else u := fun u hu => by
    dsimp only [fG]; by_cases hE : u = g
    · rw [hE]; simp
    · have hNeM : (u.metaPtr == g.metaPtr) = false :=
        beq_false_of_ne (fun hM => hE (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg hM))
      simp [hE, hNeM]
  have hSubF : ∀ u ∈ st.groups, (fG u).metaPtr = u.metaPtr ∧ (fG u).mem = u.mem ∧
      (fG u).lastIdx = u.lastIdx ∧ (fG u).sc = u.sc ∧ (fG u).maplen = u.maplen ∧
      (fG u).prev = u.prev ∧ (fG u).next = u.next ∧ (fG u).parentMeta = u.parentMeta ∧
      (fG u).nestedCap = u.nestedCap ∧ (fG u).slots = u.slots ∧
      (fG u).availMask = u.availMask ∧ (fG u).freedMask = u.freedMask ∧
      (fG u).freshZero = u.freshZero ∧ (fG u).isEmpty = u.isEmpty := fun u hu => by
    by_cases hE : u = g
    · rw [hE, hFuEq g hg]; simp [g', GroupDesc.isEmpty]
    · simp [hFuEq u hu, hE]
  have hMetaMap : (st.groups.map fG).map (·.metaPtr) = st.groups.map (·.metaPtr) := by
    rw [List.map_map]; exact List.map_congr_left fun u hu => (hSubF u hu).1
  have hMemMap : (st.groups.map fG).map (·.mem) = st.groups.map (·.mem) := by
    rw [List.map_map]; exact List.map_congr_left fun u hu => (hSubF u hu).2.1
  have hCntMap : ∀ sc', ((st.groups.map fG).filter (·.sc == sc')).map GroupDesc.cnt =
      (st.groups.filter (·.sc == sc')).map GroupDesc.cnt := fun sc' => by
    have hGen : ∀ (gs : List GroupDesc), (∀ u ∈ gs, u ∈ st.groups) →
        ((gs.map fG).filter (·.sc == sc')).map GroupDesc.cnt = (gs.filter (·.sc == sc')).map GroupDesc.cnt := by
      intro gs hSub; induction gs with
      | nil => rfl
      | cons x xt ih =>
        obtain ⟨_, _, hlx, hsx, _⟩ := hSubF x (hSub x (List.mem_cons_self ..))
        have ih' := ih (fun y hy => hSub y (List.mem_cons_of_mem _ hy))
        by_cases hc : (x.sc == sc') = true <;> simp [hsx, hc, GroupDesc.cnt, hlx, ih']
    exact hGen st.groups (fun _ h => h)
  have hRootFilt : ((st.groups.map fG).filter (fun x => decide (0 < x.maplen))).map (fun x => (x.mem, x.maplen * 4096)) =
      (st.groups.filter (fun x => decide (0 < x.maplen))).map (fun x => (x.mem, x.maplen * 4096)) := by
    have hGen : ∀ (gs : List GroupDesc), (∀ u ∈ gs, u ∈ st.groups) →
        ((gs.map fG).filter (fun x => decide (0 < x.maplen))).map (fun x => (x.mem, x.maplen * 4096)) =
          (gs.filter (fun x => decide (0 < x.maplen))).map (fun x => (x.mem, x.maplen * 4096)) := by
      intro gs hSub; induction gs with
      | nil => rfl
      | cons x xt ih =>
        obtain ⟨_, hmx, _, _, hmp, _⟩ := hSubF x (hSub x (List.mem_cons_self ..))
        have ih' := ih (fun y hy => hSub y (List.mem_cons_of_mem _ hy))
        by_cases hc : 0 < x.maplen <;> simp [hmx, hmp, hc, ih']
    exact hGen st.groups (fun _ h => h)
  have hClaimSum : ((st.groups.map fG).map (fun x => (x.slots.filter SlotState.isClaimed).length)).sum =
      (st.groups.map (fun x => (x.slots.filter SlotState.isClaimed).length)).sum := by
    congr 1; rw [List.map_map]; exact List.map_congr_left fun u hu => by simp [(hSubF u hu).2.2.2.2.2.2.2.2.2.1]
  have hLiveSum : ((st.groups.map fG).map (fun x => (x.slots.map slotLiveCount).sum)).sum =
      (st.groups.map (fun x => (x.slots.map slotLiveCount).sum)).sum := by
    congr 1; rw [List.map_map]; exact List.map_congr_left fun u hu => by simp [(hSubF u hu).2.2.2.2.2.2.2.2.2.1]
  have hEffSum : ((st.groups.map fG).map (fun x => (x.slots.map slotEffCost).sum)).sum =
      (st.groups.map (fun x => (x.slots.map slotEffCost).sum)).sum := by
    congr 1; rw [List.map_map]; exact List.map_congr_left fun u hu => by simp [(hSubF u hu).2.2.2.2.2.2.2.2.2.1]
  have hDynEq : dynamicRootRegions st1 = dynamicRootRegions st := by
    unfold dynamicRootRegions; dsimp only [st1]; rw [hRootFilt]
  have hRootIff : ∀ a, (∃ gr ∈ st1.groups, 0 < gr.maplen ∧ InRegion gr.mem (gr.maplen * 4096) a) ↔
      (∃ gr ∈ st.groups, 0 < gr.maplen ∧ InRegion gr.mem (gr.maplen * 4096) a) := fun a => by
    constructor
    · rintro ⟨u', hu', hp, hIn⟩; obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hu'
      obtain ⟨_, hmem, _, _, hmap, _⟩ := hSubF u hu
      exact ⟨u, hu, hmap ▸ hp, by rwa [hmem, hmap] at hIn⟩
    · rintro ⟨u, hu, hp, hIn⟩; obtain ⟨_, hmem, _, _, hmap, _⟩ := hSubF u hu
      exact ⟨fG u, List.mem_map_of_mem hu, hmap.symm ▸ hp, by rwa [hmem, hmap]⟩
  have hOwnIff : ∀ a, OwnedRwByte st1 a ↔ OwnedRwByte st a := by
    have hCuIff : ∀ a, CarvedUserByte st1 a ↔ CarvedUserByte st a := fun a => by
      constructor
      · rintro ⟨u', hu', s', hs', hIn'⟩
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hu'
        obtain ⟨_, hmem, hlast, hsc', hmap, _, _, _, _, hsl, _⟩ := hSubF u hu
        have hStr : (fG u).stride = u.stride := by unfold GroupDesc.stride; rw [hlast, hmap, hsc']
        exact ⟨u, hu, s', hsl ▸ hs', by simpa [GroupDesc.storage, hmem, hStr] using hIn'⟩
      · rintro ⟨u, hu, s, hs, hIn⟩
        obtain ⟨_, hmem, hlast, hsc', hmap, _, _, _, _, hsl, _⟩ := hSubF u hu
        have hStr : (fG u).stride = u.stride := by unfold GroupDesc.stride; rw [hlast, hmap, hsc']
        exact ⟨fG u, List.mem_map_of_mem hu, s, hsl.symm ▸ hs, by simpa [GroupDesc.storage, hmem, hStr] using hIn⟩
    intro a; unfold OwnedRwByte CarvedMetaByte; dsimp only [st1]
    rw [hRootIff a, hCuIff a]
  have hPnIff : ∀ a, OwnedProtNoneByte st1 a ↔ OwnedProtNoneByte st a := fun _ => Iff.rfl
  have hMpIff : ∀ a, OwnedMappedByte st1 a ↔ OwnedMappedByte st a := fun a => by
    unfold OwnedMappedByte; simp only [hRootIff a]; rfl
  have hDisjSlotNonNest : ∀ u ∈ st.groups, ∀ j (hj : j < u.slots.length),
      (∀ cm, u.slots[j]'hj ≠ .liveNested cm) →
      ∀ a : BitVec 64, (u.slotStart j).toNat - 4 ≤ a.toNat → a.toNat < (u.slotEnd j).toNat → a ≠ a₀ := by
    intro u hu j hj hNotNest a hLoA hHiA hEqA
    have huWf := hwf.groups_wf u hu
    have huGs := group_slot_toNat huWf
    have hjCnt : j < u.cnt := huWf.2.2.1 ▸ hj
    obtain ⟨hStJ, hEnJ, _⟩ := huGs.2.2.2.2.2 j hjCnt
    have hEndMonoU : (u.slotEnd j).toNat ≤ (u.slotEnd u.lastIdx).toNat := by
      rw [hEnJ, huGs.2.2.2.1]
      have : (j + 1) * u.stride ≤ u.cnt * u.stride := Nat.mul_le_mul_right _ (by omega); omega
    have huMem4096 : 4096 ≤ u.mem.toNat := huWf.2.2.2.2.1
    have huCont0 : GroupContains u a₀.toNat := ⟨by rw [← hEqA]; omega, by rw [← hEqA]; omega⟩
    rcases comparable_of_groupContains hwf hg hu hgCont0 huCont0 with rfl | hAncGU | hAncUG
    · rw [hEqA] at hLoA; omega
    · obtain ⟨_, _, k, hk, _, hLoK, _, _, _⟩ := strictAncestor_slot_bounds hwf hAncGU hg
      obtain ⟨hStKG, _, _⟩ := hGsG.2.2.2.2.2 k (hgWf.2.2.1 ▸ hk)
      rw [hEqA] at hLoA; omega
    · obtain ⟨ch, _, k, hk, hsK, hLoK, hChLeG, hGEndLeCh, hChEndLeK⟩ := strictAncestor_slot_bounds hwf hAncUG hu
      obtain ⟨hStK, hEnK, _⟩ := huGs.2.2.2.2.2 k (huWf.2.2.1 ▸ hk)
      by_cases hJK : j = k
      · subst hJK; exact hNotNest ch.metaPtr hsK
      · by_cases hLtJK : j < k
        · have : (j + 1) * u.stride ≤ k * u.stride := Nat.mul_le_mul_right _ (by omega)
          rw [hEqA] at hHiA; omega
        · have : (k + 1) * u.stride ≤ j * u.stride := Nat.mul_le_mul_right _ (by omega)
          have := hGsG.1; have := hGsG.2.1
          have : g.mem.toNat + 28 ≤ (g.slotEnd g.lastIdx).toNat := hEndGe28
          rw [hEqA] at hLoA; omega
  have hGroupsWf1 : ∀ u' ∈ st1.groups, GroupWf st1 u' := by
    simp only [st1, List.mem_map]; rintro _ ⟨u, hu, rfl⟩
    have huWf := hwf.groups_wf u hu
    have huGs := group_slot_toNat huWf
    obtain ⟨hm, hmem, hlast, hsc', hmap, hpv, hnx, hpar, hnc, hsl, hav, hfr, hfz, _⟩ := hSubF u hu
    have hcnt : (fG u).cnt = u.cnt := by simp [GroupDesc.cnt, hlast]
    have hstr : (fG u).stride = u.stride := by unfold GroupDesc.stride; rw [hlast, hmap, hsc']
    have hstor : (fG u).storage = u.storage := by unfold GroupDesc.storage; rw [hmem]
    have htot : (fG u).totalBytes = u.totalBytes := by unfold GroupDesc.totalBytes; rw [hmap, hnc]
    have hMetaRead1 : readBytesFromMap st1.byteVal (fG u).metaPtr 40 = (fG u).metaBytes := by
      rw [hm]
      have hId : (fG u).metaBytes = u.metaBytes := by
        by_cases hEU : u = g
        · rw [hEU, hFuEq g hg]; simp only [↓reduceIte]; rfl
        · simp [hFuEq u hu, hEU]
      rw [hId]
      have huAll : u.metaPtr ∈ allMetaSlots st := (hwf.free_bump_metas_wf.2.2.2.2.2 u.metaPtr).mp
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hu))))
      exact (readBytesFromMap_congr (by decide) fun a ha => hOutBv1 a (hNotInMeta u.metaPtr huAll a ha)).trans
        huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have huEndLim : (u.slotEnd u.lastIdx).toNat ≤ 2 ^ 48 := by
      obtain ⟨gr, hgr, hgrPos, _, hEndLe, _⟩ := group_root_containment hwf hu
      have hGrBnd := (hwf.groups_wf gr hgr).2.2.2.2.2.2.1
      have hTot : gr.totalBytes = gr.maplen * 4096 := by simp [GroupDesc.totalBytes, hgrPos]
      omega
    have huEndGe28 : u.mem.toNat + 28 ≤ (u.slotEnd u.lastIdx).toNat := by
      rw [huGs.2.2.2.1]; have := Nat.mul_le_mul huGs.2.1 huGs.1; omega
    have hHdrMem8 : readBytesFromMap st1.byteVal (fG u).mem 8 = unpack64 (fG u).metaPtr := by
      rw [hmem, hm]
      refine (readBytesFromMap_congr (by decide) fun a ha => hOutBv1 a (fun hEq => ?_)).trans
        huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hb := (inRegion_bounds (by omega)).mp ha
      by_cases hEU : u = g
      · rw [hEU, hEq] at hb; omega
      · have huCont0 : GroupContains u a₀.toNat := ⟨by rw [← hEq]; omega, by rw [← hEq]; omega⟩
        rcases comparable_of_groupContains hwf hg hu hgCont0 huCont0 with rfl | hAncGU | hAncUG
        · exact hEU rfl
        · obtain ⟨_, _, k, hk, _, _, _, _, _⟩ := strictAncestor_slot_bounds hwf hAncGU hg
          have := hGsG.2.2.2.2.2 k (hgWf.2.2.1 ▸ hk); rw [hEq] at hb; omega
        · obtain ⟨_, _, k, hk, _, _, _, _, _⟩ := strictAncestor_slot_bounds hwf hAncUG hu
          have := huGs.2.2.2.2.2 k (huWf.2.2.1 ▸ hk); rw [hEq] at hb; omega
    have hHdrAct1 : st1.byteVal ((fG u).mem + 8#64) = (fG u).activeByte := by
      by_cases hEU : u = g
      · rw [hEU, hFuEq g hg]; simp only [↓reduceIte, g', st1]; exact hAtBv1
      · simp only [hFuEq u hu, hEU, ↓reduceIte, st1]
        refine (hOutBv1 (u.mem + 8#64) fun hEq => ?_).trans
          huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have huMem4096 : 4096 ≤ u.mem.toNat := huWf.2.2.2.2.1
        have hEndGe16U : u.mem.toNat + 16 ≤ (u.slotEnd u.lastIdx).toNat := by
          rw [huGs.2.2.2.1]; have := Nat.mul_le_mul huGs.2.1 huGs.1; omega
        have hEndLimU : (u.slotEnd u.lastIdx).toNat ≤ 2 ^ 48 := by
          obtain ⟨gr, hgr, hgrPos, _, hEndLe, _⟩ := group_root_containment hwf hu
          have hGrBnd := (hwf.groups_wf gr hgr).2.2.2.2.2.2.1
          have hTot : gr.totalBytes = gr.maplen * 4096 := by simp [GroupDesc.totalBytes, hgrPos]
          omega
        have huAdd8 : (u.mem + 8#64).toNat = u.mem.toNat + 8 := add_ofNat_toNat (by omega)
        have huCont0 : GroupContains u a₀.toNat := ⟨by rw [← hEq]; omega, by rw [← hEq]; omega⟩
        rcases comparable_of_groupContains hwf hg hu hgCont0 huCont0 with rfl | hAncGU | hAncUG
        · exact hEU rfl
        · obtain ⟨_, _, k, hk, _, _, _, _, _⟩ := strictAncestor_slot_bounds hwf hAncGU hg
          have := hGsG.2.2.2.2.2 k (hgWf.2.2.1 ▸ hk); rw [hEq] at huAdd8; omega
        · obtain ⟨_, _, k, hk, _, _, _, _, _⟩ := strictAncestor_slot_bounds hwf hAncUG hu
          have := huGs.2.2.2.2.2 k (huWf.2.2.1 ▸ hk); rw [hEq] at huAdd8; omega
    have hEndLastEq : (fG u).slotEnd (fG u).lastIdx = u.slotEnd u.lastIdx := by
      simp [GroupDesc.slotEnd, GroupDesc.slotStart, hstor, hstr, hlast]
    refine ⟨hsc' ▸ huWf.1, hlast ▸ huWf.2.1, by rw [hsl, hcnt]; exact huWf.2.2.1,
      by rw [hsc', hlast, hmap, hpv, hnx]; exact huWf.2.2.2.1,
      hmem ▸ huWf.2.2.2.2.1, hmem ▸ huWf.2.2.2.2.2.1,
      by rw [hmem, htot]; exact huWf.2.2.2.2.2.2.1,
      by rw [hcnt, hstr, htot]; exact huWf.2.2.2.2.2.2.2.1,
      by rw [hmap, hcnt, hstr, htot]; exact huWf.2.2.2.2.2.2.2.2.1,
      ?_, by rw [hmap, hpar]; exact huWf.2.2.2.2.2.2.2.2.2.2.1,
      by rw [hmap, hmem, hnc, hsc', hlast, hstr]; exact huWf.2.2.2.2.2.2.2.2.2.2.2.1,
      ?_, by rw [hav, hfr]; exact huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      by rw [hav, hfr, hcnt]; exact huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      ?_, hMetaRead1, hHdrMem8, hHdrAct1, ?_⟩
    · change bv1 ((fG u).slotEnd (fG u).lastIdx) = 0#8
      rw [hEndLastEq]
      refine (hOutBv1 (u.slotEnd u.lastIdx) fun hEq => ?_).trans huWf.2.2.2.2.2.2.2.2.2.1
      have hEndGe28U : u.mem.toNat + 28 ≤ (u.slotEnd u.lastIdx).toNat := by
        rw [huGs.2.2.2.1]; have := Nat.mul_le_mul huGs.2.1 huGs.1; omega
      have huCont0 : GroupContains u a₀.toNat := ⟨by rw [← hEq]; omega, by rw [← hEq]; exact Nat.le_refl _⟩
      rcases comparable_of_groupContains hwf hg hu hgCont0 huCont0 with rfl | hAncGU | hAncUG
      · rw [hEq] at hEndGe28U; omega
      · obtain ⟨_, _, k, hk, _, _, _, _, _⟩ := strictAncestor_slot_bounds hwf hAncGU hg
        have := hGsG.2.2.2.2.2 k (hgWf.2.2.1 ▸ hk); rw [hEq] at hEndGe28U; omega
      · obtain ⟨ch, _, k, hk, _, _, _, _, hChEndLeK⟩ := strictAncestor_slot_bounds hwf hAncUG hu
        obtain ⟨_, hEnK, _⟩ := huGs.2.2.2.2.2 k (huWf.2.2.1 ▸ hk)
        have : (u.slotEnd k).toNat ≤ (u.slotEnd u.lastIdx).toNat := by
          rw [hEnK, huGs.2.2.2.1]
          have := Nat.mul_le_mul_right u.stride (show k + 1 ≤ u.cnt by rw [← huWf.2.2.1]; omega)
          omega
        rw [hEq] at this; omega
    · intro hZero
      obtain ⟨h1Last, pg, hpg, pIdx, hp, hParPg, hPgSc, hScLt, hPg24, hPgSl, hStLe, hCapLe, hCapEq⟩ :=
        huWf.2.2.2.2.2.2.2.2.2.2.2.2.1 (hmap ▸ hZero)
      obtain ⟨pgM, pgMem, pgLast, pgSc, pgMap, _, _, _, _, pgSl, _⟩ := hSubF pg hpg
      have hp1 : pIdx < (fG pg).slots.length := pgSl.symm ▸ hp
      have hPgStr : (fG pg).stride = pg.stride := by unfold GroupDesc.stride; rw [pgLast, pgMap, pgSc]
      have hPgSto : (fG pg).storage = pg.storage := by unfold GroupDesc.storage; rw [pgMem]
      refine ⟨hlast ▸ h1Last, fG pg, List.mem_map_of_mem hpg, pIdx, hp1, ?_⟩
      rw [hpar, pgM, pgSc, hsc', hmem, hnc]
      simp only [GroupDesc.slotStart, GroupDesc.slotEnd, hPgSto, hPgStr]
      exact ⟨hParPg, hPgSc, hScLt, hPg24, by simpa [pgSl, hm] using hPgSl, hStLe, hCapLe, hCapEq⟩
    · by_cases hEU : u = g
      · rw [hEU, hFuEq g hg]; simp only [↓reduceIte]; exact hHi
      · simp [hFuEq u hu, hEU, huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    · intro j hjF
      have hjU : j < u.slots.length := hsl ▸ hjF
      have hGetEq : (fG u).slots[j]'hjF = u.slots[j]'hjU := by simp [hsl]
      rw [hGetEq]
      have hjCnt : j < u.cnt := huWf.2.2.1 ▸ hjU
      obtain ⟨hStJ, hEnJ, _⟩ := huGs.2.2.2.2.2 j hjCnt
      have hStrGe16 : 16 ≤ u.stride := huGs.1
      have hMulSuccJ : (j + 1) * u.stride = j * u.stride + u.stride := Nat.succ_mul j u.stride
      have hEndLimU : (u.slotEnd u.lastIdx).toNat ≤ 2 ^ 48 := by
        obtain ⟨gr, hgr, hgrPos, _, hEndLe, _⟩ := group_root_containment hwf hu
        have hGrBnd := (hwf.groups_wf gr hgr).2.2.2.2.2.2.1
        have hTot : gr.totalBytes = gr.maplen * 4096 := by simp [GroupDesc.totalBytes, hgrPos]
        omega
      have hEndMonoJ : (u.slotEnd j).toNat ≤ (u.slotEnd u.lastIdx).toNat := by
        rw [hEnJ, huGs.2.2.2.1]
        have := Nat.mul_le_mul_right u.stride (show j + 1 ≤ u.cnt by omega)
        omega
      have huMem4096 : 4096 ≤ u.mem.toNat := huWf.2.2.2.2.1
      have hSub4J := sub_ofNat_toNat (x := u.slotStart j) (k := 4) (by omega)
      have hZNe : u.slotStart j - 4#64 ≠ a₀ := by
        by_cases hNest : ∃ cm, u.slots[j]'hjU = .liveNested cm
        · obtain ⟨cm, hN⟩ := hNest
          have hSwOld := huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hjU
          rw [hN] at hSwOld
          obtain ⟨_, cg₀, hcg₀, rfl, hpar₀, hlo₀, _, hhi₀, _⟩ := hSwOld.2.2.2.2
          intro hEqZ
          have huCont0 : GroupContains u a₀.toNat := ⟨by rw [← hEqZ]; omega, by rw [← hEqZ]; omega⟩
          rcases comparable_of_groupContains hwf hg hu hgCont0 huCont0 with rfl | hAncGU | hAncUG
          · rw [hEqZ] at hSub4J; omega
          · obtain ⟨_, _, k, hk, _, _, _, _, _⟩ := strictAncestor_slot_bounds hwf hAncGU hg
            have := hGsG.2.2.2.2.2 k (hgWf.2.2.1 ▸ hk); rw [hEqZ] at hSub4J; omega
          · obtain ⟨ch, _, k, hk, hsK, _, hChLeG, hGEndLeCh, hChEndLeK⟩ := strictAncestor_slot_bounds hwf hAncUG hu
            obtain ⟨hStK, hEnK, _⟩ := huGs.2.2.2.2.2 k (huWf.2.2.1 ▸ hk)
            by_cases hJK : j = k
            · subst hJK; rw [hN] at hsK; injection hsK with hM
              have hEqCg : cg₀ = ch := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg₀ ‹_› hM
              rw [← hEqCg] at hChLeG hGEndLeCh; rw [hEqZ] at hSub4J; omega
            · by_cases hLtJK : j < k
              · have := Nat.mul_le_mul_right u.stride (show j + 1 ≤ k by omega); rw [hEqZ] at hSub4J; omega
              · have := Nat.mul_le_mul_right u.stride (show k + 1 ≤ j by omega); rw [hEqZ] at hSub4J; omega
        · exact hDisjSlotNonNest u hu j hjU (fun cm hN => hNest ⟨cm, hN⟩) (u.slotStart j - 4#64)
            (by omega) (by omega)
      have hSwBase : SlotWf st1 u j (u.slots[j]'hjU) :=
        slotWf_congr huWf hjU ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          (huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hjU)
          (hOutBv1 _ hZNe)
          (fun cm hN cg₀ hcg₀ hcm hpar₀ => by
            refine ⟨fun a ha => hOutBv1 a fun hEq => ?_,
              fG cg₀, List.mem_map_of_mem hcg₀, (hSubF cg₀ hcg₀).1, (hSubF cg₀ hcg₀).2.2.2.2.2.2.2.1,
              (hSubF cg₀ hcg₀).2.1, (hSubF cg₀ hcg₀).2.2.2.2.2.2.2.2.1⟩
            have hcgWf := hwf.groups_wf cg₀ hcg₀
            have hcgGs := group_slot_toNat hcgWf
            have hcgMem4096 : 4096 ≤ cg₀.mem.toNat := hcgWf.2.2.2.2.1
            have hSub4 := sub_ofNat_toNat (x := cg₀.mem) (k := 4) (by omega)
            have haB := (inRegion_bounds (by omega)).mp (hEq ▸ ha)
            have hSwOld := huWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hjU; rw [hN] at hSwOld
            obtain ⟨_, cg₁, hcg₁, hcm₁, _, hlo₁, _, hhi₁, _⟩ := hSwOld.2.2.2.2
            have rflCg := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg₀ hcg₁ (hcm.trans hcm₁.symm)
            rw [← rflCg] at hlo₁ hhi₁
            have hEndGe16Cg : cg₀.mem.toNat + 16 ≤ (cg₀.slotEnd cg₀.lastIdx).toNat := by
              rw [hcgGs.2.2.2.1]; have := Nat.mul_le_mul hcgGs.2.1 hcgGs.1; omega
            have hMap0 : cg₀.maplen = 0 := Nat.eq_zero_of_not_pos fun hp => by
              have hN0 := hcgWf.2.2.2.2.2.2.2.2.2.2.1.mp hp; rw [hN0] at hpar₀; cases hpar₀
            have hCapGe : (cg₀.slotEnd cg₀.lastIdx).toNat ≤ cg₀.mem.toNat + cg₀.nestedCap := by
              have h := hcgGs.2.2.2.2.1; rw [← hcgGs.2.2.2.1] at h
              simpa [GroupDesc.totalBytes, hMap0] using h
            have huCont0 : GroupContains u a₀.toNat := ⟨by omega, by omega⟩
            rcases comparable_of_groupContains hwf hg hu hgCont0 huCont0 with rfl | hAncGU | hAncUG
            · omega
            · obtain ⟨_, _, k, hk, _, _, _, _, _⟩ := strictAncestor_slot_bounds hwf hAncGU hg
              have := hGsG.2.2.2.2.2 k (hgWf.2.2.1 ▸ hk); omega
            · obtain ⟨ch, hch, k, hk, hsK, _, hChLeG, hGEndLeCh, hChEndLeK⟩ := strictAncestor_slot_bounds hwf hAncUG hu
              obtain ⟨hStK, hEnK, _⟩ := huGs.2.2.2.2.2 k (huWf.2.2.1 ▸ hk)
              by_cases hJK : j = k
              · subst hJK; rw [hN] at hsK; injection hsK with hM
                have rflCh := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg₀ hch (hcm.trans hM)
                rw [← rflCh] at hChLeG hGEndLeCh; omega
              · by_cases hLtJK : j < k
                · have := Nat.mul_le_mul_right u.stride (show j + 1 ≤ k by omega); omega
                · have := Nat.mul_le_mul_right u.stride (show k + 1 ≤ j by omega); omega)
          (fun us rq ef hU a ha => by
            have haB := (inRegion_bounds (by omega)).mp ha
            exact hOutBv1 a (hDisjSlotNonNest u hu j hjU (by rw [hU]; intro _ h; cases h) a
              (by omega) (by rw [hEnJ]; omega)))
      obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := hSwBase
      have hStartEq : (fG u).slotStart j = u.slotStart j := by unfold GroupDesc.slotStart; rw [hstor, hstr]
      have hEndEq : (fG u).slotEnd j = u.slotEnd j := by unfold GroupDesc.slotEnd; rw [hStartEq, hstr]
      refine ⟨hStartEq ▸ hs1, hav ▸ hs2, hfr ▸ hs3, fun hGt => hs4 ?_, ?_⟩
      · by_cases hEU : u = g
        · rw [hEU] at hGt ⊢; rw [hFuEq g hg] at hGt; simp only [↓reduceIte] at hGt
          change g.activeIdx + 1 ≤ g'.activeIdx at hLo; omega
        · simp only [hFuEq u hu, hEU, ↓reduceIte] at hGt; exact hGt
      · cases hsJ : u.slots[j]'hjU with
        | freeAvail | freeInactive | claimed => simp [hsJ] at hs5 ⊢
        | liveNested cm =>
          rw [hsJ] at hs5; simp only [hm, hStartEq, hEndEq, hstor, hsc']
          exact hs5
        | liveUser us rq ef =>
          rw [hsJ] at hs5; simp only [hStartEq, hEndEq, hstor, hsc', hmap]
          exact hs5
  have hMaskNz : ((2#32 <<< g'.activeIdx) - 1#32) &&& g'.freedMask ≠ 0#32 := by
    let k : Nat := g.activeIdx + 1
    have hk : k < g.slots.length := by rw [hgWf.2.2.1]; unfold GroupDesc.cnt; omega
    have hSwK := hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 k hk
    have hFrK : g.freedMask.getLsbD k = true := hSwK.2.2.1.mpr (hSwK.2.2.2.1 (by omega))
    have hActMaskK : ((2#32 <<< g'.activeIdx) - 1#32).getLsbD k = true := by
      have hBits := (activateMask_props (m := 0#32) hHi hLast (Nat.two_pow_pos _)).1 k (by dsimp [k]; omega)
      rw [hBits.1]
      exact decide_eq_true (by dsimp [k]; change g.activeIdx + 1 ≤ g'.activeIdx at hLo; omega)
    intro hZero
    have hBit : (((2#32 <<< g'.activeIdx) - 1#32) &&& g'.freedMask).getLsbD k = true := by
      simp [BitVec.getLsbD_and, hActMaskK, show g'.freedMask = g.freedMask from rfl, hFrK]
    rw [hZero] at hBit; simp at hBit
  have hDisjPage : ∀ p : BitVec 64,
      (p ∈ st.metaAreas.map (·.base) ∨ p ∈ st.guardPages ∨ p ∈ st.availMetaPages) →
      ∀ a : BitVec 64, InRegion p 4096 a → a ≠ a₀ := by
    intro p hp a ha hEq
    have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd
    rw [PairwiseDisjointRegions.append_iff] at hpd
    have hpMem : (p, 4096) ∈ st.metaAreas.map (fun ma => (ma.base, 4096)) ++
        st.guardPages.map (fun gp => (gp, 4096)) ++ st.availMetaPages.map (fun ap => (ap, 4096)) := by
      rcases hp with hm | hg' | ha'
      · obtain ⟨ma, hma, rfl⟩ := List.mem_map.mp hm
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma))
      · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hg'))
      · exact List.mem_append_right _ (List.mem_map_of_mem ha')
    have hGrMem : (grG.mem, grG.maplen * 4096) ∈
        (st.groups.filter fun x => decide (0 < x.maplen)).map (fun x => (x.mem, x.maplen * 4096)) :=
      List.mem_map_of_mem (List.mem_filter.mpr ⟨hgrG, decide_eq_true hgrGPos⟩)
    exact DisjointRegions.not_both (hpd.2.2 (p, 4096) hpMem _ hGrMem) (hEq ▸ ha) ha₀InGrG
  have hActLtImp : ∀ u ∈ st.groups, (fG u).activeIdx < (fG u).lastIdx → u.activeIdx < u.lastIdx := by
    intro u hu hF; by_cases hE : u = g
    · exact hE ▸ hLt
    · simpa [hFuEq u hu, hE] using hF
  have hWf1 : MallocngWFInflight inflight base brkStart brk liveCost peakCost st1 := {
    base_wf := trivial
    brk_bounds := hwf.brk_bounds
    ctx_lens := hwf.ctx_lens
    initDone_wf := hwf.initDone_wf
    initZero_wf := fun hZ => by
      have hNil := (hwf.initZero_wf hZ).2.2.2.2.2.2.2.2.2.1; rw [hNil] at hg; cases hg
    bounces_wf := hwf.bounces_wf
    usage_wf := fun sc' hsc' => by simpa [st1, hCntMap sc'] using hwf.usage_wf sc' hsc'
    brk_mode_wf := hwf.brk_mode_wf
    metaAreas_wf := ⟨hwf.metaAreas_wf.1, fun ma hma => by
      obtain ⟨h1, h2, h3, h4⟩ := hwf.metaAreas_wf.2.1 ma hma
      refine ⟨h1, h2, h3, (readBytesFromMap_congr (by decide) fun a ha => hOutBv1 a ?_).trans h4⟩
      have hb := (inRegion_bounds (by omega)).mp ha
      exact hDisjPage ma.base (Or.inl (List.mem_map_of_mem hma)) a ((inRegion_bounds (by omega)).mpr ⟨hb.1, by omega⟩),
      hwf.metaAreas_wf.2.2⟩
    guard_avail_wf := ⟨hwf.guard_avail_wf.1, hwf.guard_avail_wf.2.1, hwf.guard_avail_wf.2.2.1,
      fun ap hap => by
        obtain ⟨h1, h2, h3, h4⟩ := hwf.guard_avail_wf.2.2.2 ap hap
        exact ⟨h1, h2, h3, (readBytesFromMap_congr (by decide) fun a ha =>
          hOutBv1 a (hDisjPage ap (Or.inr (Or.inr hap)) a ha)).trans h4⟩⟩
    inflight_wf := by unfold totalClaimedSlots; dsimp only [st1]; rw [hClaimSum]; exact hwf.inflight_wf
    free_bump_metas_wf := by
      obtain ⟨hDll, hFmB, hBumpC, hBmB, hNd, hAll⟩ := hwf.free_bump_metas_wf
      exact ⟨hDll, fun fm hfm => (readBytesFromMap_congr (by decide) fun a ha =>
          hOutBv1 a (hNotInMeta fm.ptr ((hAll fm.ptr).mp (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_right _ (List.mem_map_of_mem hfm))))) a ha)).trans (hFmB fm hfm),
        hBumpC, fun bm hbm => (readBytesFromMap_congr (by decide) fun a ha =>
          hOutBv1 a (hNotInMeta bm ((hAll bm).mp (List.mem_append_left _ (List.mem_append_right _ hbm))) a ha)).trans
            (hBmB bm hbm),
        by simpa [st1, hMetaMap] using hNd, fun m => by simpa [st1, hMetaMap, allMetaSlots] using hAll m⟩
    groups_nodup := ⟨by simpa [st1, hMetaMap] using hwf.groups_nodup.1,
      by simpa [st1, hMemMap] using hwf.groups_nodup.2⟩
    groups_wf := hGroupsWf1
    regions_disjoint := ⟨hDynEq ▸ hwf.regions_disjoint.1, trivial⟩
    active_wf := fun sc' h1' h2' => by
      have hOld := hwf.active_wf sc' h1' h2'
      let ms' := st.activeLists[sc']'h2'
      have hNd1 : (st1.groups.map (·.metaPtr)).Nodup := by simpa [st1, hMetaMap] using hwf.groups_nodup.1
      have hFmEq : (ms'.filterMap fun m => (findGroupByMeta st1 m).map fun x => (x.metaPtr, x.prev, x.next)) =
          (ms'.filterMap fun m => (findGroupByMeta st m).map fun x => (x.metaPtr, x.prev, x.next)) :=
        filterMap_congr_mem fun m hm => by
          obtain ⟨u, hu, rfl, _⟩ := hOld.1 m hm
          obtain ⟨hmU, _, _, _, _, hpvU, hnxU, _⟩ := hSubF u hu
          have hu1 : fG u ∈ st1.groups := List.mem_map_of_mem hu
          rw [← hmU, slot_findGroupByMeta_eq_of_mem hNd1 hu1, hmU, slot_findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hu]
          simp [hmU, hpvU, hnxU]
      refine ⟨fun m hm => ?_, hFmEq ▸ hOld.2.1, hFmEq ▸ hOld.2.2.1, ?_, ?_, ?_, ?_⟩
      · obtain ⟨u, hu, rfl, hScU⟩ := hOld.1 m hm
        exact ⟨fG u, List.mem_map_of_mem hu, (hSubF u hu).1, (hSubF u hu).2.2.2.1.trans hScU⟩
      · simp only [st1, List.mem_map]; rintro _ ⟨u, hu, rfl⟩ hScF
        obtain ⟨hmU, _, hlastU, hscU, _, hpvU, hnxU, _, _, _, havU, hfrU, _⟩ := hSubF u hu
        have hOff := hOld.2.2.2.1 u hu (hscU ▸ hScF)
        rw [hmU, hpvU, hnxU, havU, hfrU, hlastU]
        refine ⟨hOff.1, fun hNot => ⟨(hOff.2 hNot).1, (hOff.2 hNot).2.1, ?_⟩⟩
        have hEqU := (hOff.2 hNot).2.2
        have hNE : u ≠ g := fun hE => by subst hE; omega
        simpa [hFuEq u hu, hNE] using hEqU
      · simp only [st1, List.mem_map]; rintro i hi hiPos _ ⟨u, hu, rfl⟩ hMF
        obtain ⟨hmU, _, _, _, _, _, _, _, _, _, havU, hfrU, _⟩ := hSubF u hu
        rw [havU, hfrU]; exact hOld.2.2.2.2.1 i hi hiPos u hu (hmU ▸ hMF)
      · simp only [st1, List.mem_map]
        rintro _ ⟨u₁, hu₁, rfl⟩ _ ⟨u₂, hu₂, rfl⟩ hs₁ hs₂ hl₁ hl₂
        rw [(hSubF u₁ hu₁).1, (hSubF u₂ hu₂).1]
        exact hOld.2.2.2.2.2.1 u₁ hu₁ u₂ hu₂ ((hSubF u₁ hu₁).2.2.2.1 ▸ hs₁) ((hSubF u₂ hu₂).2.2.2.1 ▸ hs₂)
          (hActLtImp u₁ hu₁ hl₁) (hActLtImp u₂ hu₂ hl₂)
      · simp only [st1, List.mem_map]; rintro _ ⟨u, hu, rfl⟩ hsF hlF
        rw [(hSubF u hu).1]
        exact hOld.2.2.2.2.2.2 u hu ((hSubF u hu).2.2.2.1 ▸ hsF) (hActLtImp u hu hlF)
    liveMap_wf := fun p n => by
      rw [hwf.liveMap_wf p n]; simp only [st1, List.mem_map]
      exact ⟨fun ⟨u, hu, idx, hIdx, ef, hs⟩ =>
        ⟨fG u, ⟨u, hu, rfl⟩, idx, (hSubF u hu).2.2.2.2.2.2.2.2.2.1.symm ▸ hIdx, ef,
          by simpa [(hSubF u hu).2.2.2.2.2.2.2.2.2.1] using hs⟩,
        fun ⟨_, ⟨u, hu, rfl⟩, idx, hIdx, ef, hs⟩ =>
        ⟨u, hu, idx, (hSubF u hu).2.2.2.2.2.2.2.2.2.1 ▸ hIdx, ef,
          by simpa [(hSubF u hu).2.2.2.2.2.2.2.2.2.1] using hs⟩⟩
    live_le_peak := hwf.live_le_peak
    effCost_le_live := by unfold totalLiveEffCost; dsimp only [st1]; rw [hEffSum]; exact hwf.effCost_le_live
    meta_pages_bound := hwf.meta_pages_bound
    empty_groups_bound := fun g1 hg1 hEmpF => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg1
      obtain ⟨hmU, _, hlU, hsU, hmpU, _, _, _, _, _, _, _, _, hEmpEq⟩ := hSubF u hu
      obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hwf.empty_groups_bound u hu (hEmpEq ▸ hEmpF)
      refine ⟨hmpU ▸ e1, hsU ▸ e2, hsU ▸ e3, hmpU ▸ e4, fun hLt => ?_,
        fun g1' hg1' hEmpF' hScF' => ?_, fun hL0 => hsU ▸ hmpU ▸ e7 (hlU ▸ hL0)⟩
      · dsimp only [st1] at hLt ⊢; rw [hmU]; simpa [hsU] using e5 (hsU ▸ hLt)
      · obtain ⟨u', hu', rfl⟩ := List.mem_map.mp hg1'
        obtain ⟨hmU', _, _, hsU', _, _, _, _, _, _, _, _, _, hEmpEq'⟩ := hSubF u' hu'
        rw [hmU', hmU]
        exact e6 u' hu' (hEmpEq' ▸ hEmpF') (hsU'.symm.trans (hScF'.trans hsU))
    masterDom_wf := ⟨hwf.masterDom_wf.1,
      fun a h => hwf.masterDom_wf.2.1 a (by rwa [← hOwnIff a, ← hPnIff a, ← hMpIff a]),
      fun a ha => hDynEq ▸ hwf.masterDom_wf.2.2 a ha⟩
  }
  have hIn1Eq : ∀ a : BitVec 64, InRegion a₀ 1 a → a = a₀ := fun a ha => by
    have hb := (inRegion_bounds (by omega)).mp ha; exact BitVec.eq_of_toNat_eq (by omega)
  have hExtr1 := ByteMap_extract_slice hwf.masterDom_wf.1 (keep := OwnedRwByte st) st.byteVal a₀ (n := 1)
    (by decide) (fun a ha => hIn1Eq a ha ▸ hDom0) (fun a ha => hIn1Eq a ha ▸ hOwn0)
  have hRead1 : readBytesFromMap st.byteVal a₀ 1 = [g.activeByte] := by
    rw [readBytesFromMap_one, hActRead0]
  have hAbs1 := ByteMap_absorb_slice hwf.masterDom_wf.1
    (keep := fun a => OwnedRwByte st a ∧ ¬ InRegion a₀ 1 a) st.byteVal a₀ [newActByte]
    (by simp) (fun a ha => hIn1Eq a (by simpa using ha) ▸ hDom0) (fun _ ha h => h.2 (by simpa using ha))
  refine ⟨List.mem_map.mpr ⟨g, hg, by simp [fG]⟩,
    hMaskNz, hWf1,
    by unfold totalLiveCount; dsimp only [st1]; exact hLiveSum,
    by unfold totalLiveEffCost; dsimp only [st1]; exact hEffSum,
    hDynEq,
    SetSep_congr (fun _ _ => Iff.rfl) (fun a _ hPn => by
      rcases hPn with ⟨gp, hgp, ha⟩ | ⟨ap, hap, ha⟩
      · exact congrArg (fun b => a ↦₈ₙ b) (hOutBv1 a (hDisjPage gp (Or.inr (Or.inl hgp)) a ha)).symm
      · exact congrArg (fun b => a ↦₈ₙ b) (hOutBv1 a (hDisjPage ap (Or.inr (Or.inr hap)) a ha)).symm),
    SetSep_congr (fun a _ => (hMpIff a).symm) (fun _ _ _ => rfl),
    by rw [hExtr1, hRead1],
    hAbs1.trans (SetSep_congr (fun a _ => by
      simp only [List.length_singleton]; rw [hOwnIff a]
      exact ⟨fun h => h.elim (·.1) (fun ha => hIn1Eq a ha ▸ hOwn0),
        fun h => Classical.byCases (fun ha : InRegion a₀ 1 a => Or.inr ha) (fun ha => Or.inl ⟨h, ha⟩)⟩)
      (fun _ _ _ => rfl))⟩

end VerifiedLibraries.Mallocng.Proofs
