/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.VendorFree.PlacedFreeHelpers3
public import VerifiedLibraries.Mallocng.Proofs.AllocMetaHelpers

/-!
# Placed `__libc_free` and `nontrivial_free` Invariant Helpers

`MallocngWFInflight` transitions for the `__libc_free` lockless `avail_mask` fast path,
active-list circular DLL membership and singleton characterizations, and the `nontrivial_free`
kept-group `freed_mask` update.
-/

set_option autoImplicit false

namespace LibsignalBinary.Heap.Fine.VendorFree
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib VerifiedLibraries.Mallocng

@[expose] public section

/-! ## `__libc_free` Lockless Fast Path -/

def mkFastFreeGroup (g : GroupDesc) (idx : Nat) : GroupDesc :=
  { g with
    availMask := g.availMask + (1#32 <<< idx)
    slots     := g.slots.set idx .freeAvail }

set_option maxHeartbeats 400000 in
theorem free_set_availMask_fast {k : Nat} {base brkStart brk : BitVec 64}
    {b : MallocngBudget} {ivs : List (BitVec 64 × Nat)} {st : MallocngSt}
    (hwf : MallocngWFInflight (k + 1) base brkStart brk b.liveCost b.peakCost st)
    (hCntIvs : MallocngCountIvsWF b ivs st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hSlot : g.slots[idx]'hIdx = .claimed)
    (hAvailNe0 : g.availMask ≠ 0#32)
    (hNotAll : (g.availMask ||| g.freedMask) + (1#32 <<< idx) ≠ (2#32 <<< g.lastIdx) - 1#32) :
    let g1 := mkFastFreeGroup g idx
    let bv1 := writeBytesToMap st.byteVal g.metaPtr g1.metaBytes
    let st1 := { st with groups := replaceGroupByMeta st.groups g.metaPtr g1, byteVal := bv1 }
    ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧
    MappedSet st1.masterDom (OwnedMappedByte st1) =
      MappedSet st.masterDom (OwnedMappedByte st) ∧
    (((g.metaPtr ↦ₛ g1.metaBytes) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal) =
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal) ∧
    MallocngCountIvsWF b ivs st1 ∧
    MallocngWFInflight k base brkStart brk b.liveCost b.peakCost st1 ∧
    (EmptyGroupKeepWf st → EmptyGroupKeepWf st1) := by
  dsimp only []
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  let g1 := mkFastFreeGroup g idx
  let bv1 := writeBytesToMap st.byteVal g.metaPtr g1.metaBytes
  let st1 : MallocngSt := { st with groups := replaceGroupByMeta st.groups g.metaPtr g1, byteVal := bv1 }
  have hGWf := hwf.groups_wf g hg
  have hSWf := hGWf.slot_wf idx hIdx
  rw [hSlot] at hSWf
  have hIdxLe : idx ≤ g.lastIdx := by have := hGWf.2.2.1; unfold GroupDesc.cnt at this; omega
  have hAv0 : g.availMask.getLsbD idx = false :=
    Bool.eq_false_iff.mpr fun h => by have := hSWf.2.1.mp h; cases this
  have hFr0 : g.freedMask.getLsbD idx = false :=
    Bool.eq_false_iff.mpr fun h => by have := hSWf.2.2.1.mp h; cases this
  have hMP := freeSlot_mask_props hIdxLe hGWf.2.1
    (BitVec.and_comm g.availMask g.freedMask ▸ hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    (BitVec.or_comm g.availMask g.freedMask ▸ hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1)
    hFr0 hAv0
  have hAvAddOr : g.availMask + (1#32 <<< idx) = g.availMask ||| (1#32 <<< idx) := by
    have hDisjSelf : g.availMask &&& (1#32 <<< idx) = 0#32 := by
      have hSub := hMP.2.1; revert hSub; bv_robdd
    revert hDisjSelf; bv_robdd
  have hSpat := metaBytes_update_spatial hwf hg hIdx hSlot (by intro _ _ _ h; cases h)
    rfl rfl rfl rfl rfl (g1 := g1) rfl
  have hRep := replaceGroupByMeta_props hwf.groups_nodup.1 hg rfl rfl rfl rfl rfl (g1 := g1)
  have hClaimSum : totalClaimedSlots st1 + 1 = totalClaimedSlots st := by
    have hG := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg
      (fun h => (h.slots.filter SlotState.isClaimed).length) (g1 := g1)
    have hS := list_set_filter_len g.slots hIdx .freeAvail SlotState.isClaimed
    rw [hSlot] at hS
    unfold totalClaimedSlots
    simp only [st1, g1, mkFastFreeGroup, SlotState.isClaimed, Bool.false_eq_true, ↓reduceIte] at hG hS ⊢
    omega
  have hEffEq : totalLiveEffCost st1 = totalLiveEffCost st := by
    have hG := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg
      (fun h => (h.slots.map slotEffCost).sum) (g1 := g1)
    have hS := list_set_map_sum g.slots hIdx .freeAvail slotEffCost
    rw [hSlot] at hS
    unfold totalLiveEffCost
    simp only [st1, g1, mkFastFreeGroup, slotEffCost] at hG hS ⊢
    omega
  have hCntEq : totalLiveCount st1 = totalLiveCount st := by
    have hG := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg
      (fun h => (h.slots.map slotLiveCount).sum) (g1 := g1)
    have hS := list_set_map_sum g.slots hIdx .freeAvail slotLiveCount
    rw [hSlot] at hS
    unfold totalLiveCount
    simp only [st1, g1, mkFastFreeGroup, slotLiveCount] at hG hS ⊢
    omega
  have hNotEmp1 : g1.isEmpty = false := by
    cases hE : g1.isEmpty with
    | false => rfl
    | true =>
      exfalso; apply hNotAll
      rw [BitVec.or_comm g.availMask g.freedMask]
      refine hMP.2.2.2.2.2.2.mpr fun j hjLe hjNe => ?_
      have hj1 : j < g1.slots.length := by
        simp only [g1, mkFastFreeGroup, List.length_set, hGWf.2.2.1]; unfold GroupDesc.cnt; omega
      have hj0 : j < g.slots.length := by simpa [g1, mkFastFreeGroup] using hj1
      have hFreeJ := List.all_eq_true.mp hE (g1.slots[j]'hj1) (List.getElem_mem hj1)
      have hGetJ : g1.slots[j]'hj1 = g.slots[j]'hj0 := by
        simp only [g1, mkFastFreeGroup, List.getElem_set, Ne.symm hjNe, ↓reduceIte]
      rw [hGetJ] at hFreeJ
      have hSWfJ := hGWf.slot_wf j hj0
      cases hSJ : g.slots[j]'hj0 <;> simp [hSJ, SlotState.isFree] at hFreeJ
      · exact Or.inr ((hSWfJ.2.1).mpr hSJ)
      · exact Or.inl ((hSWfJ.2.2.1).mpr hSJ)
  have hDynEq : dynamicRootRegions st1 = dynamicRootRegions st := by
    unfold dynamicRootRegions; dsimp only [st1] at hRep ⊢; rw [hRep.2.2.1]
  refine ⟨hSpat.2.2.1, hSpat.2.2.2.1, hSpat.2.2.2.2,
    ⟨hCntIvs.1, hCntEq ▸ hCntIvs.2.1, hCntIvs.2.2.1.trans hDynEq.symm, hCntIvs.2.2.2.1,
      hCntIvs.2.2.2.2.1,
      groupsGrpBound_replaceGroupByMeta hCntIvs.2.2.2.2.2 hg _ rfl rfl⟩,
    ?_, fun hKeep h' hh' hMp h7 h38 => ?_⟩
  · refine wf_of_inPlaceSlotMod hwf hg hIdx (by simp [hSlot])
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun j _ hjNe => ⟨by simp [mkFastFreeGroup, hAvAddOr, hMP.2.2.2.2.2.1 j, hjNe], rfl⟩)
      (by simp only [mkFastFreeGroup, hAvAddOr]
          exact BitVec.and_comm g.freedMask _ ▸ hMP.2.2.2.1)
      (by simp only [mkFastFreeGroup, hAvAddOr]
          exact BitVec.or_comm g.freedMask _ ▸ hMP.2.2.2.2.1)
      (fun a hNotM => writeBytesToMap_out _ _ _ fun hIn => hNotM (Or.inl (by simpa using hIn)))
      (readBytesFromMap_writeBytesToMap st.byteVal g.metaPtr g1.metaBytes
        (by rw [GroupDesc.metaBytes_length]; decide))
      (by dsimp only [SlotWf]
          have hStEq : (mkFastFreeGroup g idx).slotStart idx = g.slotStart idx := rfl
          have hFrEq : (mkFastFreeGroup g idx).freedMask = g.freedMask := rfl
          have hAcEq : (mkFastFreeGroup g idx).activeIdx = g.activeIdx := rfl
          rw [hStEq, hFrEq, hAcEq]
          have hNotM0 : ¬ InRegion g.metaPtr g1.metaBytes.length (g.slotStart idx - 4#64) := fun hIn => by
            obtain ⟨_, _, _, ⟨maG, hmaG, hInMaG⟩, _⟩ := allMetaSlots_info hwf
              ((hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
                (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg)))))
            obtain ⟨rgG, hrgG, hRgMp, hRgLo, hRgHi⟩ := group_in_root_region hwf hg
            have hRgTot : rgG.totalBytes = rgG.maplen * 4096 := by simp [GroupDesc.totalBytes, hRgMp]
            have hRg48 : rgG.mem.toNat + rgG.totalBytes ≤ 2 ^ 48 := (hwf.groups_wf rgG hrgG).2.2.2.2.2.2.1
            have ⟨_, hStor, hSt, hSub4, hEn, hEnLe, h48, _, _⟩ := group_slot_bounds hGWf hIdx
            have ⟨hStr, _⟩ := group_stride_pos_and_align hGWf
            have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
            have hInRg0 : InRegion rgG.mem (rgG.maplen * 4096) (g.slotStart idx - 4#64) :=
              (inRegion_iff_toNat (by omega) (g.slotStart idx - 4#64)).mpr ⟨by omega, by omega⟩
            exact not_both_inRegion_of_disjointRegions
              (metaArea_disjoint_root_group hwf hmaG hrgG hRgMp)
              (hInMaG _ (by simpa using hIn)) hInRg0
          refine ⟨(writeBytesToMap_out _ _ _ hNotM0).trans hSWf.1,
            by simp [mkFastFreeGroup, hAvAddOr, hMP.2.2.2.2.2.1 idx],
            ⟨fun hFr => False.elim (by rw [hFr0] at hFr; cases hFr), fun hC => by cases hC⟩,
            fun hLt => False.elim (by have := hSWf.2.2.2.1 hLt; cases this), trivial⟩)
      (fun hScLt hNot => False.elim (by
        have hSc48 : g.sc < 48 := by
          rcases hGWf.1 with h48 | h63; exact h48; rw [hwf.ctx_lens.2.2.2.2.2] at hScLt; omega
        have hAct := hwf.active_wf g.sc (by rw [hwf.ctx_lens.1]; exact hSc48) hScLt
        exact hAvailNe0 ((hAct.2.2.2.1 g hg rfl).2 hNot).1))
      (fun hScLt i hi hPos hEqM => False.elim (by
        have hSc48 : g.sc < 48 := by
          rcases hGWf.1 with h48 | h63; exact h48; rw [hwf.ctx_lens.2.2.2.2.2] at hScLt; omega
        have hAct := hwf.active_wf g.sc (by rw [hwf.ctx_lens.1]; exact hSc48) hScLt
        exact hAvailNe0 (hAct.2.2.2.2.1 i hi hPos g hg hEqM).1))
      (fun hEmp => by rw [hNotEmp1] at hEmp; cases hEmp)
      (by have := hwf.inflight_wf; dsimp only [st1, bv1, g1] at hClaimSum ⊢; omega)
      hwf.live_le_peak
      (by dsimp only [st1, bv1, g1] at hEffEq ⊢; rw [hEffEq]; exact hwf.effCost_le_live)
      (fun q r => by
        rw [hwf.liveMap_wf q r]; constructor
        · rintro ⟨h0, hh0, j, hj0, c, hSlot0⟩
          by_cases hEq : h0.metaPtr = g.metaPtr
          · have hE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hEq; subst hE
            have hjNe : j ≠ idx := fun hJ => by subst hJ; rw [hSlot] at hSlot0; cases hSlot0
            refine ⟨g1, hRep.2.2.2.2.1, j, by simp [g1, mkFastFreeGroup, hj0], c, ?_⟩
            simp only [g1, mkFastFreeGroup, List.getElem_set, Ne.symm hjNe, ↓reduceIte, hSlot0]
          · exact ⟨h0, hRep.2.2.2.2.2.2.1 h0 hh0 hEq, j, hj0, c, hSlot0⟩
        · rintro ⟨h', hh', j, hj', c, hSlot'⟩
          rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, _⟩
          · have hj0 : j < g.slots.length := by simpa [g1, mkFastFreeGroup] using hj'
            by_cases hjEq : j = idx
            · subst hjEq; simp [g1, mkFastFreeGroup] at hSlot'
            · simp only [g1, mkFastFreeGroup, List.getElem_set, Ne.symm hjEq, ↓reduceIte] at hSlot'
              exact ⟨g, hg, j, hj0, c, hSlot'⟩
          · exact ⟨h', hh0, j, hj', c, hSlot'⟩)
      (fun a hRw => hwf.masterDom_wf.2.1 a (Or.inl ((hSpat.2.1 a).mp hRw)))
  · rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, _⟩
    · exact hKeep g hg hMp h7 h38
    · exact hKeep h' hh0 hMp h7 h38

/-! ## `ActiveClassWf` Membership, Head, and Singleton Characterizations -/

theorem findGroupByMeta_eq_of_mem {gs : List GroupDesc} (hNd : (gs.map (·.metaPtr)).Nodup)
    {g : GroupDesc} (hg : g ∈ gs) :
    gs.find? (·.metaPtr == g.metaPtr) = some g := by
  obtain ⟨pre, post, hEq, hPreNe, _, _, _⟩ := split_groups_at_mem hNd hg
  rw [hEq, List.find?_append, List.find?_cons]
  have hPreNone : pre.find? (·.metaPtr == g.metaPtr) = none :=
    List.find?_eq_none.mpr fun h hh => by simp [hPreNe h hh]
  simp [hPreNone]

theorem activeList_nodes_eq_map {st : MallocngSt} (hNd : (st.groups.map (·.metaPtr)).Nodup)
    {ms : List (BitVec 64)}
    (hMem : ∀ m ∈ ms, ∃ g ∈ st.groups, g.metaPtr = m) :
    (ms.filterMap fun m => (findGroupByMeta st m).map fun g => (g.metaPtr, g.prev, g.next)).map Prod.fst =
      ms := by
  induction ms with
  | nil => rfl
  | cons m tl ih =>
    obtain ⟨g, hg, rfl⟩ := hMem m (List.mem_cons_self ..)
    have hFind : findGroupByMeta st g.metaPtr = some g := findGroupByMeta_eq_of_mem hNd hg
    simp only [List.filterMap_cons, hFind, Option.map_some, List.map_cons]
    exact congrArg (g.metaPtr :: ·) (ih fun x hx => hMem x (List.mem_cons_of_mem _ hx))

theorem activeList_getElem_node {st : MallocngSt} (hNd : (st.groups.map (·.metaPtr)).Nodup)
    {ms : List (BitVec 64)}
    (hMem : ∀ m ∈ ms, ∃ g ∈ st.groups, g.metaPtr = m) :
    ∀ {i : Nat} (hi : i < ms.length),
      let ns := ms.filterMap fun m => (findGroupByMeta st m).map fun g => (g.metaPtr, g.prev, g.next)
      ∃ (hiN : i < ns.length) (g : GroupDesc),
        g ∈ st.groups ∧ g.metaPtr = ms[i]'hi ∧ ns[i]'hiN = (g.metaPtr, g.prev, g.next) := by
  induction ms with
  | nil => intro i hi; simp at hi
  | cons m tl ih =>
    intro i hi
    obtain ⟨g0, hg0, rfl⟩ := hMem m (List.mem_cons_self ..)
    have hFind0 : findGroupByMeta st g0.metaPtr = some g0 := findGroupByMeta_eq_of_mem hNd hg0
    cases i with
    | zero =>
      refine ⟨by simp [hFind0], g0, hg0, rfl, by simp [hFind0]⟩
    | succ i' =>
      obtain ⟨hiN', g', hg', hM', hEq'⟩ :=
        ih (fun x hx => hMem x (List.mem_cons_of_mem _ hx)) (Nat.lt_of_succ_lt_succ hi)
      refine ⟨by simp [hFind0]; exact hiN', g', hg', hM', ?_⟩
      simpa [hFind0] using hEq'

theorem nodup_idx_eq {α : Type} {xs : List α} (h : xs.Nodup)
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length)
    (heq : xs[i]'hi = xs[j]'hj) : i = j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x tl ih =>
    obtain ⟨hxNot, htl⟩ := List.nodup_cons.mp h
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact False.elim (hxNot (heq ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hj)))
    | succ i' =>
      cases j with
      | zero =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact False.elim (hxNot (heq.symm ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hi)))
      | succ j' =>
        simp only [List.getElem_cons_succ] at heq
        exact congrArg Nat.succ (ih htl (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) heq)

theorem activeList_head_and_singleton_props {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hSc48 : g.sc < 48) :
    let h1 : g.sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hSc48
    let h2 : g.sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hSc48
    let head := st.ctx.active[g.sc]'h1
    let ms := st.activeLists[g.sc]'h2
    g.metaPtr ≠ 0#64 ∧
    (g.next = 0#64 ↔ g.metaPtr ∉ ms) ∧
    (g.next = 0#64 → g.prev = 0#64) ∧
    (g.next = g.metaPtr ↔ ms = [g.metaPtr]) ∧
    (g.next = g.metaPtr → head = g.metaPtr ∧ g.prev = g.metaPtr) ∧
    (head = g.metaPtr → g.metaPtr ∈ ms) ∧
    (head ≠ g.metaPtr → g.freedMask = 0#32 → g.metaPtr ∉ ms ∧ g.prev = 0#64 ∧ g.next = 0#64) := by
  dsimp only []
  have h1 : g.sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hSc48
  have h2 : g.sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hSc48
  let head := st.ctx.active[g.sc]'h1
  let ms := st.activeLists[g.sc]'h2
  have hAct := hwf.active_wf g.sc h1 h2
  have hMemW : ∀ m ∈ ms, ∃ h ∈ st.groups, h.metaPtr = m := fun m hm => by
    obtain ⟨h, hh, hM, _⟩ := hAct.1 m hm; exact ⟨h, hh, hM⟩
  have hAllG : g.metaPtr ∈ allMetaSlots st :=
    (hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg))))
  have hmGe : 4096 ≤ g.metaPtr.toNat := (allMetaSlots_info hwf hAllG).1
  have hmNe0 : g.metaPtr ≠ 0#64 := fun h0 => by rw [h0] at hmGe; simp at hmGe
  have hNotIff := (hAct.2.2.2.1 g hg rfl).1
  let ns := ms.filterMap fun m => (findGroupByMeta st m).map fun h => (h.metaPtr, h.prev, h.next)
  have hDll : CircularDllWf head ns := hAct.2.1
  have hMapFst : ns.map Prod.fst = ms := activeList_nodes_eq_map hwf.groups_nodup.1 hMemW
  have hNx0Iff : g.next = 0#64 ↔ g.metaPtr ∉ ms := by
    constructor
    · intro hNx0 hIn
      obtain ⟨i, hi, hMsI⟩ := List.getElem_of_mem hIn
      obtain ⟨hiN, gi, hgi, hGiM, hNsI⟩ := activeList_getElem_node hwf.groups_nodup.1 hMemW hi
      have hEqG := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hgi hg (hGiM.trans hMsI)
      subst gi
      have hiN' : i < ns.length := hiN
      have hNsOpt : ns[i]? = some (g.metaPtr, g.prev, g.next) :=
        (List.getElem?_eq_getElem hiN').trans (congrArg some hNsI)
      cases hNs : ns with
      | nil => rw [hNs] at hiN'; simp at hiN'
      | cons hd tl =>
        have hDllC : CircularDllWf head (hd :: tl) := hNs ▸ hDll
        obtain ⟨_, _, hNz, hLinks⟩ := hDllC
        have hiC : i < (hd :: tl).length := hNs ▸ hiN'
        have hNxtLink := (hLinks i hiC).1
        rw [hNs, List.getElem?_eq_getElem hiC] at hNsOpt
        have hNodeEq : (hd :: tl)[i]'hiC = (g.metaPtr, g.prev, g.next) := Option.some.inj hNsOpt
        rw [hNodeEq] at hNxtLink
        dsimp only [] at hNxtLink
        have hModLt : (i + 1) % (hd :: tl).length < (hd :: tl).length := Nat.mod_lt _ (by simp)
        have hTgtMem : (hd :: tl)[(i + 1) % (hd :: tl).length]'hModLt ∈ (hd :: tl) :=
          List.getElem_mem hModLt
        have hTgtNz := hNz _ hTgtMem
        exact hTgtNz (hNxtLink.symm.trans hNx0)
    · intro hNot; exact (hNotIff.mp hNot).2
  have hSingProps : (g.next = g.metaPtr ↔ ms = [g.metaPtr]) ∧
      (g.next = g.metaPtr → head = g.metaPtr ∧ g.prev = g.metaPtr) := by
    have hImp : g.next = g.metaPtr → ms = [g.metaPtr] ∧ head = g.metaPtr ∧ g.prev = g.metaPtr := by
      intro hNxSelf
      have hIn : g.metaPtr ∈ ms := Classical.byContradiction fun hNot =>
        hmNe0 (hNxSelf.symm.trans (hNx0Iff.mpr hNot))
      obtain ⟨i, hi, hMsI⟩ := List.getElem_of_mem hIn
      obtain ⟨hiN, gi, hgi, hGiM, hNsI⟩ := activeList_getElem_node hwf.groups_nodup.1 hMemW hi
      have hEqG := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hgi hg (hGiM.trans hMsI)
      subst gi
      have hiN' : i < ns.length := hiN
      have hNsOpt : ns[i]? = some (g.metaPtr, g.prev, g.next) :=
        (List.getElem?_eq_getElem hiN').trans (congrArg some hNsI)
      cases hNs : ns with
      | nil => rw [hNs] at hiN'; simp at hiN'
      | cons hd tl =>
        have hDllC : CircularDllWf head (hd :: tl) := hNs ▸ hDll
        obtain ⟨hHdEq, hNdNs, _, hLinks⟩ := hDllC
        have hiC : i < (hd :: tl).length := hNs ▸ hiN'
        have hLenPos : 0 < (hd :: tl).length := by simp
        have hModLt : (i + 1) % (hd :: tl).length < (hd :: tl).length := Nat.mod_lt _ hLenPos
        have hLinkI := hLinks i hiC
        rw [hNs, List.getElem?_eq_getElem hiC] at hNsOpt
        have hNodeEq : (hd :: tl)[i]'hiC = (g.metaPtr, g.prev, g.next) := Option.some.inj hNsOpt
        have hFstEq : ((hd :: tl).map Prod.fst)[(i + 1) % (hd :: tl).length]'(by simpa using hModLt) =
            ((hd :: tl).map Prod.fst)[i]'(by simpa using hiC) := by
          simp only [List.getElem_map]
          exact hLinkI.1.symm.trans ((congrArg (fun x => x.2.2) hNodeEq).trans
            (hNxSelf.trans (congrArg Prod.fst hNodeEq).symm))
        have hIdxEq : (i + 1) % (hd :: tl).length = i :=
          nodup_idx_eq hNdNs (by simpa using hModLt) (by simpa using hiC) hFstEq
        have hLen1 : (hd :: tl).length = 1 := by
          by_cases hGt1 : 1 < (hd :: tl).length
          · by_cases hLast : i + 1 < (hd :: tl).length
            · rw [Nat.mod_eq_of_lt hLast] at hIdxEq; omega
            · have hIEq : i + 1 = (hd :: tl).length := by omega
              rw [hIEq, Nat.mod_self] at hIdxEq; omega
          · omega
        have hTlNil : tl = [] := by simpa using hLen1
        subst hTlNil
        have hi0 : i = 0 := by simp at hiC; exact hiC
        subst hi0
        simp only [List.getElem_cons_zero] at hNodeEq
        subst hNodeEq
        have hMsEq : ms = [g.metaPtr] := by
          rw [← hMapFst, hNs]; rfl
        have hPrv0 := (hLinks 0 (by simp)).2
        simp only [List.length_singleton, Nat.mod_one, List.getElem_cons_zero] at hPrv0
        exact ⟨hMsEq, hHdEq, hPrv0⟩
    refine ⟨⟨fun h => (hImp h).1, fun hMs1 => ?_⟩, fun h => ⟨(hImp h).2.1, (hImp h).2.2⟩⟩
    have h0Lt : 0 < ms.length := by rw [hMs1]; simp
    obtain ⟨h0N, g0, hg0, hG0M, hNs0⟩ := activeList_getElem_node hwf.groups_nodup.1 hMemW h0Lt
    have hMs0 : ms[0]'h0Lt = g.metaPtr := by simp [hMs1]
    have hEqG := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hg0 hg (hG0M.trans hMs0)
    subst g0
    have h0N' : 0 < ns.length := h0N
    have hNsOpt : ns[0]? = some (g.metaPtr, g.prev, g.next) :=
      (List.getElem?_eq_getElem h0N').trans (congrArg some hNs0)
    have hNsLen : ns.length = 1 := by rw [← List.length_map Prod.fst, hMapFst, hMs1]; rfl
    cases hNs : ns with
    | nil => rw [hNs] at hNsLen; simp at hNsLen
    | cons hd tl =>
      have hTlNil : tl = [] := by rw [hNs] at hNsLen; simpa using hNsLen
      subst hTlNil
      have hDllC : CircularDllWf head [hd] := hNs ▸ hDll
      rw [hNs] at hNsOpt
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hNsOpt
      subst hNsOpt
      exact (CircularDllWf.singleton_iff_next_eq hDllC).2 rfl |>.2
  refine ⟨hmNe0, hNx0Iff, fun hNx0 => (hNotIff.mp (hNx0Iff.mp hNx0)).1,
    hSingProps.1, hSingProps.2,
    fun hHdEq => ?_, fun hHdNe hFr0 => ?_⟩
  · change head = g.metaPtr at hHdEq
    cases hNs : ns with
    | nil =>
      have hHd0 := (CircularDllWf.head_eq_zero_iff (hNs ▸ hDll)).mpr rfl
      exact False.elim (hmNe0 (hHdEq.symm.trans hHd0))
    | cons hd tl =>
      have hDllC : CircularDllWf head (hd :: tl) := hNs ▸ hDll
      change g.metaPtr ∈ ms
      rw [← hMapFst, hNs, List.map_cons, ← hDllC.1, hHdEq]
      exact List.mem_cons_self ..
  · change head ≠ g.metaPtr at hHdNe
    have hNot : g.metaPtr ∉ ms := fun hIn => by
      obtain ⟨i, hi, hMsI⟩ := List.getElem_of_mem hIn
      cases i with
      | zero =>
        cases hNs : ns with
        | nil =>
          have : ms = [] := by rw [← hMapFst, hNs]; rfl
          simp [this] at hi
        | cons hd tl =>
          have hDllC : CircularDllWf head (hd :: tl) := hNs ▸ hDll
          have hMsC : ms = hd.1 :: tl.map Prod.fst := by rw [← hMapFst, hNs]; rfl
          have hMs0 : ms[0]'hi = hd.1 := by simp [hMsC]
          exact hHdNe (hDllC.1.trans (hMs0.symm.trans hMsI))
      | succ i' =>
        exact (hAct.2.2.2.2.1 (i' + 1) hi (Nat.succ_pos _) g hg hMsI.symm).2 hFr0
    exact ⟨hNot, (hNotIff.mp hNot).1, (hNotIff.mp hNot).2⟩

/-! ## `nontrivial_free` Keep-Group `freed_mask` Update -/

def mkFreedKeepGroup (g : GroupDesc) (idx : Nat) : GroupDesc :=
  { g with
    freedMask := g.freedMask ||| (1#32 <<< idx)
    slots     := g.slots.set idx .freeInactive }

set_option maxHeartbeats 400000 in
theorem free_set_freedMask_keep {k : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight (k + 1) base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hSlot : g.slots[idx]'hIdx = .claimed)
    (hSc48 : g.sc < 48)
    (hInActive : ∀ hScLt : g.sc < st.activeLists.length, g.metaPtr ∈ st.activeLists[g.sc]'hScLt)
    (hEmptyOrNot :
      (g.availMask ||| g.freedMask) + (1#32 <<< idx) ≠ (2#32 <<< g.lastIdx) - 1#32 ∨
      (0 < g.maplen ∧ 7 ≤ g.sc ∧ g.sc ≤ 38 ∧ g.maplen * 4096 ≤ 1048576 ∧
        (∀ hScLt : g.sc < st.activeLists.length, st.activeLists[g.sc]'hScLt = [g.metaPtr]) ∧
        (g.lastIdx = 0 → slotStride g.sc + 16 ≤ g.maplen * 4096))) :
    let g1 := mkFreedKeepGroup g idx
    let bv1 := writeBytesToMap st.byteVal g.metaPtr g1.metaBytes
    let st1 := { st with groups := replaceGroupByMeta st.groups g.metaPtr g1, byteVal := bv1 }
    ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧
    MappedSet st1.masterDom (OwnedMappedByte st1) =
      MappedSet st.masterDom (OwnedMappedByte st) ∧
    (((g.metaPtr ↦ₛ g1.metaBytes) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal) =
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal) ∧
    dynamicRootRegions st1 = dynamicRootRegions st ∧
    totalLiveCount st1 = totalLiveCount st ∧
    MallocngWFInflight k base brkStart brk liveCost peakCost st1 ∧
    (EmptyGroupKeepWf st → EmptyGroupKeepWf st1) := by
  dsimp only []
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  let g1 := mkFreedKeepGroup g idx
  let bv1 := writeBytesToMap st.byteVal g.metaPtr g1.metaBytes
  let st1 : MallocngSt := { st with groups := replaceGroupByMeta st.groups g.metaPtr g1, byteVal := bv1 }
  have hGWf := hwf.groups_wf g hg
  have hSWf := hGWf.slot_wf idx hIdx
  rw [hSlot] at hSWf
  have hIdxLe : idx ≤ g.lastIdx := by have := hGWf.2.2.1; unfold GroupDesc.cnt at this; omega
  have hAv0 : g.availMask.getLsbD idx = false :=
    Bool.eq_false_iff.mpr fun h => by have := hSWf.2.1.mp h; cases this
  have hFr0 : g.freedMask.getLsbD idx = false :=
    Bool.eq_false_iff.mpr fun h => by have := hSWf.2.2.1.mp h; cases this
  have hMP := freeSlot_mask_props hIdxLe hGWf.2.1
    hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hGWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hAv0 hFr0
  have hSpat := metaBytes_update_spatial hwf hg hIdx hSlot (by intro _ _ _ h; cases h)
    rfl rfl rfl rfl rfl (g1 := g1) rfl
  have hRep := replaceGroupByMeta_props hwf.groups_nodup.1 hg rfl rfl rfl rfl rfl (g1 := g1)
  have hClaimSum : totalClaimedSlots st1 + 1 = totalClaimedSlots st := by
    have hG := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg
      (fun h => (h.slots.filter SlotState.isClaimed).length) (g1 := g1)
    have hS := list_set_filter_len g.slots hIdx .freeInactive SlotState.isClaimed
    rw [hSlot] at hS
    unfold totalClaimedSlots
    simp only [st1, g1, mkFreedKeepGroup, SlotState.isClaimed, Bool.false_eq_true, ↓reduceIte] at hG hS ⊢
    omega
  have hEffEq : totalLiveEffCost st1 = totalLiveEffCost st := by
    have hG := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg
      (fun h => (h.slots.map slotEffCost).sum) (g1 := g1)
    have hS := list_set_map_sum g.slots hIdx .freeInactive slotEffCost
    rw [hSlot] at hS
    unfold totalLiveEffCost
    simp only [st1, g1, mkFreedKeepGroup, slotEffCost] at hG hS ⊢
    omega
  have hCntEq : totalLiveCount st1 = totalLiveCount st := by
    have hG := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg
      (fun h => (h.slots.map slotLiveCount).sum) (g1 := g1)
    have hS := list_set_map_sum g.slots hIdx .freeInactive slotLiveCount
    rw [hSlot] at hS
    unfold totalLiveCount
    simp only [st1, g1, mkFreedKeepGroup, slotLiveCount] at hG hS ⊢
    omega
  have hFrNe0 : g1.freedMask ≠ 0#32 := fun h0 => by
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD idx) h0
    simp [g1, mkFreedKeepGroup, hMP.2.2.2.2.2.1 idx] at hb
  have hDynEq : dynamicRootRegions st1 = dynamicRootRegions st := by
    unfold dynamicRootRegions; dsimp only [st1] at hRep ⊢; rw [hRep.2.2.1]
  refine ⟨hSpat.2.2.1, hSpat.2.2.2.1, hSpat.2.2.2.2, hDynEq, hCntEq, ?_,
    fun hKeep h' hh' hMp h7 h38 => ?_⟩
  · refine wf_of_inPlaceSlotMod hwf hg hIdx (by simp [hSlot])
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun j _ hjNe => ⟨rfl, by simp [mkFreedKeepGroup, hMP.2.2.2.2.2.1 j, hjNe]⟩)
      hMP.2.2.2.1
      hMP.2.2.2.2.1
      (fun a hNotM => writeBytesToMap_out _ _ _ fun hIn => hNotM (Or.inl (by simpa using hIn)))
      (readBytesFromMap_writeBytesToMap st.byteVal g.metaPtr g1.metaBytes
        (by rw [GroupDesc.metaBytes_length]; decide))
      (by dsimp only [SlotWf]
          have hStEq : (mkFreedKeepGroup g idx).slotStart idx = g.slotStart idx := rfl
          have hAvEq : (mkFreedKeepGroup g idx).availMask = g.availMask := rfl
          have hAcEq : (mkFreedKeepGroup g idx).activeIdx = g.activeIdx := rfl
          rw [hStEq, hAvEq, hAcEq]
          have hNotM0 : ¬ InRegion g.metaPtr g1.metaBytes.length (g.slotStart idx - 4#64) := fun hIn => by
            obtain ⟨_, _, _, ⟨maG, hmaG, hInMaG⟩, _⟩ := allMetaSlots_info hwf
              ((hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
                (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg)))))
            obtain ⟨rgG, hrgG, hRgMp, hRgLo, hRgHi⟩ := group_in_root_region hwf hg
            have hRgTot : rgG.totalBytes = rgG.maplen * 4096 := by simp [GroupDesc.totalBytes, hRgMp]
            have hRg48 : rgG.mem.toNat + rgG.totalBytes ≤ 2 ^ 48 := (hwf.groups_wf rgG hrgG).2.2.2.2.2.2.1
            have ⟨_, hStor, hSt, hSub4, hEn, hEnLe, h48, _, _⟩ := group_slot_bounds hGWf hIdx
            have ⟨hStr, _⟩ := group_stride_pos_and_align hGWf
            have hSM : (idx + 1) * g.stride = idx * g.stride + g.stride := Nat.succ_mul idx g.stride
            have hInRg0 : InRegion rgG.mem (rgG.maplen * 4096) (g.slotStart idx - 4#64) :=
              (inRegion_iff_toNat (by omega) (g.slotStart idx - 4#64)).mpr ⟨by omega, by omega⟩
            exact not_both_inRegion_of_disjointRegions
              (metaArea_disjoint_root_group hwf hmaG hrgG hRgMp)
              (hInMaG _ (by simpa using hIn)) hInRg0
          refine ⟨(writeBytesToMap_out _ _ _ hNotM0).trans hSWf.1,
            ⟨fun hAv => False.elim (by rw [hAv0] at hAv; cases hAv), fun hC => by cases hC⟩,
            by simp [mkFreedKeepGroup, hMP.2.2.2.2.2.1 idx],
            fun _ => rfl, trivial⟩)
      (fun hScLt hNot => False.elim (hNot (hInActive hScLt)))
      (fun hScLt i hi hPos hEqM => by
        have hAct := hwf.active_wf g.sc (by rw [hwf.ctx_lens.1]; exact hSc48) hScLt
        exact ⟨(hAct.2.2.2.2.1 i hi hPos g hg hEqM).1, hFrNe0⟩)
      (fun hEmp => by
        rcases hEmptyOrNot with hNotAll | hKeepProps
        · exfalso; apply hNotAll
          refine hMP.2.2.2.2.2.2.mpr fun j hjLe hjNe => ?_
          have hj1 : j < g1.slots.length := by
            simp only [g1, mkFreedKeepGroup, List.length_set, hGWf.2.2.1]; unfold GroupDesc.cnt; omega
          have hj0 : j < g.slots.length := by simpa [g1, mkFreedKeepGroup] using hj1
          have hFreeJ := List.all_eq_true.mp hEmp (g1.slots[j]'hj1) (List.getElem_mem hj1)
          have hGetJ : g1.slots[j]'hj1 = g.slots[j]'hj0 := by
            simp only [g1, mkFreedKeepGroup, List.getElem_set, Ne.symm hjNe, ↓reduceIte]
          rw [hGetJ] at hFreeJ
          have hSWfJ := hGWf.slot_wf j hj0
          cases hSJ : g.slots[j]'hj0 <;> simp [hSJ, SlotState.isFree] at hFreeJ
          · exact Or.inl ((hSWfJ.2.1).mpr hSJ)
          · exact Or.inr ((hSWfJ.2.2.1).mpr hSJ)
        · exact hKeepProps)
      (by have := hwf.inflight_wf; dsimp only [st1, bv1, g1] at hClaimSum ⊢; omega)
      hwf.live_le_peak
      (by dsimp only [st1, bv1, g1] at hEffEq ⊢; rw [hEffEq]; exact hwf.effCost_le_live)
      (fun q r => by
        rw [hwf.liveMap_wf q r]; constructor
        · rintro ⟨h0, hh0, j, hj0, c, hSlot0⟩
          by_cases hEq : h0.metaPtr = g.metaPtr
          · have hE := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hEq; subst hE
            have hjNe : j ≠ idx := fun hJ => by subst hJ; rw [hSlot] at hSlot0; cases hSlot0
            refine ⟨g1, hRep.2.2.2.2.1, j, by simp [g1, mkFreedKeepGroup, hj0], c, ?_⟩
            simp only [g1, mkFreedKeepGroup, List.getElem_set, Ne.symm hjNe, ↓reduceIte, hSlot0]
          · exact ⟨h0, hRep.2.2.2.2.2.2.1 h0 hh0 hEq, j, hj0, c, hSlot0⟩
        · rintro ⟨h', hh', j, hj', c, hSlot'⟩
          rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, _⟩
          · have hj0 : j < g.slots.length := by simpa [g1, mkFreedKeepGroup] using hj'
            by_cases hjEq : j = idx
            · subst hjEq; simp [g1, mkFreedKeepGroup] at hSlot'
            · simp only [g1, mkFreedKeepGroup, List.getElem_set, Ne.symm hjEq, ↓reduceIte] at hSlot'
              exact ⟨g, hg, j, hj0, c, hSlot'⟩
          · exact ⟨h', hh0, j, hj', c, hSlot'⟩)
      (fun a hRw => hwf.masterDom_wf.2.1 a (Or.inl ((hSpat.2.1 a).mp hRw)))
  · rcases hRep.2.2.2.2.2.1 h' hh' with rfl | ⟨hh0, _⟩
    · exact hKeep g hg hMp h7 h38
    · exact hKeep h' hh0 hMp h7 h38

end

end LibsignalBinary.Heap.Fine.VendorFree
