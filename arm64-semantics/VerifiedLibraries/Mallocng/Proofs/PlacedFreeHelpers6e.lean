/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import VerifiedLibraries.Mallocng.Proofs.PlacedFreeHelpers6d

/-!
# Root Group Retirement Helpers for `nontrivial_free`

Invariant-transition lemmas (`packedWord_and_pageMask`, `dequeue_origin_bijection`,
`pairwiseDisjoint_remove_mid`, and `free_retire_rootGroup`) for retiring an all-free root group
(`0 < g.maplen`) in `nontrivial_free` (`+0x1d4..+0x220`) under `MallocngWFInflight`.
-/

set_option autoImplicit false

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

theorem packedWord_and_pageMask (g : GroupDesc) :
    g.packedWord &&& 0xfffffffffffff000#64 = BitVec.ofNat 64 (g.maplen * 4096) := by
  unfold GroupDesc.packedWord
  have hMask :
      ∀ a b c : BitVec 64,
        (((a &&& 0x1f#64) ||| (1#64 <<< 5) ||| ((b &&& 0x3f#64) <<< 6) ||| (c <<< 12)) &&&
          0xfffffffffffff000#64) = (c <<< 12) := by
    intro a b c; bv_robdd
  rw [hMask]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  change ((g.maplen % 2 ^ 64) * 4096) % 2 ^ 64 = (g.maplen * 4096) % 2 ^ 64
  rw [Nat.mod_mul_mod]

theorem dequeue_origin_bijection {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} {active1 usage1 : List (BitVec 64)} {actLists1 : List (List (BitVec 64))}
    {gsDeq : List GroupDesc} {bvDeq : BitVec 64 → BitVec 8}
    (hDeq : DequeueOutcome st g active1 usage1 actLists1 gsDeq bvDeq) :
    ∀ h0 ∈ st.groups, h0.metaPtr ≠ g.metaPtr →
      ∃ h ∈ gsDeq,
        h.metaPtr = h0.metaPtr ∧ h.mem = h0.mem ∧ h.maplen = h0.maplen ∧
        h.sc = h0.sc ∧ h.lastIdx = h0.lastIdx ∧ h.activeByte = h0.activeByte ∧
        h.parentMeta = h0.parentMeta ∧ h.nestedCap = h0.nestedCap ∧
        h.slots.length = h0.slots.length ∧ h.isEmpty = h0.isEmpty ∧
        (h.availMask = 0#32 ∧ h.freedMask = 0#32 → h0.availMask = 0#32 ∧ h0.freedMask = 0#32) ∧
        (∀ j (hj : j < h.slots.length) (hj0 : j < h0.slots.length),
          (∀ cm, h.slots[j]'hj = .liveNested cm ↔ h0.slots[j]'hj0 = .liveNested cm) ∧
          (∀ p n ec, h.slots[j]'hj = .liveUser p n ec ↔ h0.slots[j]'hj0 = .liveUser p n ec)) := by
  intro h0 hh0 hNe
  have hInMap : h0.metaPtr ∈ gsDeq.map (·.metaPtr) :=
    (hDeq.meta_set h0.metaPtr).mpr ⟨List.mem_map_of_mem hh0, hNe⟩
  obtain ⟨h, hh, hHM⟩ := List.mem_map.mp hInMap
  obtain ⟨_, h0', hh0', hM', hRest⟩ := hDeq.each_preserved h hh
  have hEq : h0' = h0 :=
    mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0' hh0 (hM'.symm.trans hHM)
  subst hEq
  exact ⟨h, hh, hM', hRest⟩

theorem group_stride_total_slot_eq {h h0 : GroupDesc}
    (hMem : h.mem = h0.mem) (hMp : h.maplen = h0.maplen)
    (hSc : h.sc = h0.sc) (hLast : h.lastIdx = h0.lastIdx) (hCap : h.nestedCap = h0.nestedCap) :
    h.cnt = h0.cnt ∧ h.stride = h0.stride ∧ h.totalBytes = h0.totalBytes ∧
    h.storage = h0.storage ∧
    (∀ j, h.slotStart j = h0.slotStart j ∧ h.slotEnd j = h0.slotEnd j) := by
  have hCnt : h.cnt = h0.cnt := by simp [GroupDesc.cnt, hLast]
  have hStr : h.stride = h0.stride := by simp [GroupDesc.stride, hLast, hMp, hSc]
  have hTot : h.totalBytes = h0.totalBytes := by simp [GroupDesc.totalBytes, hMp, hCap]
  have hSto : h.storage = h0.storage := by simp [GroupDesc.storage, hMem]
  exact ⟨hCnt, hStr, hTot, hSto, fun j =>
    ⟨by simp [GroupDesc.slotStart, hSto, hStr], by simp [GroupDesc.slotEnd, GroupDesc.slotStart, hSto, hStr]⟩⟩

theorem pairwiseDisjoint_remove_mid {xs zs : List (BitVec 64 × Nat)} {y : BitVec 64 × Nat}
    (hpd : PairwiseDisjointRegions (xs ++ y :: zs)) :
    PairwiseDisjointRegions (xs ++ zs) ∧
    (∀ r ∈ xs ++ zs, ∀ a : BitVec 64, InRegion r.1 r.2 a → InRegion y.1 y.2 a → False) := by
  induction xs with
  | nil =>
    simp only [List.nil_append] at hpd ⊢
    obtain ⟨hYZ, hZ⟩ := hpd
    refine ⟨hZ, fun r hr a haR haY => ?_⟩
    exact DisjointRegions.not_both (hYZ r hr) haY haR
  | cons x tl ih =>
    simp only [List.cons_append] at hpd ⊢
    obtain ⟨hXAll, hTl⟩ := hpd
    obtain ⟨hPdRest, hDisjRest⟩ := ih hTl
    refine ⟨⟨fun r hr => hXAll r ?_, hPdRest⟩, fun r hr a haR haY => ?_⟩
    · rcases List.mem_append.mp hr with hInTl | hInZ
      · exact List.mem_append_left _ hInTl
      · exact List.mem_append_right _ (List.mem_cons_of_mem y hInZ)
    · rcases List.mem_cons.mp hr with rfl | hrRest
      · exact DisjointRegions.not_both
          (hXAll y (List.mem_append_right _ (List.mem_cons_self ..))) haR haY
      · exact hDisjRest r hrRest a haR haY

theorem retire_usedAndFree_props {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {gs : List GroupDesc}
    (hGsNd : (gs.map (·.metaPtr)).Nodup)
    (hMetaSet : ∀ x, x ∈ gs.map (·.metaPtr) ↔ (x ∈ st.groups.map (·.metaPtr) ∧ x ≠ g.metaPtr)) :
    let uf1 := gs.map (·.metaPtr) ++ st.freeMetas.map (·.ptr) ++ st.bumpMetas ++
      (g.metaPtr :: st.reservedMetas)
    g.metaPtr ∉ st.reservedMetas ∧
    uf1.Nodup ∧
    (∀ m, m ∈ uf1 ↔ m ∈ allMetaSlots st) := by
  dsimp only []
  have ⟨_, _, _, _, hUfNd0, hUfIff0⟩ := hwf.free_bump_metas_wf
  have hgMap : g.metaPtr ∈ st.groups.map (·.metaPtr) := List.mem_map_of_mem hg
  rw [List.append_assoc, List.append_assoc] at hUfNd0
  obtain ⟨hGrpNd0, hTailNd0, hGrpTailDisj⟩ := List.nodup_append.mp hUfNd0
  have hgNotTail : g.metaPtr ∉ st.freeMetas.map (·.ptr) ++ (st.bumpMetas ++ st.reservedMetas) :=
    fun hIn => hGrpTailDisj g.metaPtr hgMap g.metaPtr hIn rfl
  have hgNotRes : g.metaPtr ∉ st.reservedMetas := fun hIn =>
    hgNotTail (List.mem_append_right _ (List.mem_append_right _ hIn))
  obtain ⟨hFmNd0, hBmResNd0, hFmBmResDisj⟩ := List.nodup_append.mp hTailNd0
  obtain ⟨hBmNd0, hResNd0, hBmResDisj⟩ := List.nodup_append.mp hBmResNd0
  have hRes1Nd : (g.metaPtr :: st.reservedMetas).Nodup := List.nodup_cons.mpr ⟨hgNotRes, hResNd0⟩
  have hBmRes1Nd : (st.bumpMetas ++ (g.metaPtr :: st.reservedMetas)).Nodup :=
    List.nodup_append.mpr ⟨hBmNd0, hRes1Nd, fun x hx y hy hEq => by
      subst hEq
      rcases List.mem_cons.mp hy with rfl | hyR
      · exact hgNotTail (List.mem_append_right _ (List.mem_append_left _ hx))
      · exact hBmResDisj x hx x hyR rfl⟩
  have hTail1Nd : (st.freeMetas.map (·.ptr) ++ (st.bumpMetas ++ (g.metaPtr :: st.reservedMetas))).Nodup :=
    List.nodup_append.mpr ⟨hFmNd0, hBmRes1Nd, fun x hx y hy hEq => by
      subst hEq
      rcases List.mem_append.mp hy with hyB | hyR1
      · exact hFmBmResDisj x hx x (List.mem_append_left _ hyB) rfl
      · rcases List.mem_cons.mp hyR1 with rfl | hyR
        · exact hgNotTail (List.mem_append_left _ hx)
        · exact hFmBmResDisj x hx x (List.mem_append_right _ hyR) rfl⟩
  have hUf1Nd : (gs.map (·.metaPtr) ++
      (st.freeMetas.map (·.ptr) ++ (st.bumpMetas ++ (g.metaPtr :: st.reservedMetas)))).Nodup :=
    List.nodup_append.mpr ⟨hGsNd, hTail1Nd, fun x hx y hy hEq => by
      subst hEq
      obtain ⟨hx0, hxNeG⟩ := (hMetaSet x).mp hx
      rcases List.mem_append.mp hy with hyF | hyBR
      · exact hGrpTailDisj x hx0 x (List.mem_append_left _ hyF) rfl
      · rcases List.mem_append.mp hyBR with hyB | hyR1
        · exact hGrpTailDisj x hx0 x (List.mem_append_right _ (List.mem_append_left _ hyB)) rfl
        · rcases List.mem_cons.mp hyR1 with rfl | hyR
          · exact hxNeG rfl
          · exact hGrpTailDisj x hx0 x (List.mem_append_right _ (List.mem_append_right _ hyR)) rfl⟩
  refine ⟨hgNotRes, by simpa only [List.append_assoc] using hUf1Nd, fun m => ?_⟩
  rw [← hUfIff0 m]
  simp only [List.mem_append, List.mem_cons, hMetaSet m]
  constructor
  · rintro ((((⟨hm0, _⟩ | hmF) | hmB) | (rfl | hmR)))
    · exact Or.inl (Or.inl (Or.inl hm0))
    · exact Or.inl (Or.inl (Or.inr hmF))
    · exact Or.inl (Or.inr hmB)
    · exact Or.inl (Or.inl (Or.inl hgMap))
    · exact Or.inr hmR
  · rintro (((hm0 | hmF) | hmB) | hmR)
    · by_cases hEq : m = g.metaPtr
      · exact Or.inr (Or.inl hEq)
      · exact Or.inl (Or.inl (Or.inl ⟨hm0, hEq⟩))
    · exact Or.inl (Or.inl (Or.inr hmF))
    · exact Or.inl (Or.inr hmB)
    · exact Or.inr (Or.inr hmR)

theorem slotWf_transfer_retire {st st1 : MallocngSt} {h0 h : GroupDesc}
    (hGWf0 : GroupWf st h0)
    (hBvEq : ∀ a, InRegion h0.mem h0.totalBytes a → st1.byteVal a = st.byteVal a)
    (hMeta : h.metaPtr = h0.metaPtr) (hMem : h.mem = h0.mem) (hMp : h.maplen = h0.maplen)
    (hSc : h.sc = h0.sc) (hLast : h.lastIdx = h0.lastIdx) (hActB : h.activeByte = h0.activeByte)
    (hCap : h.nestedCap = h0.nestedCap)
    {j : Nat} (hj : j < h.slots.length) (hj0 : j < h0.slots.length)
    (hMaskJ : (h.availMask.getLsbD j = true ↔ h.slots[j]'hj = .freeAvail) ∧
              (h.freedMask.getLsbD j = true ↔ h.slots[j]'hj = .freeInactive) ∧
              (h.activeIdx < j → h.slots[j]'hj = .freeInactive))
    (hSlotPres :
      (∀ cm, h.slots[j]'hj = .liveNested cm ↔ h0.slots[j]'hj0 = .liveNested cm) ∧
      (∀ p n ec, h.slots[j]'hj = .liveUser p n ec ↔ h0.slots[j]'hj0 = .liveUser p n ec))
    (hChildLift : ∀ cm, h0.slots[j]'hj0 = .liveNested cm →
      ∀ cg ∈ st.groups, cg.metaPtr = cm →
        ∃ cg1 ∈ st1.groups, cg1.metaPtr = cg.metaPtr ∧ cg1.parentMeta = cg.parentMeta ∧
          cg1.mem = cg.mem ∧ cg1.nestedCap = cg.nestedCap)
    (hLiveOv : st1.liveMap.ov = st.liveMap.ov := by rfl) :
    SlotWf st1 h j (h.slots[j]'hj) := by
  have ⟨_, _, _, _, hSlotSE⟩ := group_stride_total_slot_eq hMem hMp hSc hLast hCap
  have hS0 := hGWf0.slot_wf j hj0
  cases hSj : h.slots[j]'hj with
  | freeAvail | freeInactive | claimed =>
    have ⟨hStrGe0, _, _, hEndLast0, _, hSlotCalc0⟩ := group_slot_toNat hGWf0
    have hjCnt0 : j < h0.cnt := hGWf0.2.2.1 ▸ hj0
    have ⟨hStart0, hEnd0, hSub40⟩ := hSlotCalc0 j hjCnt0
    have hSucc0 : (j + 1) * h0.stride = j * h0.stride + h0.stride := Nat.succ_mul j h0.stride
    have hMulLe0 : (j + 1) * h0.stride ≤ h0.cnt * h0.stride := Nat.mul_le_mul_right _ hjCnt0
    have hEndLeTot0 : (h0.slotEnd h0.lastIdx).toNat ≤ h0.mem.toNat + h0.totalBytes := by
      have := hGWf0.2.2.2.2.2.2.2.1; omega
    have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
    have hFit64 : h0.mem.toNat + h0.totalBytes ≤ 2 ^ 64 := by
      have := hGWf0.2.2.2.2.2.2.1; omega
    have hStartM4 : st1.byteVal (h.slotStart j - 4#64) = 0#8 := by
      rw [(hSlotSE j).1, hBvEq _ ((inRegion_iff_toNat hFit64 _).mpr ⟨by omega, by omega⟩)]
      exact hS0.1
    rw [hSj] at hMaskJ
    exact ⟨hStartM4, hMaskJ.1, hMaskJ.2.1, hMaskJ.2.2, trivial⟩
  | liveNested cm =>
    have hSj0 : h0.slots[j]'hj0 = .liveNested cm := (hSlotPres.1 cm).mp hSj
    rw [hSj0] at hS0
    rw [hSj] at hMaskJ
    exact slotWf_of_groupDataEq hGWf0 hj0 hS0 hBvEq hMeta hMem hSc hLast hMp hActB
      (hOv := fun u _ _ _ => congrFun hLiveOv u)
      hMaskJ.1 hMaskJ.2.1 hMaskJ.2.2 fun cm' hEq => by
        cases hEq
        exact hChildLift cm hSj0
  | liveUser p req ec =>
    have hSj0 : h0.slots[j]'hj0 = .liveUser p req ec := (hSlotPres.2 p req ec).mp hSj
    rw [hSj0] at hS0
    rw [hSj] at hMaskJ
    exact slotWf_of_groupDataEq hGWf0 hj0 hS0 hBvEq hMeta hMem hSc hLast hMp hActB
      hMaskJ.1 hMaskJ.2.1 hMaskJ.2.2 (fun _ hEq => by cases hEq)
      (hOv := fun u _ _ _ => congrFun hLiveOv u)

theorem no_other_group_overlaps_allFree_root {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hMpPos : 0 < g.maplen)
    (hNoChild : ∀ cg ∈ st.groups, cg.parentMeta ≠ some g.metaPtr)
    {u : GroupDesc} (hu : u ∈ st.groups) (hUNe : u.metaPtr ≠ g.metaPtr)
    {a : BitVec 64} (haU : InRegion u.mem u.totalBytes a)
    (haG : InRegion g.mem (g.maplen * 4096) a) :
    False := by
  suffices hRec : ∀ (fuel : Nat) (v : GroupDesc), v ∈ st.groups → v.metaPtr ≠ g.metaPtr →
      groupNestBound v ≤ fuel → InRegion v.mem v.totalBytes a → False from
    hRec (groupNestBound u) u hu hUNe (Nat.le_refl _) haU
  intro fuel
  induction fuel with
  | zero =>
    intro v hv hVNe hBnd haV
    by_cases hVMp : 0 < v.maplen
    · have hVTot : v.totalBytes = v.maplen * 4096 := by simp [GroupDesc.totalBytes, hVMp]
      rw [hVTot] at haV
      let flt := st.groups.filter fun x => decide (0 < x.maplen)
      have hvF : v ∈ flt := List.mem_filter.mpr ⟨hv, decide_eq_true hVMp⟩
      have hgF : g ∈ flt := List.mem_filter.mpr ⟨hg, decide_eq_true hMpPos⟩
      obtain ⟨i1, hi1, hEq1⟩ := List.getElem_of_mem hvF
      obtain ⟨i2, hi2, hEq2⟩ := List.getElem_of_mem hgF
      have hIdxNe : i1 ≠ i2 := fun hEqI => by
        subst hEqI; rw [hEq1] at hEq2; exact hVNe (congrArg GroupDesc.metaPtr hEq2)
      have hpd := (PairwiseDisjointRegions.append_iff.mp hwf.regions_disjoint.1).2.1
      have hDisj := PairwiseDisjointRegions.getElem_disjoint hpd
        (by simp [flt, hi1]) (by simp [flt, hi2]) hIdxNe
      simp only [flt, List.getElem_map, hEq1, hEq2] at hDisj
      exact DisjointRegions.not_both hDisj haV haG
    · have hVMp0 : v.maplen = 0 := by omega
      have hPosB : 0 < groupNestBound v := by
        unfold groupNestBound; simp only [hVMp, ↓reduceIte]
        split <;> try omega
        split <;> try omega
        split <;> try omega
        split <;> try omega
        split <;> omega
      omega
  | succ fuel' ih =>
    intro v hv hVNe hBnd haV
    by_cases hVMp : 0 < v.maplen
    · have hVTot : v.totalBytes = v.maplen * 4096 := by simp [GroupDesc.totalBytes, hVMp]
      rw [hVTot] at haV
      let flt := st.groups.filter fun x => decide (0 < x.maplen)
      have hvF : v ∈ flt := List.mem_filter.mpr ⟨hv, decide_eq_true hVMp⟩
      have hgF : g ∈ flt := List.mem_filter.mpr ⟨hg, decide_eq_true hMpPos⟩
      obtain ⟨i1, hi1, hEq1⟩ := List.getElem_of_mem hvF
      obtain ⟨i2, hi2, hEq2⟩ := List.getElem_of_mem hgF
      have hIdxNe : i1 ≠ i2 := fun hEqI => by
        subst hEqI; rw [hEq1] at hEq2; exact hVNe (congrArg GroupDesc.metaPtr hEq2)
      have hpd := (PairwiseDisjointRegions.append_iff.mp hwf.regions_disjoint.1).2.1
      have hDisj := PairwiseDisjointRegions.getElem_disjoint hpd
        (by simp [flt, hi1]) (by simp [flt, hi2]) hIdxNe
      simp only [flt, List.getElem_map, hEq1, hEq2] at hDisj
      exact DisjointRegions.not_both hDisj haV haG
    · have hVMp0 : v.maplen = 0 := by omega
      have hVWf := hwf.groups_wf v hv
      obtain ⟨_, pg, hpg, pIdx, hp, hPar, _, _, _, _, hStartLe, hEndLe, _⟩ :=
        hVWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hVMp0
      have hPgNeG : pg.metaPtr ≠ g.metaPtr := fun hEq =>
        hNoChild v hv (hPar.trans (congrArg some hEq))
      have hLt := groupNestBound_parent_lt hwf hv hVMp0 hpg hPar
      have hPgWf := hwf.groups_wf pg hpg
      have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
      have hVTot : v.totalBytes = v.nestedCap := by simp [GroupDesc.totalBytes, hVMp0]
      rw [hVTot] at haV
      have ⟨haLo, haHi⟩ := (inRegion_iff_toNat (by
        have := hVWf.2.2.2.2.2.2.1; rw [hVTot] at this; omega) a).mp haV
      have ⟨_, _, hPgStor, hPgEndLast, _, hPgSlotCalc⟩ := group_slot_toNat hPgWf
      have hpCnt : pIdx < pg.cnt := hPgWf.2.2.1 ▸ hp
      have ⟨hPgStart, hPgEnd, _⟩ := hPgSlotCalc pIdx hpCnt
      have hMulLe : (pIdx + 1) * pg.stride ≤ pg.cnt * pg.stride := Nat.mul_le_mul_right _ hpCnt
      have hEndLeTot : (pg.slotEnd pg.lastIdx).toNat ≤ pg.mem.toNat + pg.totalBytes := by
        have := hPgWf.2.2.2.2.2.2.2.1; omega
      have hVPos : 0 < v.nestedCap := by
        have := hVWf.2.2.2.2.2.2.2.1; rw [hVTot] at this; omega
      have haPg : InRegion pg.mem pg.totalBytes a :=
        (inRegion_iff_toNat (by have := hPgWf.2.2.2.2.2.2.1; omega) a).mpr ⟨by omega, by omega⟩
      exact ih pg hpg hPgNeG (by omega) haPg

theorem groupWf_transfer_deq_retire_root {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st st1 : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) (hMpPos : 0 < g.maplen)
    {active1 usage1 : List (BitVec 64)} {actLists1 : List (List (BitVec 64))}
    {gsDeq : List GroupDesc} {bvDeq : BitVec 64 → BitVec 8}
    (hDeq : DequeueOutcome st g active1 usage1 actLists1 gsDeq bvDeq)
    (hNoChild : ∀ cg ∈ st.groups, cg.parentMeta ≠ some g.metaPtr)
    (hSt1Groups : st1.groups = gsDeq) (hSt1Bv : st1.byteVal = bvDeq)
    {h : GroupDesc} (hh : h ∈ gsDeq)
    (hSt1Ov : st1.liveMap.ov = st.liveMap.ov := by rfl) :
    GroupWf st1 h := by
  obtain ⟨_, h0, hh0, hMeta, hMem, hMp, hSc, hLast, hActB, hPar, hCap, hSLen, _, _, hSlotPres⟩ :=
    hDeq.each_preserved h hh
  have hGWf0 := hwf.groups_wf h0 hh0
  have hGParNone : g.parentMeta = none := (hwf.groups_wf g hg).2.2.2.2.2.2.2.2.2.2.1.mp hMpPos
  have ⟨hCnt, hStr, hTot, hSto, hSlotSE⟩ := group_stride_total_slot_eq hMem hMp hSc hLast hCap
  have hDisj := groupMetaMod_disjoint hwf hDeq.only_group_metas
  have ⟨hBvData0, hBvEnd0⟩ := hDisj.2.2.2.2.2 h0 hh0
  have ⟨hAvFr0, hOrLt, h63PvNx, hMasks⟩ := hDeq.each_masks h hh
  have hMetaB := hDeq.each_meta_bytes h hh
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hFit64 : h0.mem.toNat + h0.totalBytes ≤ 2 ^ 64 := by
    have := hGWf0.2.2.2.2.2.2.1; omega
  have hTotGe12 : 12 ≤ h0.totalBytes := by
    have := hGWf0.2.2.2.2.2.2.2.1; omega
  have hBij := dequeue_origin_bijection hwf hDeq
  refine ⟨hSc ▸ hGWf0.1, hLast ▸ hGWf0.2.1, hSLen.trans (hGWf0.2.2.1.trans hCnt.symm),
    fun h63 => ⟨hLast ▸ (hGWf0.2.2.2.1 (hSc ▸ h63)).1, hMp ▸ (hGWf0.2.2.2.1 (hSc ▸ h63)).2.1,
      (h63PvNx h63).1, (h63PvNx h63).2⟩,
    hMem ▸ hGWf0.2.2.2.2.1, hMem ▸ hGWf0.2.2.2.2.2.1,
    by rw [hMem, hTot]; exact hGWf0.2.2.2.2.2.2.1,
    by rw [hCnt, hStr, hTot]; exact hGWf0.2.2.2.2.2.2.2.1,
    fun hPos => by rw [hCnt, hStr, hTot]; exact hGWf0.2.2.2.2.2.2.2.2.1 (hMp ▸ hPos),
    by rw [hSt1Bv, hLast, (hSlotSE h0.lastIdx).2, hBvEnd0]
       exact hGWf0.2.2.2.2.2.2.2.2.2.1,
    by rw [hMp, hPar]; exact hGWf0.2.2.2.2.2.2.2.2.2.2.1,
    fun hPos => by
      obtain ⟨hM1, hM2, hM3, hM4⟩ := hGWf0.2.2.2.2.2.2.2.2.2.2.2.1 (hMp ▸ hPos)
      exact ⟨hMem ▸ hM1, hCap ▸ hM2,
        fun hLe25 => by rw [hMp]; exact hM3 (hSc ▸ hLe25),
        fun hLt48 => ⟨by rw [hMp]; exact (hM4 (hSc ▸ hLt48)).1,
          fun hL0 => by
            rw [hStr, hSc, hMp]
            exact (hM4 (hSc ▸ hLt48)).2 (hLast ▸ hL0)⟩⟩,
    fun hMp0 => by
      obtain ⟨hL1, pg0, hpg0, pIdx, hp0, hPar0, hPg48, hLtSc, hPg24, hPSlot0,
        hStartLe, hEndLe, hCapEq⟩ := hGWf0.2.2.2.2.2.2.2.2.2.2.2.2.1 (hMp ▸ hMp0)
      have hPgNeG : pg0.metaPtr ≠ g.metaPtr := fun hEq =>
        hNoChild h0 hh0 (hPar0.trans (congrArg some hEq))
      obtain ⟨pg, hpg, hPgMeta, hPgMem, hPgMp, hPgSc, hPgLast, _, _, hPgCap, hPgSLen, _, _, hPgSP⟩ :=
        hBij pg0 hpg0 hPgNeG
      have ⟨_, _, _, _, hPgSE⟩ := group_stride_total_slot_eq hPgMem hPgMp hPgSc hPgLast hPgCap
      have hp : pIdx < pg.slots.length := hPgSLen ▸ hp0
      have hPSlot : pg.slots[pIdx]'hp = .liveNested h.metaPtr := by
        rw [hMeta]
        exact ((hPgSP pIdx hp hp0).1 h0.metaPtr).mpr hPSlot0
      refine ⟨hLast ▸ hL1, pg, hSt1Groups ▸ hpg, pIdx, hp,
        hPar.trans (hPar0.trans (congrArg some hPgMeta.symm)),
        hPgSc ▸ hPg48, by omega, by omega, hPSlot,
        by rw [(hPgSE pIdx).1, hMem]; exact hStartLe,
        by rw [(hPgSE pIdx).2, hMem, hCap]; exact hEndLe,
        by rw [hCap, hPgSc]; exact hCapEq⟩,
    hAvFr0, hOrLt,
    by simp only [GroupDesc.activeIdx, hActB, hLast]; exact hGWf0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    by rw [hSt1Bv]; exact hMetaB,
    by rw [hSt1Bv, hMem, hMeta, readBytesFromMap_eq_of_inRegion (by omega) fun a ha => by
         have ⟨x1, x2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
         exact hBvData0 a ((inRegion_iff_toNat hFit64 a).mpr ⟨x1, by omega⟩)]
       exact hGWf0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    by rw [hSt1Bv, hMem, hActB, hBvData0 (h0.mem + 8#64) ((inRegion_iff_toNat hFit64 _).mpr
         ⟨by rw [bv64_add_toNat (by omega)]; omega,
          by rw [bv64_add_toNat (by omega)]; omega⟩)]
       exact hGWf0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun j hj => ?_⟩
  have hj0 : j < h0.slots.length := hSLen ▸ hj
  refine slotWf_transfer_retire hGWf0
    (fun a ha => by rw [hSt1Bv]; exact hBvData0 a ha)
    hMeta hMem hMp hSc hLast hActB hCap hj hj0 (hMasks j hj) (hSlotPres j hj hj0)
    (fun cm hS0N cg0 hcg0 hCg0M => ?_) (hLiveOv := hSt1Ov)
  have hS0 := hGWf0.slot_wf j hj0
  rw [hS0N] at hS0
  obtain ⟨_, cg', hcg', hCg'M, hCg'Par, _⟩ := hS0.2.2.2.2
  have hCgEq : cg' = cg0 := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg' hcg0 (hCg'M.trans hCg0M.symm)
  subst hCgEq
  have hCgNeG : cg'.metaPtr ≠ g.metaPtr := fun hEq => by
    have hEqG : cg' = g := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg' hg hEq
    subst hEqG
    rw [hGParNone] at hCg'Par
    cases hCg'Par
  obtain ⟨cg1, hcg1, hCg1M, hCg1Mem, _, _, _, _, hCg1Par, hCg1Cap, _⟩ := hBij cg' hcg' hCgNeG
  exact ⟨cg1, hSt1Groups ▸ hcg1, hCg1M, hCg1Par, hCg1Mem, hCg1Cap⟩

set_option maxHeartbeats 400000 in
/-- Retires an all-free root group `g` (`0 < g.maplen`) at `+0x1d4..+0x220`: removes `g` from
    `st.groups`, pushes `g.metaPtr` onto `st1.reservedMetas`, carves out the zeroed meta slot and
    backing region `g.mem` (`g.maplen * 4096` bytes), and re-establishes `MallocngWFInflight`. -/
theorem free_retire_rootGroup {k : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight (k + 1) base brkStart brk liveCost peakCost st)
    {g : GroupDesc} (hg : g ∈ st.groups) {idx : Nat} (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hAllFree : (g.availMask ||| g.freedMask) + (1#32 <<< idx) = (2#32 <<< g.lastIdx) - 1#32)
    (hMpPos : 0 < g.maplen)
    {active1 usage1 : List (BitVec 64)} {actLists1 : List (List (BitVec 64))}
    {gsDeq : List GroupDesc} {bvDeq : BitVec 64 → BitVec 8}
    (hDeq : DequeueOutcome st g active1 usage1 actLists1 gsDeq bvDeq)
    (seq1 : BitVec 8) (unmapSeq1 : List (BitVec 8)) (hUSeqLen : unmapSeq1.length = 32) :
    let nBytes := g.maplen * 4096
    let gZero : GroupDesc := { g with prev := 0#64, next := 0#64 }
    let dom1 := st.masterDom.filter (fun a => !decide (InRegion g.mem nBytes a))
    let st1 : MallocngSt :=
      { st with
        ctx :=
          { st.ctx with
            active := active1
            usageByClass := usage1
            unmapSeq := unmapSeq1
            seq := seq1 }
        reservedMetas := g.metaPtr :: st.reservedMetas
        groups := gsDeq
        activeLists := actLists1
        masterDom := dom1
        byteVal := bvDeq }
    0 < nBytes ∧
    4096 ∣ g.mem.toNat ∧
    4096 ∣ nBytes ∧
    g.mem.toNat + nBytes ≤ 2 ^ 48 ∧
    BitVec.ofNat 64 nBytes ≠ 0#64 ∧
    (BitVec.ofNat 64 nBytes).toNat = nBytes ∧
    g.metaPtr ∈ st1.reservedMetas ∧
    st1.reservedMetas.erase g.metaPtr = st.reservedMetas ∧
    totalLiveCount st1 = totalLiveCount st ∧
    (dynamicRootRegions st1).length + 1 = (dynamicRootRegions st).length ∧
    (∀ a : BitVec 64, MallocngInIntervals (dynamicRootRegions st) a →
      InRegion g.mem nBytes a ∨ MallocngInIntervals (dynamicRootRegions st1) a) ∧
    MallocngWFInflight (k + 1) base brkStart brk liveCost peakCost st1 ∧
    (ByteMap st.masterDom (OwnedRwByte st) bvDeq ⊢
      (g.metaPtr ↦ₛ gZero.metaBytes) ∗
      memRegion g.mem nBytes ∗
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal) ∧
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal ∧
    MappedSet st.masterDom (OwnedMappedByte st) =
      (memMapped g.mem nBytes ∗ MappedSet st1.masterDom (OwnedMappedByte st1)) := by
  dsimp only []
  let nBytes := g.maplen * 4096
  let gZero : GroupDesc := { g with prev := 0#64, next := 0#64 }
  let dom1 := st.masterDom.filter (fun a => !decide (InRegion g.mem nBytes a))
  let st1 : MallocngSt :=
    { st with
      ctx :=
        { st.ctx with
          active := active1
          usageByClass := usage1
          unmapSeq := unmapSeq1
          seq := seq1 }
      reservedMetas := g.metaPtr :: st.reservedMetas
      groups := gsDeq
      activeLists := actLists1
      masterDom := dom1
      byteVal := bvDeq }
  have hGWf := hwf.groups_wf g hg
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hGTot : g.totalBytes = nBytes := by simp [GroupDesc.totalBytes, hMpPos, nBytes]
  have hMem48 : g.mem.toNat + nBytes ≤ 2 ^ 48 := by
    have := hGWf.2.2.2.2.2.2.1; rw [hGTot] at this; exact this
  have hNBytesPos : 0 < nBytes := by dsimp [nBytes]; omega
  have hMemMod4096 : g.mem.toNat % 4096 = 0 := (hGWf.2.2.2.2.2.2.2.2.2.2.2.1 hMpPos).1
  have hDvdMem : 4096 ∣ g.mem.toNat := Nat.dvd_of_mod_eq_zero hMemMod4096
  have hDvdLen : 4096 ∣ nBytes := ⟨g.maplen, Nat.mul_comm g.maplen 4096⟩
  have hNBytes64 : nBytes ≤ 2 ^ 64 := by omega
  have hBvToNat : (BitVec.ofNat 64 nBytes).toNat = nBytes := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hBvNe0 : BitVec.ofNat 64 nBytes ≠ 0#64 := fun hEq => by
    have := congrArg BitVec.toNat hEq; rw [hBvToNat] at this; simp at this; omega
  have ⟨_, hClaim1, hEff0, hLive0, hNoLiveUserG, hNoChild⟩ :=
    free_no_child_groups_of_allFree hwf hg hIdx hClaimed hAllFree
  have ⟨hgNotRes, hUf1Nd, hUf1Iff⟩ := retire_usedAndFree_props hwf hg hDeq.nodup.1 hDeq.meta_set
  have hInit1 : st.ctx.initDone = 1#32 := by
    rcases hwf.initDone_wf with h0 | h1
    · have := (hwf.initZero_wf h0).2.2.2.2.2.2.2.2.2.1; rw [this] at hg; cases hg
    · exact h1
  obtain ⟨preG, postG, hGsSplit, _, _, _, hFiltOutEq⟩ := split_groups_at_mem hwf.groups_nodup.1 hg
  let baseR := st.metaAreas.map (fun ma => (ma.base, 4096)) ++
    st.guardPages.map (fun gp => (gp, 4096)) ++
    st.availMetaPages.map (fun ap => (ap, 4096))
  let preR := (preG.filter (fun h => decide (0 < h.maplen))).map (fun h => (h.mem, h.maplen * 4096))
  let postR := (postG.filter (fun h => decide (0 < h.maplen))).map (fun h => (h.mem, h.maplen * 4096))
  have hDyn0 : dynamicRootRegions st = (baseR ++ preR) ++ (g.mem, nBytes) :: postR := by
    unfold dynamicRootRegions
    rw [hGsSplit, List.filter_append]
    simp only [List.filter_cons, decide_eq_true hMpPos, ↓reduceIte,
      List.map_append, List.map_cons, baseR, preR, postR, nBytes, List.append_assoc]
  have hDyn1 : dynamicRootRegions st1 = (baseR ++ preR) ++ postR := by
    unfold dynamicRootRegions
    change baseR ++ (gsDeq.filter (fun h => decide (0 < h.maplen))).map
      (fun h => (h.mem, h.maplen * 4096)) = _
    rw [hDeq.root_filter_eq]
    unfold filterOutGroup
    rw [hFiltOutEq, List.filter_append, List.map_append]
    simp only [baseR, preR, postR, List.append_assoc]
  have ⟨hPd1, hDyn1Disj⟩ := pairwiseDisjoint_remove_mid (hDyn0 ▸ hwf.regions_disjoint.1)
  have hDynLen : (dynamicRootRegions st1).length + 1 = (dynamicRootRegions st).length := by
    simp [hDyn0, hDyn1]; omega
  have hDynIvs : ∀ a : BitVec 64, MallocngInIntervals (dynamicRootRegions st) a →
      InRegion g.mem nBytes a ∨ MallocngInIntervals (dynamicRootRegions st1) a := by
    intro a ⟨iv, hiv, haIv⟩
    rw [hDyn0] at hiv
    rcases List.mem_append.mp hiv with hL | hCons
    · exact Or.inr ⟨iv, hDyn1 ▸ List.mem_append_left _ hL, haIv⟩
    · rcases List.mem_cons.mp hCons with rfl | hR
      · exact Or.inl haIv
      · exact Or.inr ⟨iv, hDyn1 ▸ List.mem_append_right _ hR, haIv⟩
  have ⟨_, _, _, _, _, hUfIff0⟩ := hwf.free_bump_metas_wf
  have hgMetaAll : g.metaPtr ∈ allMetaSlots st :=
    (hUfIff0 g.metaPtr).mp (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map_of_mem hg))))
  obtain ⟨_, ⟨maG, hmaG, hMetaSubMa⟩, hMetaNotCu, _, _, _, hMetaDisjRoot⟩ :=
    allMetaSlot_disjoint_other hwf hgMetaAll
  have hMetaDisjGMem : ∀ a, InRegion g.metaPtr 40 a → ¬ InRegion g.mem nBytes a :=
    fun a haM haMem => hMetaDisjRoot g hg hMpPos a haMem haM
  have hMetaNotCm0 : ∀ a, InRegion g.metaPtr 40 a → ¬ CarvedMetaByte st a := by
    rintro a haM ⟨x, hxRes, haX⟩
    have hxAll : x ∈ allMetaSlots st := (hUfIff0 x).mp (List.mem_append_right _ hxRes)
    have hxNe : x ≠ g.metaPtr := fun hEq => by subst hEq; exact hgNotRes hxRes
    exact metaSlot_disjoint_of_ne hwf hxAll hgMetaAll hxNe haX haM
  have hMetaInRw0 : ∀ a, InRegion g.metaPtr 40 a → OwnedRwByte st a := fun a haM =>
    ⟨Or.inl ⟨maG, hmaG, hMetaSubMa a haM⟩, hMetaNotCu a haM, hMetaNotCm0 a haM⟩
  have hCuIff : ∀ a : BitVec 64, CarvedUserByte st1 a ↔ CarvedUserByte st a := by
    intro a; constructor
    · rintro ⟨h, hh, s, hs, hMatch⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
      obtain ⟨_, h0, hh0, _, _, _, _, _, _, _, _, hSLen, _, _, hSP⟩ := hDeq.each_preserved h hh
      have hj0 : j < h0.slots.length := hSLen ▸ hj
      cases hSj : h.slots[j]'hj with
      | freeAvail | freeInactive | claimed | liveNested _ => rw [hSj] at hMatch; cases hMatch
      | liveUser p req ec =>
        rw [hSj] at hMatch
        have hSj0 := ((hSP j hj hj0).2 p req ec).mp hSj
        exact ⟨h0, hh0, .liveUser p req ec, hSj0 ▸ List.getElem_mem hj0, hMatch⟩
    · rintro ⟨h0, hh0, s, hs, hMatch⟩
      obtain ⟨j, hj0, rfl⟩ := List.getElem_of_mem hs
      cases hSj0 : h0.slots[j]'hj0 with
      | freeAvail | freeInactive | claimed | liveNested _ => rw [hSj0] at hMatch; cases hMatch
      | liveUser p req ec =>
        rw [hSj0] at hMatch
        have hNeG : h0.metaPtr ≠ g.metaPtr := fun hEq => by
          have hEqG := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hEq
          subst hEqG
          exact hNoLiveUserG _ (List.getElem_mem hj0) p req ec hSj0
        obtain ⟨h, hh, _, _, _, _, _, _, _, _, hSLen, _, _, hSP⟩ :=
          dequeue_origin_bijection hwf hDeq h0 hh0 hNeG
        have hj : j < h.slots.length := hSLen.symm ▸ hj0
        have hSj := ((hSP j hj hj0).2 p req ec).mpr hSj0
        exact ⟨h, hh, .liveUser p req ec, hSj ▸ List.getElem_mem hj, hMatch⟩
  have hMemNotCu0 : ∀ a, InRegion g.mem nBytes a → ¬ CarvedUserByte st a := by
    rintro a haMem ⟨u, hu, s, hs, hMatch⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
    cases hSj : u.slots[j]'hj with
    | freeAvail | freeInactive | claimed | liveNested _ => rw [hSj] at hMatch; cases hMatch
    | liveUser p req ec =>
      rw [hSj] at hMatch
      have hUNe : u.metaPtr ≠ g.metaPtr := fun hEq => by
        have hEqG := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hu hg hEq
        subst hEqG
        exact hNoLiveUserG _ (List.getElem_mem hj) p req ec hSj
      have hUWf := hwf.groups_wf u hu
      have hUS := hUWf.slot_wf j hj; rw [hSj] at hUS
      obtain ⟨⟨_, _, hpN48, _⟩, hStartLeP, hPNLeEnd, _⟩ := hUS.2.2.2.2
      have ⟨_, _, hStorU, hEndLastU, _, hSlotCalcU⟩ := group_slot_toNat hUWf
      have hjCnt : j < u.cnt := hUWf.2.2.1 ▸ hj
      have ⟨hStartU, hEndU, _⟩ := hSlotCalcU j hjCnt
      have hMulLeU : (j + 1) * u.stride ≤ u.cnt * u.stride := Nat.mul_le_mul_right _ hjCnt
      have hEndLeTotU : (u.slotEnd u.lastIdx).toNat ≤ u.mem.toNat + u.totalBytes := by
        have := hUWf.2.2.2.2.2.2.2.1; omega
      have hReqPos : 0 < req := by unfold InRegion at hMatch; omega
      have ⟨haLo, haHi⟩ := (inRegion_iff_toNat (by omega) a).mp hMatch
      have haU : InRegion u.mem u.totalBytes a :=
        (inRegion_iff_toNat (by have := hUWf.2.2.2.2.2.2.1; omega) a).mpr ⟨by omega, by omega⟩
      exact no_other_group_overlaps_allFree_root hwf hg hMpPos hNoChild hu hUNe haU haMem
  have hMemNotCm0 : ∀ a, InRegion g.mem nBytes a → ¬ CarvedMetaByte st a := by
    rintro a haMem ⟨x, hxRes, haX⟩
    have hxAll : x ∈ allMetaSlots st := (hUfIff0 x).mp (List.mem_append_right _ hxRes)
    obtain ⟨_, _, _, _, _, _, hXDisjR⟩ := allMetaSlot_disjoint_other hwf hxAll
    exact hXDisjR g hg hMpPos a haMem haX
  have hMemInRw0 : ∀ a, InRegion g.mem nBytes a → OwnedRwByte st a := fun a haMem =>
    ⟨Or.inr ⟨g, hg, hMpPos, haMem⟩, hMemNotCu0 a haMem, hMemNotCm0 a haMem⟩
  have hSt1RootDisj : ∀ r ∈ dynamicRootRegions st1, ∀ a, InRegion r.1 r.2 a →
      ¬ InRegion g.mem nBytes a := fun r hr a haR haG =>
    hDyn1Disj r (hDyn1 ▸ hr) a haR haG
  have hSrc1Eq : ∀ a : BitVec 64,
      ((∃ ma ∈ st1.metaAreas, InRegion ma.base 4096 a) ∨
       (∃ h ∈ st1.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a)) ↔
      (((∃ ma ∈ st.metaAreas, InRegion ma.base 4096 a) ∨
        (∃ h ∈ st.groups, 0 < h.maplen ∧ InRegion h.mem (h.maplen * 4096) a)) ∧
       ¬ InRegion g.mem nBytes a) := by
    intro a; constructor
    · rintro (⟨ma, hma, haMa⟩ | ⟨h, hh, hHMp, haH⟩)
      · have hNotG : ¬ InRegion g.mem nBytes a := hSt1RootDisj (ma.base, 4096)
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
            (List.mem_map_of_mem hma)))) a haMa
        exact ⟨Or.inl ⟨ma, hma, haMa⟩, hNotG⟩
      · have hNotG : ¬ InRegion g.mem nBytes a := hSt1RootDisj (h.mem, h.maplen * 4096)
          (List.mem_append_right _ (List.mem_map_of_mem
            (List.mem_filter.mpr ⟨hh, decide_eq_true hHMp⟩))) a haH
        obtain ⟨_, h0, hh0, _, hMem, hMp, _⟩ := hDeq.each_preserved h hh
        exact ⟨Or.inr ⟨h0, hh0, hMp ▸ hHMp, by rwa [← hMem, ← hMp]⟩, hNotG⟩
    · rintro ⟨⟨ma, hma, haMa⟩ | ⟨h0, hh0, h0Mp, haH0⟩, hNotG⟩
      · exact Or.inl ⟨ma, hma, haMa⟩
      · have hNeG : h0.metaPtr ≠ g.metaPtr := fun hEq => by
          have hEqG := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hEq
          subst hEqG; exact hNotG haH0
        obtain ⟨h, hh, _, hMem, hMp, _⟩ := dequeue_origin_bijection hwf hDeq h0 hh0 hNeG
        exact Or.inr ⟨h, hh, hMp.symm ▸ h0Mp, by rwa [hMem, hMp]⟩
  have hCm1Iff : ∀ a : BitVec 64, CarvedMetaByte st1 a ↔
      (CarvedMetaByte st a ∨ InRegion g.metaPtr 40 a) := by
    intro a; unfold CarvedMetaByte; simp only [st1, List.mem_cons]
    exact ⟨fun ⟨m, hm, ha⟩ => hm.elim (fun hEq => Or.inr (hEq ▸ ha)) (fun hm0 => Or.inl ⟨m, hm0, ha⟩),
      fun h => h.elim (fun ⟨m, hm0, ha⟩ => ⟨m, Or.inr hm0, ha⟩) (fun ha => ⟨g.metaPtr, Or.inl rfl, ha⟩)⟩
  have hRwRestIff : ∀ a : BitVec 64,
      ((OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) ∧ ¬ InRegion g.mem nBytes a) ↔
      OwnedRwByte st1 a := by
    intro a; unfold OwnedRwByte
    rw [hSrc1Eq a, hCuIff a, hCm1Iff a]
    constructor
    · rintro ⟨⟨⟨hSrc0, hNCu, hNCm0⟩, hNM⟩, hNG⟩
      exact ⟨⟨hSrc0, hNG⟩, hNCu, fun h => h.elim hNCm0 hNM⟩
    · rintro ⟨⟨hSrc0, hNG⟩, hNCu, hNCm1⟩
      exact ⟨⟨⟨hSrc0, hNCu, fun h0 => hNCm1 (Or.inl h0)⟩, fun hm => hNCm1 (Or.inr hm)⟩, hNG⟩
  have hMpRestIff : ∀ a : BitVec 64,
      (OwnedMappedByte st a ∧ ¬ InRegion g.mem nBytes a) ↔ OwnedMappedByte st1 a := by
    intro a; unfold OwnedMappedByte
    constructor
    · rintro ⟨hMb | hMg | hAp | ⟨h0, hh0, h0Mp, haH0⟩, hNotG⟩
      · exact Or.inl hMb
      · exact Or.inr (Or.inl hMg)
      · exact Or.inr (Or.inr (Or.inl hAp))
      · have hNeG : h0.metaPtr ≠ g.metaPtr := fun hEq => by
          have hEqG := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hEq
          subst hEqG; exact hNotG haH0
        obtain ⟨h, hh, _, hMem, hMp, _⟩ := dequeue_origin_bijection hwf hDeq h0 hh0 hNeG
        exact Or.inr (Or.inr (Or.inr ⟨h, hh, hMp.symm ▸ h0Mp, by rwa [hMem, hMp]⟩))
    · rintro (⟨mb, hmb, haMb⟩ | ⟨mg, hmg, haMg⟩ | ⟨ap, hap, haAp⟩ | ⟨h, hh, hHMp, haH⟩)
      · have hmb' := hwf.brk_mode_wf.2.1 ▸ hmb
        obtain ⟨_, hma, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hmb').1
        exact ⟨Or.inl ⟨_, hmb, haMb⟩, hSt1RootDisj _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_map_of_mem hma)))) a haMb⟩
      · have hmg' := hwf.brk_mode_wf.2.2.1 ▸ hmg
        have hgp := (List.mem_filter.mp hmg').1
        exact ⟨Or.inr (Or.inl ⟨_, hmg, haMg⟩), hSt1RootDisj _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hgp)))) a haMg⟩
      · exact ⟨Or.inr (Or.inr (Or.inl ⟨_, hap, haAp⟩)), hSt1RootDisj _ (List.mem_append_left _
          (List.mem_append_right _ (List.mem_map_of_mem hap))) a haAp⟩
      · have hNotG := hSt1RootDisj (h.mem, h.maplen * 4096) (List.mem_append_right _
          (List.mem_map_of_mem (List.mem_filter.mpr ⟨hh, decide_eq_true hHMp⟩))) a haH
        obtain ⟨_, h0, hh0, _, hMem, hMp, _⟩ := hDeq.each_preserved h hh
        exact ⟨Or.inr (Or.inr (Or.inr ⟨h0, hh0, hMp ▸ hHMp, by rwa [← hMem, ← hMp]⟩)), hNotG⟩
  have hDom0Nd := hwf.masterDom_wf.1
  have hDom1Nd : dom1.Nodup := nodup_filter_pred _ hDom0Nd
  have hByteEnt : ByteMap st.masterDom (OwnedRwByte st) bvDeq ⊢
      (g.metaPtr ↦ₛ gZero.metaBytes) ∗
      memRegion g.mem nBytes ∗
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal := by
    have hEx1 := ByteMap_extract_slice hDom0Nd bvDeq g.metaPtr (n := 40) (by decide)
      (fun a ha => hwf.masterDom_wf.2.1 a (Or.inl (hMetaInRw0 a ha))) hMetaInRw0
    rw [hDeq.g_zero_bytes] at hEx1
    have hEx2 := ByteMap_extract_slice hDom0Nd
      (keep := fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a)
      bvDeq g.mem (n := nBytes) hNBytes64
      (fun a ha => hwf.masterDom_wf.2.1 a (Or.inl (hMemInRw0 a ha)))
      (fun a ha => ⟨hMemInRw0 a ha, fun haM => hMetaDisjGMem a haM ha⟩)
    have hRestEq : ByteMap st.masterDom
        (fun a => (OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) ∧ ¬ InRegion g.mem nBytes a) bvDeq =
        ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal := by
      have hC : ByteMap st.masterDom
          (fun a => (OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) ∧ ¬ InRegion g.mem nBytes a) bvDeq =
          ByteMap st.masterDom (OwnedRwByte st1) bvDeq :=
        SetSep_congr (fun a _ => hRwRestIff a) (fun _ _ _ => rfl)
      rw [hC]
      exact (SetSep_filter_of_imp (fun a => !decide (InRegion g.mem nBytes a)) _
        fun a _ hRw1 => by
          have hNot := ((hRwRestIff a).mpr hRw1).2
          simp [hNot]).symm
    rw [hEx1, hEx2, hRestEq]
    have hMemEnt : (g.mem ↦ₛ readBytesFromMap bvDeq g.mem nBytes) ⊢ memRegion g.mem nBytes :=
      IsBlock.entails
        (IsBlock.pointsToBytes_len (readBytesFromMap_length bvDeq g.mem nBytes))
        (IsBlock.memRegion g.mem nBytes) fun _ _ => trivial
    exact sepConj_mono_right (sepConj_mono_left hMemEnt)
  have hDisjDeq := groupMetaMod_disjoint hwf hDeq.only_group_metas
  have hProtEq : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
      ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal := by
    have hValEq : ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
        ProtNoneByteMap st.masterDom (OwnedProtNoneByte st1) bvDeq :=
      SetSep_congr (fun _ _ => Iff.rfl) fun a _ hPn => by
        rcases hPn with ⟨gp, hgp, ha⟩ | ⟨ap, hap, ha⟩
        · exact congrArg (a ↦₈ₙ ·) (hDisjDeq.2.2.1 gp hgp a ha).symm
        · exact congrArg (a ↦₈ₙ ·) (hDisjDeq.2.1 ap hap a ha).symm
    rw [hValEq]
    exact (SetSep_filter_of_imp (fun a => !decide (InRegion g.mem nBytes a)) _
      fun a _ hPn => by
        have hNot : ¬ InRegion g.mem nBytes a := by
          rcases hPn with ⟨gp, hgp, ha⟩ | ⟨ap, hap, ha⟩
          · exact hSt1RootDisj _ (List.mem_append_left _ (List.mem_append_left _
              (List.mem_append_right _ (List.mem_map_of_mem hgp)))) a ha
          · exact hSt1RootDisj _ (List.mem_append_left _
              (List.mem_append_right _ (List.mem_map_of_mem hap))) a ha
        simp [hNot]).symm
  have hMappedEq : MappedSet st.masterDom (OwnedMappedByte st) =
      (memMapped g.mem nBytes ∗ MappedSet st1.masterDom (OwnedMappedByte st1)) := by
    have hInMp0 : ∀ a, InRegion g.mem nBytes a → OwnedMappedByte st a :=
      fun a ha => Or.inr (Or.inr (Or.inr ⟨g, hg, hMpPos, ha⟩))
    rw [MappedSet_extract_slice hDom0Nd g.mem hNBytes64
      (fun a ha => hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (hInMp0 a ha)))) hInMp0]
    refine congrArg (memMapped g.mem nBytes ∗ ·) ?_
    have hC : MappedSet st.masterDom (fun a => OwnedMappedByte st a ∧ ¬ InRegion g.mem nBytes a) =
        MappedSet st.masterDom (OwnedMappedByte st1) :=
      SetSep_congr (fun a _ => hMpRestIff a) (fun _ _ _ => rfl)
    rw [hC]
    exact (SetSep_filter_of_imp (fun a => !decide (InRegion g.mem nBytes a)) _
      fun a _ hMp1 => by
        have hNot := ((hMpRestIff a).mpr hMp1).2
        simp [hNot]).symm
  have hLiveCntEq : totalLiveCount st1 = totalLiveCount st := by
    have hS := hDeq.sum_live; rw [hLive0, Nat.add_zero] at hS; exact hS
  have hEffSumEq : totalLiveEffCost st1 = totalLiveEffCost st := by
    have hS := hDeq.sum_eff; rw [hEff0, Nat.add_zero] at hS; exact hS
  have hWf1 : MallocngWFInflight (k + 1) base brkStart brk liveCost peakCost st1 :=
    { base_wf := trivial
      brk_bounds := hwf.brk_bounds
      ctx_lens := ⟨hDeq.lens.1, hDeq.lens.2.1, hUSeqLen, hwf.ctx_lens.2.2.2.1,
        hwf.ctx_lens.2.2.2.2.1, hDeq.lens.2.2⟩
      initDone_wf := hwf.initDone_wf
      initZero_wf := fun h0 => by simp [st1, hInit1] at h0
      bounces_wf := hwf.bounces_wf
      usage_wf := fun sc hsc => hDeq.usage_eq sc hsc
      brk_mode_wf := hwf.brk_mode_wf
      metaAreas_wf := ⟨hwf.metaAreas_wf.1, fun ma hma => by
        obtain ⟨h1, h2, h3, hHdr⟩ := hwf.metaAreas_wf.2.1 ma hma
        exact ⟨h1, h2, h3, (readBytesFromMap_eq_of_inRegion (by decide) fun a ha =>
          hDisjDeq.1 ma hma a ha).trans hHdr⟩,
        hwf.metaAreas_wf.2.2⟩
      guard_avail_wf := ⟨hwf.guard_avail_wf.1, hwf.guard_avail_wf.2.1, hwf.guard_avail_wf.2.2.1,
        fun ap hap => by
          obtain ⟨h1, h2, h3, hZ⟩ := hwf.guard_avail_wf.2.2.2 ap hap
          exact ⟨h1, h2, h3, (readBytesFromMap_eq_of_inRegion (by decide) fun a ha =>
            hDisjDeq.2.1 ap hap a ha).trans hZ⟩⟩
      inflight_wf := by
        have hInf := hwf.inflight_wf
        have hSumC := hDeq.sum_claimed; rw [hClaim1] at hSumC
        change (g.metaPtr :: st.reservedMetas).length +
          (gsDeq.map (fun h => (h.slots.filter SlotState.isClaimed).length)).sum ≤ k + 1
        simp only [List.length_cons]; omega
      free_bump_metas_wf := ⟨hwf.free_bump_metas_wf.1,
        fun fm hfm => (readBytesFromMap_eq_of_inRegion (by decide) fun a ha =>
          hDisjDeq.2.2.2.1 fm hfm a ha).trans (hwf.free_bump_metas_wf.2.1 fm hfm),
        hwf.free_bump_metas_wf.2.2.1,
        fun bm hbm => (readBytesFromMap_eq_of_inRegion (by decide) fun a ha =>
          hDisjDeq.2.2.2.2.1 bm hbm a ha).trans (hwf.free_bump_metas_wf.2.2.2.1 bm hbm),
        hUf1Nd, hUf1Iff⟩
      groups_nodup := hDeq.nodup
      groups_wf := fun h hh =>
        groupWf_transfer_deq_retire_root hwf hg hMpPos hDeq hNoChild rfl rfl hh
      regions_disjoint := ⟨hDyn1 ▸ hPd1, trivial⟩
      active_wf := fun sc h1 h2 => hDeq.active_wf_deq sc h1 h2
      liveMap_wf := fun p n => by
        rw [hwf.liveMap_wf p n]
        constructor
        · rintro ⟨h0, hh0, j, hj0, ec, hSj0⟩
          have hNeG : h0.metaPtr ≠ g.metaPtr := fun hEq => by
            have hEqG := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hEq
            subst hEqG
            exact hNoLiveUserG _ (List.getElem_mem hj0) p n ec hSj0
          obtain ⟨h, hh, _, _, _, _, _, _, _, _, hSLen, _, _, hSP⟩ :=
            dequeue_origin_bijection hwf hDeq h0 hh0 hNeG
          have hj : j < h.slots.length := hSLen.symm ▸ hj0
          exact ⟨h, hh, j, hj, ec, ((hSP j hj hj0).2 p n ec).mpr hSj0⟩
        · rintro ⟨h, hh, j, hj, ec, hSj⟩
          obtain ⟨_, h0, hh0, _, _, _, _, _, _, _, _, hSLen, _, _, hSP⟩ := hDeq.each_preserved h hh
          have hj0 : j < h0.slots.length := hSLen ▸ hj
          exact ⟨h0, hh0, j, hj0, ec, ((hSP j hj hj0).2 p n ec).mp hSj⟩
      live_le_peak := hwf.live_le_peak
      effCost_le_live := hEffSumEq ▸ hwf.effCost_le_live
      meta_pages_bound := hwf.meta_pages_bound
      empty_groups_bound := fun h hh hEmp => by
        obtain ⟨_, h0, hh0, _, _, hMp, hSc, hLast, _, _, _, _, hEmpEq, _⟩ := hDeq.each_preserved h hh
        have ⟨e1, e2, e3, e4, _, _, e7⟩ := hwf.empty_groups_bound h0 hh0 (hEmpEq ▸ hEmp)
        have ⟨hMemAct, hUniqDeq⟩ := hDeq.empty_act_singleton h hh hEmp
        exact ⟨hMp ▸ e1, hSc ▸ e2, hSc ▸ e3, hMp ▸ e4, hMemAct, hUniqDeq,
          fun hL0 => by rw [hSc, hMp]; exact e7 (hLast ▸ hL0)⟩
      masterDom_wf := ⟨hDom1Nd,
        fun a hOwn => by
          rcases hOwn with hRw1 | hPn1 | hMp1
          · have h0 := (hRwRestIff a).mpr hRw1
            exact List.mem_filter.mpr ⟨hwf.masterDom_wf.2.1 a (Or.inl h0.1.1), by simp [h0.2]⟩
          · have hNot : ¬ InRegion g.mem nBytes a := by
              rcases hPn1 with ⟨gp, hgp, ha⟩ | ⟨ap, hap, ha⟩
              · exact hSt1RootDisj _ (List.mem_append_left _ (List.mem_append_left _
                  (List.mem_append_right _ (List.mem_map_of_mem hgp)))) a ha
              · exact hSt1RootDisj _ (List.mem_append_left _
                  (List.mem_append_right _ (List.mem_map_of_mem hap))) a ha
            exact List.mem_filter.mpr ⟨hwf.masterDom_wf.2.1 a (Or.inr (Or.inl hPn1)), by simp [hNot]⟩
          · have h0 := (hMpRestIff a).mpr hMp1
            exact List.mem_filter.mpr ⟨hwf.masterDom_wf.2.1 a (Or.inr (Or.inr h0.1)), by simp [h0.2]⟩,
        fun a ha => by
          obtain ⟨ha0, hNotB⟩ := List.mem_filter.mp ha
          have hNotG : ¬ InRegion g.mem nBytes a := by simpa using hNotB
          obtain ⟨r, hr0, haR⟩ := hwf.masterDom_wf.2.2 a ha0
          rw [hDyn0] at hr0
          rcases List.mem_append.mp hr0 with hL | hCons
          · exact ⟨r, hDyn1 ▸ List.mem_append_left _ hL, haR⟩
          · rcases List.mem_cons.mp hCons with rfl | hR
            · exact False.elim (hNotG haR)
            · exact ⟨r, hDyn1 ▸ List.mem_append_right _ hR, haR⟩⟩ }
  exact ⟨hNBytesPos, hDvdMem, hDvdLen, hMem48, hBvNe0, hBvToNat,
    List.mem_cons_self .., List.erase_cons_head .., hLiveCntEq, hDynLen, hDynIvs,
    hWf1, hByteEnt, hProtEq, hMappedEq⟩

end VerifiedLibraries.Mallocng.Proofs

