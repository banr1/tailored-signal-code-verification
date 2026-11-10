/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.VendorFree.PlacedFreeHelpers4

/-!
# Metadata-Only Invariant Lifts and Empty-Queue Enqueueing for `nontrivial_free`

Proves byte-map disjointness and `SlotWf`/`GroupWf` frame lifts for modifications confined to
40-byte `struct meta` slots, together with the `MallocngWFInflight (k + 1) -> MallocngWFInflight k`
transition when `nontrivial_free` enqueues a group onto an empty `ctx.active[g.sc]`.
-/

set_option autoImplicit false

namespace LibsignalBinary.Heap.Fine.VendorFree
open VerifiedLibraries VerifiedLibraries.Mallocng VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

@[expose] public section

/-- Trivial compatibility predicate retained for queue-transition helper signatures. -/
def FullQueueKeepWf (_st : MallocngSt) : Prop := True

theorem isEmpty_set_of_not_free {slots : List SlotState} {idx : Nat}
    (hIdx : idx < slots.length) {s1 : SlotState}
    (hOld : (slots[idx]'hIdx).isFree = false) (hNew : s1.isFree = false) :
    (slots.set idx s1).all SlotState.isFree = slots.all SlotState.isFree := by
  have hFalse1 : slots.all SlotState.isFree = false :=
    Bool.eq_false_iff.mpr fun hAll => by
      have := List.all_eq_true.mp hAll (slots[idx]'hIdx) (List.getElem_mem hIdx)
      rw [hOld] at this; cases this
  have hIdx' : idx < (slots.set idx s1).length := by simp [hIdx]
  have hFalse2 : (slots.set idx s1).all SlotState.isFree = false :=
    Bool.eq_false_iff.mpr fun hAll => by
      have := List.all_eq_true.mp hAll ((slots.set idx s1)[idx]'hIdx') (List.getElem_mem hIdx')
      simp [hNew] at this
  rw [hFalse1, hFalse2]

theorem keepWf_of_release_userSlot {st : MallocngSt} {g : GroupDesc} {idx : Nat}
    (hNdm : (st.groups.map (·.metaPtr)).Nodup)
    (hg : g ∈ st.groups) (hIdx : idx < g.slots.length)
    {p : BitVec 64} {reqSize effCost : Nat}
    (_hLive : g.slots[idx]'hIdx = .liveUser p reqSize effCost)
    {bs : List (BitVec 8)}
    (hKeep : EmptyGroupKeepWf st) (_hFq : FullQueueKeepWf st) :
    EmptyGroupKeepWf (mkReleasedSt st g idx p bs) ∧
    FullQueueKeepWf (mkReleasedSt st g idx p bs) := by
  have hRep := replaceGroupByMeta_props hNdm hg (g1 := mkReleasedGroup g idx) rfl rfl rfl rfl rfl
  refine ⟨fun h' hh' hPos h7 h38 => ?_, trivial⟩
  rcases hRep.2.2.2.2.2.1 h' hh' with hEq | ⟨hh0, _⟩
  · subst h'; exact hKeep g hg hPos h7 h38
  · exact hKeep h' hh0 hPos h7 h38

theorem groupMetaMod_disjoint {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {bv1 : BitVec 64 → BitVec 8}
    (hOnlyMetas : ∀ a : BitVec 64, bv1 a ≠ st.byteVal a →
      ∃ u ∈ st.groups, InRegion u.metaPtr 40 a) :
    (∀ ma ∈ st.metaAreas, ∀ a, InRegion ma.base 24 a → bv1 a = st.byteVal a) ∧
    (∀ ap ∈ st.availMetaPages, ∀ a, InRegion ap 4096 a → bv1 a = st.byteVal a) ∧
    (∀ gp ∈ st.guardPages, ∀ a, InRegion gp 4096 a → bv1 a = st.byteVal a) ∧
    (∀ fm ∈ st.freeMetas, ∀ a, InRegion fm.ptr 40 a → bv1 a = st.byteVal a) ∧
    (∀ bm ∈ st.bumpMetas, ∀ a, InRegion bm 40 a → bv1 a = st.byteVal a) ∧
    (∀ h ∈ st.groups,
      (∀ a, InRegion h.mem h.totalBytes a → bv1 a = st.byteVal a) ∧
      bv1 (h.slotEnd h.lastIdx) = st.byteVal (h.slotEnd h.lastIdx)) := by
  have ⟨_, _, _, _, hUfNd, hUfIff⟩ := hwf.free_bump_metas_wf
  have hGroupInAll : ∀ u ∈ st.groups, u.metaPtr ∈ allMetaSlots st := fun u hu =>
    (hUfIff u.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hu))))
  refine ⟨fun ma hma a ha => Classical.byContradiction fun hNe => ?_,
    fun ap hap a ha => Classical.byContradiction fun hNe => ?_,
    fun gp hgp a ha => Classical.byContradiction fun hNe => ?_,
    fun fm hfm a ha => Classical.byContradiction fun hNe => ?_,
    fun bm hbm a ha => Classical.byContradiction fun hNe => ?_,
    fun h hh => ⟨fun a ha => Classical.byContradiction fun hNe => ?_,
      Classical.byContradiction fun hNe => ?_⟩⟩
  · obtain ⟨u, hu, haU⟩ := hOnlyMetas a hNe
    have hmAll := hGroupInAll u hu
    unfold allMetaSlots at hmAll
    obtain ⟨maU, hmaU, hmU⟩ := List.mem_flatMap.mp hmAll
    obtain ⟨kU, hkUr, hSlotU⟩ := List.mem_map.mp hmU
    have hMaWf := hwf.metaAreas_wf.2.1 ma hma
    obtain ⟨hLoU, hAlU, hHiU, _⟩ := hwf.metaAreas_wf.2.1 maU hmaU
    obtain ⟨hEqNatU, _, _, hSlotFitU, hSubU⟩ :=
      slotAddr_bounds hLoU hAlU hHiU (List.mem_range.mp hkUr)
    have ⟨haLo, haHi⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    have ⟨huLo, _⟩ := (inRegion_iff_toNat (by rw [← hSlotU]; omega) a).mp haU
    rw [← hSlotU, hEqNatU] at huLo
    by_cases hSameMa : ma.base = maU.base
    · rw [← hSameMa] at huLo; omega
    · obtain ⟨i1, hi1, hEq1⟩ := List.getElem_of_mem hma
      obtain ⟨i2, hi2, hEq2⟩ := List.getElem_of_mem hmaU
      have hIdxNe : i1 ≠ i2 := fun hEqI => by
        subst hEqI; rw [hEq1] at hEq2; exact hSameMa (congrArg MetaAreaDesc.base hEq2)
      have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd
      rw [List.append_assoc, List.append_assoc, PairwiseDisjointRegions.append_iff] at hpd
      have hDisj := PairwiseDisjointRegions.getElem_disjoint hpd.1
        (by simp [hi1]) (by simp [hi2]) hIdxNe
      simp only [List.getElem_map, hEq1, hEq2] at hDisj
      have hIn1 : InRegion ma.base 4096 a := (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
      exact DisjointRegions.not_both hDisj hIn1 (hSubU a (hSlotU ▸ haU))
  · obtain ⟨u, hu, haU⟩ := hOnlyMetas a hNe
    obtain ⟨_, _, _, ⟨maU, hmaU, hInMaU⟩, _⟩ := allMetaSlots_info hwf (hGroupInAll u hu)
    have hDisj := (PairwiseDisjointRegions.append_iff.mp
      (PairwiseDisjointRegions.append_iff.mp hwf.regions_disjoint.1).1).2.2
      (maU.base, 4096) (List.mem_append_left _ (List.mem_map_of_mem hmaU))
      (ap, 4096) (List.mem_map_of_mem hap)
    exact DisjointRegions.not_both hDisj (hInMaU a haU) ha
  · obtain ⟨u, hu, haU⟩ := hOnlyMetas a hNe
    obtain ⟨_, _, _, ⟨maU, hmaU, hInMaU⟩, _⟩ := allMetaSlots_info hwf (hGroupInAll u hu)
    have hDisj := (PairwiseDisjointRegions.append_iff.mp
      (PairwiseDisjointRegions.append_iff.mp
        (PairwiseDisjointRegions.append_iff.mp hwf.regions_disjoint.1).1).1).2.2
      (maU.base, 4096) (List.mem_map_of_mem hmaU)
      (gp, 4096) (List.mem_map_of_mem hgp)
    exact DisjointRegions.not_both hDisj (hInMaU a haU) ha
  · obtain ⟨u, hu, haU⟩ := hOnlyMetas a hNe
    have hInFm : fm.ptr ∈ st.freeMetas.map (·.ptr) := List.mem_map_of_mem hfm
    have hInGr : u.metaPtr ∈ st.groups.map (·.metaPtr) := List.mem_map_of_mem hu
    have hNd12 := List.nodup_append.mp (List.nodup_append.mp (List.nodup_append.mp hUfNd).1).1
    have hPtrNe : fm.ptr ≠ u.metaPtr := fun hEq => hNd12.2.2 u.metaPtr hInGr fm.ptr hInFm hEq.symm
    have hAllFm : fm.ptr ∈ allMetaSlots st :=
      (hUfIff fm.ptr).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hInFm)))
    exact DisjointRegions.not_both ((allMetaSlots_info hwf (hGroupInAll u hu)).2.2.2.2 fm.ptr hAllFm hPtrNe) haU ha
  · obtain ⟨u, hu, haU⟩ := hOnlyMetas a hNe
    have hInGr : u.metaPtr ∈ st.groups.map (·.metaPtr) := List.mem_map_of_mem hu
    have hNd123 := List.nodup_append.mp (List.nodup_append.mp hUfNd).1
    have hPtrNe : bm ≠ u.metaPtr := fun hEq =>
      hNd123.2.2 u.metaPtr (List.mem_append_left _ hInGr) bm hbm hEq.symm
    have hAllBm : bm ∈ allMetaSlots st :=
      (hUfIff bm).mp (List.mem_append_left _ (List.mem_append_right _ hbm))
    exact DisjointRegions.not_both ((allMetaSlots_info hwf (hGroupInAll u hu)).2.2.2.2 bm hAllBm hPtrNe) haU ha
  · obtain ⟨u, hu, haU⟩ := hOnlyMetas a hNe
    obtain ⟨_, _, _, ⟨maU, hmaU, hInMaU⟩, _⟩ := allMetaSlots_info hwf (hGroupInAll u hu)
    obtain ⟨rgH, hrgH, hRgPos, hRgLo, hRgHi, _⟩ := group_root_containment hwf hh
    have hRgWf := hwf.groups_wf rgH hrgH
    have hRgTot : rgH.totalBytes = rgH.maplen * 4096 := by simp [GroupDesc.totalBytes, hRgPos]
    have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
    have ⟨haLo, haHi⟩ := (inRegion_iff_toNat (by
      have := (hwf.groups_wf h hh).2.2.2.2.2.2.1; omega) a).mp ha
    have hInRg : InRegion rgH.mem (rgH.maplen * 4096) a :=
      (inRegion_iff_toNat (by have := hRgWf.2.2.2.2.2.2.1; omega) a).mpr ⟨by omega, by omega⟩
    exact DisjointRegions.not_both (metaArea_disjoint_rootGroup hwf hmaU hrgH hRgPos)
      (hInMaU a haU) hInRg
  · obtain ⟨u, hu, haU⟩ := hOnlyMetas (h.slotEnd h.lastIdx) hNe
    obtain ⟨_, _, _, ⟨maU, hmaU, hInMaU⟩, _⟩ := allMetaSlots_info hwf (hGroupInAll u hu)
    obtain ⟨rgH, hrgH, hRgPos, hRgLo, _, hEndLt⟩ := group_root_containment hwf hh
    have hRgWf := hwf.groups_wf rgH hrgH
    have hRgTot : rgH.totalBytes = rgH.maplen * 4096 := by simp [GroupDesc.totalBytes, hRgPos]
    have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
    have hHWf := hwf.groups_wf h hh
    have hEndLo : h.mem.toNat ≤ (h.slotEnd h.lastIdx).toNat := by
      have := (group_slot_toNat hHWf).2.2.2.1; have := (group_slot_toNat hHWf).1; omega
    have hInRg : InRegion rgH.mem (rgH.maplen * 4096) (h.slotEnd h.lastIdx) :=
      (inRegion_iff_toNat (by have := hRgWf.2.2.2.2.2.2.1; omega) _).mpr ⟨by omega, by omega⟩
    exact DisjointRegions.not_both (metaArea_disjoint_rootGroup hwf hmaU hrgH hRgPos)
      (hInMaU _ haU) hInRg

set_option maxHeartbeats 400000 in
theorem slotWf_of_groupDataEq {st st1 : MallocngSt} {h h1 : GroupDesc} {j : Nat} {s : SlotState}
    (hHWf : GroupWf st h) (hj : j < h.slots.length)
    (hSWf : SlotWf st h j s)
    (hDataEq : ∀ a, InRegion h.mem h.totalBytes a → st1.byteVal a = st.byteVal a)
    (hMeta : h1.metaPtr = h.metaPtr) (hMem : h1.mem = h.mem)
    (hSc : h1.sc = h.sc) (hLast : h1.lastIdx = h.lastIdx)
    (hMaplen : h1.maplen = h.maplen) (hActB : h1.activeByte = h.activeByte)
    (hAvIff : h1.availMask.getLsbD j = true ↔ s = .freeAvail)
    (hFrIff : h1.freedMask.getLsbD j = true ↔ s = .freeInactive)
    (hActLt : h1.activeIdx < j → s = .freeInactive)
    (hChildLift : ∀ cm, s = .liveNested cm → ∀ cg ∈ st.groups, cg.metaPtr = cm →
      ∃ cg1 ∈ st1.groups, cg1.metaPtr = cg.metaPtr ∧ cg1.parentMeta = cg.parentMeta ∧
        cg1.mem = cg.mem ∧ cg1.nestedCap = cg.nestedCap)
    (hOv : ∀ u r e, s = .liveUser u r e → st1.liveMap.ov u = st.liveMap.ov u := by intros; rfl) :
    SlotWf st1 h1 j s := by
  let _ := hActB
  have hjCnt : j < h.cnt := by rw [← hHWf.2.2.1]; exact hj
  have hMemGe : 4096 ≤ h.mem.toNat := hHWf.2.2.2.2.1
  have ⟨hStrGe, _, hStorNat, _, hEndTot, hSlotCalc⟩ := group_slot_toNat hHWf
  have ⟨hStartNat, hEndNat, hSub4Nat⟩ := hSlotCalc j hjCnt
  have hMulLe : (j + 1) * h.stride ≤ h.cnt * h.stride := Nat.mul_le_mul_right _ hjCnt
  have hSuccMul : (j + 1) * h.stride = j * h.stride + h.stride := Nat.succ_mul j h.stride
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hFit64 : h.mem.toNat + h.totalBytes ≤ 2 ^ 64 := by
    have := hHWf.2.2.2.2.2.2.1; omega
  have hStrEq : h1.stride = h.stride := by simp [GroupDesc.stride, hLast, hMaplen, hSc]
  have hStorEq : h1.storage = h.storage := by simp [GroupDesc.storage, hMem]
  have hSStartEq : h1.slotStart j = h.slotStart j := by simp [GroupDesc.slotStart, hStorEq, hStrEq]
  have hSEndEq : h1.slotEnd j = h.slotEnd j := by simp [GroupDesc.slotEnd, hSStartEq, hStrEq]
  have hInTot : ∀ x : BitVec 64, h.mem.toNat ≤ x.toNat → x.toNat < h.mem.toNat + h.totalBytes →
      st1.byteVal x = st.byteVal x := fun x hxLo hxHi =>
    hDataEq x ((inRegion_iff_toNat hFit64 x).mpr ⟨hxLo, hxHi⟩)
  have hBounds : h.mem.toNat ≤ (h.slotStart j).toNat - 4 ∧
      (h.slotEnd j).toNat ≤ h.mem.toNat + h.totalBytes ∧
      8 ≤ (h.slotStart j).toNat := ⟨by omega, by omega, by omega⟩
  have hSlotIn : ∀ x : BitVec 64, (h.slotStart j).toNat - 4 ≤ x.toNat →
      x.toNat < (h.slotEnd j).toNat → st1.byteVal x = st.byteVal x :=
    fun x hx1 hx2 => hInTot x (by omega) (by omega)
  have hRegEq : ∀ (p : BitVec 64) (n : Nat),
      (h.slotStart j).toNat - 8 ≤ p.toNat → p.toNat + n ≤ (h.slotEnd j).toNat →
      readBytesFromMap st1.byteVal p n = readBytesFromMap st.byteVal p n := by
    intro p n hp1 hp2
    have hpLo : h.mem.toNat ≤ p.toNat := by omega
    have hpHi : p.toNat + n ≤ h.mem.toNat + h.totalBytes := by omega
    exact readBytesFromMap_eq_of_inRegion (by omega) fun a ha => by
      have ⟨x1, x2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
      exact hInTot a (by omega) (by omega)
  unfold SlotWf at hSWf ⊢
  simp only [hSStartEq, hSEndEq, hStorEq, hSc, hMaplen, hMeta]
  obtain ⟨hB0, _, _, _, hBody⟩ := hSWf
  refine ⟨(hSlotIn (h.slotStart j - 4#64) (by omega) (by omega)).trans hB0,
    hAvIff, hFrIff, hActLt, ?_⟩
  clear hB0 hAvIff hFrIff hActLt
  cases s with
  | freeAvail => trivial
  | freeInactive => trivial
  | claimed => trivial
  | liveNested cm =>
    obtain ⟨hHSc48, cg, hcg, hCgM, hCgPar, hCgLo, hCgMod, hCgHi, hCgCap, hOffLe,
      hB4, hB3, hB2⟩ := hBody
    obtain ⟨cg1, hcg1, hCg1M, hCg1Par, hCg1Mem, hCg1Cap⟩ := hChildLift cm rfl cg hcg hCgM
    have hCapGe : 12 ≤ cg.nestedCap := by
      have := (sizeClass_bounds hHSc48).1; unfold slotStride at hCgCap; omega
    clear hChildLift
    have hCg4 : (cg.mem - 4#64).toNat = cg.mem.toNat - 4 := bv64_sub_toNat (by omega)
    have hCg3 : (cg.mem - 3#64).toNat = cg.mem.toNat - 3 := bv64_sub_toNat (by omega)
    have hCg2 : (cg.mem - 2#64).toNat = cg.mem.toNat - 2 := bv64_sub_toNat (by omega)
    refine ⟨hHSc48, cg1, hcg1, hCg1M.trans hCgM, hCg1Par.trans hCgPar,
      hCg1Mem ▸ hCgLo, hCg1Mem ▸ hCgMod, by rw [hCg1Mem, hCg1Cap]; exact hCgHi,
      hCg1Cap.trans hCgCap, hCg1Mem ▸ hOffLe,
      by rw [hCg1Mem]; exact (hSlotIn (cg.mem - 4#64) (by omega) (by omega)).trans hB4,
      by rw [hCg1Mem]; exact (hSlotIn (cg.mem - 3#64) (by omega) (by omega)).trans hB3,
      by rw [hCg1Mem, hRegEq (cg.mem - 2#64) 2 (by omega) (by omega)]; exact hB2⟩
  | liveUser userPtr reqSize effCost =>
    obtain ⟨hBlk, hULo, hUHi, hMinEc, hOffB, hRes31, hScProps, h63Prop,
      hUB3, hIfOff, hPost0, hTrail⟩ := hBody
    refine ⟨hBlk, hULo, hUHi, hMinEc, by rw [hOv _ _ _ rfl]; exact hOffB, hRes31, hScProps, h63Prop, ?_⟩
    clear hBlk hMinEc hOffB hRes31 hScProps h63Prop hChildLift hOv
    have hU3 : (userPtr - 3#64).toNat = userPtr.toNat - 3 := bv64_sub_toNat (by omega)
    have hU4 : (userPtr - 4#64).toNat = userPtr.toNat - 4 := bv64_sub_toNat (by omega)
    have hU2 : (userPtr - 2#64).toNat = userPtr.toNat - 2 := bv64_sub_toNat (by omega)
    have hU8 : (userPtr - 8#64).toNat = userPtr.toNat - 8 := bv64_sub_toNat (by omega)
    refine ⟨(hSlotIn (userPtr - 3#64) (by omega) (by omega)).trans hUB3, ?_, ?_, ?_⟩
    · by_cases hOff16 : (userPtr.toNat - h.storage.toNat) / 16 ≤ 0xffff <;>
        simp only [hOff16, ↓reduceIte] at hIfOff ⊢
      · exact ⟨(hSlotIn (userPtr - 4#64) (by omega) (by omega)).trans hIfOff.1,
          (hRegEq (userPtr - 2#64) 2 (by omega) (by omega)).trans hIfOff.2⟩
      · exact ⟨hIfOff.1, hIfOff.2.1, hIfOff.2.2.1,
          (hSlotIn (userPtr - 4#64) (by omega) (by omega)).trans hIfOff.2.2.2.1,
          (hRegEq (userPtr - 2#64) 2 (by omega) (by omega)).trans hIfOff.2.2.2.2.1,
          (hRegEq (userPtr - 8#64) 4 (by omega) (by omega)).trans hIfOff.2.2.2.2.2⟩
    · intro hRes1
      have hAdd : (userPtr + BitVec.ofNat 64 reqSize).toNat = userPtr.toNat + reqSize :=
        bv64_add_toNat (by omega)
      exact (hSlotIn (userPtr + BitVec.ofNat 64 reqSize) (by omega) (by omega)).trans (hPost0 hRes1)
    · intro hRes5
      have hE5 : (h.slotEnd j - 5#64).toNat = (h.slotEnd j).toNat - 5 := bv64_sub_toNat (by omega)
      have hE4 : (h.slotEnd j - 4#64).toNat = (h.slotEnd j).toNat - 4 := bv64_sub_toNat (by omega)
      exact ⟨(hSlotIn (h.slotEnd j - 5#64) (by omega) (by omega)).trans (hTrail hRes5).1,
        (hRegEq (h.slotEnd j - 4#64) 4 (by omega) (by omega)).trans (hTrail hRes5).2⟩

theorem groupWf_of_metaOnlyMod {st st1 : MallocngSt} {h0 : GroupDesc} {pv1 nx1 : BitVec 64}
    (hHWf : GroupWf st h0)
    (h63PvNx : h0.sc = 63 → pv1 = 0#64 ∧ nx1 = 0#64)
    (hMetaBytes : readBytesFromMap st1.byteVal h0.metaPtr 40 =
      ({ h0 with prev := pv1, next := nx1 } : GroupDesc).metaBytes)
    (hDataEq : ∀ a, InRegion h0.mem h0.totalBytes a → st1.byteVal a = st.byteVal a)
    (hEndEq : st1.byteVal (h0.slotEnd h0.lastIdx) = st.byteVal (h0.slotEnd h0.lastIdx))
    (hParentLift : h0.maplen = 0 →
      1 ≤ h0.lastIdx ∧
      ∃ pg ∈ st1.groups, ∃ pIdx : Nat, ∃ hp : pIdx < pg.slots.length,
        h0.parentMeta = some pg.metaPtr ∧ pg.sc < 48 ∧ h0.sc < pg.sc ∧ pg.sc ≤ 24 ∧
        pg.slots[pIdx]'hp = .liveNested h0.metaPtr ∧
        (pg.slotStart pIdx).toNat ≤ h0.mem.toNat ∧
        h0.mem.toNat + h0.nestedCap ≤ (pg.slotEnd pIdx).toNat ∧
        h0.nestedCap = slotStride pg.sc - 4)
    (hChildLift : ∀ j (hj : j < h0.slots.length) cm, h0.slots[j]'hj = .liveNested cm →
      ∀ cg ∈ st.groups, cg.metaPtr = cm →
      ∃ cg1 ∈ st1.groups, cg1.metaPtr = cg.metaPtr ∧ cg1.parentMeta = cg.parentMeta ∧
        cg1.mem = cg.mem ∧ cg1.nestedCap = cg.nestedCap)
    (hLiveOv : st1.liveMap.ov = st.liveMap.ov := by rfl) :
    GroupWf st1 { h0 with prev := pv1, next := nx1 } := by
  have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hFit64 : h0.mem.toNat + h0.totalBytes ≤ 2 ^ 64 := by
    have := hHWf.2.2.2.2.2.2.1; omega
  have hTotGe12 : 12 ≤ h0.totalBytes := by
    have := hHWf.2.2.2.2.2.2.2.1; omega
  refine ⟨hHWf.1, hHWf.2.1, hHWf.2.2.1,
    fun h63 => ⟨(hHWf.2.2.2.1 h63).1, (hHWf.2.2.2.1 h63).2.1, (h63PvNx h63).1, (h63PvNx h63).2⟩,
    hHWf.2.2.2.2.1, hHWf.2.2.2.2.2.1, hHWf.2.2.2.2.2.2.1, hHWf.2.2.2.2.2.2.2.1,
    hHWf.2.2.2.2.2.2.2.2.1, hEndEq.trans hHWf.2.2.2.2.2.2.2.2.2.1,
    hHWf.2.2.2.2.2.2.2.2.2.2.1, hHWf.2.2.2.2.2.2.2.2.2.2.2.1,
    hParentLift, hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hMetaBytes,
    by dsimp only []
       rw [readBytesFromMap_eq_of_inRegion (by omega) fun a ha => by
         have ⟨x1, x2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
         exact hDataEq a ((inRegion_iff_toNat hFit64 a).mpr ⟨x1, by omega⟩)]
       exact hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    (hDataEq (h0.mem + 8#64) ((inRegion_iff_toNat hFit64 _).mpr
      ⟨by rw [bv64_add_toNat (by omega)]; omega,
       by rw [bv64_add_toNat (by omega)]; omega⟩)).trans
      hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    fun j hj => ?_⟩
  have hSWf := hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj
  exact slotWf_of_groupDataEq hHWf hj hSWf hDataEq rfl rfl rfl rfl rfl rfl
    hSWf.2.1 hSWf.2.2.1 hSWf.2.2.2.1 (hChildLift j hj) (hOv := fun u _ _ _ => congrFun hLiveOv u)

private theorem powSubOne_getLsbD_fin :
    ∀ (cnt : Fin 33) (j : Fin 32),
      (BitVec.ofNat 32 (2 ^ cnt.val - 1)).getLsbD j.val = decide (j.val < cnt.val) := by
  decide +kernel

private theorem bv32_eq_pow_sub_one_of_bits (w : BitVec 32) (cnt : Nat)
    (hCntLe : cnt ≤ 32) (hLt : w.toNat < 2 ^ cnt)
    (hBits : ∀ j < cnt, w.getLsbD j = true) :
    w.toNat = 2 ^ cnt - 1 := by
  have hEq : w = BitVec.ofNat 32 (2 ^ cnt - 1) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [powSubOne_getLsbD_fin ⟨cnt, by omega⟩ ⟨j, hj⟩]
    by_cases hjCnt : j < cnt
    · simp [hjCnt, hBits j hjCnt]
    · simp only [hjCnt, decide_false]
      rw [BitVec.getLsbD, Nat.testBit_lt_two_pow]
      exact Nat.lt_of_lt_of_le hLt (Nat.pow_le_pow_right (by decide) (by omega))
  rw [hEq, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have hPowLe : 2 ^ cnt ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hCntLe
  have hPos : 1 ≤ 2 ^ cnt := Nat.one_le_pow cnt 2 (by decide)
  omega

theorem isEmpty_false_of_mask_ne {g : GroupDesc}
    (hLast : g.lastIdx ≤ 31) (hLen : g.slots.length = g.cnt)
    (hLt : (g.availMask ||| g.freedMask).toNat < 2 ^ g.cnt)
    (hSlotMasks : ∀ j : Nat, (hj : j < g.slots.length) →
      (g.availMask.getLsbD j = true ↔ g.slots[j]'hj = .freeAvail) ∧
      (g.freedMask.getLsbD j = true ↔ g.slots[j]'hj = .freeInactive))
    (hNeFull : (g.availMask ||| g.freedMask).toNat ≠ 2 ^ g.cnt - 1) :
    g.isEmpty = false := by
  apply Bool.eq_false_iff.mpr
  intro hEmp
  apply hNeFull
  have hCntLe32 : g.cnt ≤ 32 := by unfold GroupDesc.cnt; omega
  apply bv32_eq_pow_sub_one_of_bits (g.availMask ||| g.freedMask) g.cnt hCntLe32 hLt
  intro j hjCnt
  have hjL : j < g.slots.length := by omega
  have hFree := List.all_eq_true.mp hEmp (g.slots[j]'hjL) (List.getElem_mem hjL)
  rw [BitVec.getLsbD_or]
  cases hs : g.slots[j]'hjL <;> simp [hs, SlotState.isFree] at hFree
  · rw [(hSlotMasks j hjL).1.mpr hs]; rfl
  · rw [(hSlotMasks j hjL).2.mpr hs, Bool.or_true]

/-! ## Queueing onto an Empty `ctx.active[g.sc]` -/

def mkQueuedEmptyGroup (g : GroupDesc) (idx : Nat) : GroupDesc :=
  { g with
    prev      := g.metaPtr
    next      := g.metaPtr
    freedMask := g.freedMask ||| (1#32 <<< idx)
    slots     := g.slots.set idx .freeInactive }

set_option maxHeartbeats 400000 in
/-- Enqueues a group `g` whose slot `idx` is claimed onto an empty `ctx.active[g.sc]`
    (`head = 0#64`), stepping `MallocngWFInflight (k + 1)` to `MallocngWFInflight k`. -/
theorem free_queue_empty_active {k : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight (k + 1) base brkStart brk liveCost peakCost st)
    {g : GroupDesc} {idx : Nat}
    (hg : g ∈ st.groups) (hSc48 : g.sc < 48)
    (hIdx : idx < g.slots.length)
    (hClaimed : g.slots[idx]'hIdx = .claimed)
    (hNotAllFree : (g.availMask ||| (g.freedMask ||| (1#32 <<< idx))).toNat ≠ 2 ^ g.cnt - 1)
    (hHead0 : st.ctx.active[g.sc]'(by rw [hwf.ctx_lens.1]; exact hSc48) = 0#64) :
    let g1 := mkQueuedEmptyGroup g idx
    let ctx1 : CtxFields := { st.ctx with active := st.ctx.active.set g.sc g.metaPtr }
    let bv1 := writeBytesToMap st.byteVal g.metaPtr g1.metaBytes
    let st1 : MallocngSt :=
      { st with
        ctx         := ctx1
        groups      := replaceGroupByMeta st.groups g.metaPtr g1
        activeLists := st.activeLists.set g.sc [g.metaPtr]
        byteVal     := bv1 }
    g.prev = 0#64 ∧ g.next = 0#64 ∧
    MallocngWFInflight k base brkStart brk liveCost peakCost st1 ∧
    dynamicRootRegions st1 = dynamicRootRegions st ∧
    totalLiveCount st1 = totalLiveCount st ∧
    ProtNoneByteMap st1.masterDom (OwnedProtNoneByte st1) st1.byteVal =
      ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal ∧
    MappedSet st1.masterDom (OwnedMappedByte st1) =
      MappedSet st.masterDom (OwnedMappedByte st) ∧
    (((g.metaPtr ↦ₛ g1.metaBytes) ∗
        ByteMap st.masterDom (fun a => OwnedRwByte st a ∧ ¬ InRegion g.metaPtr 40 a) st.byteVal) =
      ByteMap st1.masterDom (OwnedRwByte st1) st1.byteVal) := by
  dsimp only []
  have h1 : g.sc < st.ctx.active.length := by rw [hwf.ctx_lens.1]; exact hSc48
  have h2 : g.sc < st.activeLists.length := by rw [hwf.ctx_lens.2.2.2.2.2]; exact hSc48
  have hActG := hwf.active_wf g.sc h1 h2
  have hMsNil : st.activeLists[g.sc]'h2 = [] := by
    have hDll := hActG.2.1
    have hLen := hActG.2.2.1
    cases hNs : ((st.activeLists[g.sc]'h2).filterMap fun m =>
        (findGroupByMeta st m).map fun h => (h.metaPtr, h.prev, h.next)) with
    | nil =>
      rw [hNs] at hLen; exact List.eq_nil_of_length_eq_zero hLen.symm
    | cons hd tl =>
      have hHd0 := (CircularDllWf.head_eq_zero_iff (hNs ▸ hDll)).mp hHead0
      cases hHd0
  have hNotMemG : g.metaPtr ∉ st.activeLists[g.sc]'h2 := by rw [hMsNil]; simp
  have ⟨hPvNx0, hNotMemMasks⟩ := hActG.2.2.2.1 g hg rfl
  have ⟨hPv0, hNx0⟩ := hPvNx0.mp hNotMemG
  have ⟨_, _, hActIdxEq⟩ := hNotMemMasks hNotMemG
  have hgWf := hwf.groups_wf g hg
  have hSlotWf := hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 idx hIdx
  have hAvBitF : g.availMask.getLsbD idx = false :=
    Bool.eq_false_iff.mpr fun hT => by have := hSlotWf.2.1.mp hT; rw [hClaimed] at this; cases this
  have hFrBitF : g.freedMask.getLsbD idx = false :=
    Bool.eq_false_iff.mpr fun hT => by have := hSlotWf.2.2.1.mp hT; rw [hClaimed] at this; cases this
  have hIdxCnt : idx < g.cnt := by rw [← hgWf.2.2.1]; exact hIdx
  have hIdxLeLast : idx ≤ g.lastIdx := by unfold GroupDesc.cnt at hIdxCnt; omega
  have hMaskProps := freeSlot_mask_props hIdxLeLast hgWf.2.1 hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hAvBitF hFrBitF
  let g1 := mkQueuedEmptyGroup g idx
  let ctx1 : CtxFields := { st.ctx with active := st.ctx.active.set g.sc g.metaPtr }
  let bv1 := writeBytesToMap st.byteVal g.metaPtr g1.metaBytes
  let st1 : MallocngSt :=
    { st with
      ctx         := ctx1
      groups      := replaceGroupByMeta st.groups g.metaPtr g1
      activeLists := st.activeLists.set g.sc [g.metaPtr]
      byteVal     := bv1 }
  have hSpatial := metaBytes_update_spatial hwf (g1 := g1) hg hIdx hClaimed
    (s1 := .freeInactive) (fun _ _ _ h => by cases h) rfl rfl rfl rfl rfl rfl
  have hAllG : g.metaPtr ∈ allMetaSlots st :=
    (hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg))))
  have ⟨hmGe, _, hmFit, _, hDisjG⟩ := allMetaSlots_info hwf hAllG
  have hmNe0 : g.metaPtr ≠ 0#64 := fun h0 => by rw [h0] at hmGe; simp at hmGe
  have hOnlyG : ∀ a, bv1 a ≠ st.byteVal a → ∃ u ∈ st.groups, InRegion u.metaPtr 40 a := fun a hNe =>
    ⟨g, hg, Classical.byContradiction fun hOut => hNe (writeBytesToMap_out st.byteVal g.metaPtr g1.metaBytes
      (by simpa [GroupDesc.metaBytes_length] using hOut))⟩
  have hDisj := groupMetaMod_disjoint hwf hOnlyG
  have hRep := replaceGroupByMeta_props hwf.groups_nodup.1 hg (g1 := g1) rfl rfl rfl rfl rfl
  have hDynEq : dynamicRootRegions st1 = dynamicRootRegions st := by
    unfold dynamicRootRegions; dsimp only [st1]; rw [hRep.2.2.1]
  have hCntEq : totalLiveCount st1 = totalLiveCount st := by
    have hSum := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg
      (fun h => (h.slots.map slotLiveCount).sum) (g1 := g1)
    have hSlot := list_set_map_sum g.slots hIdx .freeInactive slotLiveCount
    rw [hClaimed] at hSlot
    unfold totalLiveCount
    simp only [st1, g1, mkQueuedEmptyGroup, slotLiveCount] at hSum hSlot ⊢
    omega
  have hEffEq : totalLiveEffCost st1 = totalLiveEffCost st := by
    have hSum := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg
      (fun h => (h.slots.map slotEffCost).sum) (g1 := g1)
    have hSlot := list_set_map_sum g.slots hIdx .freeInactive slotEffCost
    rw [hClaimed] at hSlot
    unfold totalLiveEffCost
    simp only [st1, g1, mkQueuedEmptyGroup, slotEffCost] at hSum hSlot ⊢
    omega
  have hClaimSum : totalClaimedSlots st = totalClaimedSlots st1 + 1 := by
    have hSum := replaceGroupByMeta_map_sum hwf.groups_nodup.1 hg
      (fun h => (h.slots.filter SlotState.isClaimed).length) (g1 := g1)
    have hGSet := list_set_filter_len g.slots hIdx .freeInactive SlotState.isClaimed
    rw [hClaimed] at hGSet
    unfold totalClaimedSlots
    simp only [st1, g1, mkQueuedEmptyGroup, SlotState.isClaimed, Bool.false_eq_true, ↓reduceIte] at hSum hGSet ⊢
    omega
  have hInit1 : st.ctx.initDone = 1#32 := by
    rcases hwf.initDone_wf with h0 | h1'
    · have := (hwf.initZero_wf h0).2.2.2.2.2.2.2.2.2.1; rw [this] at hg; cases hg
    · exact h1'
  have hG1SlotMasks : ∀ j : Nat, (hj1 : j < g1.slots.length) →
      (g1.availMask.getLsbD j = true ↔ g1.slots[j]'hj1 = .freeAvail) ∧
      (g1.freedMask.getLsbD j = true ↔ g1.slots[j]'hj1 = .freeInactive) := fun j hj1 => by
    have hj : j < g.slots.length := by simpa [g1, mkQueuedEmptyGroup] using hj1
    by_cases hjEq : j = idx
    · subst hjEq
      simp only [g1, mkQueuedEmptyGroup, List.getElem_set_self, reduceCtorEq, iff_false, iff_true,
        Bool.not_eq_true]
      exact ⟨hAvBitF, by simpa using hMaskProps.2.2.2.2.2.1 j⟩
    · simp only [g1, mkQueuedEmptyGroup, List.getElem_set, Ne.symm hjEq, ↓reduceIte]
      have hSWf := hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj
      exact ⟨hSWf.2.1, by simp only [hMaskProps.2.2.2.2.2.1 j, hjEq, ↓reduceIte]; exact hSWf.2.2.1⟩
  have hG1NotEmp : g1.isEmpty = false :=
    isEmpty_false_of_mask_ne hgWf.2.1 (by simp [g1, mkQueuedEmptyGroup, hgWf.2.2.1])
      hMaskProps.2.2.2.2.1 hG1SlotMasks hNotAllFree
  have hChildLift : ∀ cm : BitVec 64, ∀ cg ∈ st.groups, cg.metaPtr = cm →
      ∃ cg1 ∈ st1.groups, cg1.metaPtr = cg.metaPtr ∧ cg1.parentMeta = cg.parentMeta ∧
        cg1.mem = cg.mem ∧ cg1.nestedCap = cg.nestedCap := fun _ cg hcg _ => by
    by_cases hEqC : cg.metaPtr = g.metaPtr
    · have hEq := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg hg hEqC; subst cg
      exact ⟨g1, hRep.2.2.2.2.1, rfl, rfl, rfl, rfl⟩
    · exact ⟨cg, hRep.2.2.2.2.2.2.1 cg hcg hEqC, rfl, rfl, rfl, rfl⟩
  have hParentLift : ∀ h0 ∈ st.groups, h0.maplen = 0 →
      1 ≤ h0.lastIdx ∧
      ∃ pg ∈ st1.groups, ∃ pIdx : Nat, ∃ hp : pIdx < pg.slots.length,
        h0.parentMeta = some pg.metaPtr ∧ pg.sc < 48 ∧ h0.sc < pg.sc ∧ pg.sc ≤ 24 ∧
        pg.slots[pIdx]'hp = .liveNested h0.metaPtr ∧
        (pg.slotStart pIdx).toNat ≤ h0.mem.toNat ∧
        h0.mem.toNat + h0.nestedCap ≤ (pg.slotEnd pIdx).toNat ∧
        h0.nestedCap = slotStride pg.sc - 4 := fun h0 hh0 hM0 => by
    obtain ⟨hLast1, pg, hpg, pIdx, hp, hPM, hP48, hScLt, hP24, hPSlot, hSLe, hELe, hNCap⟩ :=
      (hwf.groups_wf h0 hh0).2.2.2.2.2.2.2.2.2.2.2.2.1 hM0
    refine ⟨hLast1, ?_⟩
    by_cases hEqPg : pg.metaPtr = g.metaPtr
    · have hEq := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg hg hEqPg; subst pg
      have hpNe : pIdx ≠ idx := fun hEqI => by subst hEqI; rw [hClaimed] at hPSlot; cases hPSlot
      refine ⟨g1, hRep.2.2.2.2.1, pIdx, by simpa [g1, mkQueuedEmptyGroup] using hp,
        hPM, hP48, hScLt, hP24, ?_, hSLe, hELe, hNCap⟩
      simp [g1, mkQueuedEmptyGroup, Ne.symm hpNe, hPSlot]
    · exact ⟨pg, hRep.2.2.2.2.2.2.1 pg hpg hEqPg, pIdx, hp, hPM, hP48, hScLt, hP24,
        hPSlot, hSLe, hELe, hNCap⟩
  have hWf1 : MallocngWFInflight k base brkStart brk liveCost peakCost st1 :=
    { base_wf := trivial
      brk_bounds := hwf.brk_bounds
      ctx_lens := ⟨by simp [st1, ctx1, hwf.ctx_lens.1], hwf.ctx_lens.2.1, hwf.ctx_lens.2.2.1,
        hwf.ctx_lens.2.2.2.1, hwf.ctx_lens.2.2.2.2.1, by simp [st1, hwf.ctx_lens.2.2.2.2.2]⟩
      initDone_wf := hwf.initDone_wf
      initZero_wf := fun h0 => by rw [hInit1] at h0; cases h0
      bounces_wf := hwf.bounces_wf
      usage_wf := fun sc hsc => by
        dsimp only [st1, ctx1] at hsc ⊢
        rw [hRep.2.2.2.1 sc]
        exact hwf.usage_wf sc hsc
      brk_mode_wf := hwf.brk_mode_wf
      metaAreas_wf := ⟨hwf.metaAreas_wf.1,
        fun ma hma => by
          have hM := hwf.metaAreas_wf.2.1 ma hma
          exact ⟨hM.1, hM.2.1, hM.2.2.1,
            (readBytesFromMap_eq_of_inRegion (by have := hM.2.2.1; omega)
              (hDisj.1 ma hma)).trans hM.2.2.2⟩,
        hwf.metaAreas_wf.2.2⟩
      guard_avail_wf := ⟨hwf.guard_avail_wf.1, hwf.guard_avail_wf.2.1, hwf.guard_avail_wf.2.2.1,
        fun ap hap => by
          have hA := hwf.guard_avail_wf.2.2.2 ap hap
          exact ⟨hA.1, hA.2.1, hA.2.2.1,
            (readBytesFromMap_eq_of_inRegion (by have := hA.2.2.1; omega)
              (hDisj.2.1 ap hap)).trans hA.2.2.2⟩⟩
      inflight_wf := by
        have := hwf.inflight_wf; dsimp only [st1] at hClaimSum ⊢; omega
      free_bump_metas_wf := by
        obtain ⟨hFmDll, hFmBytes, hBmMode, hBmBytes, hUfNd, hUfIff⟩ := hwf.free_bump_metas_wf
        refine ⟨hFmDll, fun fm hfm => ?_, hBmMode, fun bm hbm => ?_,
          by simpa only [st1, hRep.1] using hUfNd,
          fun m => by simpa only [st1, hRep.1, allMetaSlots] using hUfIff m⟩
        · have hAllFm := (hUfIff fm.ptr).mp
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hfm))))
          have ⟨_, _, hFit, _⟩ := allMetaSlots_info hwf hAllFm
          exact (readBytesFromMap_eq_of_inRegion (by omega) (hDisj.2.2.2.1 fm hfm)).trans (hFmBytes fm hfm)
        · have hAllBm := (hUfIff bm).mp (List.mem_append_left _ (List.mem_append_right _ hbm))
          have ⟨_, _, hFit, _⟩ := allMetaSlots_info hwf hAllBm
          exact (readBytesFromMap_eq_of_inRegion (by omega) (hDisj.2.2.2.2.1 bm hbm)).trans (hBmBytes bm hbm)
      groups_nodup := ⟨hRep.1 ▸ hwf.groups_nodup.1, hRep.2.1 ▸ hwf.groups_nodup.2⟩
      groups_wf := fun h' hh' => by
        rcases hRep.2.2.2.2.2.1 h' hh' with hEq | ⟨hh0, hNeM⟩
        · subst h'
          have hHdrDisj := hDisj.2.2.2.2.2 g hg
          have hFit64 : g.mem.toNat + g.totalBytes ≤ 2 ^ 64 := by
            have := hgWf.2.2.2.2.2.2.1; omega
          have hTotGe12 : 12 ≤ g.totalBytes := by
            have := hgWf.2.2.2.2.2.2.2.1; omega
          refine ⟨hgWf.1, hgWf.2.1, by simp [g1, mkQueuedEmptyGroup, hgWf.2.2.1],
            fun h63 => by dsimp only [g1, mkQueuedEmptyGroup] at h63; omega,
            hgWf.2.2.2.2.1, hgWf.2.2.2.2.2.1, hgWf.2.2.2.2.2.2.1, hgWf.2.2.2.2.2.2.2.1,
            hgWf.2.2.2.2.2.2.2.2.1, hHdrDisj.2.trans hgWf.2.2.2.2.2.2.2.2.2.1,
            hgWf.2.2.2.2.2.2.2.2.2.2.1, hgWf.2.2.2.2.2.2.2.2.2.2.2.1,
            hParentLift g hg, hMaskProps.2.2.2.1, hMaskProps.2.2.2.2.1,
            hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            readBytesFromMap_writeBytesToMap st.byteVal g.metaPtr g1.metaBytes
              (by rw [GroupDesc.metaBytes_length]; omega),
            by dsimp only [st1, g1, mkQueuedEmptyGroup]
               rw [readBytesFromMap_eq_of_inRegion (by omega) fun a ha => by
                 have ⟨x1, x2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
                 exact hHdrDisj.1 a ((inRegion_iff_toNat hFit64 a).mpr ⟨x1, by omega⟩)]
               exact hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            (hHdrDisj.1 (g.mem + 8#64) ((inRegion_iff_toNat hFit64 _).mpr
              ⟨by rw [bv64_add_toNat (by omega)]; omega,
               by rw [bv64_add_toNat (by omega)]; omega⟩)).trans
              hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            fun j hj1 => ?_⟩
          have hj : j < g.slots.length := by simpa [g1, mkQueuedEmptyGroup] using hj1
          by_cases hjEq : j = idx
          · subst hjEq
            have ⟨hStrGe, _, hStorNat, _, hEndTot, hSlotCalc⟩ := group_slot_toNat hgWf
            have ⟨hStartNat, hEndNat, hSub4Nat⟩ := hSlotCalc j hIdxCnt
            have hMulLe : (j + 1) * g.stride ≤ g.cnt * g.stride := Nat.mul_le_mul_right _ hIdxCnt
            have hSuccMul : (j + 1) * g.stride = j * g.stride + g.stride := Nat.succ_mul j g.stride
            have hSetSelf : g1.slots[j]'hj1 = .freeInactive := by simp [g1, mkQueuedEmptyGroup]
            have hAv1 := hSetSelf ▸ (hG1SlotMasks j hj1).1
            have hFr1 := hSetSelf ▸ (hG1SlotMasks j hj1).2
            rw [hSetSelf]
            refine ⟨?_, hAv1, hFr1, fun _ => rfl, trivial⟩
            change bv1 (g.slotStart j - 4#64) = 0#8
            exact (hHdrDisj.1 _ ((inRegion_iff_toNat hFit64 _).mpr ⟨by omega, by omega⟩)).trans hSlotWf.1
          · have hGet : g1.slots[j]'hj1 = g.slots[j]'hj := by
              simp [g1, mkQueuedEmptyGroup, Ne.symm hjEq]
            rw [hGet]
            have hSWf := hgWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj
            exact slotWf_of_groupDataEq hgWf hj hSWf hHdrDisj.1 rfl rfl rfl rfl rfl rfl
              (hGet ▸ (hG1SlotMasks j hj1).1) (hGet ▸ (hG1SlotMasks j hj1).2) hSWf.2.2.2.1
              (fun cm _ => hChildLift cm)
        · have hHWf := hwf.groups_wf h' hh0
          have hAllH := (hwf.free_bump_metas_wf.2.2.2.2.2 h'.metaPtr).mp
            (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hh0))))
          have ⟨_, _, hFitH, _⟩ := allMetaSlots_info hwf hAllH
          have h2_48_lt : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
          have hMetaEq : readBytesFromMap bv1 h'.metaPtr 40 = h'.metaBytes := by
            rw [readBytesFromMap_eq_of_inRegion (by omega) fun a ha =>
              writeBytesToMap_out st.byteVal g.metaPtr g1.metaBytes
                (fun haG => DisjointRegions.not_both (hDisjG h'.metaPtr hAllH hNeM)
                  (by simpa [GroupDesc.metaBytes_length] using haG) ha)]
            exact hHWf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          exact groupWf_of_metaOnlyMod hHWf
            (fun h63 => ⟨(hHWf.2.2.2.1 h63).2.2.1, (hHWf.2.2.2.1 h63).2.2.2⟩)
            hMetaEq (hDisj.2.2.2.2.2 h' hh0).1 (hDisj.2.2.2.2.2 h' hh0).2
            (hParentLift h' hh0) (fun _ _ cm _ => hChildLift cm)
      regions_disjoint := ⟨hDynEq ▸ hwf.regions_disjoint.1, trivial⟩
      active_wf := fun sc h1' h2' => by
        have h1_0 : sc < st.ctx.active.length := by simpa [st1, ctx1] using h1'
        have h2_0 : sc < st.activeLists.length := by simpa [st1] using h2'
        by_cases hScEq : sc = g.sc
        · subst hScEq
          have hHd1 : st1.ctx.active[g.sc]'h1' = g.metaPtr := by simp [st1, ctx1]
          have hMs1 : st1.activeLists[g.sc]'h2' = [g.metaPtr] := by simp [st1]
          have hFindG1 : findGroupByMeta st1 g.metaPtr = some g1 :=
            findGroupByMeta_eq_of_mem (hRep.1 ▸ hwf.groups_nodup.1) hRep.2.2.2.2.1
          rw [ActiveClassWf, hHd1, hMs1]
          simp only [List.filterMap_cons, List.filterMap_nil, hFindG1, Option.map_some]
          refine ⟨fun m hm => ?_, CircularDllWf.singleton hmNe0, rfl,
            fun h' hh' hSc' => ?_, fun i hi hPos => by simp at hi; omega,
            fun h₁ hh₁ h₂ hh₂ hSc₁ _ hLt₁ _ => ?_,
            fun h' hh' hSc' hLt => ?_⟩
          · have hmEq : m = g.metaPtr := by simpa using hm
            subst hmEq; exact ⟨g1, hRep.2.2.2.2.1, rfl, rfl⟩
          · rcases hRep.2.2.2.2.2.1 h' hh' with hEq | ⟨hh0, hNeM⟩
            · subst h'
              simp only [List.mem_singleton, not_true_eq_false, false_iff, g1, mkQueuedEmptyGroup]
              exact ⟨fun ⟨h0, _⟩ => hmNe0 h0, fun hF => False.elim hF⟩
            · have hNot0 : h'.metaPtr ∉ st.activeLists[g.sc]'h2 := by rw [hMsNil]; simp
              have hSub := hActG.2.2.2.1 h' hh0 hSc'
              simp only [List.mem_singleton, hNeM, not_false_eq_true, true_iff, forall_const]
              exact ⟨hSub.1.mp hNot0, hSub.2 hNot0⟩
          · exfalso
            rcases hRep.2.2.2.2.2.1 h₁ hh₁ with hEq | ⟨hh0, _⟩
            · subst h₁
              have : g.activeIdx < g.lastIdx := hLt₁
              omega
            · have ⟨hMem0, _⟩ := hActG.2.2.2.2.2.2 h₁ hh0 hSc₁ hLt₁
              rw [hMsNil] at hMem0; cases hMem0
          · exfalso
            rcases hRep.2.2.2.2.2.1 h' hh' with hEq | ⟨hh0, _⟩
            · subst h'
              have : g.activeIdx < g.lastIdx := hLt
              omega
            · have ⟨hMem0, _⟩ := hActG.2.2.2.2.2.2 h' hh0 hSc' hLt
              rw [hMsNil] at hMem0; cases hMem0
        · have hAct0 := hwf.active_wf sc h1_0 h2_0
          have hHd1 : st1.ctx.active[sc]'h1' = st.ctx.active[sc]'h1_0 := by
            simp [st1, ctx1, Ne.symm hScEq]
          have hMs1 : st1.activeLists[sc]'h2' = st.activeLists[sc]'h2_0 := by
            simp [st1, Ne.symm hScEq]
          have hFMapEq :
              ((st.activeLists[sc]'h2_0).filterMap fun m =>
                (findGroupByMeta st1 m).map fun h => (h.metaPtr, h.prev, h.next)) =
              ((st.activeLists[sc]'h2_0).filterMap fun m =>
                (findGroupByMeta st m).map fun h => (h.metaPtr, h.prev, h.next)) := by
            have hStep : ∀ l : List (BitVec 64), (∀ m ∈ l, m ∈ st.activeLists[sc]'h2_0) →
                (l.filterMap fun m => (findGroupByMeta st1 m).map fun h => (h.metaPtr, h.prev, h.next)) =
                (l.filterMap fun m => (findGroupByMeta st m).map fun h => (h.metaPtr, h.prev, h.next)) := by
              intro l hl; induction l with
              | nil => rfl
              | cons m rest ih =>
                obtain ⟨h0, hh0, hM0, hSc0⟩ := hAct0.1 m (hl m List.mem_cons_self)
                have hNeG : h0.metaPtr ≠ g.metaPtr := fun hEq =>
                  hScEq (hSc0.symm.trans (congrArg GroupDesc.sc
                    (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hEq)))
                have hF0 : findGroupByMeta st h0.metaPtr = some h0 :=
                  findGroupByMeta_eq_of_mem hwf.groups_nodup.1 hh0
                have hF1 : findGroupByMeta st1 h0.metaPtr = some h0 :=
                  findGroupByMeta_eq_of_mem (hRep.1 ▸ hwf.groups_nodup.1)
                    (hRep.2.2.2.2.2.2.1 h0 hh0 hNeG)
                rw [← hM0]
                simp [hF0, hF1, ih fun x hx => hl x (List.mem_cons_of_mem _ hx)]
            exact hStep _ fun _ hm => hm
          rw [ActiveClassWf, hHd1, hMs1]
          refine ⟨fun m hm => ?_, hFMapEq ▸ hAct0.2.1, hFMapEq ▸ hAct0.2.2.1,
            fun h' hh' hSc' => ?_, fun i hi hPos h' hh' hEqM => ?_,
            fun h₁ hh₁ h₂ hh₂ hSc₁ hSc₂ hLt₁ hLt₂ => ?_,
            fun h' hh' hSc' hLt => ?_⟩
          · obtain ⟨h0, hh0, hM0, hSc0⟩ := hAct0.1 m hm
            have hNeM : h0.metaPtr ≠ g.metaPtr := fun hEq =>
              hScEq (hSc0.symm.trans (congrArg GroupDesc.sc
                (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hEq)))
            exact ⟨h0, hRep.2.2.2.2.2.2.1 h0 hh0 hNeM, hM0, hSc0⟩
          · rcases hRep.2.2.2.2.2.1 h' hh' with hEq | ⟨hh0, _⟩
            · subst h'; exact False.elim (hScEq hSc'.symm)
            · exact hAct0.2.2.2.1 h' hh0 hSc'
          · rcases hRep.2.2.2.2.2.1 h' hh' with hEq | ⟨hh0, _⟩
            · subst h'
              obtain ⟨h0, hh0, hM0, hSc0⟩ := hAct0.1 _ (List.getElem_mem hi)
              have hEqG := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg (hM0.trans hEqM.symm)
              subst h0; exact False.elim (hScEq hSc0.symm)
            · exact hAct0.2.2.2.2.1 i hi hPos h' hh0 hEqM
          · rcases hRep.2.2.2.2.2.1 h₁ hh₁ with hEq | ⟨hh₁0, _⟩
            · subst h₁; exact False.elim (hScEq hSc₁.symm)
            · rcases hRep.2.2.2.2.2.1 h₂ hh₂ with hEq2 | ⟨hh₂0, _⟩
              · subst h₂; exact False.elim (hScEq hSc₂.symm)
              · exact hAct0.2.2.2.2.2.1 h₁ hh₁0 h₂ hh₂0 hSc₁ hSc₂ hLt₁ hLt₂
          · rcases hRep.2.2.2.2.2.1 h' hh' with hEq | ⟨hh0, _⟩
            · subst h'; exact False.elim (hScEq hSc'.symm)
            · exact hAct0.2.2.2.2.2.2 h' hh0 hSc' hLt
      liveMap_wf := fun p req => by
        rw [show st1.liveMap = st.liveMap from rfl, hwf.liveMap_wf]
        constructor
        · rintro ⟨h0, hh0, j, hj0, ec, hS0⟩
          by_cases hEqM : h0.metaPtr = g.metaPtr
          · have hEqG := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hh0 hg hEqM; subst h0
            have hjNe : j ≠ idx := fun hEqJ => by subst hEqJ; rw [hClaimed] at hS0; cases hS0
            refine ⟨g1, hRep.2.2.2.2.1, j, by simpa [g1, mkQueuedEmptyGroup] using hj0, ec, ?_⟩
            simp [g1, mkQueuedEmptyGroup, Ne.symm hjNe, hS0]
          · exact ⟨h0, hRep.2.2.2.2.2.2.1 h0 hh0 hEqM, j, hj0, ec, hS0⟩
        · rintro ⟨h', hh', j, hj', ec, hS'⟩
          rcases hRep.2.2.2.2.2.1 h' hh' with hEq | ⟨hh0, _⟩
          · subst h'
            have hj0 : j < g.slots.length := by simpa [g1, mkQueuedEmptyGroup] using hj'
            have hjNe : j ≠ idx := fun hEqJ => by subst hEqJ; simp [g1, mkQueuedEmptyGroup] at hS'
            simp only [g1, mkQueuedEmptyGroup, List.getElem_set, Ne.symm hjNe, ↓reduceIte] at hS'
            exact ⟨g, hg, j, hj0, ec, hS'⟩
          · exact ⟨h', hh0, j, hj', ec, hS'⟩
      live_le_peak := hwf.live_le_peak
      effCost_le_live := hEffEq ▸ hwf.effCost_le_live
      meta_pages_bound := hwf.meta_pages_bound
      empty_groups_bound := fun h' hh' hEmp => by
        rcases hRep.2.2.2.2.2.1 h' hh' with hEq | ⟨hh0, _⟩
        · subst h'; rw [hG1NotEmp] at hEmp; cases hEmp
        · have ⟨hPos, h7, h38, hCap, hActMem, hUniq, hSlk⟩ := hwf.empty_groups_bound h' hh0 hEmp
          have hScNe : h'.sc ≠ g.sc := fun hScEq => by
            have hIn : h'.metaPtr ∈ st.activeLists[g.sc]'h2 := by
              simpa [hScEq] using hActMem (hScEq ▸ h2)
            rw [hMsNil] at hIn; cases hIn
          refine ⟨hPos, h7, h38, hCap, fun hL => ?_, fun g' hg' hEmp' hSc' => ?_, hSlk⟩
          · have hL0 : h'.sc < st.activeLists.length := by simpa [st1] using hL
            have hSetEq : st1.activeLists[h'.sc]'hL = st.activeLists[h'.sc]'hL0 := by
              simp [st1, Ne.symm hScNe]
            exact hSetEq ▸ hActMem hL0
          · rcases hRep.2.2.2.2.2.1 g' hg' with hEq' | ⟨hg0, _⟩
            · subst g'; rw [hG1NotEmp] at hEmp'; cases hEmp'
            · exact hUniq g' hg0 hEmp' hSc'
      masterDom_wf := ⟨hwf.masterDom_wf.1,
        fun a hOwn => hwf.masterDom_wf.2.1 a (by
          rcases hOwn with hRw | hPn | hMp
          · exact Or.inl ((hSpatial.2.1 a).mp hRw)
          · exact Or.inr (Or.inl hPn)
          · exact Or.inr (Or.inr (by
              unfold OwnedMappedByte at hMp ⊢
              rcases hMp with h1m | h2m | h3m | ⟨h0', hh0', hMp', hIn'⟩
              · exact Or.inl h1m
              · exact Or.inr (Or.inl h2m)
              · exact Or.inr (Or.inr (Or.inl h3m))
              · right; right; right
                rcases hRep.2.2.2.2.2.1 h0' hh0' with hEq | ⟨hh0, _⟩
                · subst h0'; exact ⟨g, hg, hMp', hIn'⟩
                · exact ⟨h0', hh0, hMp', hIn'⟩))),
        by rw [hDynEq]; exact hwf.masterDom_wf.2.2⟩ }
  exact ⟨hPv0, hNx0, hWf1, hDynEq, hCntEq, hSpatial.2.2.1, hSpatial.2.2.2.1, hSpatial.2.2.2.2⟩

end

end LibsignalBinary.Heap.Fine.VendorFree
