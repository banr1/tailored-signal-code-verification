/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocMetaStage1
public import VerifiedLibraries.Mallocng.Proofs.PlacedAllocGroupHelpers1

/-!
# Root-`mmap` Group Creation and Placed OOM Helpers

Heap invariant preservation for root-`mmap` group creation (`wf_alloc_root_mmap`), `slotStride`
and parent-slot bounds, `PureStatePres`, and `MallocngPlacedOomCond` combinators for placed
`alloc_group` and `alloc_slot`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

/-! ## Root-`mmap` Group Creation -/

set_option maxHeartbeats 400000 in
theorem wf_alloc_root_mmap {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {sc : Nat} (hsc48 : sc < 48) (hscA : sc < st.ctx.active.length)
    (hscL : sc < st.activeLists.length) (hscU : sc < st.ctx.usageByClass.length)
    (hActZero : st.ctx.active[sc]'hscA = 0#64)
    {m : BitVec 64} {resTail : List (BitVec 64)} (hRes : st.reservedMetas = m :: resTail)
    {mb : BitVec 64} {maplen lastIdx : Nat} {actB : BitVec 8}
    (hMapPos : 0 < maplen) (hMbLo : 4096 ≤ mb.toNat) (hMbAl : mb.toNat % 4096 = 0)
    (hMbHi : mb.toNat + maplen * 4096 ≤ 2 ^ 48)
    (hSc25 : sc ≤ 25 → maplen * 4096 ≤ 65536) (hSc48M : maplen * 4096 ≤ 1048576)
    (hLast0 : lastIdx = 0 →
      maplen * 4096 - 16 ≤ slotStride sc ∨
        (24 ≤ sc ∧ maplen * 4096 = pageAlignUp (slotStride sc + 16)))
    (hLast31 : lastIdx ≤ 31) (hActLe : (actB &&& 0x1f#8).toNat ≤ lastIdx)
    (hActPos : (actB &&& 0x1f#8).toNat < lastIdx → 0 < sc)
    (hCapLt : 12 + (lastIdx + 1) *
      (if lastIdx == 0 && 0 < maplen then maplen * 4096 - 16 else slotStride sc) < maplen * 4096)
    (hDisjRoot : ∀ r ∈ dynamicRootRegions st, DisjointRegions mb (maplen * 4096) r.1 r.2)
    {mmapCtr' : BitVec 32} {unmapSeq' bounces' : List (BitVec 8)} {seq' : BitVec 8}
    (hUnmL : unmapSeq'.length = 32) (hBncL : bounces'.length = 32)
    (hBnc : ∀ b ∈ bounces', b.toNat ≤ 150) :
    let activeIdx := (actB &&& 0x1f#8).toNat
    let initAvail : BitVec 32 := (2#32 <<< BitVec.ofNat 32 activeIdx) - 1#32
    let cg : GroupDesc := {
      metaPtr := m, prev := m, next := m, mem := mb,
      availMask := initAvail - 1#32,
      freedMask := (2#32 <<< BitVec.ofNat 32 lastIdx) + ~~~initAvail,
      lastIdx := lastIdx, sc := sc, maplen := maplen, activeByte := actB,
      parentMeta := none, nestedCap := 0, slots := newGroupSlots lastIdx activeIdx, freshZero := true }
    let grpBs : List (BitVec 8) := unpack64 m ++ [actB] ++ List.replicate (maplen * 4096 - 9) 0#8
    let val₁ := writeBytesToMap st.byteVal mb grpBs
    let val' := writeBytesToMap val₁ m cg.metaBytes
    let ctx' : CtxFields := { st.ctx with
      mmapCounter := mmapCtr', active := st.ctx.active.set sc m,
      usageByClass := st.ctx.usageByClass.set sc (st.ctx.usageByClass[sc]'hscU + BitVec.ofNat 64 cg.cnt),
      unmapSeq := unmapSeq', bounces := bounces', seq := seq' }
    let st' : MallocngSt := { st with
      ctx := ctx', reservedMetas := resTail, groups := cg :: st.groups,
      activeLists := st.activeLists.set sc [m],
      masterDom := extendDom (extendDom st.masterDom m 40) mb (maplen * 4096), byteVal := val' }
    MallocngWFInflight inflight base brkStart brk liveCost peakCost st' ∧
    totalLiveEffCost st' = totalLiveEffCost st ∧
    totalLiveCount st' = totalLiveCount st ∧
    ((m ↦ₛ cg.metaBytes) ∗ (mb ↦ₛ grpBs) ∗ ByteMap st.masterDom (OwnedRwByte st) st.byteVal) =
      ByteMap st'.masterDom (OwnedRwByte st') st'.byteVal ∧
    ProtNoneByteMap st.masterDom (OwnedProtNoneByte st) st.byteVal =
      ProtNoneByteMap st'.masterDom (OwnedProtNoneByte st') st'.byteVal ∧
    (memMapped mb (maplen * 4096) ∗ MappedSet st.masterDom (OwnedMappedByte st)) =
      MappedSet st'.masterDom (OwnedMappedByte st') ∧
    (∀ a : BitVec 64, InRegion (cg.slotStart 0) cg.stride a → st'.byteVal a = 0#8) := by
  intro activeIdx initAvail cg grpBs val₁ val' ctx' st'
  have hmMem : m ∈ st.reservedMetas := hRes ▸ List.Mem.head _
  obtain ⟨hmLo, _, hmHi, hmNotGrp, ⟨maM, hmaM, hInMaM⟩, hmNoCu, hmNoRw, hmDisjRes, hmDisjGrp⟩ :=
    reservedMeta_info hwf hmMem
  have hmNe0 : m ≠ 0#64 := fun h => by rw [h] at hmLo; simp at hmLo
  have hMap4096 : 4096 ≤ maplen * 4096 := by omega
  have hGrpBsLen : grpBs.length = maplen * 4096 := by
    simp only [grpBs, List.length_append, unpack64_length, List.length_singleton, List.length_replicate]; omega
  have hDisjMbMa : ∀ ma ∈ st.metaAreas, DisjointRegions mb (maplen * 4096) ma.base 4096 := fun ma hma =>
    hDisjRoot (ma.base, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma))))
  have hDisjMbM : DisjointRegions mb (maplen * 4096) m 40 := by
    obtain ⟨_, _, hMaHi, _⟩ := hwf.metaAreas_wf.2.1 maM hmaM
    have hDisjB := disjointRegions_bounds (by omega) (by omega) (by omega) (by omega) (hDisjMbMa maM hmaM)
    have hM0 := (inRegion_bounds (by omega)).mp (hInMaM m ((inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩))
    have hM39 := (inRegion_bounds (by omega)).mp (hInMaM (m + 39#64) ((inRegion_bounds (by omega)).mpr
      (by have := add_ofNat_toNat (x := m) (k := 39) (by omega); omega)))
    have := add_ofNat_toNat (x := m) (k := 39) (by omega)
    exact disjointRegions_of_bounds (by omega) (by omega) (by omega) (by omega) (by omega)
  have hOutBoth : ∀ r ∈ dynamicRootRegions st, ∀ a : BitVec 64, InRegion r.1 r.2 a → ¬ InRegion m 40 a →
      val' a = st.byteVal a := fun r hr a ha haM => by
    dsimp only [val', val₁]
    rw [writeBytesToMap_out _ _ _ (by simpa using haM),
        writeBytesToMap_out _ _ _ (by rw [hGrpBsLen]; exact fun hMb => DisjointRegions.not_both (hDisjRoot r hr) hMb ha)]
  obtain ⟨_, _, _, _, hUsedNd, hUsedAll⟩ := hwf.free_bump_metas_wf
  have hmAll : m ∈ allMetaSlots st := (hUsedAll m).mp (List.mem_append_right _ hmMem)
  obtain ⟨_, _, _, _, hDisjAllSlots⟩ := allMetaSlots_info hwf hmAll
  have hEmptyAct : st.activeLists[sc]'hscL = [] := by
    have hAct := hwf.active_wf sc hscA hscL
    have hNil := (CircularDllWf.head_eq_zero_iff hAct.2.1).mp hActZero
    exact List.eq_nil_of_length_eq_zero (hAct.2.2.1.symm.trans (by simp [hNil]))
  obtain ⟨hSlLen, hSlNotEmp, hSlCl, _, hSlIdx⟩ := newGroupSlots_info hActLe
  obtain ⟨hBmDisj, hBmOr, hBmBits⟩ := newGroupBitmaps_spec hLast31 hActLe
  obtain ⟨hDom1Nd, hDom1Mem, hBmRwExt1, hBmPnExt1, hMpExt1⟩ :=
    extendDom_spec hwf.masterDom_wf.1 hwf.masterDom_wf.2.1 m (n := 40) (by omega)
  obtain ⟨hDomNd, hDomMem, hBmRwExt2, hBmPnExt2, hMpExt2⟩ :=
    extendDom_spec hDom1Nd (fun a h => (hDom1Mem a).mpr (Or.inl (hwf.masterDom_wf.2.1 a h)))
      mb (n := maplen * 4096) (by omega)
  have hValCgMem : ∀ (i : Nat) (hi : i < maplen * 4096),
      val' (mb + BitVec.ofNat 64 i) = grpBs[i]'(hGrpBsLen ▸ hi) := fun i hi => by
    have hInMb : InRegion mb (maplen * 4096) (mb + BitVec.ofNat 64 i) :=
      (mem_rangeAddrs_iff_inRegion mb (by omega) _).mp (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    dsimp only [val', val₁]
    rw [writeBytesToMap_out _ _ _ (by simpa using fun hM => DisjointRegions.not_both hDisjMbM hInMb hM),
        writeBytesToMap_in st.byteVal mb grpBs (hGrpBsLen ▸ hi) (by omega)]
  have hCgWf : GroupWf st' cg := by
    have hStrideEq : cg.stride = if lastIdx == 0 && 0 < maplen then maplen * 4096 - 16 else slotStride sc := rfl
    have hStrideGe16 : 16 ≤ cg.stride := by
      rw [hStrideEq]; split
      · omega
      · have hb := (sizeClass_bounds hsc48).1; unfold slotStride; omega
    have hCapCg : 12 + (lastIdx + 1) * cg.stride < maplen * 4096 := hStrideEq ▸ hCapLt
    have hCntEq : cg.cnt = lastIdx + 1 := rfl
    have hTotEq : cg.totalBytes = maplen * 4096 := by simp [GroupDesc.totalBytes, show cg.maplen = maplen from rfl, hMapPos]
    have hCgLast0 : cg.lastIdx = 0 →
        cg.stride ≤ slotStride cg.sc ∨ (24 ≤ cg.sc ∧ cg.maplen * 4096 = pageAlignUp (slotStride cg.sc + 16)) := by
      intro hz
      have hz' : lastIdx = 0 := hz
      have hStr0 : cg.stride = maplen * 4096 - 16 := by
        rw [hStrideEq]; simp [hz', hMapPos]
      rw [hStr0]; exact hLast0 hz'
    refine ⟨Or.inl hsc48, hLast31, hSlLen, fun h63 => absurd h63 (by change sc ≠ 63; omega),
      hMbLo, by change mb.toNat % 16 = 0; omega, by rw [hTotEq]; exact hMbHi,
      by rw [hCntEq, hTotEq]; omega,
      fun _ => by rw [hCntEq, hTotEq]; exact hCapCg,
      ?_, ⟨fun _ => rfl, fun _ => hMapPos⟩, fun _ => ⟨hMbAl, rfl, hSc25, fun _ => ⟨hSc48M, hCgLast0⟩⟩,
      fun h0 => absurd h0 (by change maplen = 0 → _ at *; omega), hBmDisj, hBmOr, hActLe,
      by simpa [st', val', cg] using readBytesFromMap_writeBytesToMap val₁ m cg.metaBytes (by simp),
      ?_, ?_, fun idx hIdx => ?_⟩
    · have hMulEq : (lastIdx + 1) * cg.stride = lastIdx * cg.stride + cg.stride := by
        rw [Nat.add_mul, Nat.one_mul]
      have hOff : cg.slotEnd cg.lastIdx = mb + BitVec.ofNat 64 (12 + (lastIdx + 1) * cg.stride) := by
        apply BitVec.eq_of_toNat_eq
        unfold GroupDesc.slotEnd GroupDesc.slotStart GroupDesc.storage
        have hLastEq : cg.lastIdx = lastIdx := rfl
        have hMemEq : cg.mem = mb := rfl
        rw [hLastEq, hMemEq]
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      dsimp only [st']
      rw [hOff, hValCgMem _ hCapCg]
      simp only [grpBs, List.append_assoc]
      rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by simp; omega), List.getElem_replicate]
    · apply List.ext_getElem (by simp)
      intro i hi1 hi2; rw [readBytesFromMap_getElem _ _ _ _ hi1]; dsimp only [st', cg]
      rw [hValCgMem i (by simp at hi1; omega)]
      simp only [grpBs, List.append_assoc]
      rw [List.getElem_append_left (by simp at hi1 ⊢; exact hi1)]
    · dsimp only [st', cg]; rw [show mb + 8#64 = mb + BitVec.ofNat 64 8 from rfl, hValCgMem 8 (by omega)]
      simp only [grpBs, List.append_assoc]
      rw [List.getElem_append_right (by simp), List.getElem_append_left (by simp)]; rfl
    · have hIdxLt : idx < lastIdx + 1 := hSlLen ▸ hIdx
      have hIdxMulLe : idx * cg.stride ≤ (lastIdx + 1) * cg.stride := Nat.mul_le_mul_right _ (by omega)
      have hKLt : 12 + idx * cg.stride < maplen * 4096 := by omega
      have hOff : cg.slotStart idx - 4#64 = mb + BitVec.ofNat 64 (12 + idx * cg.stride) := by
        apply BitVec.eq_of_toNat_eq
        unfold GroupDesc.slotStart GroupDesc.storage
        have hMemEq : cg.mem = mb := rfl
        rw [hMemEq, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      refine ⟨by dsimp only [st']; rw [hOff, hValCgMem _ hKLt]; simp only [grpBs, List.append_assoc]
                 rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by simp; omega), List.getElem_replicate],
        (hBmBits idx hIdxLt).1.trans (hSlIdx idx hIdx).2.1,
        (hBmBits idx hIdxLt).2.trans (hSlIdx idx hIdx).2.2,
        fun hAi => (hSlIdx idx hIdx).2.2.mp hAi, ?_⟩
      cases idx with
      | zero => rw [(hSlIdx 0 hIdx).1 rfl]; trivial
      | succ j =>
        by_cases hj : j + 1 ≤ activeIdx
        · rw [(hSlIdx (j + 1) hIdx).2.1.mp ⟨by omega, hj⟩]; trivial
        · rw [(hSlIdx (j + 1) hIdx).2.2.mp (by omega)]; trivial
  have hOldSlotNoM : ∀ p ∈ allMetaSlots st, p ≠ m →
      readBytesFromMap val' p 40 = readBytesFromMap st.byteVal p 40 := fun p hp hpNe => by
    obtain ⟨_, _, _, ⟨maP, hmaP, hInMaP⟩, _⟩ := allMetaSlots_info hwf hp
    exact readBytesFromMap_congr (by decide) fun a ha =>
      hOutBoth (maP.base, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hmaP))))
        a (hInMaP a ha) fun haM => DisjointRegions.not_both (hDisjAllSlots p hp hpNe) haM ha
  have hOldGrpVal : ∀ g ∈ st.groups, ∀ a : BitVec 64, g.mem.toNat ≤ a.toNat → a.toNat ≤ (g.slotEnd g.lastIdx).toNat →
      val' a = st.byteVal a := fun g hg a hlo hhi => by
    obtain ⟨gr, hgr, hgrPos, _, _, _⟩ := group_root_containment hwf hg
    have hGrB := (hwf.groups_wf gr hgr).2.2.2.2.2.2.1
    have hGrT : gr.totalBytes = gr.maplen * 4096 := by simp [GroupDesc.totalBytes, hgrPos]
    have haGr : InRegion gr.mem (gr.maplen * 4096) a := (inRegion_bounds (by omega)).mpr ⟨by omega, by omega⟩
    exact hOutBoth (gr.mem, gr.maplen * 4096)
      (List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hgr, decide_eq_true hgrPos⟩)))
      a haGr fun haM => (hmDisjGrp gr hgr).2 a haM (hGrT ▸ haGr)
  have hOldGrpWf : ∀ g ∈ st.groups, GroupWf st' g := fun g hg => by
    have hgWf := hwf.groups_wf g hg; have hgGs := group_slot_toNat hgWf
    have hgEndLim : (g.slotEnd g.lastIdx).toNat ≤ 2 ^ 48 := by
      have := hgGs.2.2.2.2.1; have := hgWf.2.2.2.2.2.2.1; omega
    have hgGe16 : g.mem.toNat + 16 ≤ (g.slotEnd g.lastIdx).toNat := by
      have := hgGs.2.2.2.1; have : 1 * 16 ≤ g.cnt * g.stride := Nat.mul_le_mul hgGs.2.1 hgGs.1; omega
    have hgMetaAll := (hUsedAll g.metaPtr).mp (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_map_of_mem hg))))
    rcases hwf.groups_wf g hg with ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20⟩
    refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9,
      (hOldGrpVal g hg _ (by omega) (Nat.le_refl _)).trans c10, c11, c12,
      fun hz => by obtain ⟨hl, pg, hpg, rest⟩ := c13 hz; exact ⟨hl, pg, List.Mem.tail _ hpg, rest⟩,
      c14, c15, c16, (hOldSlotNoM g.metaPtr hgMetaAll (fun h => hmNotGrp (h ▸ List.mem_map_of_mem hg))).trans c17,
      (readBytesFromMap_congr (by decide) fun a ha => by
        have := (inRegion_bounds (by omega)).mp ha; exact hOldGrpVal g hg a (by omega) (by omega)).trans c18,
      (by have := add_ofNat_toNat (x := g.mem) (k := 8) (by omega); exact (hOldGrpVal g hg _ (by omega) (by omega)).trans c19),
      fun idx hIdx => ?_⟩
    have hIdxCnt : idx < g.cnt := c3 ▸ hIdx
    obtain ⟨hSt, hEn, hSub4⟩ := hgGs.2.2.2.2.2 idx hIdxCnt; have hStor := hgGs.2.2.1
    have hEnLe : (g.slotEnd idx).toNat ≤ (g.slotEnd g.lastIdx).toNat := by
      have := hgGs.2.2.2.1; have : (idx + 1) * g.stride ≤ g.cnt * g.stride := Nat.mul_le_mul_right _ hIdxCnt; omega
    have hMulLe : idx * g.stride ≤ (idx + 1) * g.stride := Nat.mul_le_mul_right _ (by omega)
    exact slotWf_congr hgWf hIdx ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (c20 idx hIdx)
      (hOldGrpVal g hg _ (by omega) (by omega))
      (fun cm hs cg₀ hcg₀ hcm _ => by
        have hB := (c20 idx hIdx).2.2.2.2; rw [hs] at hB
        obtain ⟨_, cgW, hcgW, hcmW, _, _, _, _, _⟩ := hB
        cases mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg₀ hcgW (hcm.trans hcmW.symm)
        have := (hwf.groups_wf cg₀ hcg₀).2.2.2.2.1
        have := sub_ofNat_toNat (x := cg₀.mem) (k := 4) (by omega)
        exact ⟨fun a ha => by have := (inRegion_bounds (by omega)).mp ha; exact hOldGrpVal g hg a (by omega) (by omega),
          cg₀, List.Mem.tail _ hcg₀, rfl, rfl, rfl, rfl⟩)
      (fun _ _ _ _ a ha => by
        have : idx * g.stride + g.stride = (idx + 1) * g.stride := by rw [Nat.add_mul, Nat.one_mul]
        have := (inRegion_bounds (by omega)).mp ha; exact hOldGrpVal g hg a (by omega) (by omega))
  have hCuIff : ∀ a : BitVec 64, CarvedUserByte st' a ↔ CarvedUserByte st a := fun a => by
    unfold CarvedUserByte; simp only [st', List.mem_cons]
    refine ⟨?_, fun ⟨g, hg, s, hs, h⟩ => ⟨g, Or.inr hg, s, hs, h⟩⟩
    rintro ⟨g, rfl | hg, s, hs, h⟩
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
      cases i with
      | zero => rw [(hSlIdx 0 hi).1 rfl] at h; cases h
      | succ j =>
        by_cases hj : j + 1 ≤ activeIdx
        · rw [(hSlIdx (j + 1) hi).2.1.mp ⟨by omega, hj⟩] at h; cases h
        · rw [(hSlIdx (j + 1) hi).2.2.mp (by omega)] at h; cases h
    · exact ⟨g, hg, s, hs, h⟩
  have hRwIff : ∀ a : BitVec 64,
      OwnedRwByte st' a ↔ (OwnedRwByte st a ∨ InRegion mb (maplen * 4096) a) ∨ InRegion m 40 a := fun a => by
    unfold OwnedRwByte CarvedMetaByte; simp only [st', hRes, List.mem_cons, hCuIff a]
    constructor
    · rintro ⟨h1, hNoCu, hNoRes⟩
      by_cases haM : InRegion m 40 a
      · exact Or.inr haM
      · by_cases haMb : InRegion mb (maplen * 4096) a
        · exact Or.inl (Or.inr haMb)
        · refine Or.inl (Or.inl ⟨?_, hNoCu, fun ⟨mr, hmr, hInMr⟩ => ?_⟩)
          · rcases h1 with hMa | ⟨g, rfl | hg, hp, hin⟩
            · exact Or.inl hMa
            · exact absurd hin haMb
            · exact Or.inr ⟨g, hg, hp, hin⟩
          · rcases hmr with rfl | hmrT
            · exact haM hInMr
            · exact hNoRes ⟨mr, hmrT, hInMr⟩
    · rintro ((⟨h1, hNoCu, hNoRes⟩ | haMb) | haM)
      · exact ⟨h1.imp id fun ⟨g, hg, hp, hin⟩ => ⟨g, Or.inr hg, hp, hin⟩, hNoCu,
          fun ⟨mr, hmr, hin⟩ => hNoRes ⟨mr, Or.inr hmr, hin⟩⟩
      · refine ⟨Or.inr ⟨cg, Or.inl rfl, hMapPos, haMb⟩, fun hCu => ?_, fun ⟨mr, hmr, hin⟩ => ?_⟩
        · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, gr, hgr, hgrPos, haGr⟩ := carvedUserByte_witness hwf hCu
          exact DisjointRegions.not_both (hDisjRoot (gr.mem, gr.maplen * 4096)
            (List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hgr, decide_eq_true hgrPos⟩)))) haMb haGr
        · have hmrAll := (hUsedAll mr).mp (List.mem_append_right _ (hRes ▸ List.Mem.tail _ hmr))
          obtain ⟨_, _, _, ⟨maR, hmaR, hInMaR⟩, _⟩ := allMetaSlots_info hwf hmrAll
          exact DisjointRegions.not_both (hDisjMbMa maR hmaR) haMb (hInMaR a hin)
      · exact ⟨Or.inl ⟨maM, hmaM, hInMaM a haM⟩, hmNoCu a haM, fun ⟨mr, hmr, hin⟩ => by
          rw [hRes, List.nodup_append, List.nodup_cons] at hUsedNd
          exact DisjointRegions.not_both (hmDisjRes mr (hRes ▸ List.Mem.tail _ hmr)
            fun hEq => hUsedNd.2.1.1 (hEq ▸ hmr)) haM hin⟩
  have hMpIff : ∀ a : BitVec 64, OwnedMappedByte st' a ↔ OwnedMappedByte st a ∨ InRegion mb (maplen * 4096) a := fun a => by
    unfold OwnedMappedByte; simp only [st', List.mem_cons]
    exact ⟨fun h => by rcases h with h1 | h2 | h3 | ⟨g, rfl | hg, hp, hin⟩
                       · exact Or.inl (Or.inl h1)
                       · exact Or.inl (Or.inr (Or.inl h2))
                       · exact Or.inl (Or.inr (Or.inr (Or.inl h3)))
                       · exact Or.inr hin
                       · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨g, hg, hp, hin⟩))),
      fun h => by rcases h with (h1 | h2 | h3 | ⟨g, hg, hp, hin⟩) | haMb
                  · exact Or.inl h1
                  · exact Or.inr (Or.inl h2)
                  · exact Or.inr (Or.inr (Or.inl h3))
                  · exact Or.inr (Or.inr (Or.inr ⟨g, Or.inr hg, hp, hin⟩))
                  · exact Or.inr (Or.inr (Or.inr ⟨cg, Or.inl rfl, hMapPos, haMb⟩))⟩
  have hDisjMbRw : ∀ a : BitVec 64, InRegion mb (maplen * 4096) a → ¬ OwnedRwByte st a := fun a haMb hRw => by
    rcases hRw.1 with ⟨ma, hma, haMa⟩ | ⟨g, hg, hp, haG⟩
    · exact DisjointRegions.not_both (hDisjMbMa ma hma) haMb haMa
    · exact DisjointRegions.not_both (hDisjRoot (g.mem, g.maplen * 4096)
        (List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hg, decide_eq_true hp⟩)))) haMb haG
  have hDisjMbMp : ∀ a : BitVec 64, InRegion mb (maplen * 4096) a → ¬ OwnedMappedByte st a := fun a haMb hMp => by
    rcases hMp with ⟨x, hx, ha⟩ | ⟨x, hx, ha⟩ | ⟨x, hx, ha⟩ | ⟨g, hg, hp, ha⟩
    · rw [hwf.brk_mode_wf.2.1, List.mem_filter] at hx; obtain ⟨ma, hma, rfl⟩ := List.mem_map.mp hx.1
      exact DisjointRegions.not_both (hDisjMbMa ma hma) haMb ha
    · rw [hwf.brk_mode_wf.2.2.1, List.mem_filter] at hx
      exact DisjointRegions.not_both (hDisjRoot (x, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hx.1))))) haMb ha
    · exact DisjointRegions.not_both (hDisjRoot (x, 4096) (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hx)))) haMb ha
    · exact DisjointRegions.not_both (hDisjRoot (g.mem, g.maplen * 4096) (List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hg, decide_eq_true hp⟩)))) haMb ha
  have hPermUsed : (st'.groups.map (·.metaPtr) ++ st'.freeMetas.map (·.ptr) ++ st'.bumpMetas ++ st'.reservedMetas).Perm
      (st.groups.map (·.metaPtr) ++ st.freeMetas.map (·.ptr) ++ st.bumpMetas ++ st.reservedMetas) := by
    simp only [st', cg, hRes, List.map_cons, List.cons_append]
    exact List.perm_middle.symm
  have hDynSt' : ∀ x, x ∈ dynamicRootRegions st' ↔ x = (mb, maplen * 4096) ∨ x ∈ dynamicRootRegions st := fun x => by
    unfold dynamicRootRegions; dsimp only [st', cg]
    simp only [List.filter_cons, decide_eq_true hMapPos, ↓reduceIte, List.map_cons, List.mem_append, List.mem_cons]
    exact ⟨by rintro (((h | h) | h) | rfl | h)
              · exact Or.inr (Or.inl (Or.inl (Or.inl h)))
              · exact Or.inr (Or.inl (Or.inl (Or.inr h)))
              · exact Or.inr (Or.inl (Or.inr h))
              · exact Or.inl rfl
              · exact Or.inr (Or.inr h),
      by rintro (rfl | ((h | h) | h) | h)
         · exact Or.inr (Or.inl rfl)
         · exact Or.inl (Or.inl (Or.inl h))
         · exact Or.inl (Or.inl (Or.inr h))
         · exact Or.inl (Or.inr h)
         · exact Or.inr (Or.inr h)⟩
  have hCostEq : totalLiveEffCost st' = totalLiveEffCost st := by
    unfold totalLiveEffCost; dsimp only [st', cg, activeIdx]; simp [newGroupSlots, slotEffCost]
  have hCountEq : totalLiveCount st' = totalLiveCount st := by
    unfold totalLiveCount; dsimp only [st', cg, activeIdx]; simp [newGroupSlots, slotLiveCount]
  refine ⟨?_, hCostEq, hCountEq, ?_, ?_, ?_, ?_⟩
  · refine {
      base_wf := trivial
      brk_bounds := hwf.brk_bounds
      ctx_lens := ⟨by dsimp only [st', ctx']; simp [hwf.ctx_lens.1],
        by dsimp only [st', ctx']; simp [hwf.ctx_lens.2.1], hUnmL, hBncL,
        hwf.ctx_lens.2.2.2.2.1, by dsimp only [st']; simp [hwf.ctx_lens.2.2.2.2.2]⟩
      initDone_wf := hwf.initDone_wf
      initZero_wf := fun hz => by have := (hwf.initZero_wf hz).2.2.2.2.2.2.2.2.1; rw [hRes] at this; cases this
      bounces_wf := hBnc
      usage_wf := usageWf_after_allocGroup hwf hscU rfl hLast31 rfl
      brk_mode_wf := hwf.brk_mode_wf
      metaAreas_wf := ⟨hwf.metaAreas_wf.1, fun ma hma => by
        obtain ⟨h1, h2, h3, h4⟩ := hwf.metaAreas_wf.2.1 ma hma
        unfold allMetaSlots at hmAll; obtain ⟨ma0, hma0, hm0⟩ := List.mem_flatMap.mp hmAll
        obtain ⟨k0, hk0, hmEq⟩ := List.mem_map.mp hm0
        have hk101 := List.mem_range.mp hk0
        obtain ⟨l0, a0, hi0, _⟩ := hwf.metaAreas_wf.2.1 ma0 hma0
        have hs0 := (slotAddr_bounds l0 a0 hi0 hk101).1
        refine ⟨h1, h2, h3, (readBytesFromMap_congr (by decide) fun a ha => ?_).trans h4⟩
        have haB := (inRegion_bounds (b := ma.base) (n := 24) (by omega)).mp ha
        refine hOutBoth (ma.base, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma))))
          a ((inRegion_bounds (b := ma.base) (n := 4096) (by omega)).mpr ⟨by omega, by omega⟩) fun haM => ?_
        have haMB := (inRegion_bounds (b := m) (n := 40) (by omega)).mp haM; rw [← hmEq, hs0] at haMB
        have : ma0.base.toNat + 24 ≤ a.toNat ∧ a.toNat < ma0.base.toNat + 4096 := by omega
        clear hk0 hk101 hs0 hmEq haMB haM ha; omega, hwf.metaAreas_wf.2.2⟩
      guard_avail_wf := ⟨hwf.guard_avail_wf.1, hwf.guard_avail_wf.2.1, hwf.guard_avail_wf.2.2.1, fun ap hap => by
        obtain ⟨h1, h2, h3, h4⟩ := hwf.guard_avail_wf.2.2.2 ap hap
        have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd
        rw [List.append_assoc, List.append_assoc, PairwiseDisjointRegions.append_iff] at hpd
        have hDisjMaAp := hpd.2.2 (maM.base, 4096) (List.mem_map_of_mem hmaM) (ap, 4096)
          (List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem hap)))
        refine ⟨h1, h2, h3, (readBytesFromMap_congr (by decide) fun a ha => ?_).trans h4⟩
        exact hOutBoth (ap, 4096) (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hap))) a ha
          fun haM => DisjointRegions.not_both hDisjMaAp (hInMaM a haM) ha⟩
      inflight_wf := by
        have := hwf.inflight_wf; unfold totalClaimedSlots at this ⊢; dsimp only [st', cg, activeIdx]
        simp only [hRes, List.length_cons, List.map_cons, List.sum_cons, hSlCl] at this ⊢; omega
      free_bump_metas_wf := ⟨hwf.free_bump_metas_wf.1,
        fun fm hfm => by
          have hfmMem : fm.ptr ∈ st.freeMetas.map (·.ptr) := List.mem_map_of_mem hfm
          rw [List.nodup_append] at hUsedNd
          exact (hOldSlotNoM fm.ptr ((hUsedAll fm.ptr).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hfmMem))))
            fun h => hUsedNd.2.2 fm.ptr (List.mem_append_left _ (List.mem_append_right _ hfmMem)) m hmMem h).trans
            (hwf.free_bump_metas_wf.2.1 fm hfm),
        hwf.free_bump_metas_wf.2.2.1,
        fun bm hbm => by
          rw [List.nodup_append] at hUsedNd
          exact (hOldSlotNoM bm ((hUsedAll bm).mp (List.mem_append_left _ (List.mem_append_right _ hbm)))
            fun h => hUsedNd.2.2 bm (List.mem_append_right _ hbm) m hmMem h).trans
            (hwf.free_bump_metas_wf.2.2.2.1 bm hbm),
        hPermUsed.nodup_iff.mpr hUsedNd,
        fun x => hPermUsed.mem_iff.trans (hUsedAll x)⟩
      groups_nodup := ⟨List.nodup_cons.mpr ⟨hmNotGrp, hwf.groups_nodup.1⟩,
        List.nodup_cons.mpr ⟨fun hMem => by
          obtain ⟨g, hg, hEq⟩ := List.mem_map.mp hMem
          obtain ⟨gr, hgr, hgrPos, hLo, _, hHi⟩ := group_root_containment hwf hg
          have := (hwf.groups_wf gr hgr).2.2.2.2.2.2.1
          have := (group_slot_toNat (hwf.groups_wf g hg)).1
          have := (group_slot_toNat (hwf.groups_wf g hg)).2.1
          have := (group_slot_toNat (hwf.groups_wf g hg)).2.2.2.1
          have : 1 * 16 ≤ g.cnt * g.stride := Nat.mul_le_mul ‹_› ‹_›
          have hTot : gr.totalBytes = gr.maplen * 4096 := by simp [GroupDesc.totalBytes, hgrPos]
          exact DisjointRegions.not_both (hDisjRoot (gr.mem, gr.maplen * 4096)
            (List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hgr, decide_eq_true hgrPos⟩))))
            ((inRegion_bounds (b := mb) (n := maplen * 4096) (by omega)).mpr ⟨by omega, by omega⟩) (a := mb)
            ((inRegion_bounds (b := gr.mem) (n := gr.maplen * 4096) (by omega)).mpr
              (by change gr.mem.toNat ≤ mb.toNat ∧ mb.toNat < gr.mem.toNat + gr.maplen * 4096; dsimp only [cg] at hEq; have := congrArg BitVec.toNat hEq; omega)),
          hwf.groups_nodup.2⟩⟩
      groups_wf := fun g hg => by rcases List.mem_cons.mp hg with rfl | hg'; exact hCgWf; exact hOldGrpWf g hg'
      regions_disjoint := by
        refine ⟨?_, trivial⟩
        have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd ⊢; dsimp only [st']
        rw [PairwiseDisjointRegions.append_iff] at hpd ⊢
        simp only [cg, List.filter_cons, decide_eq_true hMapPos, ↓reduceIte, List.map_cons, PairwiseDisjointRegions]
        refine ⟨hpd.1, ⟨fun r hr => hDisjRoot r (List.mem_append_right _ hr), hpd.2.1⟩, fun x hx y hy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact (hDisjRoot x (List.mem_append_left _ hx)).symm
        · exact hpd.2.2 x hx y hy'
      active_wf := activeWf_after_allocGroup (cg := cg) hwf hscA hscL hEmptyAct hmNe0 hmNotGrp rfl rfl rfl rfl hActPos
        (f := id) (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) (by dsimp only [st']; simp) rfl rfl
      liveMap_wf := fun p n => by
        rw [hwf.liveMap_wf p n]; simp only [st', List.mem_cons]
        refine ⟨fun ⟨g, hg, idx, hIdx, e, hs⟩ => ⟨g, Or.inr hg, idx, hIdx, e, hs⟩, ?_⟩
        rintro ⟨g, rfl | hg, idx, hIdx, e, hs⟩
        · cases idx with
          | zero => rw [(hSlIdx 0 hIdx).1 rfl] at hs; cases hs
          | succ j =>
            by_cases hj : j + 1 ≤ activeIdx
            · rw [(hSlIdx (j + 1) hIdx).2.1.mp ⟨by omega, hj⟩] at hs; cases hs
            · rw [(hSlIdx (j + 1) hIdx).2.2.mp (by omega)] at hs; cases hs
        · exact ⟨g, hg, idx, hIdx, e, hs⟩
      live_le_peak := hwf.live_le_peak
      effCost_le_live := hCostEq ▸ hwf.effCost_le_live
      meta_pages_bound := hwf.meta_pages_bound
      empty_groups_bound := fun g hg hEmp => by
        rcases List.mem_cons.mp hg with rfl | hg'
        · unfold GroupDesc.isEmpty at hEmp; dsimp only [cg] at hEmp; rw [hSlNotEmp] at hEmp; cases hEmp
        · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hwf.empty_groups_bound g hg' hEmp
          refine ⟨e1, e2, e3, e4, fun h1 => ?_, fun g2 hg2 hEmp2 hSc2 => ?_, e7⟩
          · have h2 : g.sc < st.activeLists.length := by dsimp only [st'] at h1; simpa using h1
            have hNeSc : sc ≠ g.sc := fun hEq => by subst hEq; have := e5 h2; rw [hEmptyAct] at this; cases this
            dsimp only [st']; simpa [List.getElem_set_ne hNeSc] using e5 h2
          · rcases List.mem_cons.mp hg2 with rfl | hg2'
            · unfold GroupDesc.isEmpty at hEmp2; dsimp only [cg] at hEmp2; rw [hSlNotEmp] at hEmp2; cases hEmp2
            · exact e6 g2 hg2' hEmp2 hSc2
      masterDom_wf := ⟨hDomNd,
        fun a h => (hDomMem a).mpr (by
          rcases h with hRw | hPn | hMp
          · rcases (hRwIff a).mp hRw with (hRw0 | haMb) | haM
            · exact Or.inl ((hDom1Mem a).mpr (Or.inl (hwf.masterDom_wf.2.1 a (Or.inl hRw0))))
            · exact Or.inr haMb
            · exact Or.inl ((hDom1Mem a).mpr (Or.inr haM))
          · exact Or.inl ((hDom1Mem a).mpr (Or.inl (hwf.masterDom_wf.2.1 a (Or.inr (Or.inl hPn)))))
          · rcases (hMpIff a).mp hMp with hMp0 | haMb
            · exact Or.inl ((hDom1Mem a).mpr (Or.inl (hwf.masterDom_wf.2.1 a (Or.inr (Or.inr hMp0)))))
            · exact Or.inr haMb),
        fun a ha => by
          rcases (hDomMem a).mp ha with ha1 | haMb
          · rcases (hDom1Mem a).mp ha1 with ha0 | haM
            · obtain ⟨r, hr, hin⟩ := hwf.masterDom_wf.2.2 a ha0
              exact ⟨r, (hDynSt' r).mpr (Or.inr hr), hin⟩
            · exact ⟨(maM.base, 4096), (hDynSt' _).mpr (Or.inr
                (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hmaM))))),
                hInMaM a haM⟩
          · exact ⟨(mb, maplen * 4096), (hDynSt' _).mpr (Or.inl rfl), haMb⟩⟩
    }
  · rw [hBmRwExt1, hBmRwExt2,
        ByteMap_absorb_slice hDomNd st.byteVal mb grpBs (by rw [hGrpBsLen]; omega)
          (fun a ha => (hDomMem a).mpr (Or.inr (hGrpBsLen ▸ ha)))
          (fun a ha => hDisjMbRw a (hGrpBsLen ▸ ha)),
        ByteMap_absorb_slice hDomNd val₁ m cg.metaBytes (by simp)
          (fun a ha => (hDomMem a).mpr (Or.inl ((hDom1Mem a).mpr (Or.inr (by simpa using ha)))))
          (fun a ha h => by
            have haM : InRegion m 40 a := by simpa using ha
            rcases h with hRw | haMb
            · exact hmNoRw a haM hRw
            · exact DisjointRegions.not_both hDisjMbM (hGrpBsLen ▸ haMb) haM)]
    exact SetSep_congr (fun a _ => by
      have h40 : cg.metaBytes.length = 40 := by simp
      rw [h40, hGrpBsLen]; exact (hRwIff a).symm) (fun _ _ _ => rfl)
  · exact (hBmPnExt1.trans hBmPnExt2).trans (SetSep_congr (fun _ _ => Iff.rfl) fun a _ hk =>
      congrArg (a ↦₈ₙ ·) (by
        dsimp only [st']
        rcases hk with ⟨gp, hgp, hin⟩ | ⟨ap, hap, hin⟩
        · exact (hOutBoth (gp, 4096) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hgp))))
            a hin fun haM => by
              have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd
              rw [List.append_assoc, List.append_assoc, PairwiseDisjointRegions.append_iff] at hpd
              exact DisjointRegions.not_both (hpd.2.2 (maM.base, 4096) (List.mem_map_of_mem hmaM) (gp, 4096)
                (List.mem_append_left _ (List.mem_map_of_mem hgp))) (hInMaM a haM) hin).symm
        · exact (hOutBoth (ap, 4096) (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hap)))
            a hin fun haM => by
              have hpd := hwf.regions_disjoint.1; unfold dynamicRootRegions at hpd
              rw [List.append_assoc, List.append_assoc, PairwiseDisjointRegions.append_iff] at hpd
              exact DisjointRegions.not_both (hpd.2.2 (maM.base, 4096) (List.mem_map_of_mem hmaM) (ap, 4096)
                (List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem hap)))) (hInMaM a haM) hin).symm))
  · rw [hMpExt1, hMpExt2, MappedSet_absorb_slice hDomNd mb (by omega) (fun a ha => (hDomMem a).mpr (Or.inr ha)) hDisjMbMp]
    exact SetSep_congr (fun a _ => (hMpIff a).symm) (fun _ _ _ => rfl)
  · intro a ha
    have hCgGs := group_slot_toNat hCgWf
    have hStrideGe16 := hCgGs.1
    have hSt0 : (cg.slotStart 0).toNat = mb.toNat + 16 := by
      simpa [show cg.mem = mb from rfl] using (hCgGs.2.2.2.2.2 0 (by change 0 < lastIdx + 1; omega)).1
    have h16StrideLe : 16 + cg.stride ≤ maplen * 4096 := by
      have hCapCg : 12 + (lastIdx + 1) * cg.stride < maplen * 4096 := by
        simpa [show cg.stride = if lastIdx == 0 && 0 < maplen then maplen * 4096 - 16 else slotStride sc from rfl] using hCapLt
      by_cases hz : lastIdx = 0
      · have : cg.stride = maplen * 4096 - 16 := by
          change (if lastIdx == 0 && 0 < maplen then maplen * 4096 - 16 else slotStride sc) = _
          simp [hz, hMapPos]
        omega
      · have : 2 * cg.stride ≤ (lastIdx + 1) * cg.stride := Nat.mul_le_mul_right _ (by omega)
        omega
    have haB := (inRegion_bounds (b := cg.slotStart 0) (n := cg.stride) (by omega)).mp ha
    have hEqI : a = mb + BitVec.ofNat 64 (a.toNat - mb.toNat) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
    rw [hEqI]; dsimp only [st']
    rw [hValCgMem (a.toNat - mb.toNat) (by omega)]
    simp only [grpBs, List.append_assoc]
    rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by simp; omega), List.getElem_replicate]

/-! ## `slotStride` Bounds, `PureStatePres`, and Placed OOM Combinators -/

private theorem slotStride_bounds_check :
    (((List.range 48).all fun sc => (16 ≤ slotStride sc) && (slotStride sc ≤ 131056)) &&
     ((List.range 25).all fun sc => slotStride sc ≤ 2336) &&
     ((List.range 24).all fun sc => slotStride sc ≤ 2032)) = true := by decide +kernel

theorem slotStride_bounds_48 {sc : Nat} (hsc : sc < 48) :
    16 ≤ slotStride sc ∧ slotStride sc ≤ 131056 := by
  have h12 := (Bool.and_eq_true _ _).mp slotStride_bounds_check
  have h := (Bool.and_eq_true _ _).mp h12.1
  simpa [Bool.and_eq_true, decide_eq_true_eq] using List.all_eq_true.mp h.1 sc (List.mem_range.mpr hsc)

theorem slotStride_le_2336_of_le_24 {sc : Nat} (hsc : sc ≤ 24) : slotStride sc ≤ 2336 := by
  have h12 := (Bool.and_eq_true _ _).mp slotStride_bounds_check
  have h := (Bool.and_eq_true _ _).mp h12.1
  simpa [decide_eq_true_eq] using List.all_eq_true.mp h.2 sc (List.mem_range.mpr (by omega))

theorem slotStride_le_2032_of_le_23 {sc : Nat} (hsc : sc ≤ 23) : slotStride sc ≤ 2032 := by
  have h12 := (Bool.and_eq_true _ _).mp slotStride_bounds_check
  simpa [decide_eq_true_eq] using List.all_eq_true.mp h12.2 sc (List.mem_range.mpr (by omega))

theorem parent_slot_bounds {inflight : Nat} {base brkStart brk : BitVec 64}
    {liveCost peakCost : Nat} {st : MallocngSt}
    (hwf : MallocngWFInflight inflight base brkStart brk liveCost peakCost st)
    {pg : GroupDesc} (hpg : pg ∈ st.groups) (hpSc24 : pg.sc ≤ 24)
    {pIdx : Nat} (hpIdx : pIdx < pg.slots.length) :
    slotStride pg.sc ≤ pg.stride ∧ pg.stride ≤ 65524 ∧
    (pg.slotEnd pIdx).toNat - pg.storage.toNat ≤ 65520 := by
  have hpgWf := hwf.groups_wf pg hpg
  have hpGs := group_slot_toNat hpgWf
  have hpCnt : pIdx < pg.cnt := hpgWf.2.2.1 ▸ hpIdx
  obtain ⟨_, hpEnEq, _⟩ := hpGs.2.2.2.2.2 pIdx hpCnt
  have hStrLo : slotStride pg.sc ≤ pg.stride := by
    have h2336 := slotStride_le_2336_of_le_24 hpSc24
    unfold GroupDesc.stride; split
    · next hB =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB
      have : 1 * 4096 ≤ pg.maplen * 4096 := Nat.mul_le_mul_right 4096 hB.2
      omega
    · exact Nat.le_refl _
  have hAncSc25 : ∀ (k : Nat) {g : GroupDesc}, g ∈ st.groups →
      (if 0 < g.maplen then 0 else 48 - g.sc) ≤ k → g.sc ≤ 25 →
      ∃ gr ∈ st.groups, 0 < gr.maplen ∧ gr.sc ≤ 25 ∧
        gr.mem.toNat ≤ g.mem.toNat ∧ (g.slotEnd g.lastIdx).toNat < gr.mem.toNat + gr.maplen * 4096 := by
    intro k; induction k with
    | zero =>
      intro g hg hle h25
      by_cases hPos : 0 < g.maplen
      · have hgWf := hwf.groups_wf g hg
        have hStrict := hgWf.2.2.2.2.2.2.2.2.1 hPos
        have hTot : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hPos]
        have hEndEq := (group_slot_toNat hgWf).2.2.2.1
        exact ⟨g, hg, hPos, h25, Nat.le_refl _, by omega⟩
      · obtain ⟨_, gp, _, _, _, _, hPgSc48, hLt, _⟩ :=
          (hwf.groups_wf g hg).2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
        simp only [hPos, ↓reduceIte] at hle; omega
    | succ k ih =>
      intro g hg hle h25
      by_cases hPos : 0 < g.maplen
      · have hgWf := hwf.groups_wf g hg
        have hStrict := hgWf.2.2.2.2.2.2.2.2.1 hPos
        have hTot : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hPos]
        have hEndEq := (group_slot_toNat hgWf).2.2.2.1
        exact ⟨g, hg, hPos, h25, Nat.le_refl _, by omega⟩
      · have hMap0 : g.maplen = 0 := by omega
        have hgWf := hwf.groups_wf g hg
        obtain ⟨_, gp, hgp, pi, hpi, _, hPgSc48, hScLt, hp24, hCap, hLo, hHi, _⟩ :=
          hgWf.2.2.2.2.2.2.2.2.2.2.2.2.1 hMap0
        simp only [hPos, ↓reduceIte] at hle
        have hgpWf := hwf.groups_wf gp hgp; have hgpGs := group_slot_toNat hgpWf
        have hpiCnt : pi < gp.cnt := hgpWf.2.2.1 ▸ hpi
        have hGpSlot := hgpGs.2.2.2.2.2 pi hpiCnt
        have hGpLast := hgpGs.2.2.2.1
        have hGTot : g.totalBytes = g.nestedCap := by simp [GroupDesc.totalBytes, hMap0]
        have hGEndLe := (group_slot_toNat hgWf).2.2.2.2.1
        have hGEndEq := (group_slot_toNat hgWf).2.2.2.1
        have hGpEndMono : (gp.slotEnd pi).toNat ≤ (gp.slotEnd gp.lastIdx).toNat := by
          rw [hGpSlot.2.1, hGpLast]
          have : (pi + 1) * gp.stride ≤ gp.cnt * gp.stride := Nat.mul_le_mul_right _ hpiCnt; omega
        obtain ⟨gr, hgr, hgrPos, hgr25, hgrLo, hgrHi⟩ := ih hgp (by split <;> omega) (by omega)
        have : gp.mem.toNat ≤ (gp.slotStart pi).toNat := by rw [hGpSlot.1]; omega
        exact ⟨gr, hgr, hgrPos, hgr25, by omega, by omega⟩
  obtain ⟨gr, hgr, hgrPos, hgr25, hgrLo, hgrHi⟩ :=
    hAncSc25 (if 0 < pg.maplen then 0 else 48 - pg.sc) hpg (Nat.le_refl _) (by omega)
  have hgrWf := hwf.groups_wf gr hgr
  have hgr64k : gr.maplen * 4096 ≤ 65536 := (hgrWf.2.2.2.2.2.2.2.2.2.2.2.1 hgrPos).2.2.1 hgr25
  have hpEnLeLast : (pg.slotEnd pIdx).toNat ≤ (pg.slotEnd pg.lastIdx).toNat := by
    have : (pIdx + 1) * pg.stride ≤ pg.cnt * pg.stride := Nat.mul_le_mul_right _ hpCnt
    have := hpGs.2.2.2.1; omega
  have h1Mul : 1 * pg.stride ≤ pg.cnt * pg.stride := Nat.mul_le_mul hpGs.2.1 (Nat.le_refl _)
  have hStorEq := hpGs.2.2.1; have hLastEq := hpGs.2.2.2.1
  refine ⟨hStrLo, by omega, by omega⟩

theorem sepWP_of_noSyscalls_block [MallocngMultiPlacement] {idx : Nat}
    {exit_pc : BitVec 64} {s0 : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP ((mallocngBlockProg mmpl idx msvc).withSvc mallocngFaultSvc) exit_pc s0 P
      (fun sf P_f => sf.mem.perm = s0.mem.perm → post sf P_f)
      (fun _ => ⌜False⌝)) :
    SepWP (mallocngBlockProg mmpl idx msvc) exit_pc s0 P post oom :=
  SepWP.mono (SepWP.lift_noSyscalls rfl rfl h) fun _ _ _ _ ⟨hp, hperm⟩ => hp hperm

theorem sepWP_seq_noSyscalls_cl [MallocngMultiPlacement] {idx : Nat}
    {mid_pc exit_pc : BitVec 64} {s0 : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : VerifiedLibraries.mallocngLib.CodeLoaded mmpl s0.mem)
    (h : SepWP ((mallocngBlockProg mmpl idx msvc).withSvc mallocngFaultSvc) mid_pc s0 P
      (fun sm P_m => sm.mem.perm = s0.mem.perm →
        VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem →
        SepWP (mallocngBlockProg mmpl idx msvc) exit_pc sm P_m post oom)
      (fun _ => ⌜False⌝)) :
    SepWP (mallocngBlockProg mmpl idx msvc) exit_pc s0 P post oom :=
  SepWP.seq (sepWP_lift_noSyscalls_cl
    (fun sm P_m => sm.mem.perm = s0.mem.perm →
      VerifiedLibraries.mallocngLib.CodeLoaded mmpl sm.mem →
      SepWP (mallocngBlockProg mmpl idx msvc) exit_pc sm P_m post oom) hcl h)
    fun _ _ _ _ ⟨hperm, _, hcl_m, hcont⟩ => hcont hperm hcl_m

abbrev PureStatePres (s0 sf : State) : Prop :=
  MallocngProcPreserved s0 sf ∧ sf.brk = s0.brk ∧ calleeSavedVRegs sf = calleeSavedVRegs s0

theorem PureStatePres.rfl {s : State} : PureStatePres s s :=
  ⟨⟨Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _, Eq.refl _⟩,
   Eq.refl _, Eq.refl _⟩

theorem PureStatePres.trans {s0 s1 s2 : State}
    (h01 : PureStatePres s0 s1) (h12 : PureStatePres s1 s2) : PureStatePres s0 s2 :=
  ⟨MallocngProcPreserved.trans h01.1 h12.1, h12.2.1.trans h01.2.1, h12.2.2.trans h01.2.2⟩

macro "psp_rfl" : term => `(⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩)

namespace AllocGroupHelpers2
theorem mappedDelta_of_perm_eq {k b : Nat} {m0 m1 : Memory} (h : m1.perm = m0.perm) :
    MallocngMappedDelta k b m0 m1 :=
  ⟨[], Nat.zero_le k, Nat.zero_le b, fun a ha => Or.inl (by simpa [h] using ha)⟩
end AllocGroupHelpers2
export AllocGroupHelpers2 (mappedDelta_of_perm_eq)

theorem mappedDelta_perm_left {k b : Nat} {m0 m1 m2 : Memory}
    (hp : m1.perm = m0.perm) (hd : MallocngMappedDelta k b m1 m2) :
    MallocngMappedDelta k b m0 m2 := by
  obtain ⟨ivs, hl, hs, hc⟩ := hd
  exact ⟨ivs, hl, hs, fun a ha => by simpa [hp] using hc a ha⟩

theorem mappedDelta_perm_right {k b : Nat} {m0 m1 m2 : Memory}
    (hd : MallocngMappedDelta k b m0 m1) (hp : m2.perm = m1.perm) :
    MallocngMappedDelta k b m0 m2 := by
  obtain ⟨ivs, hl, hs, hc⟩ := hd
  exact ⟨ivs, hl, hs, fun a ha => hc a (by simpa [hp] using ha)⟩

theorem oom_from_allocMeta_placed {svc : State → State} {sc peakCount : Nat} {s0 s_call sf : State}
    (hProc : MallocngProcPreserved s0 s_call)
    (hperm : s_call.mem.perm = s0.mem.perm)
    (hoom : MallocngPlacedOomCond svc 1 (allocMetaPlacedByteBound peakCount) s_call sf) :
    MallocngPlacedOomCond svc (2 * (allocSlotDepthBound sc + 1))
      (allocSlotPlacedByteBound sc peakCount) s0 sf := by
  obtain ⟨hfs', htr', hsig', ivs, hl, hs, hc, hgap⟩ := hoom
  have hb := allocMetaPlacedByteBound_le_allocSlot sc peakCount
  refine ⟨hfs'.trans hProc.1, htr'.trans hProc.2.1, hsig'.trans hProc.2.2.2.2.2.2, ivs, by omega,
    Nat.le_trans hs hb, fun a ha => (hc a ha).imp (fun hm => hperm ▸ hm) id, fun hsan => ?_⟩
  obtain ⟨sz, hlo, hmod, hhi, hng⟩ := hgap hsan
  exact ⟨sz, hlo, hmod, Nat.le_trans hhi hb, hng⟩

theorem oom_from_mmapGap_placed {svc : State → State} {sc peakCount len : Nat} {s0 sf : State}
    (hProc : MallocngProcPreserved s0 sf)
    (hd : MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) s0.mem sf.mem)
    (hlenLo : PAGE_SIZE ≤ len) (hlenMod : len % PAGE_SIZE = 0)
    (hlenHi : len ≤ Cost.mallocngRootGroupBoundAt peakCount)
    (hgap : MallocngSanitizedSvc svc → MallocngNoGapOrPhys sf len) :
    MallocngPlacedOomCond svc (2 * (allocSlotDepthBound sc + 1))
      (allocSlotPlacedByteBound sc peakCount) s0 sf := by
  have hb := allocMetaPlacedByteBound_le_allocSlot sc peakCount
  have hlenB : allocMetaPlacedByteBound peakCount + len ≤ allocSlotPlacedByteBound sc peakCount :=
    allocSlotPlacedByteBound_root_add hlenHi
  exact MallocngPlacedOomCond.of_delta hProc.1 hProc.2.1 hProc.2.2.2.2.2.2 hd (by omega) hb
    fun hsan => ⟨len, hlenLo, hlenMod, hlenB, hgap hsan⟩

theorem oom_from_recAllocSlot_placed {svc : State → State} {sc p_sc peakCount : Nat}
    {s0 s_call sf : State}
    (hdepth : allocSlotDepthBound p_sc + 1 ≤ allocSlotDepthBound sc)
    (hProc : MallocngProcPreserved s0 s_call)
    (hd0 : MallocngMappedDelta 1 (allocMetaPlacedByteBound peakCount) s0.mem s_call.mem)
    (hoom : MallocngPlacedOomCond svc (2 * (allocSlotDepthBound p_sc + 1))
      (allocSlotPlacedByteBound p_sc peakCount) s_call sf) :
    MallocngPlacedOomCond svc (2 * (allocSlotDepthBound sc + 1))
      (allocSlotPlacedByteBound sc peakCount) s0 sf := by
  have hbSum : allocMetaPlacedByteBound peakCount + allocSlotPlacedByteBound p_sc peakCount ≤
      allocSlotPlacedByteBound sc peakCount :=
    allocSlotPlacedByteBound_nested_add hdepth
  exact MallocngPlacedOomCond.mono (by omega) hbSum
    (MallocngPlacedOomCond.append_delta hProc.1 hProc.2.1 hProc.2.2.2.2.2.2 hd0 hoom)

end VerifiedLibraries.Mallocng.Proofs
