/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedReallocMremapAbsorb
import VerifiedLibraries.Mallocng.Proofs.MallocLargeProof

/-!
# `MallocngWF` Preservation for `mremap` Realloc

Proves `MallocngWF` and `MallocngCountIvsWF` preservation for `sc = 63` `mmap` resize (`mremap` or
same-page-count in-place header update) in `__libc_realloc`.
-/

set_option autoImplicit false

@[expose] public section

namespace VerifiedLibraries.Mallocng.Proofs

open Arm64 Arm64.Obj ProofLib ProofLib.SepLogic VerifiedLibraries.Mallocng

set_option maxHeartbeats 400000 in
theorem reallocMremap_wf {base brkStart brk : BitVec 64}
    {b : MallocngBudget} {ivs0 : List (BitVec 64 × Nat)} {st : MallocngSt}
    (hwf : MallocngWF base brkStart brk b.liveCost b.peakCost st)
    (hCount : MallocngCountIvsWF b ivs0 st)
    {g : GroupDesc} (hg : g ∈ st.groups)
    (hIdx0 : 0 < g.slots.length)
    {p : BitVec 64} {oldSz oldEff : Nat} (origBs : List (BitVec 8))
    (_hOrigLe : origBs.length ≤ oldSz)
    (hSlot0 : g.slots[0]'hIdx0 = .liveUser p oldSz oldEff)
    (hSc63 : g.sc = 63)
    {newBase newP : BitVec 64} {needed newSz : Nat}
    (bsFinal : List (BitVec 8))
    (hNewSzHi : newSz ≤ MallocngMaxAllocSize)
    (hNewBaseGe : 4096 ≤ newBase.toNat) (hNewBaseAl : newBase.toNat % 4096 = 0)
    (hNeedLo : 4096 ≤ needed) (hNeedDvd : 4096 ∣ needed)
    (hNewBaseFit : newBase.toNat + needed ≤ 2 ^ 48)
    (hNewPNat : newP.toNat = newBase.toNat + 16 + (p.toNat - (g.slotStart 0).toNat))
    (hNewSlotFit : 16 + (p.toNat - (g.slotStart 0).toNat) + newSz + 4 ≤ needed)
    (hNeedResHi : (needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz) < 2 ^ 31)
    (hNewEffBound :
      needed ≤ ((oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost) + 8195)
    (hDisjMa : ∀ ma ∈ st.metaAreas, DisjointRegions ma.base 4096 newBase needed)
    (hDisjGp : ∀ gp ∈ st.guardPages, DisjointRegions gp 4096 newBase needed)
    (hDisjAp : ∀ ap ∈ st.availMetaPages, DisjointRegions ap 4096 newBase needed)
    (hDisjRg : ∀ rg ∈ st.groups, 0 < rg.maplen → rg.metaPtr ≠ g.metaPtr →
      DisjointRegions rg.mem (rg.maplen * 4096) newBase needed)
    (hFinalLen : bsFinal.length = needed)
    (hFinalEndZero : bsFinal.getD (needed - 4) 0#8 = 0#8)
    (hFinalPre : ∀ i, i < 16 + (p.toNat - (g.slotStart 0).toNat) →
      i ≠ 13 + (p.toNat - (g.slotStart 0).toNat) →
      bsFinal.getD i 0#8 = st.byteVal (g.mem + BitVec.ofNat 64 i))
    (hFinalUser : ∀ k (hk : k < min origBs.length newSz),
      bsFinal.getD (16 + (p.toNat - (g.slotStart 0).toNat) + k) 0#8 = origBs[k]'(by omega))
    (hFinalHdr : bsFinal.getD (13 + (p.toNat - (g.slotStart 0).toNat)) 0#8 =
      BitVec.ofNat 8 (min ((needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz)) 5 <<< 5))
    (hFinalRes1 : 1 ≤ (needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz) →
      bsFinal.getD (16 + (p.toNat - (g.slotStart 0).toNat) + newSz) 0#8 = 0#8)
    (hFinalRes5 : 5 ≤ (needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz) →
      bsFinal.getD ((needed - 4) - 5) 0#8 = 0#8 ∧
      ∀ j < 4, bsFinal.getD ((needed - 4) - 4 + j) 0#8 =
        (BitVec.ofNat 32 ((needed - 4) - (16 + (p.toNat - (g.slotStart 0).toNat) + newSz))).extractLsb' (8 * j) 8) :
    let newEff := (oldEff - max oldSz MallocngMinBlockCost) + max newSz MallocngMinBlockCost
    let st' := mkReallocMremapSt st g p newBase newP needed newSz newEff bsFinal
    let bf := mallocngReallocBudget true (some (oldSz, origBs)) newSz b
    MallocngBlockWf newP newSz ∧
    (newP = p ∨ st.liveMap newP = none) ∧
    MallocngCountIvsWF bf (dynamicRootRegions st') st' ∧
    MallocngWF base brkStart brk bf.liveCost bf.peakCost st' ∧
    (∀ a, ¬ InRegion g.metaPtr 40 a → ¬ InRegion g.mem (g.maplen * 4096) a →
      ¬ InRegion newBase needed a →
      (OwnedRwByte st' a ↔ OwnedRwByte st a) ∧ st'.byteVal a = st.byteVal a) ∧
    (∀ a, InRegion newBase needed a → (OwnedRwByte st' a ↔ ¬ InRegion newP newSz a)) ∧
    (∀ k (hk : k < min origBs.length newSz),
      st'.byteVal (newP + BitVec.ofNat 64 k) = origBs[k]'(by omega)) := by
  intro newEff st' bf
  have h2_48 : (2 : Nat) ^ 48 < 2 ^ 64 := by omega
  have hMaxAllocVal : MallocngMaxAllocSize = 0x7fffffffffffeffe := rfl
  have hgw0 := hwf.groups_wf g hg
  have ⟨hLast0, hMpG, _, _⟩ := hgw0.2.2.2.1 hSc63
  have hSlotsLen1 : g.slots.length = 1 := by have hL := hgw0.2.2.1; unfold GroupDesc.cnt at hL; omega
  have hOldSt0Nat : (g.slotStart 0).toNat = g.mem.toNat + 16 := by
    simpa using (group_slot_bounds hgw0 hIdx0).2.2.1
  have hTotG : g.totalBytes = g.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpG]
  have hOldG48 : g.mem.toNat + g.maplen * 4096 ≤ 2 ^ 48 :=
    hTotG ▸ (group_slot_bounds hgw0 hIdx0).2.2.2.2.2.2.1
  have hsw0 := hgw0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 0 hIdx0; rw [hSlot0] at hsw0
  have hOldBWf : MallocngBlockWf p oldSz := hsw0.2.2.2.2.1
  have hLoP : (g.slotStart 0).toNat ≤ p.toNat := hsw0.2.2.2.2.2.1
  have hHiP : p.toNat + oldSz ≤ (g.slotEnd 0).toNat := hsw0.2.2.2.2.2.right.left
  have hEn0LeOld : (g.slotEnd 0).toNat ≤ g.mem.toNat + g.maplen * 4096 :=
    hTotG ▸ (group_slot_bounds hgw0 hIdx0).2.2.2.2.2.1
  have hMaxLeOld : max oldSz MallocngMinBlockCost ≤ oldEff := hsw0.2.2.2.2.2.2.2.1
  clear hsw0 hgw0 hTotG
  obtain ⟨hOldEfTot, _⟩ := liveUser_cost_count_le_totals hg hIdx0 hSlot0
  have hResNil : st.reservedMetas = [] := by
    have h := hwf.inflight_wf
    cases hm : st.reservedMetas with | nil => rfl | cons _ _ => rw [hm] at h; simp at h
  generalize hExtraEq : p.toNat - (g.slotStart 0).toNat = extra at hNewPNat hNewSlotFit hNeedResHi hFinalPre hFinalUser hFinalHdr hFinalRes1 hFinalRes5
  have hPNatOld : p.toNat = g.mem.toNat + 16 + extra := by omega
  have hExtraAl : extra % 16 = 0 := by
    have hPAl := hOldBWf.2.1; have hGAl := (hwf.groups_wf g hg).2.2.2.2.2.1; omega
  have hNewBWf : MallocngBlockWf newP newSz :=
    ⟨fun hZ => by have h0 : newP.toNat = 0 := (by rw [hZ]; rfl); omega,
     by omega, by omega, hNewSzHi⟩
  have hMapMul : (needed / 4096) * 4096 = needed := Nat.div_mul_cancel hNeedDvd
  have hMpG' : 0 < needed / 4096 := by
    rcases hNeedDvd with ⟨k, rfl⟩; rw [Nat.mul_div_cancel_left k (by decide)]; omega
  let g' := mkReallocMremapGroup g newBase newP needed newSz newEff
  have hg'Meta : g'.metaPtr = g.metaPtr := rfl
  have hg'MemEq : g'.mem = newBase := rfl
  have hg'MpPos : 0 < g'.maplen := hMpG'
  have hg'LenEq : g'.maplen * 4096 = needed := hMapMul
  obtain ⟨hg'In, hGsCases, hGsKeep, hGsMapMeta, hGsFindSelf, hGsFindNe⟩ :=
    replaceGroup_props st.groups g g' hg hwf.groups_nodup.1 hg'Meta
  have hmAllG : g.metaPtr ∈ allMetaSlots st :=
    (hwf.free_bump_metas_wf.2.2.2.2.2 g.metaPtr).mp
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hg))))
  obtain ⟨maG, hmaG, _, _, _, hmNatG, hmFitG, hMaG48⟩ := metaSlot_in_metaArea hwf hmAllG
  have hMetaGSubMa : ∀ a, InRegion g.metaPtr 40 a → InRegion maG.base 4096 a := fun a ha => by
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  have hDisjMetaNew : ∀ a, InRegion g.metaPtr 40 a → ¬ InRegion newBase needed a := fun a ha hN =>
    not_both_inRegion_of_disjointRegions (hDisjMa maG hmaG) (hMetaGSubMa a ha) hN
  have hMetaBytesLen : g'.metaBytes.length = 40 := GroupDesc.metaBytes_length g'
  have hValInNew : ∀ i (hi : i < needed),
      st'.byteVal (newBase + BitVec.ofNat 64 i) = bsFinal.getD i 0#8 := fun i hi => by
    show writeBytesToMap (writeBytesToMap st.byteVal g.metaPtr g'.metaBytes) newBase bsFinal
      (newBase + BitVec.ofNat 64 i) = _
    have hiF : i < bsFinal.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiF]
    exact writeBytesToMap_in _ newBase bsFinal hiF (by omega)
  have hValOut : ∀ a, ¬ InRegion g.metaPtr 40 a → ¬ InRegion newBase needed a →
      st'.byteVal a = st.byteVal a := fun a hNM hNN => by
    show writeBytesToMap (writeBytesToMap st.byteVal g.metaPtr g'.metaBytes) newBase bsFinal a = _
    rw [writeBytesToMap_out _ newBase bsFinal (by rwa [hFinalLen]),
      writeBytesToMap_out _ g.metaPtr g'.metaBytes (by rwa [hMetaBytesLen])]
  have hOutRead : ∀ (b0 : BitVec 64) (n : Nat), n ≤ 2 ^ 64 →
      (∀ a, InRegion b0 n a → ¬ InRegion g.metaPtr 40 a ∧ ¬ InRegion newBase needed a) →
      readBytesFromMap st'.byteVal b0 n = readBytesFromMap st.byteVal b0 n :=
    fun b0 n hn hD =>
      readBytesFromMap_congr_pred (W := fun a => InRegion g.metaPtr 40 a ∨ InRegion newBase needed a) hn
        (fun a ha hOr => hOr.elim (hD a ha).1 (hD a ha).2)
        (fun a hNOr => hValOut a (fun h1 => hNOr (Or.inl h1)) (fun h2 => hNOr (Or.inr h2)))
  have hMetaSelf : readBytesFromMap st'.byteVal g.metaPtr 40 = g'.metaBytes := by
    have hCongr : readBytesFromMap st'.byteVal g.metaPtr 40 =
        readBytesFromMap (writeBytesToMap st.byteVal g.metaPtr g'.metaBytes) g.metaPtr 40 :=
      readBytesFromMap_congr_pred (W := InRegion newBase bsFinal.length) (by decide)
        (fun a ha hN => hDisjMetaNew a ha (by rwa [hFinalLen] at hN))
        (fun a hNN => writeBytesToMap_out _ newBase bsFinal hNN)
    rw [hCongr]
    have hRW := readBytesFromMap_writeBytesToMap st.byteVal g.metaPtr g'.metaBytes
      (by rw [hMetaBytesLen]; decide)
    rwa [hMetaBytesLen] at hRW
  have hSub3New : newP - 3#64 = newBase + BitVec.ofNat 64 (13 + extra) := by
    apply BitVec.eq_of_toNat_eq
    rw [bv64_sub_toNat (by omega), bv64_add_toNat (by omega)]; omega
  have hAddSzNew : newP + BitVec.ofNat 64 newSz =
      newBase + BitVec.ofNat 64 (16 + extra + newSz) := by
    apply BitVec.eq_of_toNat_eq
    rw [bv64_add_toNat (by omega), bv64_add_toNat (by omega)]; omega
  have hGroupWfSelf : GroupWf st' g' := by
    refine reallocMremap_groupWf_self (hwf.groups_wf g hg) hIdx0 hSlot0 hSc63 hNewBWf
      hNewBaseGe hNewBaseAl hNeedLo hNeedDvd hNewBaseFit
      (by rwa [hExtraEq]) (by rwa [hExtraEq]) (by rwa [hExtraEq]) rfl hNewEffBound
      (by simp only [st', mkReallocMremapSt, MallocngLiveMap.insert_ov, ↓reduceIte])
      (hValInNew (needed - 4) (by omega) |>.trans hFinalEndZero)
      hMetaSelf
      (fun i hi1 hi2 => (hValInNew i (by rw [hExtraEq] at hi1; omega)).trans
        (hFinalPre i (by rwa [← hExtraEq]) (by rwa [← hExtraEq])))
      (by rw [hSub3New, hValInNew (13 + extra) (by omega), hExtraEq]; exact hFinalHdr)
      (fun h1 => by
        rw [hAddSzNew, hValInNew (16 + extra + newSz) (by rw [hExtraEq] at h1; omega)]
        exact hFinalRes1 (by rwa [← hExtraEq]))
      (fun h5 => ?_)
    obtain ⟨h5a, h5b⟩ := hFinalRes5 (by rwa [← hExtraEq])
    refine ⟨(hValInNew ((needed - 4) - 5) (by rw [hExtraEq] at h5; omega)).trans h5a, ?_⟩
    rw [hExtraEq, ← extractLsb_list_eq_unpack32]
    apply List.ext_getElem (by rw [readBytesFromMap_length]; rfl)
    intro j hj1 hj2
    have hj4 : j < 4 := by rwa [readBytesFromMap_length] at hj1
    have hAddrJ : newBase + BitVec.ofNat 64 ((needed - 4) - 4) + BitVec.ofNat 64 j =
        newBase + BitVec.ofNat 64 ((needed - 4) - 4 + j) := by
      apply BitVec.eq_of_toNat_eq
      rw [bv64_add_toNat (by rw [bv64_add_toNat (by omega)]; omega),
        bv64_add_toNat (by omega), bv64_add_toNat (by omega)]; omega
    rw [readBytesFromMap_getElem _ _ _ _ hj1, hAddrJ,
      hValInNew ((needed - 4) - 4 + j) (by rw [hExtraEq] at h5; omega),
      h5b j hj4]
    match j, hj4 with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
  have hNewPNotOther : ∀ gx ∈ st.groups, gx.metaPtr ≠ g.metaPtr →
      ∀ j (hj : j < gx.slots.length) (m ef : Nat), gx.slots[j]'hj ≠ .liveUser newP m ef := by
    intro gx hgx hNe j hj m ef hSl
    obtain ⟨rg, hrg, hMpRg, hRgNe, hRgLo, hRgHi⟩ :=
      non_sc63_group_in_other_root hwf hg hSc63 48 gx hgx (by omega) hNe
    have hgwx := hwf.groups_wf gx hgx
    have hswx := hgwx.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj
    rw [hSl] at hswx
    have hStLe := hswx.2.2.2.2.2.1
    have hEnGe := hswx.2.2.2.2.2.2.1
    have hStNat := (group_slot_bounds hgwx hj).2.2.1
    have hEnLeTot := (group_slot_bounds hgwx hj).2.2.2.2.2.1
    have hRg48 : rg.mem.toNat + rg.maplen * 4096 ≤ 2 ^ 48 := by
      have h := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1
      have hT : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpRg]
      rwa [hT] at h
    have hPm1Nat : (newP - 1#64).toNat = newP.toNat - 1 := bv64_sub_toNat (by omega)
    have hInNew : InRegion newBase needed (newP - 1#64) :=
      (inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩
    have hInRg : InRegion rg.mem (rg.maplen * 4096) (newP - 1#64) :=
      (inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩
    exact not_both_inRegion_of_disjointRegions (hDisjRg rg hrg hMpRg hRgNe) hInRg hInNew
  have hFreshNewP : newP = p ∨ st.liveMap newP = none := by
    by_cases hEqP : newP = p
    · exact Or.inl hEqP
    · refine Or.inr (Classical.byContradiction fun hSome => ?_)
      cases hL : st.liveMap newP with
      | none => exact hSome hL
      | some m =>
        obtain ⟨gx, hgx, j, hj, ef, hSl⟩ := (hwf.liveMap_wf newP m).mp hL
        by_cases hM : gx.metaPtr = g.metaPtr
        · have r := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hgx hg hM
          subst r
          have hj0 : j = 0 := by omega
          subst hj0
          rw [hSlot0] at hSl; injection hSl with h1 _ _; exact hEqP h1.symm
        · exact hNewPNotOther gx hgx hM j hj m ef hSl
  obtain ⟨hP123, hPRgOld, hCross123Old⟩ := pairwiseDisjoint_append hwf.regions_disjoint.1
  obtain ⟨hP12, _, _⟩ := pairwiseDisjoint_append hP123
  obtain ⟨hPMa, _, _⟩ := pairwiseDisjoint_append hP12
  have hGMemRg : (g.mem, g.maplen * 4096) ∈
      (st.groups.filter fun x => decide (0 < x.maplen)).map (fun x => (x.mem, x.maplen * 4096)) :=
    List.mem_map_of_mem (List.mem_filter.mpr ⟨hg, decide_eq_true hMpG⟩)
  have hOtherMetaDisj : ∀ m' ∈ allMetaSlots st, m' ≠ g.metaPtr →
      ∀ a, InRegion m' 40 a → ¬ InRegion g.metaPtr 40 a ∧ ¬ InRegion newBase needed a := by
    intro m' hm' hNeM a ha
    obtain ⟨ma', hma', _, _, _, hm'Nat, hm'Fit, hMa'48⟩ := metaSlot_in_metaArea hwf hm'
    have haMa' : InRegion ma'.base 4096 a := by
      have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
      exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
    exact ⟨fun hMG => metaSlots_disjoint hwf hm' hmAllG hNeM ha hMG,
      fun hNB => not_both_inRegion_of_disjointRegions (hDisjMa ma' hma') haMa' hNB⟩
  have hOtherGroupOut : ∀ gx ∈ st.groups, gx.metaPtr ≠ g.metaPtr →
      ∀ a, gx.mem.toNat ≤ a.toNat → a.toNat < gx.mem.toNat + gx.totalBytes →
      st'.byteVal a = st.byteVal a := by
    intro gx hgx hNe a hLoA hHiA
    obtain ⟨rg, hrg, hMpRg, hRgNe, hRgLo, hRgHi⟩ :=
      non_sc63_group_in_other_root hwf hg hSc63 48 gx hgx (by omega) hNe
    have hRg48 : rg.mem.toNat + rg.maplen * 4096 ≤ 2 ^ 48 := by
      have h := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1
      have hT : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpRg]
      rwa [hT] at h
    have haRg : InRegion rg.mem (rg.maplen * 4096) a :=
      (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
    exact hValOut a
      (fun hMG => not_both_inRegion_of_disjointRegions
        (metaArea_disjoint_root_group hwf hmaG hrg hMpRg) (hMetaGSubMa a hMG) haRg)
      (fun hNB => not_both_inRegion_of_disjointRegions (hDisjRg rg hrg hMpRg hRgNe) haRg hNB)
  have hDynSt' : dynamicRootRegions st' =
      st.metaAreas.map (fun ma => (ma.base, 4096)) ++
      st.guardPages.map (fun gp => (gp, 4096)) ++
      st.availMetaPages.map (fun ap => (ap, 4096)) ++
      ((replaceGroup st.groups g.metaPtr g').filter fun x => decide (0 < x.maplen)).map
        (fun x => (x.mem, x.maplen * 4096)) := rfl
  have hPairwiseSt' : PairwiseDisjointRegions (dynamicRootRegions st') := by
    rw [hDynSt']
    refine pairwiseDisjoint_append_intro hP123
      (pairwiseDisjoint_replaceGroup_root (g := g) (g' := g') hg'MpPos st.groups
        hwf.groups_nodup.1 hPRgOld (by rw [hg'MemEq, hg'LenEq]; exact hDisjRg)) ?_
    intro x hx y hy
    obtain ⟨rg, hrgF, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hrgRep, hMpB⟩ := List.mem_filter.mp hrgF
    rcases hGsCases rg hrgRep with rfl | ⟨_, hrgOld⟩
    · rw [hg'MemEq, hg'LenEq]
      rcases List.mem_append.mp hx with h12 | hAp
      · rcases List.mem_append.mp h12 with hMa | hGp
        · obtain ⟨ma, hma, rfl⟩ := List.mem_map.mp hMa; exact hDisjMa ma hma
        · obtain ⟨gp, hgp, rfl⟩ := List.mem_map.mp hGp; exact hDisjGp gp hgp
      · obtain ⟨ap, hap, rfl⟩ := List.mem_map.mp hAp; exact hDisjAp ap hap
    · exact hCross123Old x hx _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hrgOld, hMpB⟩))
  have hGSlotsSingleton : g.slots = [.liveUser p oldSz oldEff] := by
    rcases hS : g.slots with _ | ⟨s0, _ | _⟩
    · simp [hS] at hSlotsLen1
    · have h0 : s0 = .liveUser p oldSz oldEff := by simpa [hS] using hSlot0
      rw [h0]
    · simp [hS] at hSlotsLen1
  have hLiveCntEq : totalLiveCount st' = totalLiveCount st := by
    have hS := replaceGroup_sum_eq st.groups g g' hg hwf.groups_nodup.1
      (fun x => (x.slots.map slotLiveCount).sum)
    unfold totalLiveCount
    dsimp only [st', g', mkReallocMremapSt, mkReallocMremapGroup] at hS ⊢
    rw [hGSlotsSingleton] at hS
    simp only [List.map, List.sum_cons, List.sum_nil, slotLiveCount] at hS; omega
  have hEffSumEq : totalLiveEffCost st' + oldEff = totalLiveEffCost st + newEff := by
    have hS := replaceGroup_sum_eq st.groups g g' hg hwf.groups_nodup.1
      (fun x => (x.slots.map slotEffCost).sum)
    unfold totalLiveEffCost
    dsimp only [st', g', mkReallocMremapSt, mkReallocMremapGroup] at hS ⊢
    rw [hGSlotsSingleton] at hS
    simp only [List.map, List.sum_cons, List.sum_nil, slotEffCost] at hS; omega
  have hDynLenEq : (dynamicRootRegions st').length = (dynamicRootRegions st).length := by
    rw [hDynSt']; unfold dynamicRootRegions
    simp only [List.length_append, List.length_map]
    rw [replaceGroup_filter_pos_length hMpG hg'MpPos st.groups hwf.groups_nodup.1 hg]
  have hCount' : MallocngCountIvsWF bf (dynamicRootRegions st') st' := by
    obtain ⟨hC1, hC2, hC3, hC4, hC5, hC6⟩ := hCount; rw [hC3] at hC4
    have hC6' : Cost.GroupsGrpBound (b.peakCount + 6) st'.groups :=
      hC6.map_ite g.metaPtr fun _ hs => absurd hs (by
        dsimp only [g', mkReallocMremapGroup]; rw [hSc63]; decide)
    simp only [MallocngCountIvsWF, bf, mallocngReallocBudget, ↓reduceIte]
    exact ⟨by omega, by omega, trivial, by omega,
      Nat.le_trans hC5 (Nat.add_le_add_left (Nat.div_le_div_right (by omega)) 1),
      hC6'.mono (by omega)⟩
  have hPInOldG : ∀ a, InRegion p oldSz a → InRegion g.mem (g.maplen * 4096) a := fun a ha => by
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  have hNewPInNew : ∀ a, InRegion newP newSz a → InRegion newBase needed a := fun a ha => by
    have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp ha
    exact (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
  have hOtherCarvDisjNew : ∀ gx ∈ st.groups, gx.metaPtr ≠ g.metaPtr →
      ∀ s ∈ gx.slots, ∀ a,
        (match s with | .liveUser uP rS _ => InRegion uP rS a | _ => False) →
        ¬ InRegion newBase needed a ∧ ¬ InRegion g.mem (g.maplen * 4096) a := by
    intro gx hgx hNe s hs a hCarv
    cases s with
    | freeAvail | freeInactive | claimed | liveNested _ => cases hCarv
    | liveUser uP rS _ =>
      obtain ⟨j, hj, hEqS⟩ := List.getElem_of_mem hs
      obtain ⟨rg, hrg, hMpRg, hRgNe, hRgLo, hRgHi⟩ :=
        non_sc63_group_in_other_root hwf hg hSc63 48 gx hgx (by omega) hNe
      have hgwx := hwf.groups_wf gx hgx
      have hswx := hgwx.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj
      rw [hEqS] at hswx
      have hStLe := hswx.2.2.2.2.2.1
      have hEnGe := hswx.2.2.2.2.2.2.1
      have hStNat := (group_slot_bounds hgwx hj).2.2.1
      have hEnLeTot := (group_slot_bounds hgwx hj).2.2.2.2.2.1
      have hRg48 : rg.mem.toNat + rg.maplen * 4096 ≤ 2 ^ 48 := by
        have h := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1
        have hT : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpRg]
        rwa [hT] at h
      have ⟨hc1, hc2⟩ := (inRegion_iff_toNat (by omega) a).mp hCarv
      have haRg : InRegion rg.mem (rg.maplen * 4096) a :=
        (inRegion_iff_toNat (by omega) a).mpr ⟨by omega, by omega⟩
      have hDisjRgOld : DisjointRegions rg.mem (rg.maplen * 4096) g.mem (g.maplen * 4096) :=
        pairwiseDisjoint_map_ne
          (f := fun x : GroupDesc => (x.mem, x.maplen * 4096))
          hPRgOld
          (List.mem_filter.mpr ⟨hrg, decide_eq_true hMpRg⟩)
          (List.mem_filter.mpr ⟨hg, decide_eq_true hMpG⟩)
          (fun hMemEq => hRgNe (mem_groups_eq_of_mem hwf.groups_nodup.2 hrg hg hMemEq ▸ rfl))
      exact ⟨fun hNB => not_both_inRegion_of_disjointRegions (hDisjRg rg hrg hMpRg hRgNe) haRg hNB,
        fun hOG => not_both_inRegion_of_disjointRegions hDisjRgOld haRg hOG⟩
  have hRwOut : ∀ a, ¬ InRegion g.metaPtr 40 a → ¬ InRegion g.mem (g.maplen * 4096) a →
      ¬ InRegion newBase needed a →
      (OwnedRwByte st' a ↔ OwnedRwByte st a) ∧ st'.byteVal a = st.byteVal a := by
    intro a hNM hNOG hNNB
    refine ⟨?_, hValOut a hNM hNNB⟩
    have hGrpEq : (∃ x ∈ st'.groups, 0 < x.maplen ∧ InRegion x.mem (x.maplen * 4096) a) ↔
        (∃ x ∈ st.groups, 0 < x.maplen ∧ InRegion x.mem (x.maplen * 4096) a) := by
      constructor
      · rintro ⟨x, hx, hMp, hIn⟩
        rcases hGsCases x hx with rfl | ⟨_, hxOld⟩
        · exact False.elim (hNNB (by rwa [hg'MemEq, hg'LenEq] at hIn))
        · exact ⟨x, hxOld, hMp, hIn⟩
      · rintro ⟨x, hx, hMp, hIn⟩
        by_cases hE : x.metaPtr = g.metaPtr
        · have r := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE
          subst r; exact False.elim (hNOG hIn)
        · exact ⟨x, hGsKeep x hx hE, hMp, hIn⟩
    have hCarvEq : CarvedUserByte st' a ↔ CarvedUserByte st a := by
      unfold CarvedUserByte; constructor
      · rintro ⟨x, hx, s, hs, hSub⟩
        rcases hGsCases x hx with rfl | ⟨_, hxOld⟩
        · simp only [g', mkReallocMremapGroup, List.mem_singleton] at hs
          subst hs; exact False.elim (hNNB (hNewPInNew a hSub))
        · exact ⟨x, hxOld, s, hs, hSub⟩
      · rintro ⟨x, hx, s, hs, hSub⟩
        by_cases hE : x.metaPtr = g.metaPtr
        · have r := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE
          subst r; rw [hGSlotsSingleton, List.mem_singleton] at hs
          subst hs; exact False.elim (hNOG (hPInOldG a hSub))
        · exact ⟨x, hGsKeep x hx hE, s, hs, hSub⟩
    unfold OwnedRwByte
    have hMetaEq : st'.metaAreas = st.metaAreas := rfl
    have hResEq : CarvedMetaByte st' a = CarvedMetaByte st a := rfl
    rw [hMetaEq, hGrpEq, hCarvEq, hResEq]
  have hRwNew : ∀ a, InRegion newBase needed a →
      (OwnedRwByte st' a ↔ ¬ InRegion newP newSz a) := by
    intro a haNB
    unfold OwnedRwByte
    have hHasGrp : (∃ ma ∈ st'.metaAreas, InRegion ma.base 4096 a) ∨
        (∃ x ∈ st'.groups, 0 < x.maplen ∧ InRegion x.mem (x.maplen * 4096) a) :=
      Or.inr ⟨g', hg'In, hg'MpPos, by rwa [hg'MemEq, hg'LenEq]⟩
    have hCarvIff : CarvedUserByte st' a ↔ InRegion newP newSz a := by
      unfold CarvedUserByte; constructor
      · rintro ⟨x, hx, s, hs, hSub⟩
        rcases hGsCases x hx with rfl | ⟨hNe, hxOld⟩
        · simp only [g', mkReallocMremapGroup, List.mem_singleton] at hs
          subst hs; exact hSub
        · exact False.elim ((hOtherCarvDisjNew x hxOld hNe s hs a (by cases s <;> exact hSub)).1 haNB)
      · intro hSub
        exact ⟨g', hg'In, .liveUser newP newSz newEff,
          by simp [g', mkReallocMremapGroup], hSub⟩
    have hNoMeta : ¬ CarvedMetaByte st' a := by
      show ¬ CarvedMetaByte st a; simp [CarvedMetaByte, hResNil]
    exact ⟨fun ⟨_, hNC, _⟩ hIn => hNC (hCarvIff.mpr hIn),
      fun hNIn => ⟨hHasGrp, fun hC => hNIn (hCarvIff.mp hC), hNoMeta⟩⟩
  have hUserReadK : ∀ k (hk : k < min origBs.length newSz),
      st'.byteVal (newP + BitVec.ofNat 64 k) = origBs[k]'(by omega) := by
    intro k hk
    have hAddr : newP + BitVec.ofNat 64 k = newBase + BitVec.ofNat 64 (16 + extra + k) := by
      apply BitVec.eq_of_toNat_eq
      rw [bv64_add_toNat (by omega), bv64_add_toNat (by omega)]; omega
    rw [hAddr, hValInNew (16 + extra + k) (by omega)]
    exact hFinalUser k hk
  refine ⟨hNewBWf, hFreshNewP, hCount', ?_, hRwOut, hRwNew, hUserReadK⟩
  refine {
    base_wf := hwf.base_wf
    brk_bounds := hwf.brk_bounds
    ctx_lens := hwf.ctx_lens
    initDone_wf := hwf.initDone_wf
    initZero_wf := fun h0 => by exfalso; rw [(hwf.initZero_wf h0).2.2.2.2.2.2.2.2.2.1] at hg; cases hg
    bounces_wf := hwf.bounces_wf
    usage_wf := fun sc hsc => by
      dsimp only [st', mkReallocMremapSt]
      rw [replaceGroup_filter_sc_cnt_sum st.groups g g' hg hwf.groups_nodup.1 rfl rfl sc]
      exact hwf.usage_wf sc hsc
    brk_mode_wf := hwf.brk_mode_wf
    metaAreas_wf := ⟨hwf.metaAreas_wf.1, fun ma hma => by
      obtain ⟨h1, h2, h3, h4⟩ := hwf.metaAreas_wf.2.1 ma hma
      have hHdrDisj : ∀ a, InRegion ma.base 24 a →
          ¬ InRegion g.metaPtr 40 a ∧ ¬ InRegion newBase needed a := by
        intro a ha24
        have ⟨ha1, ha2⟩ := (inRegion_iff_toNat (by omega) a).mp ha24
        have ha4096 : InRegion ma.base 4096 a :=
          (inRegion_iff_toNat (by omega) a).mpr ⟨ha1, by omega⟩
        refine ⟨fun hMG => ?_,
          fun hNB => not_both_inRegion_of_disjointRegions (hDisjMa ma hma) ha4096 hNB⟩
        have ⟨hm1, hm2⟩ := (inRegion_iff_toNat (by omega) a).mp hMG
        by_cases hEqB : maG.base = ma.base
        · rw [hEqB] at hmNatG; omega
        · exact not_both_inRegion_of_disjointRegions
            (pairwiseDisjoint_map_ne (f := fun x : MetaAreaDesc => (x.base, 4096)) hPMa hma hmaG
              (fun hE => hEqB hE.symm))
            ha4096 (hMetaGSubMa a hMG)
      exact ⟨h1, h2, h3, (hOutRead ma.base 24 (by decide) hHdrDisj).trans h4⟩,
      hwf.metaAreas_wf.2.2⟩
    guard_avail_wf := ⟨hwf.guard_avail_wf.1, hwf.guard_avail_wf.2.1, hwf.guard_avail_wf.2.2.1,
      fun ap hap => by
        obtain ⟨h1, h2, h3, h4⟩ := hwf.guard_avail_wf.2.2.2 ap hap
        have hApMem123 : (ap, 4096) ∈
            st.metaAreas.map (fun m => (m.base, 4096)) ++
            st.guardPages.map (fun gp => (gp, 4096)) ++
            st.availMetaPages.map (fun ap => (ap, 4096)) :=
          List.mem_append_right _ (List.mem_map_of_mem hap)
        have hMaGMem123 : (maG.base, 4096) ∈
            st.metaAreas.map (fun m => (m.base, 4096)) ++
            st.guardPages.map (fun gp => (gp, 4096)) ++
            st.availMetaPages.map (fun ap => (ap, 4096)) :=
          List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hmaG))
        obtain ⟨_, _, hCross12Ap⟩ := pairwiseDisjoint_append hP123
        have hDisjMaGAp : DisjointRegions maG.base 4096 ap 4096 :=
          hCross12Ap _ (List.mem_append_left _ (List.mem_map_of_mem hmaG)) _ (List.mem_map_of_mem hap)
        exact ⟨h1, h2, h3, (hOutRead ap 4096 (by decide) fun a haAp =>
          ⟨fun hMG => not_both_inRegion_of_disjointRegions hDisjMaGAp (hMetaGSubMa a hMG) haAp,
           fun hNB => not_both_inRegion_of_disjointRegions (hDisjAp ap hap) haAp hNB⟩).trans h4⟩⟩
    inflight_wf := by
      have hS := replaceGroup_sum_eq st.groups g g' hg hwf.groups_nodup.1
        (fun x => (x.slots.filter SlotState.isClaimed).length)
      have hI := hwf.inflight_wf
      unfold totalClaimedSlots at hI ⊢
      dsimp only [st', g', mkReallocMremapSt, mkReallocMremapGroup] at hS ⊢
      rw [hGSlotsSingleton] at hS
      simp only [List.filter, SlotState.isClaimed, List.length] at hS
      omega
    free_bump_metas_wf := by
      obtain ⟨hDll, hFmB, hBumpC, hBmB, hUFNd, hUFIff⟩ := hwf.free_bump_metas_wf
      have hNd12 := (List.nodup_append.mp hUFNd).1
      have hNd1 := (List.nodup_append.mp hNd12).1
      refine ⟨hDll, fun fm hfm => ?_, hBumpC, fun bm hbm => ?_,
        by dsimp only [st', mkReallocMremapSt]; rw [hGsMapMeta]; exact hUFNd,
        fun m => by dsimp only [st', mkReallocMremapSt, allMetaSlots]; rw [hGsMapMeta]; exact hUFIff m⟩
      · have hNe : fm.ptr ≠ g.metaPtr := fun hE =>
          (List.nodup_append.mp hNd1).2.2 g.metaPtr (List.mem_map_of_mem hg) fm.ptr (List.mem_map_of_mem hfm) hE.symm
        have hAll := (hUFIff fm.ptr).mp (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hfm))))
        exact (hOutRead fm.ptr 40 (by decide) (hOtherMetaDisj fm.ptr hAll hNe)).trans (hFmB fm hfm)
      · have hNe : bm ≠ g.metaPtr := fun hE =>
          (List.nodup_append.mp hNd12).2.2 g.metaPtr (List.mem_append_left _ (List.mem_map_of_mem hg)) bm hbm hE.symm
        have hAll := (hUFIff bm).mp (List.mem_append_left _ (List.mem_append_right _ hbm))
        exact (hOutRead bm 40 (by decide) (hOtherMetaDisj bm hAll hNe)).trans (hBmB bm hbm)
    groups_nodup := by
      refine ⟨by dsimp only [st', mkReallocMremapSt]; rw [hGsMapMeta]; exact hwf.groups_nodup.1, ?_⟩
      dsimp only [st', mkReallocMremapSt]
      refine nodup_map_mem_replaceGroup st.groups hwf.groups_nodup.1 hwf.groups_nodup.2 ?_
      intro x hx hNe hMemEq
      obtain ⟨rg, hrg, hMpRg, hRgNe, hRgLo, hRgHi⟩ :=
        non_sc63_group_in_other_root hwf hg hSc63 48 x hx (by omega) hNe
      have hxw := hwf.groups_wf x hx
      have hGe12 : 12 ≤ x.totalBytes := by have := hxw.2.2.2.2.2.2.2.1; omega
      have hRg48 : rg.mem.toNat + rg.maplen * 4096 ≤ 2 ^ 48 := by
        have h := (hwf.groups_wf rg hrg).2.2.2.2.2.2.1
        have hT : rg.totalBytes = rg.maplen * 4096 := by simp [GroupDesc.totalBytes, hMpRg]
        rwa [hT] at h
      have hEqNB : x.mem = newBase := hMemEq.trans hg'MemEq
      have haRg : InRegion rg.mem (rg.maplen * 4096) newBase :=
        (inRegion_iff_toNat (by omega) newBase).mpr ⟨by rw [← hEqNB]; omega, by rw [← hEqNB]; omega⟩
      have haNB : InRegion newBase needed newBase :=
        (inRegion_iff_toNat (by omega) newBase).mpr ⟨Nat.le_refl _, by omega⟩
      exact not_both_inRegion_of_disjointRegions (hDisjRg rg hrg hMpRg hRgNe) haRg haNB
    groups_wf := fun x' hx' => by
      rcases hGsCases x' hx' with rfl | ⟨hNeM, hxOld⟩
      · exact hGroupWfSelf
      · have hxw := hwf.groups_wf x' hxOld
        have hGe12 : 12 ≤ x'.totalBytes := by have := hxw.2.2.2.2.2.2.2.1; omega
        have hX48 := hxw.2.2.2.2.2.2.1
        have hAdd8 : (x'.mem + 8#64).toNat = x'.mem.toNat + 8 := bv64_add_toNat (by omega)
        have hAllX := (hwf.free_bump_metas_wf.2.2.2.2.2 x'.metaPtr).mp
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hxOld))))
        have hSlotEndOut : ∀ k : Nat, ∀ y ∈ st.groups, (y.sc < 48 → 48 - y.sc ≤ k) → y.metaPtr ≠ g.metaPtr →
            ∃ rg ∈ st.groups, 0 < rg.maplen ∧ rg.metaPtr ≠ g.metaPtr ∧
              rg.mem.toNat ≤ y.mem.toNat ∧ (y.slotEnd y.lastIdx).toNat < rg.mem.toNat + rg.maplen * 4096 := by
          intro k; induction k with
          | zero =>
            intro y hy hB hNe; have hyw := hwf.groups_wf y hy
            rcases hyw.1 with h48 | h63
            · exfalso; have := hB h48; omega
            · have hMp := (hyw.2.2.2.1 h63).2.1
              have hTot : y.totalBytes = y.maplen * 4096 := by simp [GroupDesc.totalBytes, hMp]
              have hEn := (group_slot_bounds hyw (by rw [hyw.2.2.1]; unfold GroupDesc.cnt; omega : y.lastIdx < y.slots.length)).2.2.2.2.1
              have hLt := hyw.2.2.2.2.2.2.2.2.1 hMp
              exact ⟨y, hy, hMp, hNe, Nat.le_refl _, by unfold GroupDesc.cnt at hLt; omega⟩
          | succ k ih =>
            intro y hy hB hNe; have hyw := hwf.groups_wf y hy
            by_cases hMp : 0 < y.maplen
            · have hTot : y.totalBytes = y.maplen * 4096 := by simp [GroupDesc.totalBytes, hMp]
              have hEn := (group_slot_bounds hyw (by rw [hyw.2.2.1]; unfold GroupDesc.cnt; omega : y.lastIdx < y.slots.length)).2.2.2.2.1
              have hLt := hyw.2.2.2.2.2.2.2.2.1 hMp
              exact ⟨y, hy, hMp, hNe, Nat.le_refl _, by unfold GroupDesc.cnt at hLt; omega⟩
            · obtain ⟨_, pg, hpg, pIdx, hp, _, _, hScLt, hPg24, _, hPgLo, hPgHi, _⟩ :=
                hyw.2.2.2.2.2.2.2.2.2.2.2.2.1 (by omega)
              have hpgw := hwf.groups_wf pg hpg
              have hStPg := (group_slot_bounds hpgw hp).2.2.1
              have hEnPg := (group_slot_bounds hpgw hp).2.2.2.2.1
              have hEnLastPg := (group_slot_bounds hpgw (by rw [hpgw.2.2.1]; unfold GroupDesc.cnt; omega : pg.lastIdx < pg.slots.length)).2.2.2.2.1
              have hPIdxLe : pIdx ≤ pg.lastIdx := by have := hpgw.2.2.1; unfold GroupDesc.cnt at this; omega
              have hMonoPg : (pIdx + 1) * pg.stride ≤ (pg.lastIdx + 1) * pg.stride := Nat.mul_le_mul_right _ (by omega)
              have hEnYLe := (group_slot_bounds hyw (by rw [hyw.2.2.1]; unfold GroupDesc.cnt; omega : y.lastIdx < y.slots.length)).2.2.2.2.2.1
              have hYTot : y.totalBytes = y.nestedCap := by simp [GroupDesc.totalBytes, show ¬ 0 < y.maplen from hMp]
              have hPgNe : pg.metaPtr ≠ g.metaPtr := fun hE => by
                have r := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg hg hE; rw [r, hSc63] at hPg24; omega
              have hY48 : y.sc < 48 := by rcases hyw.1 with h1 | h2; exact h1; have := (hyw.2.2.2.1 h2).2.1; omega
              obtain ⟨rg, hrg, hMpRg, hRgNe, hRgLo, hRgLt⟩ := ih pg hpg (fun _ => by have := hB hY48; omega) hPgNe
              exact ⟨rg, hrg, hMpRg, hRgNe, by omega, by omega⟩
        obtain ⟨rgX, hrgX, hMpRgX, hRgXNe, hRgXLo, hRgXLt⟩ :=
          hSlotEndOut 48 x' hxOld (by omega) hNeM
        have hRgX48 : rgX.mem.toNat + rgX.maplen * 4096 ≤ 2 ^ 48 := by
          have h := (hwf.groups_wf rgX hrgX).2.2.2.2.2.2.1
          have hT : rgX.totalBytes = rgX.maplen * 4096 := (by simp [GroupDesc.totalBytes, hMpRgX]); rwa [hT] at h
        have hEnXNat := (group_slot_bounds hxw (by rw [hxw.2.2.1]; unfold GroupDesc.cnt; omega : x'.lastIdx < x'.slots.length)).2.2.2.2.1
        have haEnRg : InRegion rgX.mem (rgX.maplen * 4096) (x'.slotEnd x'.lastIdx) :=
          (inRegion_iff_toNat (by omega) _).mpr ⟨by omega, by omega⟩
        have hEndEq : st'.byteVal (x'.slotEnd x'.lastIdx) = st.byteVal (x'.slotEnd x'.lastIdx) :=
          hValOut _
            (fun hMG => not_both_inRegion_of_disjointRegions (metaArea_disjoint_root_group hwf hmaG hrgX hMpRgX) (hMetaGSubMa _ hMG) haEnRg)
            (fun hNB => not_both_inRegion_of_disjointRegions (hDisjRg rgX hrgX hMpRgX hRgXNe) haEnRg hNB)
        have hMem8Eq : readBytesFromMap st'.byteVal x'.mem 8 = readBytesFromMap st.byteVal x'.mem 8 :=
          readBytesFromMap_congr_pred (W := fun a => ¬ InRegion x'.mem 8 a) (by decide)
            (fun _ ha hN => hN ha)
            (fun a hNN => by
              have ⟨h1, h2⟩ := (inRegion_iff_toNat (by omega) a).mp (Classical.not_not.mp hNN)
              exact hOtherGroupOut x' hxOld hNeM a h1 (by omega))
        have hParLift : x'.maplen = 0 →
            1 ≤ x'.lastIdx ∧ ∃ pg ∈ st'.groups, ∃ pIdx : Nat, ∃ hp : pIdx < pg.slots.length,
              x'.parentMeta = some pg.metaPtr ∧ pg.sc < 48 ∧ x'.sc < pg.sc ∧ pg.sc ≤ 24 ∧
              pg.slots[pIdx]'hp = .liveNested x'.metaPtr ∧
              (pg.slotStart pIdx).toNat ≤ x'.mem.toNat ∧ x'.mem.toNat + x'.nestedCap ≤ (pg.slotEnd pIdx).toNat ∧
              x'.nestedCap = slotStride pg.sc - 4 := fun hM0 => by
          obtain ⟨hL1, pg, hpg, pIdx, hp, hPM, h1, h2, h3, hPS, hLoP, hHiP, hNC⟩ :=
            hxw.2.2.2.2.2.2.2.2.2.2.2.2.1 hM0
          have hPgNe : pg.metaPtr ≠ g.metaPtr := fun hE => by
            have r := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hpg hg hE; rw [r, hSc63] at h3; omega
          exact ⟨hL1, pg, hGsKeep pg hpg hPgNe, pIdx, hp, hPM, h1, h2, h3, hPS, hLoP, hHiP, hNC⟩
        refine ⟨hxw.1, hxw.2.1, hxw.2.2.1, hxw.2.2.2.1, hxw.2.2.2.2.1, hxw.2.2.2.2.2.1,
          hxw.2.2.2.2.2.2.1, hxw.2.2.2.2.2.2.2.1, hxw.2.2.2.2.2.2.2.2.1,
          hEndEq.trans hxw.2.2.2.2.2.2.2.2.2.1, hxw.2.2.2.2.2.2.2.2.2.2.1,
          hxw.2.2.2.2.2.2.2.2.2.2.2.1, hParLift,
          hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          (hOutRead x'.metaPtr 40 (by decide) (hOtherMetaDisj x'.metaPtr hAllX hNeM)).trans
            hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hMem8Eq.trans hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          (hOtherGroupOut x' hxOld hNeM (x'.mem + 8#64) (by omega) (by omega)).trans
            hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          fun j hj => ?_⟩
        have ⟨_, hStorJ, hStJ, _, hEnJ, hEnLeJ, hTotX48, _, _⟩ := group_slot_bounds hxw hj
        exact slotWf_lift_other
          (fun cg hcg hPar => hGsKeep cg hcg fun hE => by
            have r := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hcg hg hE
            rw [r] at hPar; exact hPar ((hwf.groups_wf g hg).2.2.2.2.2.2.2.2.2.2.1.mp hMpG))
          (fun a h1 h2 => hOtherGroupOut x' hxOld hNeM a h1 (Nat.lt_of_lt_of_le h2 hEnLeJ))
          ⟨hStorJ, hStJ, hEnJ, (group_stride_pos_and_align hxw).1, by omega⟩
          (hxw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 j hj)
          (hOv := fun u r e hS => by
            have hUNe : u ≠ newP := fun hE => hNewPNotOther x' hxOld hNeM j hj r e (hE ▸ hS)
            simp only [st', mkReallocMremapSt, MallocngLiveMap.insert_ov, MallocngLiveMap.erase_ov,
              hUNe, ↓reduceIte])
    regions_disjoint := ⟨hPairwiseSt', trivial⟩
    active_wf := fun sc h1 h2 => by
      have haw := hwf.active_wf sc h1 h2
      have hFmEq : ∀ ms : List (BitVec 64),
          ms.filterMap (fun m => (findGroupByMeta st' m).map fun x => (x.metaPtr, x.prev, x.next)) =
          ms.filterMap (fun m => (findGroupByMeta st m).map fun x => (x.metaPtr, x.prev, x.next)) := by
        intro ms; induction ms with
        | nil => rfl
        | cons m tl ih =>
          simp only [List.filterMap]
          by_cases hmE : m = g.metaPtr
          · subst hmE
            have hFOld := findGroupByMeta_of_mem hwf.groups_nodup.1 hg
            have hFNew : findGroupByMeta st' g.metaPtr = some g' := hGsFindSelf
            rw [hFNew, hFOld, ih]; rfl
          · have hFNe : findGroupByMeta st' m = findGroupByMeta st m := hGsFindNe m hmE
            rw [hFNe, ih]
      have hToOld : ∀ x ∈ st'.groups, ∃ y ∈ st.groups,
          y.metaPtr = x.metaPtr ∧ y.sc = x.sc ∧ y.activeIdx = x.activeIdx ∧ y.lastIdx = x.lastIdx := fun x hx =>
        (hGsCases x hx).elim (fun hE => by subst hE; exact ⟨g, hg, rfl, rfl, rfl, rfl⟩)
          (fun ⟨_, hxO⟩ => ⟨x, hxO, rfl, rfl, rfl, rfl⟩)
      refine ⟨fun m hm => ?_, by rw [hFmEq]; exact haw.2.1, by rw [hFmEq]; exact haw.2.2.1,
        fun x hx hSc => (hGsCases x hx).elim (fun hE => by subst hE; exact haw.2.2.2.1 g hg hSc)
          (fun ⟨_, hxO⟩ => haw.2.2.2.1 x hxO hSc),
        fun i hi hPos x hx hM => (hGsCases x hx).elim (fun hE => by subst hE; exact haw.2.2.2.2.1 i hi hPos g hg hM)
          (fun ⟨_, hxO⟩ => haw.2.2.2.2.1 i hi hPos x hxO hM),
        fun x1 hx1 x2 hx2 hS1 hS2 hA1 hA2 => ?_, fun x hx hSc hA => ?_⟩
      · obtain ⟨x, hx, rfl, rfl⟩ := haw.1 m hm
        exact if hE : x.metaPtr = g.metaPtr then
          ⟨g', hg'In, (congrArg GroupDesc.metaPtr (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE)).symm,
            (congrArg GroupDesc.sc (mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE)).symm⟩
        else ⟨x, hGsKeep x hx hE, rfl, rfl⟩
      · obtain ⟨y1, hy1, hM1, hY1S, hY1A, hY1L⟩ := hToOld x1 hx1
        obtain ⟨y2, hy2, hM2, hY2S, hY2A, hY2L⟩ := hToOld x2 hx2
        exact hM1.symm.trans ((haw.2.2.2.2.2.1 y1 hy1 y2 hy2 (hY1S.trans hS1) (hY2S.trans hS2)
          (by omega) (by omega)).trans hM2)
      · obtain ⟨y, hy, hM, hYS, hYA, hYL⟩ := hToOld x hx
        rw [← hM]; exact haw.2.2.2.2.2.2 y hy (hYS.trans hSc) (by omega)
    liveMap_wf := fun q m => by
      show ((st.liveMap.erase p).insert newP newSz (st.liveMap.ov p)).req q = some m ↔ _
      simp only [MallocngLiveMap.insert_req, MallocngLiveMap.erase_req]
      by_cases hqNew : q = newP
      · subst hqNew; simp only [↓reduceIte, Option.some.injEq]
        exact ⟨fun h => by subst h; exact ⟨g', hg'In, 0, by simp [g', mkReallocMremapGroup], newEff, rfl⟩,
          fun ⟨x, hx, j, hj, ef, hSl⟩ => (hGsCases x hx).elim
            (fun hE => by
              subst hE; have hj0 : j = 0 := by simpa [g', mkReallocMremapGroup] using hj
              subst hj0; simp only [g', mkReallocMremapGroup, List.getElem_cons_zero] at hSl; cases hSl; rfl)
            (fun ⟨hNeM, hxO⟩ => False.elim (hNewPNotOther x hxO hNeM j hj m ef hSl))⟩
      · by_cases hqOld : q = p
        · subst hqOld; simp only [hqNew, ↓reduceIte, reduceCtorEq, false_iff]
          rintro ⟨x, hx, j, hj, ef, hSl⟩
          rcases hGsCases x hx with rfl | ⟨hNeM, hxO⟩
          · have hj0 : j = 0 := by simpa [g', mkReallocMremapGroup] using hj
            subst hj0; simp only [g', mkReallocMremapGroup, List.getElem_cons_zero] at hSl
            injection hSl with h1 _ _; exact hqNew h1.symm
          · exact hNeM (congrArg GroupDesc.metaPtr (liveUser_ptr_unique hwf hg hxO hIdx0 hj hSlot0 hSl).1)
        · simp only [hqNew, hqOld, ↓reduceIte]; rw [hwf.liveMap_wf q m]
          exact ⟨fun ⟨x, hx, j, hj, ef, hSl⟩ =>
              if hE : x.metaPtr = g.metaPtr then by
                have r := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE; subst r
                have hj0 : j = 0 := by omega
                subst hj0; rw [hSlot0] at hSl; injection hSl with h1 _ _; exact False.elim (hqOld h1.symm)
              else ⟨x, hGsKeep x hx hE, j, hj, ef, hSl⟩,
            fun ⟨x, hx, j, hj, ef, hSl⟩ => (hGsCases x hx).elim
              (fun hE => by
                subst hE; have hj0 : j = 0 := by simpa [g', mkReallocMremapGroup] using hj
                subst hj0; simp only [g', mkReallocMremapGroup, List.getElem_cons_zero] at hSl
                injection hSl with h1 _ _; exact False.elim (hqNew h1.symm))
              (fun ⟨_, hxO⟩ => ⟨x, hxO, j, hj, ef, hSl⟩)⟩
    live_le_peak := by simp only [bf, mallocngReallocBudget, ↓reduceIte, MallocngMinBlockCost]; omega
    effCost_le_live := by
      have := hwf.effCost_le_live
      simp only [bf, mallocngReallocBudget, ↓reduceIte, MallocngMinBlockCost] at hEffSumEq hMaxLeOld hOldEfTot this ⊢
      dsimp only [newEff] at hEffSumEq; simp only [MallocngMinBlockCost] at hEffSumEq; omega
    meta_pages_bound := ⟨Nat.le_trans hwf.meta_pages_bound.1
      (Nat.add_le_add_left (Nat.div_le_div_right (by simp [bf, mallocngReallocBudget]; omega)) 2),
      hwf.meta_pages_bound.2.1, hwf.meta_pages_bound.2.2⟩
    empty_groups_bound := by
      have hNE : ¬ g'.isEmpty = true := fun hE => by
        have hA := List.all_eq_true.mp hE (.liveUser newP newSz newEff) (by simp [g', mkReallocMremapGroup])
        simp [SlotState.isFree] at hA
      intro x hx hEmp; rcases hGsCases x hx with rfl | ⟨_, hxO⟩
      · exact False.elim (hNE hEmp)
      · obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hwf.empty_groups_bound x hxO hEmp
        exact ⟨e1, e2, e3, e4, e5, fun y hy hEy hSc => (hGsCases y hy).elim
          (fun r => False.elim (hNE (r ▸ hEy))) (fun ⟨_, hyO⟩ => e6 y hyO hEy hSc), e7⟩
    masterDom_wf := by
      have hRestDisjNB : ∀ a ∈ st.masterDom, ¬ InRegion g.mem (g.maplen * 4096) a → ¬ InRegion newBase needed a := by
        intro a haDom hNOG hNB
        obtain ⟨r, hr, haR⟩ := hwf.masterDom_wf.2.2 a haDom
        unfold dynamicRootRegions at hr
        rcases List.mem_append.mp hr with h123 | hRgL
        · rcases List.mem_append.mp h123 with h12 | hAp
          · rcases List.mem_append.mp h12 with hMa | hGp
            · obtain ⟨ma, hma, rfl⟩ := List.mem_map.mp hMa
              exact not_both_inRegion_of_disjointRegions (hDisjMa ma hma) haR hNB
            · obtain ⟨gp, hgp, rfl⟩ := List.mem_map.mp hGp
              exact not_both_inRegion_of_disjointRegions (hDisjGp gp hgp) haR hNB
          · obtain ⟨ap, hap, rfl⟩ := List.mem_map.mp hAp
            exact not_both_inRegion_of_disjointRegions (hDisjAp ap hap) haR hNB
        · obtain ⟨rg, hrgF, rfl⟩ := List.mem_map.mp hRgL
          obtain ⟨hrg, hMpB⟩ := List.mem_filter.mp hrgF
          by_cases hE : rg.metaPtr = g.metaPtr
          · have r := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hrg hg hE; subst r; exact hNOG haR
          · exact not_both_inRegion_of_disjointRegions (hDisjRg rg hrg (of_decide_eq_true hMpB) hE) haR hNB
      refine ⟨List.nodup_append.mpr ⟨hwf.masterDom_wf.1.filter _, nodup_rangeAddrs newBase (by omega),
          fun a ha b hb hEq => by
            subst hEq; obtain ⟨haD, haF⟩ := List.mem_filter.mp ha
            exact hRestDisjNB a haD (by simpa using haF) ((mem_rangeAddrs_iff_inRegion newBase (by omega) a).mp hb)⟩,
        fun a hOwn => ?_, fun a ha => ?_⟩
      · by_cases haNB : InRegion newBase needed a
        · exact List.mem_append_right _ ((mem_rangeAddrs_iff_inRegion newBase (by omega) a).mpr haNB)
        · have hDisj123 : ∀ iv ∈ st.metaAreas.map (fun m => (m.base, 4096)) ++
              st.guardPages.map (fun gp => (gp, 4096)) ++ st.availMetaPages.map (fun ap => (ap, 4096)),
              InRegion iv.1 iv.2 a → ¬ InRegion g.mem (g.maplen * 4096) a :=
            fun iv hiv haIv hOG => not_both_inRegion_of_disjointRegions (hCross123Old iv hiv _ hGMemRg) haIv hOG
          have hDisjOthRg : ∀ x ∈ st.groups, 0 < x.maplen → x.metaPtr ≠ g.metaPtr →
              InRegion x.mem (x.maplen * 4096) a → ¬ InRegion g.mem (g.maplen * 4096) a := fun x hx hMp hNe haX hOG =>
            not_both_inRegion_of_disjointRegions
              (pairwiseDisjoint_map_ne (f := fun z : GroupDesc => (z.mem, z.maplen * 4096)) hPRgOld
                (List.mem_filter.mpr ⟨hx, decide_eq_true hMp⟩) (List.mem_filter.mpr ⟨hg, decide_eq_true hMpG⟩)
                (fun hM => hNe (mem_groups_eq_of_mem hwf.groups_nodup.2 hx hg hM ▸ rfl))) haX hOG
          have ⟨hNOG, haDom⟩ : ¬ InRegion g.mem (g.maplen * 4096) a ∧ a ∈ st.masterDom := by
            rcases hOwn with hRw | hPn | hMp
            · have ⟨hNOG, hSrcOld⟩ : ¬ InRegion g.mem (g.maplen * 4096) a ∧
                  ((∃ ma ∈ st.metaAreas, InRegion ma.base 4096 a) ∨
                   (∃ x ∈ st.groups, 0 < x.maplen ∧ InRegion x.mem (x.maplen * 4096) a)) := by
                rcases hRw.1 with ⟨ma, hma, haMa⟩ | ⟨x, hx, hMpX, haX⟩
                · exact ⟨hDisj123 _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma))) haMa,
                    Or.inl ⟨ma, hma, haMa⟩⟩
                · rcases hGsCases x hx with rfl | ⟨hNe, hxO⟩
                  · exact False.elim (haNB (by rwa [hg'MemEq, hg'LenEq] at haX))
                  · exact ⟨hDisjOthRg x hxO hMpX hNe haX, Or.inr ⟨x, hxO, hMpX, haX⟩⟩
              have hCarvOld : ¬ CarvedUserByte st a := fun ⟨x, hx, s, hs, hSub⟩ =>
                if hE : x.metaPtr = g.metaPtr then by
                  have r := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hx hg hE; subst r
                  rw [hGSlotsSingleton, List.mem_singleton] at hs; subst hs; exact hNOG (hPInOldG a hSub)
                else hRw.2.1 ⟨x, hGsKeep x hx hE, s, hs, hSub⟩
              exact ⟨hNOG, hwf.masterDom_wf.2.1 a (Or.inl ⟨hSrcOld, hCarvOld, by simp [CarvedMetaByte, hResNil]⟩)⟩
            · refine ⟨?_, hwf.masterDom_wf.2.1 a (Or.inr (Or.inl hPn))⟩
              rcases hPn with ⟨gp, hgp, haGp⟩ | ⟨ap, hap, haAp⟩
              · exact hDisj123 _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hgp))) haGp
              · exact hDisj123 _ (List.mem_append_right _ (List.mem_map_of_mem hap)) haAp
            · rcases hMp with ⟨mb, hmb, haMb⟩ | ⟨mg, hmg, haMg⟩ | ⟨ap, hap, haAp⟩ | ⟨x, hx, hMpX, haX⟩
              · have hmb' : mb ∈ st.mmapMetaAreas := hmb
                have hmb0 : mb ∈ st.mmapMetaAreas := hmb
                rw [hwf.brk_mode_wf.2.1] at hmb0
                obtain ⟨ma, hma, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hmb0).1
                exact ⟨hDisj123 _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hma))) haMb,
                  hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inl ⟨ma.base, hmb', haMb⟩)))⟩
              · have hmg' : mg ∈ st.mmapGuardPages := hmg
                have hmg0 : mg ∈ st.mmapGuardPages := hmg
                rw [hwf.brk_mode_wf.2.2.1] at hmg0
                exact ⟨hDisj123 _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mp hmg0).1))) haMg,
                  hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inr (Or.inl ⟨mg, hmg', haMg⟩))))⟩
              · exact ⟨hDisj123 _ (List.mem_append_right _ (List.mem_map_of_mem hap)) haAp,
                  hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ap, hap, haAp⟩)))))⟩
              · rcases hGsCases x hx with rfl | ⟨hNe, hxO⟩
                · exact False.elim (haNB (by rwa [hg'MemEq, hg'LenEq] at haX))
                · exact ⟨hDisjOthRg x hxO hMpX hNe haX,
                    hwf.masterDom_wf.2.1 a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hxO, hMpX, haX⟩)))))⟩
          exact List.mem_append_left _ (List.mem_filter.mpr ⟨haDom, by simp [hNOG]⟩)
      · rcases List.mem_append.mp ha with haR | haNB
        · obtain ⟨haD, haF⟩ := List.mem_filter.mp haR
          have hNOG : ¬ InRegion g.mem (g.maplen * 4096) a := by simpa using haF
          obtain ⟨r, hr, haIn⟩ := hwf.masterDom_wf.2.2 a haD
          unfold dynamicRootRegions at hr
          rcases List.mem_append.mp hr with h123 | hRgL
          · exact ⟨r, by rw [hDynSt']; exact List.mem_append_left _ h123, haIn⟩
          · obtain ⟨rg, hrgF, rfl⟩ := List.mem_map.mp hRgL
            obtain ⟨hrg, hMpB⟩ := List.mem_filter.mp hrgF
            have hNe : rg.metaPtr ≠ g.metaPtr := fun hE => by
              have r := mem_groups_eq_of_metaPtr hwf.groups_nodup.1 hrg hg hE; subst r; exact hNOG haIn
            exact ⟨(rg.mem, rg.maplen * 4096), by
              rw [hDynSt']
              exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hGsKeep rg hrg hNe, hMpB⟩)),
              haIn⟩
        · exact ⟨(g'.mem, g'.maplen * 4096), by
            rw [hDynSt']
            exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_filter.mpr ⟨hg'In, decide_eq_true hg'MpPos⟩)),
            by rw [hg'MemEq, hg'LenEq]; exact (mem_rangeAddrs_iff_inRegion newBase (by omega) a).mp haNB⟩
  }

end VerifiedLibraries.Mallocng.Proofs
